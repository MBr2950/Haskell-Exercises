

------------------------- Auxiliary functions

merge :: Ord a => [a] -> [a] -> [a]
merge xs [] = xs
merge [] ys = ys
merge (x:xs) (y:ys)
    | x == y    = x : merge xs ys
    | x <= y    = x : merge xs (y:ys)
    | otherwise = y : merge (x:xs) ys

minus :: Ord a => [a] -> [a] -> [a]
minus xs [] = xs
minus [] ys = []
minus (x:xs) (y:ys)
    | x <  y    = x : minus    xs (y:ys)
    | x == y    =     minus    xs    ys
    | otherwise =     minus (x:xs)   ys

variables :: [Var]
variables = [ [x] | x <- ['a'..'z'] ] ++ [ x : show i | i <- [1..] , x <- ['a'..'z'] ]

removeAll :: [Var] -> [Var] -> [Var]
removeAll xs ys = [ x | x <- xs , not (elem x ys) ]

fresh :: [Var] -> Var
fresh = head . removeAll variables


-- - - - - - - - - - - -- Terms

type Var = String

data Term =
    Variable Var
  | Lambda   Var  Term
  | Apply    Term Term

pretty :: Term -> String
pretty = f 0
    where
      f i (Variable x)   = x
      f i (Lambda x m)   = if elem i [2,3] then "(" ++ s ++ ")" else s where s = "\\" ++ x ++ ". " ++ f 1 m 
      f i (Apply  m n)   = if elem i   [3] then "(" ++ s ++ ")" else s where s = f 2 m ++ " " ++ f 3 n

instance Show Term where
  show = pretty

-- - - - - - - - - - - -- Numerals


numeral :: Int -> Term
numeral i = Lambda "f" (Lambda "x" (numeral' i))
  where
    numeral' i
      | i <= 0    = Variable "x"
      | otherwise = Apply (Variable "f") (numeral' (i-1))


-- - - - - - - - - - - -- Renaming, substitution, beta-reduction


used :: Term -> [Var]
used (Variable x) = [x]
used (Lambda x m) = [x] `merge` used m
used (Apply  m n) = used n `merge` used m


rename :: Var -> Var -> Term -> Term
rename y z (Variable x)
    | y == x    = Variable z
    | otherwise = Variable x
rename y z (Lambda x m)
    | y == x    = Lambda x m
    | otherwise = Lambda x (rename y z m)
rename y z (Apply m n) = Apply (rename y z m) (rename y z n)

substitute :: Var -> Term -> Term -> Term
substitute y p (Variable x)
    | y == x    = p
    | otherwise = Variable x
substitute y p (Lambda x m)
    | y == x    = Lambda x m
    | otherwise = Lambda z (substitute y p (rename x z m))
    where z = fresh (used p `merge` used m `merge` [x,y])
substitute y p (Apply m n) = Apply (substitute y p m) (substitute y p n)

beta :: Term -> [Term]
beta (Apply (Lambda x m) n) =
  [substitute x n m] ++ 
  [Apply (Lambda x m') n  | m' <- beta m] ++
  [Apply (Lambda x m ) n' | n' <- beta n]
beta (Variable _) = []
beta (Lambda x m) = [Lambda x m' | m' <- beta m]
beta (Apply  m n) =
  [Apply m' n  | m' <- beta m] ++
  [Apply m  n' | n' <- beta n]


-- - - - - - - - - - - -- Normalize


normalize :: Term -> IO ()
normalize m = do
  print m
  let ms = beta m
  if null ms then
    return ()
  else
    normalize (head ms)


------------------------- Assignment 1: Combinators

infixl 5 :@


data Combinator = 
    Combinator :@ Combinator
    |  V Var
    |  I
    |  K
    |  S
    -- |  :@ Combinator Combinator


example1 :: Combinator
example1 = S :@ K :@ K :@ V "x"

example2 :: Combinator
example2 = S :@ (K :@ K) :@ I :@ V "x" :@ V "y"

example3 :: Combinator
example3 = S :@ V "x" :@ I :@ V "z"

example4 :: Combinator
example4 = K :@ I :@ (S :@ I :@ K)

n1 :: Term
n1 = Apply (Lambda "x" (Variable "x")) (Variable "y")

n2 :: Term
n2 = Lambda "x" (Apply (Lambda "y" (Variable "x")) (Variable "z"))

n3 :: Term
n3 = Apply (Lambda "x" (Lambda "y" (Apply (Variable "x") (Variable "y")))) n1

n4 :: Var
n4 = "x"


-- - - - - - - - - - - -- show, parse

instance Show Combinator where
  show = f 0
    where
      f _ I = "I"
      f _ K = "K"
      f _ S = "S"
      f _ (V s) = s
      f i (c :@ d) = if i == 1 then "(" ++ s ++ ")" else s where s = f 0 c ++ " " ++ f 1 d

parse :: String -> Combinator
parse s = down [] s
  where
    down :: [Maybe Combinator] -> String -> Combinator
    down cs (' ':str) = down cs str
    down cs ('(':str) = down (Nothing : cs) str
    down cs ('I':str) = up cs I str
    down cs ('K':str) = up cs K str
    down cs ('S':str) = up cs S str
    down cs ( c :str) = up cs (V [c]) str
    up :: [Maybe Combinator] -> Combinator -> String -> Combinator
    up    []  c [] = c 
    up (Just c  : cs) d      str  = up cs (c:@d) str
    up (Nothing : cs) d (')':str) = up cs     d  str
    up            cs  d      str  = down (Just d : cs) str


-- - - - - - - - - - - -- step, run

step :: Combinator -> [Combinator]
step (S :@ x :@ y :@ z)       = [x :@ z :@ (y :@ z)] ++ step x ++ step y ++ step z
step (K :@ x :@ y)            = [x] ++ step x ++ step y
step (I :@ x)                 = [x] ++ step x
step (V _)                    = []
step otherwise                = []



run :: Combinator -> IO ()
run x  = do
  print x
  let xs = step x
  if null xs then
    return ()
  else
    run (head xs)

------------------------- Assignment 2: Combinators to Lambda-terms

toLambda :: Combinator -> Term
toLambda (V x)     = Variable x
toLambda (I)       = Lambda "x" (Variable "x")
toLambda (K)       = Lambda "x" (Lambda "y" (Variable "x"))
toLambda (S)       = Lambda ("x") (Lambda ("y") (Lambda ("z") (Apply (Apply (Variable "x") (Variable "z")) (Apply (Variable "y") (Variable "z")))))
toLambda (x :@ y)  = Apply (toLambda x) (toLambda y)



------------------------- Assignment 3: Lambda-terms to Combinators

equality :: Var -> Combinator -> Bool
equality x (V y)
  | x == y     = True
  | otherwise  = False
equality x y   = False

abstract :: Var -> Combinator -> Combinator
abstract x (a :@ b)  = S :@ (abstract x a) :@ (abstract x b)
abstract x y
  | equality x y     = I
  | otherwise        = K :@ y

toCombinator :: Term -> Combinator
toCombinator (Variable x)  = V x
toCombinator (Lambda x y)  = abstract x (toCombinator y)
toCombinator (Apply x y)   = (toCombinator x) :@ (toCombinator y)

------------------------- Assignment 4: Estimating growth

sizeL :: Term -> Int
sizeL (Variable x)  = 1
sizeL (Lambda x y)  = 1 + sizeL y
sizeL (Apply x y)   = 1 + (sizeL x) + (sizeL y)

sizeC :: Combinator -> Int
sizeC (V x)     = 1
sizeC (I)       = 1
sizeC (K)       = 1
sizeC (S)       = 1
sizeC (x :@ y)  = 1 + (sizeC x) + (sizeC y)

series :: Int -> Term
series 0  = Lambda "a" (Variable "a")
series x  = Apply (Lambda (toLetter x) (series (x - 1))) (Variable (toLetter x))

toLetter :: Int -> String
toLetter x
  | x > 25     = toLetter (x - 26)
  | otherwise  = [toEnum (97 + x)]


------------------------- Assignment 5: Optimised interpretation

data Complexity = Linear | Quadratic | Cubic | Exponential

abstr :: Var -> Combinator -> Combinator
abstr x (a :@ b)  = S :@ (abstr x a) :@ (abstr x b)
abstr x y
  | equality x y     = I
  | otherwise        = K :@ y

comb :: Term -> Combinator
comb  = toCombinator
-- comb (Variable x)  = V x
-- comb (Lambda x y)  = abstr x (comb y)
-- comb (Apply x y)   = (comb x) :@ (comb y)

claim :: Complexity
claim = Exponential