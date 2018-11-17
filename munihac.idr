import Data.Vect

NatOrError : Nat -> Type 
NatOrError Z = String  
NatOrError (S k) = Nat 


divide : Nat -> (divisor:Nat) -> NatOrError divisor 
divide k Z = "Division by 0 is not defined" 
divide k (S j) = div k (S j)  

{-
data Vect : (n:Nat) -> (a: Type) -> Type where
  VNil : Vect 0 a
  VCons : (head : a) -> (tail : Vect k a) -> Vect (S k) a

vtake : {m:Nat} -> (n:Nat) -> Vect (n+m) a -> Vect n a 
vtake Z x = VNil
vtake (S k) (VCons head tail) = VCons head (vtake k tail)


vtake2 : (n:Nat) -> Vect m a -> { auto prf : LTE n m } -> Vect n a 
vtake2 Z x = VNil
vtake2 (S k) (VCons head tail) {prf = (LTESucc y)} = VCons head (vtake2 k tail)

vdrop : (n:Nat) -> Vect (n+m) a -> Vect m a 
vdrop Z x = x
vdrop (S k) (VCons head tail) = vdrop k tail
-}

Fun : Nat -> Type
Fun Z = Nat 
Fun (S k) = Nat -> (Fun k) 

adder : ( n:Nat ) -> (acc:Nat) -> Fun n
adder Z acc = acc
adder (S k) acc = \x => adder k (acc + x)

{-
vappend : Vect n a -> Vect m a -> Vect (n+m) a 
vappend VNil y = y
vappend (VCons head tail) y = VCons head (vappend tail y)
-}

Matrix : Nat -> Nat -> Type 
Matrix k j = Vect k (Vect j Int)

zipWithV : (f : a -> b -> c) -> Vect n a -> Vect n b -> Vect n c
zipWithV f [] [] = []
zipWithV f (x :: xs) (y :: ys) = f x y :: zipWithV f xs ys

whatever : (row : Vect m Int) -> (transposed : Matrix m len) -> Vect m (Vect (S len) Int)
whatever row transposed = zipWithV (::) row transposed 

transposeMat : Matrix n m -> Matrix m n 
transposeMat {m} [] = replicate m [] 
transposeMat (row :: rows) = let transposed = transposeMat rows in
                             whatever row transposed 

vectMult : Vect n Int -> Vect n Int -> Int 
vectMult [] [] = 0 
vectMult (x :: xs) (y :: ys) = x * y + vectMult xs ys  


multVectMat : (row : Vect m Int) -> (transposed : Matrix k m) -> Vect k Int
multVectMat row [] = []
multVectMat row (x :: xs) = vectMult row x :: multVectMat row xs

multMat : Matrix n m -> Matrix m k -> Matrix n k 
multMat [] [] = []
multMat [] (x :: xs) = []
multMat (row :: rows) y = let transposed = transposeMat y in
                       multVectMat row transposed :: multMat rows y --?x --multVect row transposed

idRow : (i:Nat) -> { auto prf: LT i n } ->  Vect n Int 
idRow {n = Z} i = []
idRow {n = (S k)} Z = 1 :: replicate k 0 
idRow {n = (S k)} (S j) {prf = (LTESucc x)} = 0 :: idRow j

idMatHelper : (i:Nat) -> ( prf : LTE i n ) ->  Matrix i n
idMatHelper Z LTEZero = []
idMatHelper (S left) (LTESucc x) = ?idMatHelper_rhs_2


--mult : Matrix 2 4 -> Matrix 4 3 -> Matrix 2 3 
