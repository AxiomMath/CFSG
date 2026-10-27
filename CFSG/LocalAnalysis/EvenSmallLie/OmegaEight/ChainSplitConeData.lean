module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainZ4Data
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ShapeCPrimeData

public section

namespace CFSG.EvenSmallLie.OmegaEight.Chain

open CFSG.EvenSmallLie.UnitarySix.YamadaPar Stage1

@[expose] def tauRows : Array ℕ := #[33, 2, 4, 8, 16, 32]

@[expose] def coneN : Array ℕ := #[32, 0, 0, 0, 0, 0]

@[expose] def coneWords : Eps → List (List ℕ)
  | .plus => [[2, 3, 3, 2], [5, 4, 1, 0, 3, 2, 0]]
  | .minus => [[3], [4, 3, 1, 2, 1, 0]]

@[expose] def coneK : Eps → ℕ → Bool → Array ℕ
  | .plus, 0, false => #[12, 0, 32, 32, 0, 0]
  | .plus, 0, true => #[1, 16, 8, 4, 2, 32]
  | .plus, 1, false => #[42, 32, 32, 0, 0, 0]
  | .plus, 1, true => #[27, 56, 48, 62, 20, 32]
  | .minus, 0, false => #[40, 32, 32, 0, 0, 0]
  | .minus, 0, true => #[33, 58, 20, 8, 16, 32]
  | .minus, 1, false => #[52, 32, 32, 0, 0, 0]
  | .minus, 1, true => #[41, 58, 38, 52, 62, 32]
  | _, _, _ => zero6

@[expose] def coneDual : Eps → Bool → Bool → Bool → Array ℕ × Array ℕ × Array ℕ
  | .plus, false, false, false => (#[0, 1, 0, 0, 0, 3], #[0, 1, 2, 2, 0, 3], #[0, 3, 1, 4, 0, 7])
  | .plus, false, false, true => (#[0, 0, 0, 0, 0, 16], #[0, 0, 0, 0, 0, 0], #[1, 0, 0, 0, 0, 0])
  | .plus, false, true, false => (#[1, 0, 0, 0, 0, 12], #[1, 0, 0, 0, 0, 0], #[0, 0, 0, 0, 0, 0])
  | .plus, false, true, true => (#[1, 0, 0, 0, 0, 12], #[1, 0, 0, 0, 0, 0], #[0, 0, 0, 0, 0, 0])
  | .plus, true, _, _ => (#[0, 2, 0, 0, 0, 0], zero6, zero6)
  | .minus, false, false, false =>
      (#[0, 1, 1, 0, 0, 19], #[0, 0, 0, 6, 6, 3], #[0, 3, 7, 5, 1, 21])
  | .minus, false, false, true => (#[1, 0, 0, 0, 0, 28], #[0, 0, 0, 0, 0, 0], #[1, 0, 0, 0, 0, 0])
  | .minus, false, true, false => (#[1, 0, 0, 0, 0, 8], #[1, 0, 0, 0, 0, 0], #[0, 0, 0, 0, 0, 0])
  | .minus, false, true, true => (#[1, 0, 0, 0, 0, 8], #[1, 0, 0, 0, 0, 0], #[0, 0, 0, 0, 0, 0])
  | .minus, true, _, _ => (#[0, 2, 0, 0, 0, 0], zero6, zero6)

@[expose] def btrace (M : Array ℕ) : Bool :=
  (M.getD 0 0).testBit 0 ^^ (M.getD 1 0).testBit 1 ^^ (M.getD 2 0).testBit 2 ^^
    (M.getD 3 0).testBit 3 ^^ (M.getD 4 0).testBit 4 ^^ (M.getD 5 0).testBit 5

@[expose] def anti (Z A : Array ℕ) : Array ℕ := bxor 6 (bmul 6 6 Z A) (bmul 6 6 A Z)

@[expose] def dualCheck (ε : Eps) (s₀ s₁ s₂ : Bool) : Bool :=
  let Z := coneDual ε s₀ s₁ s₂
  let O₁ := wordRows ε ((coneWords ε).getD 0 [])
  let O₂ := wordRows ε ((coneWords ε).getD 1 [])
  let C₀ := if s₀ then bxor 6 coneN id6 else coneN
  bxor 6 (anti Z.1 tauRows) (bxor 6 (anti Z.2.1 O₁) (anti Z.2.2 O₂)) == zero6 &&
    (btrace (bmul 6 6 Z.1 C₀) ^^ btrace (bmul 6 6 Z.2.1 (coneK ε 0 s₁)) ^^
      btrace (bmul 6 6 Z.2.2 (coneK ε 1 s₂))) == true

@[expose] def coneGenCheck (ε : Eps) (j : ℕ) : Bool :=
  let w := (coneWords ε).getD j []
  let O := wordRows ε w
  let Ot := prod4 ε w
  let T := lift2 tauRows
  bmul 6 6 O tauRows == bmul 6 6 tauRows O && bmulVec 6 6 O 1 == 1 &&
    sub4 (mul4 T Ot) (mul4 Ot T) == add4 (lift2 (coneK ε j false)) (lift2 (coneK ε j false)) &&
    add4 (mul4 T Ot) (mul4 Ot T) == add4 (lift2 (coneK ε j true)) (lift2 (coneK ε j true))

@[expose] def splitConeCheck (ε : Eps) : Bool :=
  tauRows == CPrime.reflRows ε 1 &&
    mul4 (lift2 tauRows) (lift2 tauRows) == add4 one4 (add4 (lift2 coneN) (lift2 coneN)) &&
    coneGenCheck ε 0 && coneGenCheck ε 1 &&
    [false, true].all fun s₀ => [false, true].all fun s₁ => [false, true].all fun s₂ =>
      dualCheck ε s₀ s₁ s₂

end CFSG.EvenSmallLie.OmegaEight.Chain
