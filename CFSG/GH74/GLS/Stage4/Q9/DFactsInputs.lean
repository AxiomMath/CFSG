
module

public import CFSG.GH74.GLS.Stage4.Q9.ModelBaseBase
public meta import CFSG.GH74.GLS.Stage4.Q9.ModelBaseBase
public meta import Mathlib

public section

namespace CFSG.GH74.GLS.Stage4.Q9

local notation "𝕄" => Matrix (Fin 2) (Fin 2) F9

namespace DFacts

@[expose] def f9List : List F9 :=
  [⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 2⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 2⟩, ⟨2, 0⟩, ⟨2, 1⟩, ⟨2, 2⟩]

@[expose] def sl2List : List SL2 :=
  f9List.flatMap fun a => f9List.flatMap fun b => f9List.flatMap fun c =>
    f9List.filterMap fun d =>
      if h : a * d - b * c = 1 then
        some ⟨!![a, b; c, d], by rw [Matrix.det_fin_two_of]; exact h⟩
      else none

@[macro_inline, expose] def impB (a b : Bool) : Bool :=
  match a with
  | true => b
  | false => true

@[expose] def invSL (g : SL2) : SL2 :=
  ⟨!![(g : 𝕄) 1 1, -(g : 𝕄) 0 1; -(g : 𝕄) 1 0, (g : 𝕄) 0 0], by
    have h := g.det_coe
    rw [Matrix.det_fin_two] at h
    rw [Matrix.det_fin_two_of]
    linear_combination h⟩

@[expose] def cent (M : SL2) : List SL2 := sl2List.filter fun N => M * N == N * M

@[expose] def chkSqOne : Bool := sl2List.all fun M => impB (M * M == 1) (M == 1 || M == minusOne)

@[expose] def chkCenter : Bool :=
  sl2List.all fun M => impB (sl2List.all fun N => M * N == N * M) (M == 1 || M == minusOne)

@[expose] def chkQ8 : Bool :=
  sl2List.all fun p => impB (p * p == minusOne) <|
    sl2List.all fun q => impB (q * q == minusOne) <| impB (q * p == p * minusOne * q) <|
      sl2List.any fun r => (r * p == q * r || r * p == q * minusOne * r) &&
        (r * q == p * q * r || r * q == p * q * minusOne * r)

@[expose] def chkConjFixed5 : Bool :=
  sl2List.all fun M => impB (ordL (innerL M) == 5) <|
    sl2List.any fun k => sigmaAut (k * M * invSL k) == k * M * invSL k

@[expose] def chkCent5 : Bool :=
  sl2List.all fun M => impB (ordL (innerL M) == 5) ((cent M).toFinset.card == 10)

@[expose] def chkCent3 : Bool :=
  sl2List.all fun M => impB (ordL (innerL M) == 3) ((cent M).toFinset.card == 18)

@[expose] def chkCentOdd5 : Bool :=
  sl2List.all fun M => impB (ordL (innerL M) == 5) <|
    (cent M).all fun N => ordL (innerL N) % 2 == 0 || N == 1 || N == M || N == M * M ||
      N == M * M * M || N == M * M * M * M

@[expose] def chkCentOdd3 : Bool :=
  sl2List.all fun M => impB (ordL (innerL M) == 3) <|
    (cent M).all fun N => ordL (innerL N) % 2 == 0 || ordL (innerL N) == 1 || ordL (innerL N) == 3

@[expose] def chkSigmaNotConj : Bool :=
  sl2List.all fun M => impB (ordL (innerL M) == 3) <|
    sl2List.all fun k => k * sigmaAut M != M * k

@[expose] def chkInvert3 : Bool :=
  sl2List.all fun M => impB (ordL (innerL M) == 3) <|
    sl2List.any fun k => k * k == minusOne && k * M == invSL M * k

@[expose] def chkNo16 : Bool := sl2List.all fun M => ordL (innerL M) != 16

@[expose] def inQ16b (g : SL2) : Bool :=
  ((g : 𝕄) 0 1 == 0 && (g : 𝕄) 1 0 == 0) || ((g : 𝕄) 0 0 == 0 && (g : 𝕄) 1 1 == 0)

@[expose] def chkQ16 : Bool :=
  sl2List.all fun s => impB (inQ16b s) <|
    impB (sl2List.all fun w => impB (inQ16b w) (s * w == w * s)) (s == 1 || s == minusOne)

@[expose] def chkQ16card : Bool := (sl2List.filter inQ16b).toFinset.card == 16

end DFacts

end CFSG.GH74.GLS.Stage4.Q9
