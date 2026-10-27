module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24ThreeClasses
public import CFSG.Sporadic.Fi24.OctadAction
public import CFSG.ClassicalInvolution.Q3.Q3ZEval

public section

namespace CFSG.HardMathSupport.Dickson.I271.TabFi24

open CFSG.Sporadic.Fi24 (J jR cls)
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three (wordElt)
open CFSG.ClassicalInvolution.Q3.Q3Z

attribute [local instance] CFSG.Sporadic.Fi24.rAction

@[expose] def aWords : List (List ℕ) := [
  [25, 17, 25, 12, 15, 13, 16, 15, 10, 12, 12, 20],
  [24, 17, 24, 18, 14, 14, 21, 25, 13, 23, 8, 18, 14, 24, 18, 11],
  [25, 18, 22, 21, 14, 13, 23, 17, 20, 11, 24, 13, 22, 17],
  [19, 14, 20, 13, 17, 10, 17, 19, 21],
  [25, 16, 21, 16, 23, 14, 14, 14, 24, 15, 12, 12, 11, 12, 9, 24, 10],
  [25, 17, 25, 13, 18, 14, 14, 14, 11, 11, 22, 14, 13],
  [25, 18, 21, 17, 14, 12, 14, 21, 16, 15, 8, 13, 20, 8, 10],
  [16, 23, 18, 14, 14, 13, 23, 14, 24, 8, 12, 19, 21, 11, 13]]

@[expose] def q0 : Fin 306936 := ⟨0, by norm_num⟩

@[expose] def q1 : Fin 306936 := ⟨305530, by norm_num⟩


@[expose] noncomputable def aE (i : ℕ) : J := wordElt (aWords.getD i [])

@[expose] noncomputable def aSix (a b : ℕ) : Fin 6 → J :=
  ![aE (2 * a), aE (2 * a + 1), (aE (2 * a))⁻¹ * (aE (2 * b))⁻¹ * aE (2 * a) * aE (2 * b),
    ((aE (2 * a + 1))⁻¹ * (aE (2 * b + 1))⁻¹ * aE (2 * a + 1) * aE (2 * b + 1))⁻¹, aE (2 * b),
    aE (2 * b + 1)]

@[expose] def ThreeAFacts : Prop :=
  cls q0 * cls q1 ≠ cls q1 * cls q0 ∧
  (∀ k : Fin 306936, cls k * (cls q0 * cls q1) * cls k = (cls q0 * cls q1)⁻¹ →
    k = q0 ∨ k = q1 ∨ k = cls q0 • q1) ∧
  (∃ g : J, jR (g * wordElt [18] * g⁻¹) = cls q0 * cls q1) ∧
  (∀ i < 8, aE i ^ 3 = 1 ∧ aE i • q0 = q0 ∧ aE i • q1 = q1) ∧
  aE 0 ≠ 1 ∧ aE 2 ≠ 1 ∧
  (∀ e ∈ [(0, 1), (1, 2), (1, 3)], RelsHold (aSix e.1 e.2) a2Words) ∧
  (∀ e ∈ [(0, 2), (0, 3), (2, 3)], ∀ u < 2, ∀ v < 2,
    aE (2 * e.1 + u) * aE (2 * e.2 + v) = aE (2 * e.2 + v) * aE (2 * e.1 + u))

end CFSG.HardMathSupport.Dickson.I271.TabFi24
