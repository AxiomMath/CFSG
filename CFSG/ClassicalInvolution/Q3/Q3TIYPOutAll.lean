module

public import CFSG.ClassicalInvolution.Q3.Q3TIYPOutGlue
public import CFSG.ClassicalInvolution.Q3.Q3TIYPOutSp
public import CFSG.ClassicalInvolution.Q3.Q3TIYPOutL
public import CFSG.ClassicalInvolution.Q3.Q3TIYPOutU
public import CFSG.ClassicalInvolution.Q3.Q3TLKOdd

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TIY

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W CFSG.ClassicalInvolution.Q3.Q3TLK
open CFSG.ClassicalInvolution.RouteD.TwinY (IsTwinAt TwinElt TwinElt.u)
open CFSG.ClassicalInvolution.Q3 (CompData IsClassicalMember3)


theorem sqDichotomyC_small {t : StatedLieTag} {n : ℕ} (hadm : StatedLieAdmissible t n 3 1)
    (hsmall : (t = .PSp ∧ n = 2) ∨ (t = .PSL ∧ n = 4) ∨ (t = .PSU ∧ n = 4)) :
    SqDichotomyC (CompData.model t n) := by
  rcases hsmall with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact sqDichotomyC_psp2
  · exact sqDichotomyC_psl4 hadm
  · exact sqDichotomyC_psu4 hadm

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {K T : Subgroup G} {z : G}

theorem false_of_small_component3 (h3 : OddThreeFreeInput) (hnab : ∃ x y : G, x * y ≠ y * x)
    (hR : RouteD3Setup K z)
    (hshape : LocalShapeC3 2 (CompData.model .PSp 2) (conjClass3 K) z)
    (hT : IsTwinAt (conjClass3 K) K T z) (clsT : IsClassicalMember3 T z) (e : TwinElt K T z)
    (hP1 : LocalOddCentral (conjClass3 K) {e.u}) (hO3 : LocalOddThreeFree3 (conjClass3 K) e.u)
    {ι : Type}
    (D : LieSystemData3 ι (locQuot (conjClass3 K) e.u) (locFamily (conjClass3 K) e.u)) (i : ι)
    (hone : ∀ j : ι, j = i) {t' : StatedLieTag} {n' : ℕ}
    (hk : D.kind i = CompData.model t' n') (hadm : StatedLieAdmissible t' n' 3 1)
    (hsmall : (t' = .PSp ∧ n' = 2) ∨ (t' = .PSL ∧ n' = 4) ∨ (t' = .PSU ∧ n' = 4)) : False := by
  have hne : ¬ (t' = .PSL ∧ n' = 2) := by
    rintro ⟨h1, h2⟩
    rcases hsmall with ⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩
    · rw [h1] at h
      exact absurd h (by decide)
    · omega
    · rw [h1] at h
      exact absurd h (by decide)
  have hft : ModelFacts.IsFundTag t' := by
    rcases hsmall with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> trivial
  have hnc : ∀ R ∈ (D.kind i).fund, ∀ r ∈ R, r ∈ Subgroup.center (D.kind i).G → r = 1 := by
    rw [hk]
    exact fundNoncentral_model3 hft hadm hne
  have hdich : SqDichotomyC (D.kind i) := by
    rw [hk]
    exact sqDichotomyC_small hadm hsmall
  exact false_of_sqDichotomy3 h3 hnab hR hshape hT clsT e hP1 hO3 D i hone hnc hdich

end CFSG.ClassicalInvolution.Q3.Q3TIY
