module

public import CFSG.ClassicalInvolution.Q3.Q3TIYQRank
public import CFSG.ClassicalInvolution.Q3.Q3TIYQGlue
public import CFSG.ClassicalInvolution.Q3.Q3TIYQSq7
public import CFSG.ClassicalInvolution.Q3.Q3TIYQSl4Count
public import CFSG.ClassicalInvolution.Q3.Q3TIYPOutAll
public import CFSG.ClassicalInvolution.Q3.Q3URDict
public import CFSG.ClassicalInvolution.Q3.Q3URStd

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TIY

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W CFSG.ClassicalInvolution.Q3.Q3TLK
open CFSG.ClassicalInvolution.RouteD.TwinY (IsTwinAt TwinElt TwinElt.u TwinRow)
open CFSG.ClassicalInvolution.Q3 (CompData IsClassicalMember3)


variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {K T : Subgroup G} {z : G}

theorem false_of_small_component3_sl4 (h3 : OddThreeFreeInput)
    (hnab : ∃ x y : G, x * y ≠ y * x) (hR : RouteD3Setup K z)
    (hshape : LocalShapeC3 2 (CompData.model .PSL 4) (conjClass3 K) z)
    (hT : IsTwinAt (conjClass3 K) K T z) (clsT : IsClassicalMember3 T z) (e : TwinElt K T z)
    (hP1 : LocalOddCentral (conjClass3 K) {e.u}) (hO3 : LocalOddThreeFree3 (conjClass3 K) e.u)
    {ι : Type}
    (D : LieSystemData3 ι (locQuot (conjClass3 K) e.u) (locFamily (conjClass3 K) e.u)) (i : ι)
    (hone : ∀ j : ι, j = i) {t' : StatedLieTag} {n' : ℕ}
    (hk : D.kind i = CompData.model t' n') (hadm : StatedLieAdmissible t' n' 3 1)
    (hsmall : (t' = .PSp ∧ n' = 2) ∨ (t' = .PSL ∧ n' = 4) ∨ (t' = .PSU ∧ n' = 4) ∨
      (t' = .POmegaOdd ∧ n' = 3)) : False := by
  have hrow : TwinRow .PSL 4 := Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)
  have hne : ¬ (t' = .PSL ∧ n' = 2) := by
    rintro ⟨h1, h2⟩
    rcases hsmall with ⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · rw [h1] at h
      exact absurd h (by decide)
    · omega
    · rw [h1] at h
      exact absurd h (by decide)
    · rw [h1] at h
      exact absurd h (by decide)
  have hft : ModelFacts.IsFundTag t' := by
    rcases hsmall with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> trivial
  have hnc : ∀ R ∈ (D.kind i).fund, ∀ r ∈ R, r ∈ Subgroup.center (D.kind i).G → r = 1 := by
    rw [hk]
    exact fundNoncentral_model3 hft hadm hne
  have hfin : Finite (D.kind i).G := by
    rw [hk]
    exact ModelFacts.finite_modelUniv (t := t') (by norm_num) Nat.prime_three hft hadm
  have hbound : ∃ B, SqCntLe (D.kind i) B ∧ B < 162 := by
    rw [hk]
    rcases hsmall with h | h | h | ⟨rfl, rfl⟩
    · exact ⟨0, sqCntLe_of_sqDichotomy (sqDichotomyC_small hadm (Or.inl h)) 0, by norm_num⟩
    · exact ⟨0, sqCntLe_of_sqDichotomy (sqDichotomyC_small hadm (Or.inr (Or.inl h))) 0,
        by norm_num⟩
    · exact ⟨0, sqCntLe_of_sqDichotomy (sqDichotomyC_small hadm (Or.inr (Or.inr h))) 0,
        by norm_num⟩
    · exact ⟨90, sqCntLe_odd3, by norm_num⟩
  obtain ⟨B, hcnt, hB⟩ := hbound
  have h1 := ncard_le_of_sqCnt3 h3 hnab hrow hR hshape Q3P21.twinMFGenerationOn3_psl4 hT clsT e
    hP1 hO3 D i hone hnc hfin hcnt
  have h2 := card_fund_psl4_ge.trans (card_fund_le_big3 h3 hrow hR hshape hT)
  omega

theorem twinYSl4Small3_true : TwinYSl4Small3 := by
  intro h3 G _ _ _ hnab K z hR hshape T hT clsT e hP1 hO3 ι _ D hcard i t' n' hk hsmall
  obtain ⟨x₀, hx₀⟩ := Nat.card_eq_one_iff_exists.mp hcard
  have hone : ∀ j : ι, j = i := fun j => (hx₀ j).trans (hx₀ i).symm
  have hadm : StatedLieAdmissible t' n' 3 1 := by
    rcases hsmall with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Q3Z.statedLieAdmissible_psp2
    · exact Q3TC.statedLieAdmissible_sl4_three
    · exact ⟨Nat.prime_three, Nat.one_pos, by norm_num, by decide⟩
    · exact ⟨Nat.prime_three, le_rfl, le_rfl, by norm_num⟩
  exact false_of_small_component3_sl4 h3 hnab hR hshape hT clsT e hP1 hO3 D i hone hk hadm hsmall

theorem twinYType3On_sl4 (h3 : OddThreeFreeInput) :
    Q3TY.TwinYType3On (fun t n => t = .PSL ∧ n = 4) :=
  twinYType3On_sl4_of_small h3 twinYSl4Small3_true

end CFSG.ClassicalInvolution.Q3.Q3TIY
