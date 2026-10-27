module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFiveRepDef
public import CFSG.YGroups.Y443.Native.Align
public import CFSG.Monster.Existence.InvolutionClasses

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFive

open CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.Generated CFSG.AGLEmbedding.Norton
  CFSG.AGLEmbedding.Norton.MON5_7 CFSG.YGroups.Y443 CFSG.YGroups.Y443Native
  CFSG.Monster.Existence

@[expose] def TwoARep (h : Gmat) : Prop :=
  (∃ α : Gmat, IsConj tGmat α ∧ α * h * α⁻¹ = h⁻¹) ∨
    ∃ a b : Gmat, IsConj tGmat a ∧ IsConj tGmat b ∧ a * h = h * a ∧ b * h = h * b ∧
      a * b = b * a ∧ a ≠ b

section Sound

theorem gw_tW : gw tW = tGmat := Subtype.ext (by exact wordLin_tWord)

theorem inv_of_sq {G : Type*} [Group G] {A H : G} (hA : A * A = 1) (hH : H * (A * (H * A)) = 1) :
    A * H * A⁻¹ = H⁻¹ := by
  have hA' : A⁻¹ = A := (eq_inv_of_mul_eq_one_left hA).symm
  rw [hA']
  have : H * (A * H * A) = 1 := by rw [← hH]; group
  exact eq_inv_of_mul_eq_one_right this

theorem isConj_of_eq {G : Type*} [Group G] {T A c : G} (h : c * T = A * c) :
    IsConj T A := by
  refine isConj_iff.2 ⟨c, ?_⟩
  rw [h]; group


theorem repOK (R : RepWit)
    (h : agreeAll (repEqs R) = true) (hm : repMove R = true) :
    TwoARep (gw (rhsW R.v)) := by
  have hall := agreeAll_sound h
  have hrep : gw R.repW = gw (rhsW R.v) := hall (R.repW, rhsW R.v) (by
    unfold repEqs; split_ifs <;> simp)
  unfold repEqs at hall
  by_cases hk : R.kind = true
  · simp only [hk, ite_true] at hall
    left
    have e1 := hall (R.wa ++ R.wa, []) (by simp)
    have e2 := hall (R.wa ++ R.repW ++ R.wa ++ R.repW, []) (by simp)
    have e3 := hall (tW ++ R.ca, R.ca ++ R.wa) (by simp)
    simp only [gw_append, gw_nil, gw_tW] at e1 e2 e3
    refine ⟨gw R.wa, isConj_of_eq e3, ?_⟩
    rw [hrep] at e2
    exact inv_of_sq e1 (by simpa [mul_assoc] using e2)
  · have hk' : R.kind = false := by simpa using hk
    simp only [hk', Bool.false_eq_true, ite_false] at hall
    right
    have e1 := hall (R.wa ++ R.wa, []) (by simp)
    have e2 := hall (R.wb ++ R.wb, []) (by simp)
    have e3 := hall (R.wa ++ R.repW, R.repW ++ R.wa) (by simp)
    have e4 := hall (R.wb ++ R.repW, R.repW ++ R.wb) (by simp)
    have e5 := hall (R.wa ++ R.wb, R.wb ++ R.wa) (by simp)
    have e6 := hall (tW ++ R.ca, R.ca ++ R.wa) (by simp)
    have e7 := hall (tW ++ R.cb, R.cb ++ R.wb) (by simp)
    simp only [gw_append, gw_nil, gw_tW] at e1 e2 e3 e4 e5 e6 e7
    have hne : gw R.wb * gw R.wa ≠ 1 := by
      have : EdgeNoncomm.moveCheck (R.wa ++ R.wb) (aV ()) = true := by
        simpa [repMove, hk'] using hm
      have := gw_ne_one_of_moveCheck this
      simpa [gw_append] using this
    refine ⟨gw R.wa, gw R.wb, isConj_of_eq e6, isConj_of_eq e7, ?_, ?_, ?_, ?_⟩
    · rw [← hrep]; exact e3.symm
    · rw [← hrep]; exact e4.symm
    · exact e5.symm
    · intro hab
      apply hne
      rw [← hab]
      exact e1

end Sound

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFive
