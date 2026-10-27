module

public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicOne
public import CFSG.Sporadic.Schreier.MathieuOddCoreM24
public import Certificates.Certificate13508

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Monster.B.Co2 CFSG.Blueprint CFSG.Sporadic.Schreier CFSG.Open CFSG.RankThree.Native CFSG.RankThree.PartOne
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.Tables.Census CFSG.ComponentClassification.OuterAutomorphisms

theorem rep_m24ThreeA : Monster.B.Co2.Rep 24 m24ThreeA (List.formPerm [0, 3] * List.formPerm [1, 6] *
    List.formPerm [2, 16] * List.formPerm [4, 12] * List.formPerm [5, 8] * List.formPerm [7, 14] *
    List.formPerm [9, 18] * List.formPerm [10, 17] * List.formPerm [11, 20] *
    List.formPerm [13, 15] * List.formPerm [19, 23] * List.formPerm [21, 22]) := by
  unfold CFSG.Monster.B.Co2.Rep
  decide

theorem rep_m24ThreeB : CFSG.Monster.B.Co2.Rep 24 m24ThreeB (List.formPerm [0, 3, 5] * List.formPerm [1, 20, 13] *
    List.formPerm [2, 8, 14] * List.formPerm [4, 17, 9] * List.formPerm [12, 16, 15] *
    List.formPerm [18, 23, 22]) := by
  unfold CFSG.Monster.B.Co2.Rep
  decide

theorem balance_M24_three :
    IsLocallyBalancedAbs 3 2 ↥NativeSporadic.M24 := by
  have h := Certificates.certificate13508
  simp only [m24ThreeCheck, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, hvA⟩, hvB⟩, -⟩, hcent⟩, hord⟩, hne⟩, hclass⟩ := h
  have hA := rep_of_validA hvA
  have hB := rep_of_validA hvB
  have hQ : Subgroup.closure {permOfArr 24 m24ThreeA, permOfArr 24 m24ThreeB} =
      NativeSporadic.M24 := by
    rw [hA.unique rep_m24ThreeA, hB.unique rep_m24ThreeB]
    rfl
  obtain ⟨z, hz, hzo, h27, hO⟩ := gfr3_kit (by norm_num) (S := m24ThreeArrs)
    (by simp [m24ThreeArrs]) (bs := m24ThreeBase) (by decide) hA hB NativeSporadic.M24 hQ
    h1 (rels := m24ThreeRels) (gs := m24ThreeGens) (ps := m24ThreeKeys)
    (c := m24ThreeCert ()) (N := 1080) (e := 3) (f := 1) (by decide) (by simp [m24ThreeGens])
    hcent hord hne (by norm_num) hclass
  have hinner : CFSG.ComponentClassification.OuterAutomorphisms.inner NativeSporadic.M24 = ⊤ :=
    inner_eq_top_of_card_le m24_center_eq_bot' m24_mulAut_card
  have hall : ∀ α : MulAut NativeSporadic.M24, α ∈ innerAut NativeSporadic.M24 := fun α => by
    have : α ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner NativeSporadic.M24 := by rw [hinner]; trivial
    exact this
  have hnc : ∃ x y : ↥NativeSporadic.M24, x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ x * y ≠ y * x ∧
      IsPGroup 3 (Subgroup.closure ({x, y} : Set ↥NativeSporadic.M24)) := pair_M24_three
  have h81 : ¬ 3 ^ 4 ∣ Nat.card ↥NativeSporadic.M24 := by
    rw [m24_card]
    norm_num
  have hzo' : orderOf (⟨z, hz⟩ : ↥NativeSporadic.M24) = 3 := by
    rw [← Subgroup.orderOf_coe]
    exact hzo
  exact gfr3_locallyBalanced_of_good m24_center_eq_bot' (gfr3_card_outer_le_two_of_inner hall)
    (gfr3_exists_good_of_sylow hnc h81 hzo' h27 (gfr3_good_of_inner hall hO))

end CFSG.HardMathSupport.Solomon.Coordinator
