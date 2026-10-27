module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888XM
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888XPerm

public section

open Subgroup

namespace CFSG.OddStandard.SmallF3.Omega

variable {X : Type} [Group X] {V : Subgroup X} {W : Fin 4 → Subgroup X}

private lemma suppVec_ne_zero_iff (W : Fin 4 → Subgroup X) (y : X) (i : Fin 4) :
    suppVec W y i ≠ 0 ↔ ActsNontriv (W i) y := by
  classical
  unfold suppVec
  by_cases h : ActsNontriv (W i) y <;> simp [h]

private lemma vecWeight_suppVec_eq_card (W : Fin 4 → Subgroup X) (y : X) :
    vecWeight (suppVec W y) = Nat.card {i : Fin 4 // ActsNontriv (W i) y} := by
  classical
  have hf : (Finset.univ.filter fun i : Fin 4 => suppVec W y i ≠ 0) =
      (Finset.univ.filter fun i : Fin 4 => ActsNontriv (W i) y) := by
    apply Finset.filter_congr
    intro i _
    exact suppVec_ne_zero_iff W y i
  rw [vecWeight, hf, Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem mval_eq_vecWeight (hS : PlaneSys V W) (y : normalizer (V : Set X))
    (h1 : planeHom hS y = 1) : mval hS y = vecWeight (suppVec W (y : X)) := by
  classical
  have hfix : ∀ i, planeHom hS y i = i := by
    intro i
    rw [h1]
    rfl
  unfold mval vecWeight
  have hemp : (Finset.univ.filter fun i : Fin 4 => planeHom hS y i ≠ i) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro i _
    simp [hfix i]
  rw [hemp, Finset.card_empty, Nat.zero_add]
  congr 1
  apply Finset.filter_congr
  intro i _
  rw [suppVec_ne_zero_iff]
  exact ⟨fun h => h.2, fun h => ⟨hfix i, h⟩⟩

theorem suppVec_eq_zero_of_mem_centralizer (hS : PlaneSys V W) (y : normalizer (V : Set X))
    (hy : (y : X) ∈ centralizer (V : Set X)) : suppVec W (y : X) = 0 := by
  classical
  funext i
  rw [Pi.zero_apply, ← not_ne_iff, suppVec_ne_zero_iff]
  rintro ⟨a, ha, hne⟩
  exact hne (by
    have hcomm := (Subgroup.mem_centralizer_iff.mp hy) a (hS.le i ha)
    rw [mul_inv_eq_iff_eq_mul]
    exact hcomm.symm)

theorem two_le_mval (hS : PlaneSys V W) (hpar : PlaneParity V W) (y : normalizer (V : Set X))
    (hy2 : ∀ v ∈ V, (y : X) * (y : X) * v * ((y : X) * (y : X))⁻¹ = v)
    (hyC : (y : X) ∉ centralizer (V : Set X)) : 2 ≤ mval hS y := by
  classical
  by_cases h1 : planeHom hS y = 1
  · rw [mval_eq_vecWeight hS y h1, vecWeight_suppVec_eq_card W (y : X)]
    have hfix : ∀ i, ∀ w ∈ W i, (y : X) * w * (y : X)⁻¹ ∈ W i := by
      intro i w hw
      have hspec := planeHom_spec hS y i w hw
      have hii : planeHom hS y i = i := by rw [h1]; rfl
      rwa [hii] at hspec
    have heven : Even (Nat.card {i : Fin 4 // ActsNontriv (W i) (y : X)}) :=
      hpar (y : X) y.2 hfix hy2
    have hex : ∃ i : Fin 4, ActsNontriv (W i) (y : X) := by
      by_contra h
      push_neg at h
      apply hyC
      rw [Subgroup.mem_centralizer_iff]
      have hcv : ∀ v ∈ V, (y : X) * v = v * (y : X) := by
        rw [centralizes_V_iff hS y]
        intro i w hw
        have hca := (not_actsNontriv_iff (A := W i) (y := (y : X))).mp (h i) w hw
        rwa [mul_inv_eq_iff_eq_mul] at hca
      intro v hv
      exact (hcv v hv).symm
    have hpos : 0 < Nat.card {i : Fin 4 // ActsNontriv (W i) (y : X)} := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.card_pos_iff.mpr ⟨⟨hex.choose, hex.choose_spec⟩⟩
    exact Nat.succ_le_of_lt (Nat.one_lt_of_ne_zero_of_even hpos.ne' heven)
  · have hmoved := perm_two_le_moved h1
    unfold mval
    exact le_trans hmoved (Nat.le_add_right _ _)

end CFSG.OddStandard.SmallF3.Omega
