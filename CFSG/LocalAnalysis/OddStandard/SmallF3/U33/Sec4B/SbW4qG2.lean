module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbTSyl

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem w4q_exists_v {U : Subgroup G} (hU : IsPGroup 2 U) (hidx : 2 ∣ U.index) :
    ∃ v : G, v ∉ U ∧ (∀ x ∈ U, v * x * v⁻¹ ∈ U) ∧ (∀ x ∈ U, v⁻¹ * x * v ∈ U) ∧ v ^ 2 ∈ U := by
  classical
  obtain ⟨P, hPsyl, hUP⟩ := exists_isSylowIn_of_le (K := ⊤) le_top hU
  have hP2 : IsPGroup 2 P := hPsyl.2.1
  have hPodd : ¬ 2 ∣ P.relIndex ⊤ := hPsyl.2.2
  have hPidx : ¬ 2 ∣ P.index := by rwa [Subgroup.relIndex_top_right] at hPodd
  have hne : U ≠ P := by
    intro h
    rw [h] at hidx
    exact hPidx hidx
  have hgrow : ∃ n ∈ P, (∀ x ∈ U, n * x * n⁻¹ ∈ U) ∧ n ∉ U := by
    by_contra hcon
    push_neg at hcon
    exact hne (eq_of_forall_normalizes hP2 hUP hcon)
  obtain ⟨n, hPn, hnNrm, hnU⟩ := hgrow
  obtain ⟨k, hk⟩ := hP2.exists_pow_pow_eq_one ⟨n, hPn⟩
  have hnk : n ^ 2 ^ k = 1 := by
    simpa using congrArg (Subtype.val) hk
  have hex : ∃ m : ℕ, n ^ 2 ^ m ∈ U := ⟨k, by rw [hnk]; exact U.one_mem⟩
  set m := Nat.find hex with hmdef
  have hm_spec : n ^ 2 ^ m ∈ U := by
    rw [hmdef]
    exact Nat.find_spec hex
  have hm_pos : 0 < m := by
    by_contra h
    have hm0 : m = 0 := by omega
    have hmem : n ∈ U := by
      have h := hm_spec
      rw [hm0] at h
      simpa using h
    exact hnU hmem
  have hm1 : 1 ≤ m := hm_pos
  set v : G := n ^ 2 ^ (m - 1) with hvdef
  have hv_not : v ∉ U := by
    rw [hvdef]
    intro hmem
    exact Nat.find_min hex (show m - 1 < m by omega) hmem
  have hnNormalizer : n ∈ Subgroup.normalizer (U : Set G) :=
    Subgroup.mem_normalizer_fintype (fun x hx => hnNrm x hx)
  have hvNormalizer : v ∈ Subgroup.normalizer (U : Set G) := by
    rw [hvdef]
    exact Subgroup.pow_mem (Subgroup.normalizer (U : Set G)) hnNormalizer (2 ^ (m - 1))
  have hv_sq : v ^ 2 ∈ U := by
    have h2m : 2 ^ (m - 1) * 2 = 2 ^ m := by
      rw [← pow_succ, Nat.sub_add_cancel hm1]
    rw [hvdef, ← pow_mul n (2 ^ (m - 1)) 2, h2m]
    exact hm_spec
  refine ⟨v, hv_not, ?_, ?_, hv_sq⟩
  · intro x hx
    exact (Subgroup.mem_normalizer_iff.mp hvNormalizer x).mp hx
  · intro x hx
    have hx' : v⁻¹ * x * (v⁻¹)⁻¹ ∈ U :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hvNormalizer) x).mp hx
    simpa using hx'

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
