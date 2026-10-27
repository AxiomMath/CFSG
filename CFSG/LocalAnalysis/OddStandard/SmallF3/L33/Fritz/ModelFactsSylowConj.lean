module

public import Mathlib.GroupTheory.Sylow

public section

open scoped Pointwise

namespace CFSG.OddStandard.SmallF3.L33

theorem exists_conj_mem_of_sylow_two {G : Type*} [Group G] [Finite G] {S : Subgroup G}
    (hS : IsPGroup 2 S) (hidx : ¬ 2 ∣ S.index) {u : G} (hu : u ^ 2 = 1) :
    ∃ g : G, g * u * g⁻¹ ∈ S := by
  have hPu : IsPGroup 2 (Subgroup.zpowers u) := by
    apply IsPGroup.of_card_dvd_pow (n := 1)
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_dvd_iff_pow_eq_one.mpr hu
  obtain ⟨Q, hQ⟩ := hPu.exists_le_sylow
  let T : Sylow 2 G := hS.toSylow hidx
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G T Q
  have hg' : (MulAut.conj g • (T : Subgroup G)) = (Q : Subgroup G) := by
    rw [← Sylow.coe_subgroup_smul]
    exact congrArg (fun P : Sylow 2 G => (P : Subgroup G)) hg
  have huQ : u ∈ Q := hQ (Subgroup.mem_zpowers u)
  have huT : (MulAut.conj g)⁻¹ • u ∈ T := by
    have h : u ∈ (MulAut.conj g) • (T : Subgroup G) := by
      rw [hg']
      exact huQ
    rwa [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at h
  refine ⟨g⁻¹, ?_⟩
  have hm : (MulAut.conj g)⁻¹ • u = g⁻¹ * u * g := by
    rw [MulAut.smul_def, MulAut.conj_inv_apply]
  have hgT : g⁻¹ * u * g ∈ S := by
    change g⁻¹ * u * g ∈ (T : Subgroup G)
    exact hm ▸ huT
  simpa using hgT

end CFSG.OddStandard.SmallF3.L33
