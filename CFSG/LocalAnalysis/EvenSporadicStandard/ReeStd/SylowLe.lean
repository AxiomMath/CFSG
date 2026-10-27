module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.EvenSporadicStandard.ReeStd

open Subgroup
open MulAction
open scoped Pointwise

variable {G : Type*} [Group G] [Finite G]

theorem exists_isPGroup_le_odd_relIndex {A P : Subgroup G} (hP : IsPGroup 2 P) (hPA : P ≤ A) :
    ∃ T : Subgroup G, IsPGroup 2 T ∧ P ≤ T ∧ T ≤ A ∧ Odd (T.relIndex A) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := (hP.comap_subtype (K := A)).exists_le_sylow
  refine ⟨(Q : Subgroup A).map A.subtype, Q.isPGroup'.map _, ?_, ?_, ?_⟩
  · intro p hp
    exact ⟨⟨p, hPA hp⟩, hQ hp, rfl⟩
  · rintro _ ⟨x, -, rfl⟩
    exact x.2
  · have hrel : ((Q : Subgroup A).map A.subtype).relIndex A = (Q : Subgroup A).index := by
      rw [Subgroup.relIndex, Subgroup.subgroupOf,
        Subgroup.comap_map_eq_self_of_injective A.subtype_injective]
    rw [hrel]
    exact Nat.not_even_iff_odd.mp fun h => Q.not_dvd_index (even_iff_two_dvd.mp h)

theorem exists_mul_mem_normalizer_of_sylow {R T : Subgroup G} (hTR : T ≤ R) (hT : IsPGroup 2 T)
    (hodd : Odd (T.relIndex R)) {c : G} (hc : c ∈ normalizer (R : Set G)) :
    ∃ r ∈ R, r * c ∈ normalizer (T : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT' : IsPGroup 2 (T.subgroupOf R) := hT.comap_subtype
  have hnd : ¬ 2 ∣ (T.subgroupOf R).index := hodd.not_two_dvd_nat
  let S : Sylow 2 R := hT'.toSylow hnd
  haveI : Finite (Sylow 2 R) := Sylow.finite_of_finiteIndex S
  have hcR : ∀ h, h ∈ R ↔ c * h * c⁻¹ ∈ R :=
    (Subgroup.mem_normalizer_iff (H := R)).mp hc
  have hRsmul : MulAut.conj c • R = R := by
    have hle : MulAut.conj c • R ≤ R := by
      rintro x ⟨y, hy, rfl⟩
      simpa [MulAut.smul_def, MulAut.conj_apply] using (hcR y).mp hy
    refine le_antisymm hle ?_
    have hle' : (MulAut.conj c)⁻¹ • R ≤ R := by
      have hcRinv : ∀ h, h ∈ R ↔ c⁻¹ * h * c ∈ R :=
        (Subgroup.mem_normalizer_iff'' (H := R)).mp hc
      rintro x ⟨y, hy, rfl⟩
      simpa [MulAut.smul_def, MulAut.conj_inv_apply] using (hcRinv y).mp hy
    calc R = MulAut.conj c • ((MulAut.conj c)⁻¹ • R) := by
            rw [← mul_smul, mul_inv_cancel, one_smul]
      _ ≤ MulAut.conj c • R :=
            (Subgroup.pointwise_smul_le_pointwise_smul_iff (a := MulAut.conj c)).mpr hle'
  have hT''le : MulAut.conj c • T ≤ R := by
    rintro x ⟨y, hy, rfl⟩
    exact (hcR y).mp (hTR hy)
  have hT'' : IsPGroup 2 (MulAut.conj c • T : Subgroup G) := by
    rw [Subgroup.pointwise_smul_def]
    exact hT.map _
  have hU : IsPGroup 2 ((MulAut.conj c • T).subgroupOf R) := hT''.comap_subtype
  have hUidx : ((MulAut.conj c • T).subgroupOf R).index = T.relIndex R := by
    have h := Subgroup.relIndex_pointwise_smul (h := MulAut.conj c) T R
    rw [hRsmul] at h
    exact h
  have hUodd : Odd ((MulAut.conj c • T).subgroupOf R).index := hUidx ▸ hodd
  have hUnd : ¬ 2 ∣ ((MulAut.conj c • T).subgroupOf R).index := hUodd.not_two_dvd_nat
  let S' : Sylow 2 R := hU.toSylow hUnd
  obtain ⟨r, hr⟩ := exists_smul_eq R S' S
  refine ⟨r, r.2, ?_⟩
  have hcoe : MulAut.conj r • (MulAut.conj c • T).subgroupOf R = T.subgroupOf R := by
    have h := congrArg (fun P : Sylow 2 R => (P : Subgroup R)) hr
    rw [Sylow.coe_subgroup_smul] at h
    dsimp only [S', S] at h
    simpa using h
  have hconj : MulAut.conj (r : G) • (MulAut.conj c • T) = T := by
    have hle : MulAut.conj (r : G) • (MulAut.conj c • T) ≤ R :=
      Subgroup.conj_smul_le_of_le hT''le r
    have h1 : ((MulAut.conj (r : G) • (MulAut.conj c • T)).subgroupOf R).map R.subtype
        = MulAut.conj (r : G) • (MulAut.conj c • T) := by
      rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hle]
    have h2 : (T.subgroupOf R).map R.subtype = T := by
      rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hTR]
    rw [Subgroup.conj_smul_subgroupOf hT''le r] at hcoe
    have h := congrArg (Subgroup.map R.subtype) hcoe
    rw [h1, h2] at h
    exact h
  have hconj2 : MulAut.conj ((r : G) * c) • T = T := by
    rw [map_mul, mul_smul]
    exact hconj
  refine Subgroup.mem_normalizer_iff''.mpr ?_
  intro h
  have hsmul : ((r : G) * c)⁻¹ * h * ((r : G) * c)
      = (MulAut.conj ((r : G) * c))⁻¹ • h := by
    rw [MulAut.smul_def, MulAut.conj_inv_apply]
  rw [hsmul, ← Subgroup.mem_pointwise_smul_iff_inv_smul_mem, hconj2]

end CFSG.EvenSporadicStandard.ReeStd
