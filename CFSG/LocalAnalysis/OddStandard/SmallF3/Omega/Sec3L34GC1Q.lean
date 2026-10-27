module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63PBase

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

theorem l34g_T_normalizes_Q [Finite G] {K : Subgroup G} {x : G} (hxK : ∀ k ∈ K, x * k = k * x) :
    ∀ t ∈ K ⊔ zpowers x, ∀ q ∈ CFSG.inSubgroup (CFSG.pCore 2) K,
      t * q * t⁻¹ ∈ CFSG.inSubgroup (CFSG.pCore 2) K := by
  have hN : (((CFSG.pCore 2 ↥K).map K.subtype).subgroupOf K).Normal := by
    have h : ((CFSG.pCore 2 ↥K).map K.subtype).subgroupOf K = CFSG.pCore 2 ↥K :=
      Subgroup.comap_map_eq_self_of_injective K.subtype_injective _
    rw [h]
    exact CFSG.pCore_normal
  have hKN : K ≤ normalizer ((CFSG.inSubgroup (CFSG.pCore 2) K : Subgroup G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le _)).1 hN
  have hxN : x ∈ normalizer ((CFSG.inSubgroup (CFSG.pCore 2) K : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro q
    constructor
    · intro hq
      have hqK : q ∈ K := Subgroup.map_subtype_le _ hq
      have h : x * q * x⁻¹ = q := by rw [hxK q hqK]; simp
      rwa [h]
    · intro hq
      have hw : x * q * x⁻¹ ∈ K := Subgroup.map_subtype_le _ hq
      have h : x⁻¹ * (x * q * x⁻¹) * x = x * q * x⁻¹ :=
        calc x⁻¹ * (x * q * x⁻¹) * x = x⁻¹ * ((x * q * x⁻¹) * x) := mul_assoc _ _ _
          _ = x⁻¹ * (x * (x * q * x⁻¹)) := by rw [← hxK _ hw]
          _ = x * q * x⁻¹ := by simp
      have hq' : q = x * q * x⁻¹ := by
        calc q = x⁻¹ * (x * q * x⁻¹) * x := by group
          _ = x * q * x⁻¹ := h
      rwa [hq']
  intro t ht q hq
  have htN : t ∈ normalizer ((CFSG.inSubgroup (CFSG.pCore 2) K : Subgroup G) : Set G) :=
    sup_le hKN (Subgroup.zpowers_le.2 hxN) ht
  exact (Subgroup.mem_normalizer_iff.1 htN q).1 hq

theorem l34g_Q_centralizes {I Q T : Subgroup G} {𝒪 : Set (Subgroup G)}
    (hQT : ∀ t ∈ T, ∀ q ∈ Q, t * q * t⁻¹ ∈ Q)
    (h𝒪 : ∀ J ∈ 𝒪, ∃ t ∈ T, J = CFSG.conjugate I t) (hQI : ⁅Q, I⁆ = ⊥) :
    ∀ q ∈ Q, ∀ e ∈ sSup 𝒪, q * e = e * q := by
  intro q hq
  have hle : sSup 𝒪 ≤ centralizer ({q} : Set G) := by
    refine sSup_le fun J hJ => ?_
    obtain ⟨t, ht, rfl⟩ := h𝒪 J hJ
    intro a ha
    have hu : t * a * t⁻¹ ∈ I := sec63P_mem_conjugate_iff.1 ha
    have hv : t * q * t⁻¹ ∈ Q := hQT t ht q hq
    have hcomm := Subgroup.mem_centralizer_iff.1
      (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hQI hv) _ hu
    have h2 : t * (a * q) * t⁻¹ = t * (q * a) * t⁻¹ :=
      calc t * (a * q) * t⁻¹ = (t * a * t⁻¹) * (t * q * t⁻¹) := by group
        _ = (t * q * t⁻¹) * (t * a * t⁻¹) := hcomm
        _ = t * (q * a) * t⁻¹ := by group
    exact Subgroup.mem_centralizer_singleton_iff.2 (mul_left_cancel (mul_right_cancel h2))
  intro e he
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle he)).symm

end CFSG.OddStandard.SmallF3.Omega
