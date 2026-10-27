module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7Tight
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7Quaternion
public import CFSG.ClassicalInvolution.Asc77.AscT3Basic

public section

namespace CFSG.ClassicalInvolution.Hat2A7S

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

section Local

variable {G : Type} [Group G] [Finite G]

theorem uset_data {Ω : Set (Subgroup G)}
    (hcl : ∀ L ∈ Ω, ∃ z : G, Hat2A7.IsClassical2A7 ⊤ L z) {U : Subgroup G} (hU : U ∈ USet Ω) :
    ∃ J' ∈ Ω, U ≤ J' ∧ IsPGroup 2 U ∧ Nat.card U = 8 := by
  obtain ⟨R, hR, hUR, -, hidx⟩ := hU
  obtain ⟨J', hJ', P, rfl⟩ := hR
  obtain ⟨u, hu⟩ := hcl J' hJ'
  have hcardR : Nat.card (Subgroup.map J'.subtype (P : Subgroup ↥J')) = 16 := by
    rw [Subgroup.card_map_of_injective J'.subtype_injective]
    exact Hat2A7.card_sylow_of_witness hu.witness P
  have hcardU : Nat.card U = 8 := by
    have h1 := Subgroup.relIndex_mul_card U (Subgroup.map J'.subtype (P : Subgroup ↥J'))
    rw [inf_eq_left.mpr hUR, hidx, hcardR] at h1
    omega
  exact ⟨J', hJ', hUR.trans (Subgroup.map_subtype_le _), (P.isPGroup'.map J'.subtype).to_le hUR,
    hcardU⟩

theorem involution_mem_of_card {J U : Subgroup G} {j : G} (hj : IsUniqueInvolution J j)
    (hUJ : U ≤ J) (hcard : Nat.card U = 8) :
    j ∈ U ∧ ∀ x ∈ U, orderOf x = 2 → x = j := by
  have huniq : ∀ x ∈ U, orderOf x = 2 → x = j := by
    intro x hx hx2
    have hxx : x * x = 1 := by
      have := pow_orderOf_eq_one x
      rwa [hx2, pow_two] at this
    have hx1 : x ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hx2
      omega
    exact (hj.unique x (hUJ hx) hxx).resolve_left hx1
  refine ⟨?_, huniq⟩
  have hdvd : 2 ∣ Nat.card U := by
    rw [hcard]
    norm_num
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  have hw2 : orderOf (w : G) = 2 := by
    rw [Subgroup.orderOf_coe]
    exact hw
  rw [← huniq (w : G) w.2 hw2]
  exact w.2

end Local

section Centralized

variable {G : Type} [Group G] [Finite G]

theorem exists_sylow_centralized {M U : Subgroup G} {m j : G}
    (hm : Hat2A7.IsClassical2A7 ⊤ M m) (hUN : U ≤ Subgroup.normalizer (M : Set G))
    (hU2 : IsPGroup 2 U) (hjU : j ∈ U) (huniq : ∀ x ∈ U, orderOf x = 2 → x = j)
    (hcard : 4 < Nat.card U) (hjsq : j * j = 1) (hj1 : j ≠ 1) :
    ∃ R : Subgroup G, IsSylow2In R M ∧ ∀ x ∈ R, j * x = x * j := by
  have htriv := Hat2A7.oddQuotAut_conjOn_eq_one_of_card hm.witness hUN hU2 hjU huniq hcard
  have hcomm : ∀ k : ↥M, k⁻¹ * Hat2A7.conjOn M j (hUN hjU) k ∈
      classicalInvolutionOddCore ↥M := by
    intro k
    have h1 : Hat2A7.oddQuotAut M (Hat2A7.conjOn M j (hUN hjU)) (k : Hat2A7.OddQuot M) =
        (k : Hat2A7.OddQuot M) := by
      rw [htriv]
      rfl
    rw [Hat2A7.oddQuotAut_mk] at h1
    exact QuotientGroup.eq.mp h1.symm
  obtain ⟨R, hR, hRinv⟩ := Asc77.T3.exists_sylow_normalized
    (isPGroup_zpowers_of_mul_self_eq_one hjsq hj1) (Subgroup.zpowers_le.mpr (hUN hjU))
  refine ⟨R, hR, fun x hx => ?_⟩
  have hxM : x ∈ M := hR.1 hx
  have hk := hcomm ⟨x, hxM⟩
  have hxR : j * x * j⁻¹ ∈ R := by
    have h1 : conjSub j R = R := hRinv j (Subgroup.mem_zpowers j)
    rw [← h1]
    exact conj_mem_conjSub hx
  have hcoe : (((⟨x, hxM⟩ : ↥M)⁻¹ * Hat2A7.conjOn M j (hUN hjU) ⟨x, hxM⟩ : ↥M) : G) =
      x⁻¹ * (j * x * j⁻¹) := rfl
  have hmem : x⁻¹ * (j * x * j⁻¹) ∈ R := R.mul_mem (R.inv_mem hx) hxR
  have hnR : ((⟨x, hxM⟩ : ↥M)⁻¹ * Hat2A7.conjOn M j (hUN hjU) ⟨x, hxM⟩ : ↥M) ∈
      R.subgroupOf M := by
    rw [Subgroup.mem_subgroupOf, hcoe]
    exact hmem
  have hpc : IsPGroup 2 (R.subgroupOf M) := hR.2.1.comap_subtype (K := M)
  have hn1 := Asc77.eq_one_of_isPGroup_of_mem_odd (Hat2A7.odd_card_oddCore M) hk
    (hpc.to_le (Subgroup.zpowers_le.mpr hnR))
  have h2 : x⁻¹ * (j * x * j⁻¹) = 1 := hcoe.symm.trans (congrArg Subtype.val hn1)
  have h3 : x = j * x * j⁻¹ := inv_mul_eq_one.mp h2
  calc j * x = (j * x * j⁻¹) * j := by group
    _ = x * j := by rw [← h3]

end Centralized

end CFSG.ClassicalInvolution.Hat2A7S
