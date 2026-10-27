module

public import Certificates.Certificate17612
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.GF2Type.Smith1979.IdxFourModelBase

public section

namespace CFSG.GF2Type.Smith1979.IdxFour

open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA
open CFSG.GF2Type.Smith1979.GammaU.Viol CFSG.GF2Type.Smith1979.GammaU.Enum
@[expose] def K2bar0 : Subgroup (V12 ≃ₗ[ZMod 2] V12) := E0 ⊔ Lbar0

theorem Lbar0_le_K2bar0 : Lbar0 ≤ K2bar0 := le_sup_right

theorem E0_le_K2bar0 : E0 ≤ K2bar0 := le_sup_left

theorem Lbar0_le_M0 :
    Lbar0 ≤ M0 := Lbar0_le_stab.trans inf_le_left

theorem K2bar0_le_M0 :
    K2bar0 ≤ M0 := sup_le E0_le_M0 Lbar0_le_M0

theorem x0_not_mem_K2bar0 :
    x0 ∉ K2bar0 :=
  Certificates.certificate17611.2.2.2

theorem not_Lbar0_le_E0 :
    ¬ Lbar0 ≤ E0 := by
  intro h
  have h1 := card_Lbar0_inf_E0
  rw [inf_of_le_left h, card_Lbar0] at h1
  omega

theorem relIndex_K2bar0 :
    K2bar0.relIndex M0 = 2 := by
  have hle := K2bar0_le_M0
  have hK := Subgroup.relIndex_mul_card (H := K2bar0) (K := M0)
  rw [inf_of_le_left hle] at hK
  have hne1 : K2bar0.relIndex M0 ≠ 1 := fun h1 => by
    rw [Subgroup.relIndex_eq_one] at h1
    exact x0_not_mem_K2bar0 (h1 x0_mem_M0)
  have hpos : 0 < K2bar0.relIndex M0 := by
    rw [Nat.pos_iff_ne_zero]
    intro h0
    rw [h0, zero_mul] at hK
    have := Nat.card_pos (α := M0)
    omega
  have hlt : E0 < K2bar0 := lt_of_le_of_ne E0_le_K2bar0 (fun h => not_Lbar0_le_E0 (by
    rw [h]; exact Lbar0_le_K2bar0))
  have hcard := Subgroup.card_lt_of_lt hlt
  have hdvd := Subgroup.card_dvd_of_le E0_le_K2bar0
  obtain ⟨c, hc⟩ := hdvd
  have hc2 : 2 ≤ c := by
    by_contra hc'
    have : c ≤ 1 := by omega
    interval_cases c
    · rw [mul_zero] at hc
      have := Nat.card_pos (α := K2bar0)
      omega
    · rw [mul_one] at hc
      omega
  rw [card_M0] at hK
  rw [hc, card_E0] at hK
  have h4 : K2bar0.relIndex M0 * c = 4 := by
    have : 9797760 * (K2bar0.relIndex M0 * c) = 9797760 * 4 := by
      calc 9797760 * (K2bar0.relIndex M0 * c) = K2bar0.relIndex M0 * (9797760 * c) := by ring
        _ = 39191040 := hK
        _ = 9797760 * 4 := by norm_num
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) this
  have : K2bar0.relIndex M0 ≤ 2 := by nlinarith
  omega

theorem card_K2bar0 :
    Nat.card K2bar0 = 19595520 := by
  have hK := Subgroup.relIndex_mul_card (H := K2bar0) (K := M0)
  rw [inf_of_le_left K2bar0_le_M0, relIndex_K2bar0, card_M0] at hK
  omega

theorem genGrp_skGens_le : genGrp skGens ≤ K2bar0 :=
  Certificates.certificate17611.2.2.1

theorem card_genGrp_skGens : Nat.card (genGrp skGens) = 256 :=
  Certificates.certificate17612.1

theorem involution_conj_of_mem_S {s : V12 ≃ₗ[ZMod 2] V12}
    (hs : s ∈ genGrp skGens) (hss : s * s = 1) : ∃ h ∈ M0, h * s * h⁻¹ ∈ Lbar0 :=
  Certificates.certificate17612.2 s hs hss

theorem factorization_two_card : (Nat.factorization 19595520) 2 = 8 := by
  have : (19595520 : ℕ) = 2 ^ 8 * 76545 := by norm_num
  rw [this, Nat.factorization_mul (by norm_num) (by norm_num),
    Nat.Prime.factorization_pow Nat.prime_two]
  simp [Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 76545)]

theorem exists_conj_Lbar0_of_involution
    {g : V12 ≃ₗ[ZMod 2] V12} (hg : g ∈ K2bar0) (h2 : g * g = 1) :
    ∃ h ∈ M0, h * g * h⁻¹ ∈ Lbar0 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcardK : Nat.card ↥K2bar0 = 19595520 := card_K2bar0
  have hSle : genGrp skGens ≤ K2bar0 := genGrp_skGens_le
  let SK : Subgroup ↥K2bar0 := (genGrp skGens).subgroupOf K2bar0
  have hSKcard : Nat.card SK = 2 ^ (Nat.card ↥K2bar0).factorization 2 := by
    have h1 : Nat.card SK = 256 := by
      rw [card_subgroupOf_eq, inf_of_le_right hSle, card_genGrp_skGens]
    rw [h1, hcardK, factorization_two_card]
    norm_num
  let S : Sylow 2 ↥K2bar0 := Sylow.ofCard SK hSKcard
  let g' : ↥K2bar0 := ⟨g, hg⟩
  have hsq : g' ^ 2 = 1 := Subtype.ext (by simpa [pow_two] using h2)
  have hP : IsPGroup 2 (Subgroup.zpowers g') := by
    intro x
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 x.2
    refine ⟨1, Subtype.ext ?_⟩
    have : (x : ↥K2bar0) ^ 2 = 1 := by
      rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
      simp [hsq]
    simpa using this
  obtain ⟨Q, hQ⟩ := hP.exists_le_sylow
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq ↥K2bar0 S Q
  have hmem : g' ∈ (↑(k • S) : Subgroup ↥K2bar0) := by
    rw [hk]
    exact hQ (Subgroup.mem_zpowers g')
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hmem
  obtain ⟨s, hsS, hks⟩ := hmem
  have hsS' : (s : V12 ≃ₗ[ZMod 2] V12) ∈ genGrp skGens := hsS
  have hks' : k * s * k⁻¹ = g' := hks
  have hss : s * s = 1 := by
    have : k⁻¹ * (g' * g') * k = 1 := by
      rw [← pow_two, hsq]
      simp
    rw [← hks'] at this
    simpa [mul_assoc] using this
  obtain ⟨h, hh, hhs⟩ := involution_conj_of_mem_S hsS' (by simpa using congrArg Subtype.val hss)
  refine ⟨h * (k : V12 ≃ₗ[ZMod 2] V12)⁻¹, mul_mem hh (inv_mem (K2bar0_le_M0 k.2)), ?_⟩
  have hg_eq : g = (k : V12 ≃ₗ[ZMod 2] V12) * (s : V12 ≃ₗ[ZMod 2] V12) *
      (k : V12 ≃ₗ[ZMod 2] V12)⁻¹ := by
    have := congrArg Subtype.val hks'
    simpa using this.symm
  rw [hg_eq]
  simpa [mul_assoc] using hhs

end CFSG.GF2Type.Smith1979.IdxFour
