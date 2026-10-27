module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreXSetup
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreXConfig

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly

variable {J : Type} [Group J] [Finite J] {Q : Sylow 2 J} {B : Subgroup J} {z u : J}

theorem quasi_oddCore_odd (u : J) : Odd (Nat.card (pPrimeCore 2 (quasiNormalizer u))) :=
  Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2))

theorem quasi_orderOf_mk (u : J) {t : quasiNormalizer u} (ht : orderOf t = 2) :
    orderOf (quasiMk u t) = 2 :=
  orderOf_mk_eq_two (quasi_oddCore_odd u) ht

theorem quasiMk_injOn_twoGroup (u : J) {P : Subgroup (quasiNormalizer u)} (hP : IsPGroup 2 P)
    {a b : quasiNormalizer u} (ha : a ∈ P) (hb : b ∈ P) (hab : quasiMk u a = quasiMk u b) :
    a = b := by
  have hO : a⁻¹ * b ∈ pPrimeCore 2 (quasiNormalizer u) := QuotientGroup.eq.mp hab
  obtain ⟨k, hk⟩ := hP ⟨_, P.mul_mem (P.inv_mem ha) hb⟩
  have hk' : (a⁻¹ * b) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hdvd1 : orderOf (a⁻¹ * b) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have hdvd2 : orderOf (a⁻¹ * b) ∣ Nat.card (pPrimeCore 2 (quasiNormalizer u)) :=
    Subgroup.orderOf_dvd_natCard _ hO
  have hcop : Nat.Coprime (2 ^ k) (Nat.card (pPrimeCore 2 (quasiNormalizer u))) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr (quasi_oddCore_odd u))
  have h1 : orderOf (a⁻¹ * b) = 1 := Nat.eq_one_of_dvd_coprimes hcop hdvd1 hdvd2
  rw [orderOf_eq_one_iff, inv_mul_eq_one] at h1
  exact h1

theorem twoRank_quasiNormalizer (u : J) :
    twoRank (quasiNormalizer u) = CFSG.Open.pRank 2 (quasiNormalizer u) :=
  (CFSG.RankThreeCoreUniqueness.Helpers.pRank_subgroup_eq_internal_top 2 (by decide) _).symm

theorem twoRank_quasiQuotient (u : J) :
    twoRank (QuasiQuotient u) = CFSG.Open.pRank 2 (quasiNormalizer u) := by
  rw [two_rank_eq_odd_normal_quotient _ (quasi_oddCore_odd u), twoRank_quasiNormalizer]

omit [Finite J] in
theorem zpowers_quasiBar_normal (u : J) : (Subgroup.zpowers (quasiBar u)).Normal := by
  rw [← MonoidHom.map_zpowers]
  have := zpowers_quasiSelf_normal u
  exact Subgroup.Normal.map this _ (QuotientGroup.mk'_surjective _)

omit [Finite J] in
theorem quasiBar_mul_self (u : J) : quasiBar u * quasiBar u = quasiCentral u := rfl

namespace EscapingLift

theorem quasiMk_centralElt (hu : EscapingLift B z u) (h : Setting J Q B) :
    quasiMk u ⟨centralElt J, h.centralElt_mem_quasiNormalizer u⟩ = quasiCentral u := by
  rw [hu.centralElt_mk_eq h, map_mul]

theorem quasiCentral_mem_center (hu : EscapingLift B z u) (h : Setting J Q B) :
    quasiCentral u ∈ Subgroup.center (QuasiQuotient u) ∧ orderOf (quasiCentral u) = 2 := by
  rw [← hu.quasiMk_centralElt h]
  exact central_involution_odd_quotient _ (quasi_oddCore_odd u) _
    (h.centralElt_mk_mem_center u) (h.orderOf_centralElt_mk u)

theorem orderOf_quasiBar (hu : EscapingLift B z u) (h : Setting J Q B) :
    orderOf (quasiBar u) = 4 := by
  obtain ⟨-, hord⟩ := hu.quasiCentral_mem_center h
  have he1 : quasiCentral u ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hord
    exact absurd hord (by decide)
  have hee : quasiCentral u * quasiCentral u = 1 := by
    have h2 := pow_orderOf_eq_one (quasiCentral u)
    rwa [hord, pow_two] at h2
  have h4 : orderOf (quasiBar u) = 2 ^ (1 + 1) := by
    refine orderOf_eq_prime_pow ?_ ?_
    · rw [pow_one, pow_two]
      exact he1
    · rw [show 2 ^ (1 + 1) = 2 + 2 by norm_num, pow_add, pow_two, quasiBar_mul_self, hee]
  rw [h4]
  norm_num

theorem oddCore_le (hu : EscapingLift B z u) (h : Setting J Q B) (hz : FourGen Q z)
    (hrank : 3 ≤ CFSG.Open.pRank 2 (quasiNormalizer u)) :
    pPrimeCore 2 (quasiNormalizer u) ≤ B.subgroupOf (quasiNormalizer u) := by
  obtain ⟨T, hT, -, -⟩ := hu.exists_sylow h hz
  have hT3 : 3 ≤ CFSG.Open.pRank 2 (T : Subgroup (quasiNormalizer u)) := by
    rw [sylow_two_rank_eq, twoRank_quasiNormalizer]
    exact hrank
  exact (odd_normal_le_full_core T hT3 _ (quasi_oddCore_odd u)).trans (h.gamma_le _ T hT)

theorem mk_mem_quasiImage_iff (hu : EscapingLift B z u) (h : Setting J Q B) (hz : FourGen Q z)
    (hrank : 3 ≤ CFSG.Open.pRank 2 (quasiNormalizer u)) (x : quasiNormalizer u) :
    quasiMk u x ∈ quasiImage B u ↔ (x : J) ∈ B := by
  rw [← Subgroup.mem_comap, Subgroup.comap_map_eq_self (by
    rw [QuotientGroup.ker_mk']
    exact hu.oddCore_le h hz hrank)]
  exact Subgroup.mem_subgroupOf

theorem baseConfig (hu : EscapingLift B z u) (h : Setting J Q B) (hz : FourGen Q z)
    (hrank : 3 ≤ CFSG.Open.pRank 2 (quasiNormalizer u)) :
    BaseConfig (quasiImage B u) (quasiCentral u) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT, -, -⟩ := hu.exists_sylow h hz
  have hcore := h.gamma_le _ T hT
  obtain ⟨hcen, hord⟩ := hu.quasiCentral_mem_center h
  refine ⟨pPrimeCore_quotient_pPrimeCore_eq_bot 2, hcen, hord, ?_, ?_⟩
  · intro htop
    apply hu.subgroupOf_ne_top h
    have hcomap := congrArg (Subgroup.comap (quasiMk u)) htop
    rwa [Subgroup.comap_map_eq_self (by
      rw [QuotientGroup.ker_mk']
      exact hu.oddCore_le h hz hrank), Subgroup.comap_top] at hcomap
  · refine ⟨T.mapSurjective (QuotientGroup.mk'_surjective _), ?_, ?_⟩
    · rw [Sylow.coe_mapSurjective]
      exact Subgroup.map_mono hT
    · rw [Sylow.coe_mapSurjective, ← gamma_image_odd_normal_quotient T _ (quasi_oddCore_odd u) 2]
      exact Subgroup.map_mono hcore

end EscapingLift

theorem three_le_twoRank_quasiQuotient (hrank : 3 ≤ CFSG.Open.pRank 2 (quasiNormalizer u)) :
    3 ≤ twoRank (QuasiQuotient u) := by
  rw [twoRank_quasiQuotient]
  exact hrank

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
