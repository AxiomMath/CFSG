module

public import CFSG.GH74.GLS.TwoThin.Equivariance
public import CFSG.GH74.GLS.TwoThin.Cover
public import CFSG.GroupTheory.ABGLocalTools.PStabilityCoreQuaternion

public section

namespace CFSG.GH74.GLS.TwoThin

open Subgroup Blueprint Assembly.LowTwoRank CFSG.ComponentClassification
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def centralLift (K : Subgroup G) : Subgroup G :=
  ((center (↥K ⧸ pPrimeCore 2 ↥K)).comap (QuotientGroup.mk' (pPrimeCore 2 ↥K))).map K.subtype

theorem mem_centralLift {K : Subgroup G} {g : G} :
    g ∈ centralLift K ↔ ∃ hg : g ∈ K,
      QuotientGroup.mk' (pPrimeCore 2 ↥K) ⟨g, hg⟩ ∈ center (↥K ⧸ pPrimeCore 2 ↥K) := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k.2, hk⟩
  · rintro ⟨hg, h⟩
    exact ⟨⟨g, hg⟩, h, rfl⟩

theorem centralLift_le (K : Subgroup G) : centralLift K ≤ K := by
  rintro _ ⟨k, -, rfl⟩
  exact k.2

theorem mk_commutator_eq_one {K : Subgroup G} {k c : G} (hk : k ∈ K) (hc : c ∈ centralLift K) :
    ⁅k, c⁆ ∈ pPrimeCoreOf 2 K := by
  obtain ⟨hcK, hz⟩ := mem_centralLift.mp hc
  have hkc : ⁅k, c⁆ ∈ K := by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hk hcK) (inv_mem hk)) (inv_mem hcK)
  have h1 : (⟨⁅k, c⁆, hkc⟩ : ↥K) = ⁅(⟨k, hk⟩ : ↥K), ⟨c, hcK⟩⁆ := rfl
  have h2 : hatMap (le_refl K) ⟨⁅k, c⁆, hkc⟩ = 1 := by
    change QuotientGroup.mk' (pPrimeCore 2 ↥K) ⟨⁅k, c⁆, hkc⟩ = 1
    rw [h1, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr
      (Subgroup.mem_center_iff.mp hz (QuotientGroup.mk' (pPrimeCore 2 ↥K) ⟨k, hk⟩))
  exact (hatMap_eq_one_iff (le_refl K) ⟨⁅k, c⁆, hkc⟩).mp h2

theorem centralLift_le_centralizerSection (K : Subgroup G) :
    centralLift K ≤ centralizerSection K (pPrimeCoreOf 2 K) := by
  intro c hc
  have hcK : c ∈ K := centralLift_le K hc
  exact ⟨Subgroup.le_normalizer hcK, mem_normalizer_pPrimeCoreOf (Subgroup.le_normalizer hcK),
    fun k hk => mk_commutator_eq_one hk hc⟩

theorem conj_mem_centralLift {K : Subgroup G} {c q : G} (hc : c ∈ centralLift K)
    (hq : q ∈ centralizerSection K (pPrimeCoreOf 2 K)) : q * c * q⁻¹ ∈ centralLift K := by
  obtain ⟨hcK, hz⟩ := mem_centralLift.mp hc
  have hqc : q * c * q⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hq.1 c).mp hcK
  refine mem_centralLift.mpr ⟨hqc, ?_⟩
  have hO : q * c * q⁻¹ * c⁻¹ ∈ pPrimeCoreOf 2 K := by
    have := inv_mem (hq.2.2 c hcK)
    simpa [commutatorElement_def, mul_assoc] using this
  have hmk : QuotientGroup.mk' (pPrimeCore 2 ↥K) ⟨q * c * q⁻¹ * c⁻¹, K.mul_mem hqc (K.inv_mem hcK)⟩
      = 1 := by
    have := (hatMap_eq_one_iff (le_refl K)
      ⟨q * c * q⁻¹ * c⁻¹, K.mul_mem hqc (K.inv_mem hcK)⟩).mpr hO
    exact this
  have : (⟨q * c * q⁻¹, hqc⟩ : ↥K) =
      ⟨q * c * q⁻¹ * c⁻¹, K.mul_mem hqc (K.inv_mem hcK)⟩ * ⟨c, hcK⟩ := by
    apply Subtype.ext
    simp
  rw [this, map_mul, hmk, one_mul]
  exact hz

variable [Finite G]

theorem exists_sylow_central_lift {x : G} {K : Subgroup G}
    (hK : IsPCompIn 2 (centralizer ({x} : Set G)) K)
    (hKB : InB2 (↥K ⧸ pPrimeCore 2 ↥K)) :
    ∃ Q : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 2 Q (CxK x K) ∧ ∃ u : G, u ∈ Q ∧
      (∀ q ∈ Q, u * q = q * u) ∧ u ∈ centralLift K ∧ orderOf u = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hzc, hz2⟩ : ∃ z ∈ center (↥K ⧸ pPrimeCore 2 ↥K), orderOf z = 2 := by
    have hne : center (↥K ⧸ pPrimeCore 2 ↥K) ≠ ⊥ := hKB.2
    have heven : 2 ∣ Nat.card ↥(center (↥K ⧸ pPrimeCore 2 ↥K)) := by
      by_contra hn
      have hodd : Odd (Nat.card ↥(center (↥K ⧸ pPrimeCore 2 ↥K))) := by
        rw [← Nat.not_even_iff_odd]
        exact fun h => hn (even_iff_two_dvd.mp h)
      have hle : center (↥K ⧸ pPrimeCore 2 ↥K) ≤ pPrimeCore 2 (↥K ⧸ pPrimeCore 2 ↥K) :=
        le_sSup ⟨inferInstance, Nat.coprime_two_left.mpr hodd⟩
      rw [pPrimeCore_quotient_eq_bot] at hle
      exact hne (le_bot_iff.mp hle)
    obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' 2 heven
    exact ⟨c, c.2, by rw [orderOf_coe]; exact hc⟩
  obtain ⟨k, hk⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥K) z
  obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos k).ne'
  set k₂ : ↥K := k ^ b with hk₂
  have hk₂2 : k₂ ^ (2 ^ a) = 1 := by
    rw [hk₂, ← pow_mul, mul_comm, ← hab]
    exact pow_orderOf_eq_one k
  have hz2' : z ^ 2 = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz2] at this
  have hmk₂ : QuotientGroup.mk' (pPrimeCore 2 ↥K) k₂ = z := by
    rw [hk₂, map_pow, hk]
    obtain ⟨m, rfl⟩ := hb
    rw [pow_succ, pow_mul, hz2', one_pow, one_mul]
  have hu₀c : (k₂ : G) ∈ centralLift K := by
    refine mem_centralLift.mpr ⟨k₂.2, ?_⟩
    rw [hmk₂]
    exact hzc
  have hu₀D : (k₂ : G) ∈ CxK x K :=
    Subgroup.mem_inf.mpr ⟨by simpa using hK.1 k₂.2, centralLift_le_centralizerSection K hu₀c⟩
  let u₀D : ↥(CxK x K) := ⟨k₂, hu₀D⟩
  have h2G : (k₂ : G) ^ (2 ^ a) = 1 := by
    have := congrArg Subtype.val hk₂2
    simpa using this
  have hP2 : IsPGroup 2 ↥(Subgroup.zpowers u₀D) :=
    isPGroup_zpowers_of_pow_eq_one (n := a) (Subtype.ext (by simpa using h2G))
  obtain ⟨S, hS⟩ := IsPGroup.exists_le_sylow hP2
  set Q : Subgroup G := (S : Subgroup ↥(CxK x K)).map (CxK x K).subtype with hQdef
  have hQ : CFSG.ABGLocalTools.IsSylowOf 2 Q (CxK x K) := ⟨S, rfl⟩
  have hu₀Q : (k₂ : G) ∈ Q := ⟨u₀D, hS (Subgroup.mem_zpowers u₀D), rfl⟩
  have hQp : IsPGroup 2 ↥Q := hQ.isPGroup
  have hnil : Group.IsNilpotent ↥Q := hQp.isNilpotent
  let N₀ : Subgroup ↥Q := (centralLift K).subgroupOf Q
  have hN₀ : N₀.Normal := ⟨fun n hn g => by
    have hqs : (g : G) ∈ centralizerSection K (pPrimeCoreOf 2 K) := (hQ.le g.2).2
    exact Subgroup.mem_subgroupOf.mpr (by
      simpa using conj_mem_centralLift (Subgroup.mem_subgroupOf.mp hn) hqs)⟩
  have hN₀ne : N₀ ≠ ⊥ := by
    intro h
    have hmem : (⟨k₂, hu₀Q⟩ : ↥Q) ∈ N₀ := Subgroup.mem_subgroupOf.mpr hu₀c
    rw [h, Subgroup.mem_bot] at hmem
    have hk21 : k₂ = 1 := Subtype.ext (by simpa using congrArg Subtype.val hmem)
    rw [hk21, map_one] at hmk₂
    have : orderOf z = 1 := by rw [← hmk₂]; exact orderOf_one
    omega
  have hX := Group.IsNilpotent.inf_center_ne_bot_of_normal hN₀ne
  obtain ⟨w, hw, hwo⟩ := CFSG.ABGLocalTools.exists_mem_orderOf_eq_two
    (hQp.to_subgroup (N₀ ⊓ center ↥Q)) hX
  refine ⟨Q, hQ, (w : G), w.2, fun q hq => ?_,
    Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp hw).1, ?_⟩
  · have := Subgroup.mem_center_iff.mp (Subgroup.mem_inf.mp hw).2 ⟨q, hq⟩
    exact (congrArg Subtype.val this).symm
  · rw [Subgroup.orderOf_coe]
    exact hwo

end CFSG.GH74.GLS.TwoThin
