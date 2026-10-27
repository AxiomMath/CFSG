module

public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergCCSymplecticCoreSylow
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBXLargeLocalRankCore
public import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank

public section

namespace CFSG.LocalAnalysis.GorensteinLyons

open Subgroup CFSG.Open
open CFSG.ABGLocalTools (IsSylowOf)

namespace SteinbergCH

theorem eq_one_of_odd_pow_of_isPGroup_two {X : Type*} [Group X] {K : Subgroup X}
    (hK : IsPGroup 2 K) {g : X} (hg : g ∈ K) {n : ℕ} (hn : Odd n) (hgn : g ^ n = 1) : g = 1 := by
  obtain ⟨k, hk⟩ := hK ⟨g, hg⟩
  have hk' : g ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  have hcop : Nat.Coprime (2 ^ k) n := Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hn)
  have h1 := pow_gcd_eq_one.mpr ⟨hk', hgn⟩
  rwa [Nat.Coprime.gcd_eq_one hcop, pow_one] at h1

theorem card_le_two_of_isCyclic {X : Type*} [Group X] [Finite X] [IsCyclic X]
    (h : ∀ x : X, x ^ 2 = 1) : Nat.card X ≤ 2 := by
  rw [← IsCyclic.exponent_eq_card]
  exact Nat.le_of_dvd two_pos (Monoid.exponent_dvd_of_forall_pow_eq_one h)

theorem pRank_eq_twoLocalRank_of_le {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : 1 < p)
    {B Y : Subgroup G} (hB : GLAIsBmax p B) (hY : IsTwoLocal Y) (hBY : B ≤ Y) :
    CFSG.Open.pRank p Y = GLATwoLocalRank p G :=
  le_antisymm (CFSG.LargeEvenClassification.Helpers.pRank_le_twoLocalPRank hp Y hY)
    ((CFSG.SectionRank.le_pRank hp le_rfl hB.1 hB.2.1).trans (CFSG.SectionRank.pRank_mono hp hBY))

theorem eq_one_of_trivial_on_frattini_quotient {G : Type*} [Group G] [Finite G]
    {M : Subgroup G} (hcharM : IsCharacteristicP 2 M) {b : G} (hbM : b ∈ M) {n : ℕ}
    (hn : Odd n) (hbn : b ^ n = 1)
    (htriv : ∀ q ∈ CFSG.inSubgroup (CFSG.pCore 2) M,
      q⁻¹ * (b * q * b⁻¹) ∈ (frattini (CFSG.inSubgroup (CFSG.pCore 2) M)).map
        (CFSG.inSubgroup (CFSG.pCore 2) M).subtype) :
    b = 1 := by
  have := Fact.mk Nat.prime_two
  have hQ2 : IsPGroup 2 (CFSG.inSubgroup (CFSG.pCore 2) M) := CFSG.pCore_isPGroup.map M.subtype
  have hbN : b ∈ normalizer (CFSG.inSubgroup (CFSG.pCore 2) M : Set G) := by
    have h := le_normalizer_map (H := CFSG.pCore 2 M) M.subtype
    rw [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] at h
    exact h hbM
  set φ := (CFSG.inSubgroup (CFSG.pCore 2) M).normalizerMonoidHom ⟨b, hbN⟩ with hφ
  have hφx : ∀ x : CFSG.inSubgroup (CFSG.pCore 2) M, ((φ x : _) : G) = b * x * b⁻¹ :=
    fun x => rfl
  have hker : φ ∈ (CFSG.SectionRank.Ccomm.autQuotient
      (frattini (CFSG.inSubgroup (CFSG.pCore 2) M))).ker := by
    rw [CFSG.SectionRank.Ccomm.mem_ker_autQuotient]
    intro x
    obtain ⟨y, hy, hyx⟩ := htriv x x.2
    have hyeq : y = x⁻¹ * φ x := Subtype.ext (by rw [coe_mul, coe_inv, hφx]; exact hyx)
    rw [← hyeq]
    exact hy
  have hφn : φ ^ n = 1 := by
    have h1 : (⟨b, hbN⟩ : normalizer (CFSG.inSubgroup (CFSG.pCore 2) M : Set G)) ^ n = 1 :=
      Subtype.ext (by rw [SubgroupClass.coe_pow, hbn, OneMemClass.coe_one])
    rw [hφ, ← map_pow, h1, map_one]
  have hφ1 : φ = 1 := eq_one_of_odd_pow_of_isPGroup_two
    (CFSG.SectionRank.Ccomm.isPGroup_ker_autQuotient_frattini hQ2) hker hn hφn
  have hbC : (⟨b, hbM⟩ : M) ∈ centralizer (CFSG.pCore 2 M : Set M) := by
    rw [mem_centralizer_iff]
    intro x hx
    have h1 := congrArg (fun ψ : MulAut (CFSG.inSubgroup (CFSG.pCore 2) M) =>
      ((ψ ⟨x, x, hx, rfl⟩ : CFSG.inSubgroup (CFSG.pCore 2) M) : G)) hφ1
    simp only [hφx, MulAut.one_apply] at h1
    apply Subtype.ext
    change (x : G) * b = b * x
    calc (x : G) * b = b * x * b⁻¹ * b := by rw [h1]
      _ = b * x := by group
  exact eq_one_of_odd_pow_of_isPGroup_two hQ2 ⟨_, hcharM hbC, rfl⟩ hn hbn

theorem not_isCyclic_twoCore {G : Type*} [Group G] [Finite G] {M : Subgroup G}
    (hcharM : IsCharacteristicP 2 M) (hSyl : IsSylowOf 2 M M → IsSylowOf 2 M ⊤)
    (h3 : 3 ≤ CFSG.pRank 2 G) : ¬ IsCyclic (CFSG.inSubgroup (CFSG.pCore 2) M) := by
  intro hcyc
  have := Fact.mk Nat.prime_two
  set Q₀ := CFSG.pCore 2 M with hQ₀
  have hQ₀2 : IsPGroup 2 Q₀ := CFSG.pCore_isPGroup
  have : IsCyclic (Q₀.map M.subtype) := hcyc
  have : IsCyclic Q₀ := isCyclic_of_surjective
    (Q₀.equivMapOfInjective M.subtype M.subtype_injective).symm.toMonoidHom
    (MulEquiv.surjective _)
  have hAut : IsPGroup 2 (MulAut Q₀) := by
    obtain ⟨a, ha⟩ := hQ₀2.exists_card_eq
    refine IsPGroup.of_card (n := a - 1) ?_
    rw [IsCyclic.card_mulAut, ha]
    rcases Nat.eq_zero_or_pos a with h0 | hpos
    · rw [h0]
      rfl
    · rw [Nat.totient_prime_pow Nat.prime_two hpos]
      ring
  have hM2 : IsPGroup 2 M := by
    intro m
    obtain ⟨k, hk⟩ := hAut (MulAut.conjNormal m)
    have hmk : m ^ 2 ^ k ∈ Q₀ := by
      refine hcharM (mem_centralizer_iff.mpr fun x hx => ?_)
      have h1 := congrArg (fun ψ : MulAut Q₀ => ((ψ ⟨x, hx⟩ : Q₀) : M)) hk
      simp only [← map_pow, MulAut.conjNormal_apply, MulAut.one_apply] at h1
      calc x * m ^ 2 ^ k = m ^ 2 ^ k * x * (m ^ 2 ^ k)⁻¹ * m ^ 2 ^ k := by rw [h1]
        _ = m ^ 2 ^ k * x := by group
    obtain ⟨j, hj⟩ := hQ₀2 ⟨_, hmk⟩
    refine ⟨k + j, ?_⟩
    have h1 : (m ^ 2 ^ k) ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
    rw [pow_add, pow_mul, h1]
  have hQtop : Q₀ = ⊤ := top_unique (le_sSup ⟨normal_top, hM2.to_subgroup ⊤⟩)
  have hQM : CFSG.inSubgroup (CFSG.pCore 2) M = M := by
    rw [CFSG.inSubgroup, ← hQ₀, hQtop, ← MonoidHom.range_eq_map, range_subtype]
  have hMcyc : IsCyclic M := hQM ▸ hcyc
  have hMsyl : IsSylowOf 2 M ⊤ := hSyl (CFSG.ABGLocalTools.isSylowOf_iff.mpr
    ⟨le_rfl, hM2, by rw [relIndex_self]; norm_num⟩)
  obtain ⟨-, -, hidx⟩ := CFSG.ABGLocalTools.isSylowOf_iff.mp hMsyl
  rw [relIndex_top_right] at hidx
  have hrank := (CFSG.SectionRank.pRank_sylow (hM2.toSylow hidx)).1
  rw [IsPGroup.toSylow_coe, ← CFSG.SectionRank.pRank_eq_open_pRank_top] at hrank
  obtain ⟨E, hEM, hE, hEcard⟩ := CFSG.SectionRank.exists_pRank Nat.one_lt_two M
  have : IsCyclic E := isCyclic_of_surjective (subgroupOfEquivOfLe hEM).toMonoidHom
    (MulEquiv.surjective _)
  have hE2 := card_le_two_of_isCyclic (X := E) fun x =>
    Subtype.ext (by rw [SubgroupClass.coe_pow, OneMemClass.coe_one]; exact hE.2 x x.2)
  rw [hEcard, hrank] at hE2
  have h8 : 2 ^ 3 ≤ 2 ^ CFSG.pRank 2 G := Nat.pow_le_pow_right two_pos h3
  omega

end SteinbergCH

open SteinbergCH

theorem gf2_witness_centralizer_and_rank
    {G : Type*} [Group G] [Finite G]
    (hchar : IsCharacteristicPType G 2) {M B : Subgroup G} (hM : GLAIsMaxTwoLocal M)
    (hsym : GLASymplecticType (pCoreOf 2 M)) (hB : GLAIsBmax 3 B) (hBM : B ≤ M)
    {Q : Subgroup G} (hQ : Q = CFSG.inSubgroup (CFSG.pCore 2) M) {r : ℕ}
    (hr : r = GLATwoLocalRank 3 G) :
    (∃ z ∈ (center Q).map Q.subtype, orderOf z = 2 ∧
      (∀ y ∈ (center Q).map Q.subtype, orderOf y = 2 → y = z) ∧
      M = centralizer {z} ∧ M = normalizer (Q : Set G) ∧
      M = normalizer ((center Q).map Q.subtype : Set G) ∧
      ∀ S : Subgroup G, IsSylowOf 2 S M → IsSylowOf 2 S ⊤ ∧ omegaOneCenterOf 2 S = zpowers z) ∧
    (CFSG.generalizedFitting M).map M.subtype = Q ∧ Q ≠ ⊥ ∧
    Nat.card B = 3 ^ r ∧ CFSG.Open.pRank 3 M = r ∧
    (∀ b ∈ B, (∀ q ∈ Q, q⁻¹ * (b * q * b⁻¹) ∈ (frattini Q).map Q.subtype) → b = 1) ∧
    (∃ d : ℕ, Nat.card (Q ⧸ frattini Q) = 2 ^ d ∧ 2 * r ≤ d) ∧
    (3 ≤ r → ∃ A : Subgroup Q, A.Normal ∧ IsElemAbelian 2 A ∧ Nat.card A = 8) ∧
    (3 ≤ CFSG.twoLocalOddRank G → 3 ≤ CFSG.pRank 2 G ∧ ¬ IsCyclic Q) := by
  subst hQ hr
  have hcharM : IsCharacteristicP 2 M := hchar M hM.1
  obtain ⟨hQne, -, z, hzZ, hzord, huniq, hMC, hMNQ, hMNZ, hSyl, -, hFstar, -⟩ :=
    symplectic_core_central_involution_sylow hM hcharM hsym
  have h2 : orderOf (2 : ZMod 3) = 2 := orderOf_eq_prime (by decide) (by decide)
  obtain ⟨⟨d, hd, hdr⟩, h8⟩ := twoCore_frattini_rank_and_eight Nat.prime_three (by norm_num)
    (CFSG.GH74.isCharTwoType_iff.mpr hchar) hM.1 hBM hB.1 hB.2.1
  rw [h2] at hdr h8
  refine ⟨⟨z, hzZ, hzord, huniq, hMC, hMNQ, hMNZ, fun S hS => ⟨(hSyl S hS).1, (hSyl S hS).2.2⟩⟩,
    by rw [hFstar]; rfl, hQne, hB.2.1, pRank_eq_twoLocalRank_of_le (by norm_num) hB hM.1 hBM,
    fun b hb htriv => eq_one_of_trivial_on_frattini_quotient hcharM (hBM hb) (by decide)
      (hB.1.2 b hb) htriv, ⟨d, hd, hdr⟩, fun hr3 => h8 (by omega), fun he => ?_⟩
  have hm2 := (large_local_rank_core_and_component_reduction hchar he).1
  exact ⟨hm2, not_isCyclic_twoCore hcharM (fun h => (hSyl M h).1) hm2⟩

end CFSG.LocalAnalysis.GorensteinLyons
