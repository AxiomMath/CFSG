module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltOpenDefs
public import CFSG.Sporadic.Schreier.MathieuOddCoreM12Card
public import CFSG.GroupTheory.InvolutionFixedCentralSylow

public section

namespace CFSG.ComponentClassification.RankTwoAlt

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.Blueprint
  CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.RankTwoStandard CFSG.ComponentClassification.AS76b

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem inf_eq_bot_of_odd_center {A R : Subgroup G} (hodd : Odd (Nat.card (center ↥A)))
    (hR : IsPGroup 2 R) (hRA : R ≤ centralizer (A : Set G)) : A ⊓ R = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxA, hxR⟩ := mem_inf.mp hx
  have hyc : (⟨x, hxA⟩ : ↥A) ∈ center ↥A := mem_center_iff.mpr fun a =>
    Subtype.ext (mem_centralizer_iff.mp (hRA hxR) a a.2)
  have hdvd : orderOf x ∣ Nat.card (center ↥A) := by
    have h := orderOf_dvd_natCard (⟨⟨x, hxA⟩, hyc⟩ : center ↥A)
    rwa [Subgroup.orderOf_mk, Subgroup.orderOf_mk] at h
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hR) ⟨x, hxR⟩
  rw [Subgroup.orderOf_mk] at hk
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rw [pow_zero, orderOf_eq_one_iff] at hk
    exact mem_bot.mpr hk
  · exfalso
    have h2 : 2 ∣ Nat.card (center ↥A) :=
      (dvd_pow_self 2 hk0.ne').trans (hk ▸ hdvd)
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)

theorem altFiveM12NotTop_of :
    AltFiveM12NotTop := by
  intro G _ _ A hH _ hA5 hodd R hR _ hM12 ht hX
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, ht2, htA, htR, hout⟩ := ht
  obtain ⟨e⟩ := hM12
  obtain ⟨eq⟩ := hA5
  let eG : G ≃* NativeSporadic.Carrier .M12 :=
    (Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr hX.symm)).trans e
  have hR4 : 4 ≤ Nat.card R := by
    obtain ⟨U, hUK, hU, hU4⟩ := RankTwoSporadic.exists_four_le_of_two_le_pRank hH.rank
    obtain ⟨S, hS, hUS⟩ :=
      exists_isSylowOf_le hUK (fun v => ⟨1, Subtype.ext (by simpa using hU.2 v v.2)⟩)
    obtain ⟨c, -, hSc⟩ := Lemma22.exists_conj_eq_of_isSylowOf hR hS
    have h4 := Subgroup.card_le_of_le hUS
    rw [hSc, Lemma34.card_conj, hU4] at h4
    exact h4
  have hA60 : 60 ≤ Nat.card A := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (center ↥A)
    have h2 : Nat.card (↥A ⧸ center ↥A) = 60 := by
      rw [show (↥A ⧸ center ↥A) = rankTwoQuot A from rfl, Nat.card_congr eq.toEquiv]
      exact RankTwoAltFive.card_A5
    have h3 : 0 < Nat.card (center ↥A) := Nat.card_pos
    rw [h1, h2]
    omega
  have ht1 : t ≠ 1 := by
    rintro rfl
    exact hout ⟨1, one_mem A, fun y _ => by group⟩
  have hto : orderOf t = 2 := orderOf_eq_prime ht2 ht1
  have hRA : R ≤ centralizer (A : Set G) := hR.le
  have hAR : A ≤ normalizer (R : Set G) :=
    (le_centralizer_iff.mp hRA).trans (centralizer_le_normalizer _)
  have htAR : t ∉ A ⊔ R := by
    intro htm
    have h1 : t ∈ ((A ⊔ R : Subgroup G) : Set G) := htm
    rw [coe_mul_of_left_le_normalizer_right A R hAR] at h1
    obtain ⟨a, ha, r, hr, har⟩ := h1
    refine hout ⟨a, ha, fun y hy => ?_⟩
    have hry : r * y = y * r := (mem_centralizer_iff.mp (hRA hr) y hy).symm
    rw [← har]
    calc a * r * y * (a * r)⁻¹ = a * (r * y) * r⁻¹ * a⁻¹ := by group
      _ = a * y * a⁻¹ := by rw [hry]; group
  have htN : zpowers t ≤ normalizer (R : Set G) := zpowers_le.mpr htR
  have hT2 : IsPGroup 2 (zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hto, pow_one])
  have hW : IsPGroup 2 ↥(zpowers t ⊔ R) := hT2.to_sup_of_normal_right' hR.isPGroup htN
  have hWN : zpowers t ⊔ R ≤ normalizer (R : Set G) := sup_le htN le_normalizer
  have hReven : Even (Nat.card R) := by
    obtain ⟨k, hk⟩ := hR.isPGroup.exists_card_eq
    rw [hk] at hR4 ⊢
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · norm_num at hR4
    · exact (Nat.even_pow' hk0.ne').mpr even_two
  obtain ⟨r₀, hr₀R, hr₀o, hr₀c⟩ :=
    CFSG.GroupTheory.exists_involution_commute_of_isPGroup_le_normalizer hW hWN hReven
  have hCA : A ≤ centralizer ({r₀} : Set G) := fun a ha =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp (hRA hr₀R) a ha)
  have hCW : zpowers t ⊔ R ≤ centralizer ({r₀} : Set G) := fun p hp =>
    mem_centralizer_singleton_iff.mpr (hr₀c p hp)
  have hle : (A ⊔ R) ⊔ zpowers t ≤ centralizer ({r₀} : Set G) :=
    sup_le (sup_le hCA (le_sup_right.trans hCW)) (le_sup_left.trans hCW)
  have hcAR : Nat.card ↥(A ⊔ R) = Nat.card A * Nat.card R :=
    card_sup_eq_mul (hRA.trans (centralizer_le_normalizer _))
      (inf_eq_bot_of_odd_center hodd hR.isPGroup hRA)
  have hnT : zpowers t ≤ normalizer ((A ⊔ R : Subgroup G) : Set G) :=
    zpowers_le.mpr (RankTwoAltFive.mem_normalizer_sup htA htR)
  have hinf : (A ⊔ R) ⊓ zpowers t = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxAR, hxt⟩ := mem_inf.mp hx
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hxt
    rw [← zpow_mod_orderOf, hto] at hxAR ⊢
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · rw [show ((2 : ℕ) : ℤ) = 2 by rfl, h, zpow_zero]
      exact one_mem _
    · rw [show ((2 : ℕ) : ℤ) = 2 by rfl, h, zpow_one] at hxAR
      exact absurd hxAR htAR
  have hcard : Nat.card ↥((A ⊔ R) ⊔ zpowers t) = Nat.card A * Nat.card R * 2 := by
    rw [card_sup_eq_mul hnT hinf, hcAR, Nat.card_zpowers, hto]
  have h480 : 480 ≤ Nat.card (centralizer ({r₀} : Set G)) := by
    have h1 := Subgroup.card_le_of_le hle
    rw [hcard] at h1
    have h2 : 60 * 4 ≤ Nat.card A * Nat.card R := Nat.mul_le_mul hA60 hR4
    omega
  rcases Sporadic.Schreier.card_centralizer_involution_of_mulEquiv_M12 eG hr₀o with h | h <;>
    omega

end CFSG.ComponentClassification.RankTwoAlt
