module

import CFSG.Goldschmidt.Steps.G310Basic
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.CGT.PushingUpLit.BlocksCommuteClassX
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.Quasithin.Background.B6Sections

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L617P

open CFSG.Open Subgroup
open CFSG.CGT.PushingUp CFSG.CGT.PushingUpLit
open CFSG.RankThree.PartOne (shortU shortC IsShortGroup)
open scoped commutatorElement

theorem card_top_eq_three {G : Type} [Group G] [Finite G] {N Y : Subgroup G}
    (hY : IsBlockOfInX N Y) (hq : ¬ CFSG.IsQuasisimple (↥Y ⧸ CFSG.pCore 2 ↥Y)) :
    Nat.card (↥Y ⧸ CFSG.pCore 2 ↥Y) = 3 :=
  card_top_eq_three_of_inClassX hY.2.2 (hY.2.2.1.quotient_type.resolve_left hq)

theorem card_eq_three_mul {L : Type} [Group L] [Finite L]
    (hL : Nat.card (L ⧸ CFSG.pCore 2 L) = 3) : ∃ a : ℕ, Nat.card L = 3 * 2 ^ a := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := L))
  exact ⟨a, by rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 L), hL, ha]⟩

theorem exists_decomp {L : Type} [Group L] [Finite L] (hL : Nat.card (L ⧸ CFSG.pCore 2 L) = 3)
    {t : L} (ht : orderOf t = 3) (g : L) : ∃ c ∈ CFSG.pCore 2 L, ∃ k : ℤ, g = c * t ^ k := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have ht1 : (t : L ⧸ CFSG.pCore 2 L) ≠ 1 := by
    intro h
    have hmem : t ∈ CFSG.pCore 2 L := (QuotientGroup.eq_one_iff t).mp h
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := L)) ⟨t, hmem⟩
    have hk' : t ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have h3 : 3 ∣ 2 ^ k := ht ▸ orderOf_dvd_of_pow_eq_one hk'
    have h3' : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega
  have hz := zpowers_eq_top_of_prime_card hL ht1
  have hg : (g : L ⧸ CFSG.pCore 2 L) ∈ zpowers (t : L ⧸ CFSG.pCore 2 L) := by
    rw [hz]
    exact Subgroup.mem_top _
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hg
  refine ⟨g * t ^ (-k), ?_, k, by group⟩
  rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_zpow, ← hk]
  simp

theorem false_of_eq_mul_center {L : Type} [Group L] [Finite L] (hL : IsShortGroup L)
    (hdec : ∀ g : L, ∃ c ∈ CFSG.pCore 2 L, ∃ s ∈ Subgroup.center L, g = c * s) : False := by
  have hU : shortU L ≤ Subgroup.center L := by
    unfold shortU
    rw [Subgroup.commutator_le]
    intro a ha g _
    obtain ⟨c, hc, s, hs, rfl⟩ := hdec g
    have e1 : s * a⁻¹ = a⁻¹ * s := (Subgroup.mem_center_iff.mp hs a⁻¹).symm
    have hcomm : ⁅a, c * s⁆ = ⁅a, c⁆ := by
      calc ⁅a, c * s⁆ = a * c * (s * a⁻¹) * (s⁻¹ * c⁻¹) := by
            simp only [commutatorElement_def, mul_inv_rev]
            group
        _ = a * c * (a⁻¹ * s) * (s⁻¹ * c⁻¹) := by rw [e1]
        _ = ⁅a, c⁆ := by
            simp only [commutatorElement_def]
            group
    rw [hcomm]
    have hmemU : ⁅a, c⁆ ∈ shortU L :=
      Subgroup.commutator_mem_commutator ha (Subgroup.mem_top c)
    obtain ⟨u, hu, hue⟩ := hL.U_le_center hmemU
    rw [Subgroup.mem_center_iff]
    intro g'
    obtain ⟨c', hc', s', hs', rfl⟩ := hdec g'
    have h1 : (c' : L) * ⁅a, c⁆ = ⁅a, c⁆ * c' := by
      have := congrArg Subtype.val (Subgroup.mem_center_iff.mp hu ⟨c', hc'⟩)
      rw [← hue]
      simpa using this
    have h2 : s' * ⁅a, c⁆ = ⁅a, c⁆ * s' := (Subgroup.mem_center_iff.mp hs' ⁅a, c⁆).symm
    calc c' * s' * ⁅a, c⁆ = c' * (s' * ⁅a, c⁆) := by group
      _ = c' * (⁅a, c⁆ * s') := by rw [h2]
      _ = (c' * ⁅a, c⁆) * s' := by group
      _ = (⁅a, c⁆ * c') * s' := by rw [h1]
      _ = ⁅a, c⁆ * (c' * s') := by group
  have hC : CFSG.RankThree.PartOne.shortC L = shortU L := inf_eq_left.mpr hU
  have h := hL.nonzero
  rw [hC] at h
  exact lt_irrefl _ h

theorem exists_not_commute {G : Type} [Group G] [Finite G] {N Y : Subgroup G}
    (hY : IsBlockOfInX N Y) (hq : ¬ CFSG.IsQuasisimple (↥Y ⧸ CFSG.pCore 2 ↥Y)) {t : G}
    (htY : t ∈ Y) (ht : orderOf t = 3) : ∃ y ∈ Y, t * y ≠ y * t := by
  by_contra hcon
  push Not at hcon
  have hL := card_top_eq_three hY hq
  have ht₀ : orderOf (⟨t, htY⟩ : ↥Y) = 3 := by
    rw [← Subgroup.orderOf_coe]
    exact ht
  refine false_of_eq_mul_center hY.2.2.1 fun g => ?_
  obtain ⟨c, hc, k, hk⟩ := exists_decomp hL ht₀ g
  refine ⟨c, hc, (⟨t, htY⟩ : ↥Y) ^ k, ?_, hk⟩
  have hcen : (⟨t, htY⟩ : ↥Y) ∈ Subgroup.center ↥Y := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (hcon y y.2).symm
  exact Subgroup.zpow_mem _ hcen k

theorem exists_decomp_block {G : Type} [Group G] [Finite G] {N Y : Subgroup G}
    (hY : IsBlockOfInX N Y) (hq : ¬ CFSG.IsQuasisimple (↥Y ⧸ CFSG.pCore 2 ↥Y)) {t : G}
    (htY : t ∈ Y) (ht : orderOf t = 3) {g : G} (hg : g ∈ Y) :
    ∃ c ∈ pCoreOf 2 Y, ∃ k : ℤ, g = c * t ^ k := by
  have hL := card_top_eq_three hY hq
  have ht₀ : orderOf (⟨t, htY⟩ : ↥Y) = 3 := by
    rw [← Subgroup.orderOf_coe]
    exact ht
  obtain ⟨c, hc, k, hk⟩ := exists_decomp hL ht₀ ⟨g, hg⟩
  refine ⟨(c : G), ⟨c, hc, rfl⟩, k, ?_⟩
  have := congrArg Subtype.val hk
  simpa using this

theorem exists_zpowers_eq {G : Type} [Group G] [Finite G] {T : Subgroup G}
    (hT : Nat.card T = 3) : ∃ t : G, orderOf t = 3 ∧ T = zpowers t := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hnt : Nontrivial ↥T := Finite.one_lt_card_iff_nontrivial.mp (by rw [hT]; norm_num)
  obtain ⟨t, ht1⟩ := exists_ne (1 : ↥T)
  have hord : orderOf t = 3 := by
    have h1 : orderOf t ∣ 3 := hT ▸ orderOf_dvd_natCard t
    rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) ht1
    · exact h
  have hordG : orderOf (t : G) = 3 := by
    rw [Subgroup.orderOf_coe]
    exact hord
  refine ⟨(t : G), hordG, ?_⟩
  symm
  exact Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr t.2) (by rw [Nat.card_zpowers, hordG, hT])

theorem exists_invariant_three {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {A Y : Subgroup G} (hA : IsPGroup p A) (hcop : ¬ p ∣ Nat.card Y)
    (hAY : A ≤ normalizer (Y : Set G)) {a : ℕ} (hY : Nat.card Y = 3 * 2 ^ a) :
    ∃ T : Subgroup G, T ≤ Y ∧ Nat.card T = 3 ∧ A ≤ normalizer (T : Set G) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hbot3 : IsPGroup 3 (⊥ : Subgroup G) := IsPGroup.of_card (n := 0) (by simp)
  have hAbot : A ≤ normalizer ((⊥ : Subgroup G) : Set G) := by
    rw [normalizer_eq_top_iff.mpr inferInstance]
    exact le_top
  obtain ⟨T, hTs, -, hAT⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing hp
    Nat.prime_three hA hcop hAY bot_le hbot3 hAbot
  obtain ⟨P, hP⟩ := CFSG.Goldschmidt.G310.exists_sylow_of_fusionIsSylowIn hTs
  refine ⟨T, hTs.1, ?_, hAT⟩
  have hcard : Nat.card T = Nat.card (P : Subgroup ↥Y) := by
    rw [← hP]
    exact Subgroup.card_map_of_injective Y.subtype_injective
  have hfac : (3 * 2 ^ a).factorization 3 = 1 := by
    rw [Nat.factorization_mul (by norm_num) (by positivity), Finsupp.add_apply,
      Nat.Prime.factorization_self Nat.prime_three,
      Nat.factorization_eq_zero_of_not_dvd (fun h => by
        have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
        omega)]
  rw [hcard, P.card_eq_multiplicity, hY, hfac, pow_one]

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L617P
