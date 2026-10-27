module

public import CFSG.LieType.Steinberg.CentralExt.GriessNativeModels
public import CFSG.LocalAnalysis.ComponentClassification.TBLitInputs

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts.EvenCover

open CFSG Subgroup CFSG.Assembly.LowTwoRank CFSG.Blueprint.Multiplier
open CFSG.LieType.Steinberg.CentralExt

theorem card_center_dvd_hopf {G : Type} [Group G] [Finite G] (hq : IsQuasisimple G) :
    Nat.card (center G) ∣ Nat.card (CFSG.Open.griessHopfMultiplier (G ⧸ center G)) := by
  have : Group.IsPerfect G := hq.1
  have : Group.IsPerfect (G ⧸ center G) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (center G))
      (QuotientGroup.mk'_surjective _)
  obtain ⟨-, h, -, -, -, -, e, -⟩ :=
    RankThree.PerfectCover.perfect_central_kernel_quotient_of_hopf_multiplier
      (S := G ⧸ center G) (QuotientGroup.mk' (center G)) (QuotientGroup.mk'_surjective _)
      (by rw [QuotientGroup.ker_mk'])
  rw [Nat.card_congr (RankThree.PerfectCover.hopfMultiplierEquivGriess _).toEquiv]
  have hk : Nat.card (center G) = Nat.card (QuotientGroup.mk' (center G)).ker := by
    rw [QuotientGroup.ker_mk']
  rw [hk, ← Nat.card_congr e.toEquiv]
  exact Subgroup.card_quotient_dvd_card _

@[expose] def tableOrder (t : StatedLieTag) (n p f : ℕ) : ℕ :=
  (genericOrders t n p f).1 * (genericOrders t n p f).2 *
    ((exceptionalOrders t n p f).1 * (exceptionalOrders t n p f).2)

theorem card_center_dvd_tableOrder {G : Type} [Group G] [Finite G] (hq : IsQuasisimple G)
    {t : StatedLieTag} {n p f : ℕ} (hrow : GriessAll.GriessRow (G ⧸ center G) t n p f) :
    Nat.card (center G) ∣ tableOrder t n p f := by
  obtain ⟨-, ⟨e⟩⟩ := hrow
  have h := card_center_dvd_hopf hq
  have hm : ∀ k : ℕ, Nat.card (Multiplicative (ZMod k)) = k := fun k =>
    (Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod k) ≃ ZMod k)).trans
      (Nat.card_zmod k)
  rw [Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_prod, Nat.card_prod, hm, hm, hm,
    hm] at h
  exact h

theorem griessRow_of_classical (hGA : TBLit.GriessMultipliersAllModels) {X : Type} [Group X]
    {t : StatedLieTag} {n p f : ℕ} (hL : Blueprint.LieModel X t n p f)
    (ht : t ∈ Blueprint.classicalTags) : GriessAll.GriessRow X t n p f :=
  hGA X t n p f
    (GriessNative.models_lieModel_of_classical (GriessNative.classical_of_lieModel hL ht))

theorem griessRow_of_exceptional_two
    {X : Type} [Group X] {t : StatedLieTag} {n f : ℕ} (hL : Blueprint.LieModel X t n 2 f)
    (ht : t ∉ Blueprint.classicalTags)
    (hne : ¬ ((t = .G2 ∧ f = 2) ∨ (t = .F4 ∧ f = 1) ∨ (t = .twistedE6 ∧ f = 1))) :
    GriessAll.GriessRow X t n 2 f := by
  have hadm := GriessNative.admissible_of_lieModel hL
  cases t
  · exact absurd (by decide) ht
  · exact absurd (by decide) ht
  · exact absurd (by decide) ht
  · exact absurd (by decide) ht
  · exact absurd (by decide) ht
  · exact absurd (by decide) ht
  · obtain ⟨rfl, h⟩ := GriessNative.chevalley_of_lieModel hL (by decide)
    have hq : 3 ≤ 2 ^ f := hadm.2.2.2
    have hf3 : 3 ≤ f := by
      by_contra h3
      have : f = 2 := by
        interval_cases f <;> simp_all
      exact hne (Or.inl ⟨rfl, this⟩)
    exact GriessNative.g2_row h
      (show 5 ≤ 2 ^ f from le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hf3))
  · obtain ⟨rfl, h⟩ := GriessNative.chevalley_of_lieModel hL (by decide)
    have hf : 1 ≤ f := hadm.2.1
    have hf2 : 2 ≤ f := by
      by_contra h1
      exact hne (Or.inr (Or.inl ⟨rfl, by omega⟩))
    exact GriessNative.f4_row h
      (show 3 ≤ 2 ^ f from le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hf2))
  · obtain ⟨rfl, h⟩ := GriessNative.chevalley_of_lieModel hL (by decide)
    exact GriessNative.e6_row h
  · obtain ⟨rfl, h⟩ := GriessNative.chevalley_of_lieModel hL (by decide)
    exact GriessNative.e7_row h
  · obtain ⟨rfl, h⟩ := GriessNative.chevalley_of_lieModel hL (by decide)
    exact GriessNative.e8_row h
  · obtain ⟨rfl, h⟩ := GriessNative.chevalley_of_lieModel hL (by decide)
    have hf : 1 ≤ f := hadm.2.1
    have hf2 : 2 ≤ f := by
      by_contra h1
      exact hne (Or.inr (Or.inr ⟨rfl, by omega⟩))
    exact GriessNative.twistedE6_row h
      (show 3 ≤ 2 ^ f from le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hf2))
  · obtain ⟨rfl, h⟩ := GriessNative.chevalley_of_lieModel hL (by decide)
    exact GriessNative.trialityD4_row h
  · obtain ⟨rfl, -⟩ := GriessNative.suzuki_of_lieModel hL
    exact GriessNative.twistedB2_row hL
  · exact absurd hadm.2.2.2.1 (by norm_num)
  · obtain ⟨rfl, -⟩ := GriessNative.reeTits_of_lieModel hL (by decide)
    exact GriessNative.twistedF4_row hL
  · obtain ⟨rfl, -⟩ := GriessNative.reeTits_of_lieModel hL (by decide)
    exact GriessNative.tits_row hL

theorem not_two_dvd_generic {t : StatedLieTag} {n f : ℕ} (hadm : StatedLieAdmissible t n 2 f) :
    ¬ 2 ∣ (genericOrders t n 2 f).1 * (genericOrders t n 2 f).2 := by
  have hf : 1 ≤ f := hadm.2.1
  have hev : Even (2 ^ f) := (Nat.even_pow' (by omega)).2 even_two
  have h4 : ∀ k, 1 ≤ k → ¬ 2 ∣ (2 ^ f) ^ k - 1 := by
    intro k hk
    rw [← even_iff_two_dvd, Nat.even_sub' (Nat.one_le_pow _ _ (by positivity))]
    simp [(Nat.even_pow' (by omega : k ≠ 0)).2 hev]
  have h3 : ∀ k, 1 ≤ k → ¬ 2 ∣ (2 ^ f) ^ k + 1 := by
    intro k hk
    rw [← even_iff_two_dvd, Nat.even_add_one, not_not]
    exact (Nat.even_pow' (by omega)).2 hev
  have h1 : ¬ 2 ∣ 2 ^ f - 1 := by simpa using h4 1 le_rfl
  have h2 : ¬ 2 ∣ 2 ^ f + 1 := by simpa using h3 1 le_rfl
  have g3 : ∀ a, ¬ 2 ∣ Nat.gcd 3 a := fun a h => by
    have := h.trans (Nat.gcd_dvd_left 3 a)
    omega
  cases t
  · show ¬ 2 ∣ Nat.gcd n (2 ^ f - 1) * 1
    rw [mul_one]
    exact fun h => h1 (h.trans (Nat.gcd_dvd_right _ _))
  · show ¬ 2 ∣ Nat.gcd n (2 ^ f + 1) * 1
    rw [mul_one]
    exact fun h => h2 (h.trans (Nat.gcd_dvd_right _ _))
  · show ¬ 2 ∣ Nat.gcd 2 (2 ^ f - 1) * 1
    rw [mul_one]
    exact fun h => h1 (h.trans (Nat.gcd_dvd_right _ _))
  · exact absurd rfl hadm.2.2.2
  · have : genericOrders .POmegaPlus n 2 f = (1, 1) := by
      simp only [genericOrders, hev, ↓reduceIte]
    rw [this]
    norm_num
  · show ¬ 2 ∣ Nat.gcd 4 ((2 ^ f) ^ n + 1) * 1
    rw [mul_one]
    exact fun h => h3 n (by have := hadm.2.2; omega) (h.trans (Nat.gcd_dvd_right _ _))
  all_goals first
    | (show ¬ 2 ∣ 1 * 1; norm_num)
    | (show ¬ 2 ∣ Nat.gcd 3 (2 ^ f - 1) * 1; rw [mul_one]; exact g3 _)
    | (show ¬ 2 ∣ Nat.gcd 3 (2 ^ f + 1) * 1; rw [mul_one]; exact g3 _)
    | (show ¬ 2 ∣ Nat.gcd 2 (2 ^ f - 1) * 1; rw [mul_one];
        exact fun h => h1 (h.trans (Nat.gcd_dvd_right _ _)))

@[expose] def IsTwelve (t : StatedLieTag) (n f : ℕ) : Prop :=
  (t = .PSL ∧ n = 2 ∧ f = 2) ∨ (t = .PSL ∧ n = 3 ∧ f = 1) ∨ (t = .PSL ∧ n = 4 ∧ f = 1) ∨
    (t = .PSU ∧ n = 4 ∧ f = 1) ∨ (t = .PSp ∧ n = 3 ∧ f = 1) ∨ (t = .G2 ∧ n = 0 ∧ f = 2) ∨
    (t = .F4 ∧ n = 0 ∧ f = 1) ∨ (t = .POmegaPlus ∧ n = 4 ∧ f = 1) ∨ (t = .PSU ∧ n = 6 ∧ f = 1) ∨
    (t = .twistedB2 ∧ n = 0 ∧ f = 3) ∨ (t = .twistedE6 ∧ n = 0 ∧ f = 1) ∨
    (t = .PSL ∧ n = 3 ∧ f = 2)

theorem twelve_of_two_dvd {t : StatedLieTag} {n f : ℕ} (hadm : StatedLieAdmissible t n 2 f)
    (h2 : 2 ∣ tableOrder t n 2 f) : IsTwelve t n f := by
  unfold tableOrder at h2
  rcases (Nat.Prime.dvd_mul Nat.prime_two).1 h2 with h | h
  · exact absurd h (not_two_dvd_generic hadm)
  · unfold IsTwelve
    unfold exceptionalOrders at h
    split at h <;> simp_all

theorem twelve_of_even_center
    (hGA : TBLit.GriessMultipliersAllModels) {G : Type} [Group G] [Finite G] (hq : IsQuasisimple G)
    {t : StatedLieTag} {n f : ℕ} (hL : Blueprint.LieModel (G ⧸ center G) t n 2 f)
    (h2 : 2 ∣ Nat.card (center G)) : IsTwelve t n f := by
  have hadm := GriessNative.admissible_of_lieModel hL
  by_cases hcl : t ∈ Blueprint.classicalTags
  · exact twelve_of_two_dvd hadm
      (h2.trans (card_center_dvd_tableOrder hq (griessRow_of_classical hGA hL hcl)))
  · by_cases hne : (t = .G2 ∧ f = 2) ∨ (t = .F4 ∧ f = 1) ∨ (t = .twistedE6 ∧ f = 1)
    · have hn : n = 0 := by
        rcases hne with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
        all_goals exact (GriessNative.chevalley_of_lieModel hL (by decide)).1
      unfold IsTwelve
      rcases hne with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [hn]
    · exact twelve_of_two_dvd hadm
        (h2.trans (card_center_dvd_tableOrder hq (griessRow_of_exceptional_two hL hcl hne)))

theorem card_center_dvd_L34 (hGA : TBLit.GriessMultipliersAllModels) {G : Type} [Group G]
    [Finite G] (hq : IsQuasisimple G) (hL : Blueprint.LieModel (G ⧸ center G) .PSL 3 2 2) :
    Nat.card (center G) ∣ 48 :=
  (card_center_dvd_tableOrder hq (griessRow_of_classical hGA hL (by decide))).trans
    (by decide)

theorem card_center_dvd_U42 (hGA : TBLit.GriessMultipliersAllModels) {G : Type} [Group G]
    [Finite G] (hq : IsQuasisimple G) (hL : Blueprint.LieModel (G ⧸ center G) .PSU 4 2 1) :
    Nat.card (center G) ∣ 2 :=
  (card_center_dvd_tableOrder hq (griessRow_of_classical hGA hL (by decide))).trans
    (by decide)

theorem card_center_dvd_U62 (hGA : TBLit.GriessMultipliersAllModels) {G : Type} [Group G]
    [Finite G] (hq : IsQuasisimple G) (hL : Blueprint.LieModel (G ⧸ center G) .PSU 6 2 1) :
    Nat.card (center G) ∣ 12 :=
  (card_center_dvd_tableOrder hq (griessRow_of_classical hGA hL (by decide))).trans
    (by decide)

theorem card_center_dvd_O82 (hGA : TBLit.GriessMultipliersAllModels) {G : Type} [Group G]
    [Finite G] (hq : IsQuasisimple G) (hL : Blueprint.LieModel (G ⧸ center G) .POmegaPlus 4 2 1) :
    Nat.card (center G) ∣ 4 :=
  (card_center_dvd_tableOrder hq (griessRow_of_classical hGA hL (by decide))).trans
    (by decide)

end CFSG.ComponentClassification.GrSLit.L34Facts.EvenCover
