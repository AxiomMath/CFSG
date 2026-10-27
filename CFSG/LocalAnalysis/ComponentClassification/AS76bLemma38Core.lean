module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma37Core

public section

namespace CFSG.ComponentClassification.AS76b

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open Lemma34 Lemma22 Lemma37
open scoped Pointwise

section Product

variable {G : Type*} [Group G]

theorem exists_mul_of_mem_sup_of_le_normalizer {L H : Subgroup G}
    (hH : H ≤ normalizer (L : Set G)) {y : G} (hy : y ∈ L ⊔ H) :
    ∃ l ∈ L, ∃ h ∈ H, y = l * h := by
  have hy' : y ∈ ((L : Set G) * (H : Set G)) := by
    rw [← coe_mul_of_right_le_normalizer_left L H hH]
    exact hy
  obtain ⟨l, hl, h, hh, rfl⟩ := hy'
  exact ⟨l, hl, h, hh, rfl⟩

theorem surjective_mul_sup {L H : Subgroup G} (hH : H ≤ normalizer (L : Set G)) :
    Function.Surjective (fun p : L × H =>
      (⟨(p.1 : G) * p.2, mul_mem_sup p.1.2 p.2.2⟩ : ↥(L ⊔ H))) := by
  intro y
  obtain ⟨l, hl, h, hh, hlh⟩ := exists_mul_of_mem_sup_of_le_normalizer hH y.2
  exact ⟨(⟨l, hl⟩, ⟨h, hh⟩), Subtype.ext hlh.symm⟩

variable [Finite G]

theorem card_sup_le_mul {L H : Subgroup G} (hH : H ≤ normalizer (L : Set G)) :
    Nat.card ↥(L ⊔ H) ≤ Nat.card L * Nat.card H := by
  rw [← Nat.card_prod]
  exact Nat.card_le_card_of_surjective _ (surjective_mul_sup hH)

omit [Finite G] in
theorem card_sup_eq_mul {L H : Subgroup G} (hH : H ≤ normalizer (L : Set G))
    (hLH : L ⊓ H = ⊥) : Nat.card ↥(L ⊔ H) = Nat.card L * Nat.card H := by
  rw [← Nat.card_prod]
  symm
  refine Nat.card_congr (Equiv.ofBijective _ ⟨fun p q hpq => ?_, surjective_mul_sup hH⟩)
  exact mul_injective_of_disjoint (disjoint_iff.mpr hLH) (congrArg Subtype.val hpq)

theorem inf_eq_bot_of_card_sup {L H : Subgroup G} (hH : H ≤ normalizer (L : Set G))
    (hcard : Nat.card L * Nat.card H ≤ Nat.card ↥(L ⊔ H)) : L ⊓ H = ⊥ := by
  rw [← Nat.card_prod] at hcard
  have hinj := ((surjective_mul_sup hH).bijective_of_nat_card_le hcard).1
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨hzL, hzH⟩ := mem_inf.mp hz
  have h := @hinj (⟨z, hzL⟩, 1) (1, ⟨z, hzH⟩) (Subtype.ext (by simp))
  have h1 := congrArg (fun p : L × H => (p.1 : G)) h
  simpa using h1

end Product

section Normal

variable {G : Type} [Group G] [Finite G]

theorem le_normalizer_of_normal {W L R T : Subgroup G} (hLW : L ≤ centralizer (W : Set G))
    (hRL : R ≤ centralizer (L : Set G))
    (hRS : IsSylowOf 2 R
      (centralizer (W : Set G) ⊓ centralizer (L : Set G) ⊓ normalizer (R : Set G)))
    (hTRL : T ≤ R ⊔ L) (hTL : T ⊓ L = ⊥) (hTR : Nat.card T = Nat.card R)
    (hN : (L.subgroupOf (centralizer (W : Set G))).Normal) :
    centralizer (W : Set G) ⊓ centralizer (T : Set G) ≤ normalizer (R : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRN : R ≤ normalizer (L : Set G) := hRL.trans (centralizer_le_normalizer _)
  have hRLN : R ⊔ L ≤ normalizer (L : Set G) := sup_le hRN le_normalizer
  have hTN : T ≤ normalizer (L : Set G) := hTRL.trans hRLN
  have hRL' : R ⊔ L = L ⊔ R := sup_comm R L
  have hLT : L ⊔ T ≤ L ⊔ R := sup_le le_sup_left (hTRL.trans hRL'.le)
  have hcardT : Nat.card ↥(L ⊔ T) = Nat.card L * Nat.card R := by
    rw [card_sup_eq_mul hTN (by rw [inf_comm]; exact hTL), hTR]
  have hle : Nat.card ↥(L ⊔ R) ≤ Nat.card L * Nat.card R := card_sup_le_mul hRN
  have hTeq : L ⊔ T = L ⊔ R :=
    eq_of_le_of_card_ge hLT (hle.trans hcardT.ge)
  have hLR : L ⊓ R = ⊥ :=
    inf_eq_bot_of_card_sup hRN ((card_le_of_le hLT).trans' hcardT.ge)
  have hWL : centralizer (W : Set G) ≤ normalizer (L : Set G) :=
    le_normalizer_of_normal_subgroupOf hLW hN
  intro x hx
  obtain ⟨hxW, hxT⟩ := mem_inf.mp hx
  have hxL : x ∈ normalizer (L : Set G) := hWL hxW
  have hxLT : x ∈ normalizer ((L ⊔ T : Subgroup G) : Set G) :=
    le_normalizer_sup (A := normalizer (L : Set G) ⊓ normalizer (T : Set G)) inf_le_left
      inf_le_right ⟨hxL, centralizer_le_normalizer _ hxT⟩
  have hconj : conj R x ≤ R := by
    intro y hy
    set r := x⁻¹ * y * x with hr
    have hrR : r ∈ R := mem_conj_iff.mp hy
    have hy_eq : y = x * r * x⁻¹ := by rw [hr]; group
    have hyC : y ∈ centralizer (L : Set G) := by
      rw [mem_centralizer_iff]
      intro l hl
      have hl' : x⁻¹ * l * x ∈ L := by
        have := (mem_normalizer_iff.mp (inv_mem hxL) l).mp hl
        simpa using this
      have hcomm := mem_centralizer_iff.mp (hRL hrR) _ hl'
      rw [hy_eq]
      calc l * (x * r * x⁻¹) = x * ((x⁻¹ * l * x) * r) * x⁻¹ := by group
        _ = x * (r * (x⁻¹ * l * x)) * x⁻¹ := by rw [hcomm]
        _ = x * r * x⁻¹ * l := by group
    have hyLR : y ∈ L ⊔ R := by
      rw [← hTeq]
      have hr' : r ∈ L ⊔ T := hTeq ▸ (le_sup_right : R ≤ L ⊔ R) hrR
      rw [hy_eq]
      exact (mem_normalizer_iff.mp hxLT r).mp hr'
    obtain ⟨l, hl, r', hr', hlr⟩ := exists_mul_of_mem_sup_of_le_normalizer hRN hyLR
    have hlC : l ∈ centralizer (L : Set G) := by
      have : l = y * r'⁻¹ := by rw [hlr]; group
      rw [this]
      exact mul_mem hyC (inv_mem (hRL hr'))
    have hcomm : l * r' = r' * l := mem_centralizer_iff.mp (hRL hr') l hl
    obtain ⟨k, hk⟩ := hRS.isPGroup ⟨r, hrR⟩
    obtain ⟨j, hj⟩ := hRS.isPGroup ⟨r', hr'⟩
    have hrk : r ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hrj : r' ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
    have hyk : y ^ 2 ^ k = 1 := by
      rw [hy_eq, conj_pow, hrk, mul_one, mul_inv_cancel]
    have hyr : Commute y r' := by
      change y * r' = r' * y
      calc y * r' = l * r' * r' := by rw [hlr]
        _ = r' * l * r' := by rw [hcomm]
        _ = r' * y := by rw [hlr, mul_assoc]
    have hl_eq : l = y * r'⁻¹ := by rw [hlr]; group
    have hl2 : l ^ 2 ^ (k + j) = 1 := by
      rw [hl_eq, (hyr.inv_right).mul_pow, inv_pow, pow_add, pow_mul, hyk, one_pow, one_mul,
        mul_comm, pow_mul, hrj, one_pow, inv_one]
    have hlY : l ∈ centralizer (W : Set G) ⊓ centralizer (L : Set G) ⊓ normalizer (R : Set G) :=
      ⟨⟨hLW hl, hlC⟩, centralizer_le_normalizer _ (le_centralizer_iff.mp hRL hl)⟩
    have hP : IsPGroup 2 ↥(zpowers l ⊔ R) :=
      IsPGroup.to_sup_of_normal_right' (isPGroup_zpowers_of_pow_eq_one hl2) hRS.isPGroup
        ((zpowers_le.mpr hlY).trans inf_le_right)
    have heq : zpowers l ⊔ R = R :=
      hRS.eq_of_le le_sup_right (sup_le (zpowers_le.mpr hlY) hRS.le) hP
    have hlR : l ∈ R := heq ▸ mem_sup_left (mem_zpowers l)
    have hl1 : l = 1 := by
      have : l ∈ L ⊓ R := mem_inf.mpr ⟨hl, hlR⟩
      rwa [hLR, mem_bot] at this
    rw [hlr, hl1, one_mul]
    exact hr'
  have hcard : Nat.card R ≤ Nat.card (conj R x) := (card_conj R x).ge
  exact conj_eq_self_iff.mp (eq_of_le_of_card_ge hconj hcard)

theorem not_normal_of_card_eq {W L R T : Subgroup G} (hLW : L ≤ centralizer (W : Set G))
    (hRL : R ≤ centralizer (L : Set G))
    (hRS : IsSylowOf 2 R
      (centralizer (W : Set G) ⊓ centralizer (L : Set G) ⊓ normalizer (R : Set G)))
    (hTRL : T ≤ R ⊔ L) (hTL : T ⊓ L = ⊥) (hTR : Nat.card T = Nat.card R)
    (hRT : ¬ centralizer (W : Set G) ⊓ centralizer (T : Set G) ≤ normalizer (R : Set G)) :
    ¬ (L.subgroupOf (centralizer (W : Set G))).Normal :=
  fun hN => hRT (le_normalizer_of_normal hLW hRL hRS hTRL hTL hTR hN)

end Normal

section Lemma38

variable {G : Type} [Group G] [Finite G]

theorem lemma38_of_noConj_of_le (h4 : Asc75Theorem4) (h32 : Lemma32) (h34 : Asc08Lemma34)
    {A W L R T : Subgroup G} (hA : Hyp31 A) (hR : IsSylowOf 2 R (centralizer (A : Set G)))
    (hWA : W ≤ A) (hL : CFSG.Open.IsQuasisimple ↥L) (hLA : L ≤ A ⊓ centralizer (W : Set G))
    (hNL : normalizer (A : Set G) ⊓ centralizer (W : Set G) ≤ normalizer (L : Set G))
    (hRL : IsSylowOf 2 R
      (centralizer (W : Set G) ⊓ centralizer (L : Set G) ⊓ normalizer (R : Set G)))
    (hTRL : T ≤ R ⊔ L) (hTL : T ⊓ L = ⊥) (hTR : Nat.card T = Nat.card R)
    (hRT : ¬ centralizer (W : Set G) ⊓ centralizer (T : Set G) ≤ normalizer (R : Set G))
    (hconj : ∀ U : Subgroup G, U ≤ R → U ≠ ⊥ → ∀ g : G, ¬ conj U g ≤ L) :
    standardComponentIsStandard (L.subgroupOf (centralizer (W : Set G))) ∧
      ¬ (L.subgroupOf (centralizer (W : Set G))).Normal := by
  have hRCL : R ≤ centralizer (L : Set G) :=
    hR.le.trans (centralizer_le fun x hx => (hLA hx).1)
  refine ⟨?_, not_normal_of_card_eq (hLA.trans inf_le_right) hRCL hRL hTRL hTL hTR hRT⟩
  rcases lemma37_core_of_le h4 h32 h34 hA hR hWA hL hLA hNL hRL with h | ⟨c, -, -, -, hS⟩
  · exact h
  · exfalso
    have hU : R ⊓ conj L c ≠ ⊥ := by
      intro hbot
      apply not_le_centralizer_of_isSylowOf (isQuasisimple_conj hL c) hS
      rw [hbot]
      exact bot_le
    apply hconj _ inf_le_left hU c⁻¹
    calc conj (R ⊓ conj L c) c⁻¹ ≤ conj (conj L c) c⁻¹ := map_mono inf_le_right
      _ = L := by rw [conj_conj, inv_mul_cancel, conj_one]

theorem lemma38_of_noConj (h4 : Asc75Theorem4) (h32 : Lemma32) (h34 : Asc08Lemma34)
    {A W R T : Subgroup G} (hA : Hyp31 A) (hR : IsSylowOf 2 R (centralizer (A : Set G)))
    (hWA : W ≤ A) (hL : CFSG.Open.IsQuasisimple ↥(layerCentralizer A W))
    (hRL : IsSylowOf 2 R (centralizer (W : Set G) ⊓
      centralizer (layerCentralizer A W : Set G) ⊓ normalizer (R : Set G)))
    (hTRL : T ≤ R ⊔ layerCentralizer A W) (hTL : T ⊓ layerCentralizer A W = ⊥)
    (hTR : Nat.card T = Nat.card R)
    (hRT : ¬ centralizer (W : Set G) ⊓ centralizer (T : Set G) ≤ normalizer (R : Set G))
    (hconj : ∀ U : Subgroup G, U ≤ R → U ≠ ⊥ → ∀ g : G, ¬ conj U g ≤ layerCentralizer A W) :
    standardComponentIsStandard ((layerCentralizer A W).subgroupOf (centralizer (W : Set G))) ∧
      ¬ ((layerCentralizer A W).subgroupOf (centralizer (W : Set G))).Normal :=
  lemma38_of_noConj_of_le h4 h32 h34 hA hR hWA hL (layerCentralizer_le A W)
    (normalizer_inf_le_normalizer_layerCentralizer A W) hRL hTRL hTL hTR hRT hconj

end Lemma38

end CFSG.ComponentClassification.AS76b
