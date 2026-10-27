module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma34
public import CFSG.GroupTheory.ThompsonIndexTwo
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveIIbOuter

public section

open Subgroup CFSG.Open CFSG.Blueprint CFSG.ABGLocalTools CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard CFSG.GH74.GLS.Bg.Thompson

namespace CFSG.ComponentClassification.RankTwoAltFive

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem le_of_isPGroup_quotient {X N : Subgroup G} (hXs : IsSimpleGroup X) (hX2 : ¬ IsPGroup 2 X)
    [N.Normal] (hNp : IsPGroup 2 (G ⧸ N)) : X ≤ N := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf X) with h1 | h1
  · exfalso
    apply hX2
    intro y
    obtain ⟨n, hn⟩ := hNp (QuotientGroup.mk (y : G))
    refine ⟨n, ?_⟩
    have h2 : (y : G) ^ 2 ^ n ∈ N := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
      exact hn
    have h3 : y ^ 2 ^ n ∈ N.subgroupOf X := by
      rw [mem_subgroupOf, coe_pow]
      exact h2
    rw [h1, mem_bot] at h3
    exact h3
  · intro y hy
    have h3 : (⟨y, hy⟩ : X) ∈ N.subgroupOf X := by
      rw [h1]
      exact mem_top _
    exact mem_subgroupOf.mp h3

theorem exists_conj_mem_of_thompson {X : Subgroup G} (hXs : IsSimpleGroup X)
    (hX2 : ¬ IsPGroup 2 X) {T U : Subgroup G} (hT : IsPGroup 2 T) (hTidx : ¬ 2 ∣ T.index)
    (hUT : U ≤ T) (hUidx : U.relIndex T = 2) {u : G} (huT : u ∈ T) (huU : u ∉ U) (huX : u ∈ X)
    (hb : ∀ (g : G) (k : ℕ), g⁻¹ * u ^ (2 * k) * g ∈ T → g⁻¹ * u ^ (2 * k) * g ∈ U) :
    ∃ g : G, g⁻¹ * u * g ∈ U ∧ IsExtremalIn 2 T (g⁻¹ * u * g) ∧
      ∀ c ∈ T ⊓ centralizer ({u} : Set G),
        g⁻¹ * c * g ∈ T ⊓ centralizer ({g⁻¹ * u * g} : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : (U.subgroupOf T).Normal := Subgroup.normal_of_index_eq_two hUidx
  have hQn : ∀ t ∈ T, ∀ q ∈ U, t * q * t⁻¹ ∈ U := fun t ht q hq =>
    Subgroup.mem_subgroupOf.1
      (hn.conj_mem ⟨q, hUT hq⟩ (Subgroup.mem_subgroupOf.2 hq) ⟨t, ht⟩)
  have hcyc : ∃ b ∈ T, ∀ t ∈ T, ∃ k : ℤ, (b ^ k)⁻¹ * t ∈ U := by
    refine ⟨u, huT, fun t ht => ?_⟩
    by_cases htU : t ∈ U
    · exact ⟨0, by simpa using htU⟩
    · exact ⟨1, by simpa using CFSG.ThompsonIndexTwo.inv_mul_mem_of_not_mem hUidx huT ht huU htU⟩
  have hc : ∀ g : G, g⁻¹ * u * g ∈ T → IsExtremalIn 2 T (g⁻¹ * u * g) →
      g⁻¹ * u * g ∈ U ∨ u⁻¹ * (g⁻¹ * u * g) ∈ U := by
    intro g hgT _
    by_cases hgU : g⁻¹ * u * g ∈ U
    · exact Or.inl hgU
    · exact Or.inr (CFSG.ThompsonIndexTwo.inv_mul_mem_of_not_mem hUidx huT hgT huU hgU)
  rcases thompson_transfer_1515 (p := 2) hT hTidx hQn hcyc huT huU hb hc with
    ⟨N, hN, -, hNp, huN⟩ | hg
  · exact absurd (le_of_isPGroup_quotient hXs hX2 hNp huX) huN
  · exact hg

namespace Setting310

variable {A R T V₀ : Subgroup G} {g : G} (h : Setting310 A R g T V₀)
include h

theorem toHyp31 : Hyp31 A := by
  obtain ⟨e⟩ := h.equiv
  have hZ : center ↥A = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have h1 : e x ∈ center A5 := mem_center_iff.mpr fun y => by
      obtain ⟨y', rfl⟩ := e.surjective y
      rw [← map_mul, ← map_mul, mem_center_iff.mp hx y']
    rw [alternatingGroup.center_eq_bot (by simp), mem_bot] at h1
    exact mem_bot.mpr (e.injective (h1.trans (map_one e).symm))
  exact ⟨h.hyp.standard, RankTwoClassical.hypIIAlt5 ↥A h.hyp.standard.1.1
    ⟨(QuotientGroup.quotientMulEquivOfEq hZ).trans (QuotientGroup.quotientBot.trans e)⟩,
    h.oddCore, by have := h.hyp.rank; omega, h.hyp.not_normal⟩

theorem isSimpleGroup_X : IsSimpleGroup ↥(rankTwoX A) := by
  obtain ⟨hXF, hXs⟩ := asc08Lemma34 G A h.toHyp31
  rw [show rankTwoX A = CFSG.generalizedFitting G from hXF]
  exact hXs

theorem not_isPGroup_X : ¬ IsPGroup 2 ↥(rankTwoX A) := by
  intro h2
  obtain ⟨eA⟩ := h.equiv
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAX : A ≤ rankTwoX A := le_normalClosure
  have hA2 : IsPGroup 2 A := fun a => by
    obtain ⟨n, hn⟩ := h2 ⟨a, hAX a.2⟩
    refine ⟨n, Subtype.ext ?_⟩
    have := congrArg Subtype.val hn
    simpa using this
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hA2
  rw [Nat.card_congr eA.toEquiv, card_A5] at hk
  have h4 : ¬ (3 : ℕ) ∣ 2 ^ k := fun h5 =>
    absurd ((Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 3) h5)) (by norm_num)
  exact h4 (hk ▸ (by norm_num : (3 : ℕ) ∣ 60))

theorem exists_conj_mem_of_thompson_X {T U : Subgroup G}
    (hT : IsSylowOf 2 T ⊤) (hUT : U ≤ T) (hUidx : U.relIndex T = 2) {u : G} (huT : u ∈ T)
    (huU : u ∉ U) (huX : u ∈ rankTwoX A)
    (hb : ∀ (g : G) (k : ℕ), g⁻¹ * u ^ (2 * k) * g ∈ T → g⁻¹ * u ^ (2 * k) * g ∈ U) :
    ∃ g : G, g⁻¹ * u * g ∈ U ∧ IsExtremalIn 2 T (g⁻¹ * u * g) ∧
      ∀ c ∈ T ⊓ centralizer ({u} : Set G),
        g⁻¹ * c * g ∈ T ⊓ centralizer ({g⁻¹ * u * g} : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hT2, hTidx⟩ := isSylowOf_iff.mp hT
  rw [relIndex_top_right] at hTidx
  exact exists_conj_mem_of_thompson h.isSimpleGroup_X h.not_isPGroup_X hT2 hTidx hUT hUidx huT
    huU huX hb

section Outer

variable {P : Subgroup G} {x z r₁ : G} (hx : OuterInvol R T V₀ P x z r₁)
include hx

theorem mul_mem_X_of_not_mem {u v : G} (hu : u ∉ rankTwoX A) (hv : v ∉ rankTwoX A) :
    u * v ∈ rankTwoX A := by
  have hXn : (rankTwoX A).Normal := normalClosure_normal
  have hR2 : ∀ y ∈ R, y * y = 1 := fun y hy => h.mul_self (mem_sup_left hy)
  have hr₁X := h.outer_r_mem_X hx
  have hdec : ∀ w : G, ∃ y ∈ rankTwoX A, ∃ s ∈ R, w = y * s := fun w => by
    have hw : w ∈ rankTwoX A ⊔ R := by rw [h.sup_top]; exact mem_top w
    exact AS76b.exists_mul_of_mem_sup_of_le_normalizer
      (by rw [normalizer_eq_top_iff.mpr hXn]; exact le_top) hw
  obtain ⟨y₁, hy₁, s₁, hs₁, rfl⟩ := hdec u
  obtain ⟨y₂, hy₂, s₂, hs₂, rfl⟩ := hdec v
  have hs₁X : s₁ ∉ rankTwoX A := fun he => hu (mul_mem hy₁ he)
  have hs₂X : s₂ ∉ rankTwoX A := fun he => hv (mul_mem hy₂ he)
  have hs₁1 : s₁ ≠ 1 := fun he => hs₁X (he ▸ one_mem _)
  have hs₁r : s₁ ≠ r₁ := fun he => hs₁X (he ▸ hr₁X)
  have hs : s₁ * s₂ ∈ rankTwoX A := by
    rcases mem_four h.cardR hR2 hx.r_mem hs₁ hx.r_ne hs₁1 hs₁r.symm hs₂ with e | e | e | e
    · exact absurd (e ▸ one_mem _) hs₂X
    · exact absurd (e ▸ hr₁X) hs₂X
    · rw [e, hR2 s₁ hs₁]
      exact one_mem _
    · rw [e, ← mul_assoc, h.comm (mem_sup_left hs₁) (mem_sup_left hx.r_mem), mul_assoc,
        hR2 s₁ hs₁, mul_one]
      exact hr₁X
  have e : y₁ * s₁ * (y₂ * s₂) = y₁ * (s₁ * y₂ * s₁⁻¹) * (s₁ * s₂) := by group
  rw [e]
  exact mul_mem (mul_mem hy₁ (hXn.conj_mem y₂ hy₂ s₁)) hs

end Outer

end Setting310

end CFSG.ComponentClassification.RankTwoAltFive
