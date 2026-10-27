module

public import CFSG.ClassicalInvolution.Asc77.ModOApi
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3WeaklyClosed
public import CFSG.ClassicalInvolution.Asc77.WP1Section6

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic
open CFSG.ComponentClassification.AschbacherTheorem3
open CFSG.ComponentClassification.AschbacherTightEmbedding
open scoped commutatorElement

variable {G : Type} [Group G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

@[expose] def L6_7On (Ω : Set (Subgroup G)) : Prop :=
  ∀ S : Sylow 2 G, ∀ R ∈ RSet Ω, ∀ R' ∈ RSet Ω, R ≤ (S : Subgroup G) →
    R' ≤ (S : Subgroup G) → R ≠ R' → Commutes R R'

theorem l6_7On_of_l6_7 (h : L6_7 p f) (hp : p ≠ 2) (hq : 5 ≤ p ^ f) [Finite G]
    (hΩ : HypOmegaMod p f Ω) : L6_7On Ω :=
  h hp hq G Ω hΩ

theorem mem_normalizer_of_normal_in {X Y : Subgroup G} (hXn : ∀ y ∈ Y, conjSub y X = X) {y : G}
    (hy : y ∈ Y) : y ∈ Subgroup.normalizer (X : Set G) :=
  mem_normalizer_iff_conjSub_eq.mpr (hXn y hy)

theorem conjSub_le_of_le_of_mem_left {R Y : Subgroup G} (hRY : R ≤ Y) {g : G} (hg : g ∈ Y) :
    conjSub g R ≤ Y := by
  intro x hx
  rw [mem_conjSub_iff] at hx
  have h1 : g⁻¹ * x * g ∈ Y := hRY hx
  have h2 : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
  rw [h2]
  exact Y.mul_mem (Y.mul_mem hg h1) (Y.inv_mem hg)

theorem eq_of_conjSub_le_of_l6_7 [Finite G] (hp : p ≠ 2) (h67 : L6_7On Ω)
    (hΩ : HypOmegaMod p f Ω) {R Y X S : Subgroup G} (hR : R ∈ RSet Ω) (hRY : R ≤ Y)
    (hXn : ∀ y ∈ Y, conjSub y X = X) (hRX : R ⊓ X = ⊥) (hS2 : IsPGroup 2 S)
    (hRS : R ≤ S) (hSH : S ≤ X ⊔ R) {g : G} (hg : g ∈ Y) (hle : conjSub g R ≤ S) :
    conjSub g R = R := by
  by_contra hne
  have hR2 : IsPGroup 2 R := (mem_RSet_iff.mp hR).choose_spec.2.2.1
  have hR'' : conjSub g R ∈ RSet Ω := RSet.conj hΩ.conjInvariant hR g
  obtain ⟨S₀, hS₀⟩ := IsPGroup.exists_le_sylow hS2
  have hcomm : Commutes R (conjSub g R) :=
    h67 S₀ R hR (conjSub g R) hR'' (hRS.trans hS₀) (hle.trans hS₀) (Ne.symm hne)
  have hRN : R ≤ Subgroup.normalizer (X : Set G) := fun x hx =>
    mem_normalizer_of_normal_in hXn (hRY hx)
  have hR''Y : conjSub g R ≤ Y := conjSub_le_of_le_of_mem_left hRY hg
  have hR''N : conjSub g R ≤ Subgroup.normalizer (X : Set G) := fun x hx =>
    mem_normalizer_of_normal_in hXn (hR''Y hx)
  have hR''X : X ⊓ conjSub g R = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxX, hxR⟩ := Subgroup.mem_inf.mp hx
    rw [mem_conjSub_iff] at hxR
    have hxX' : g⁻¹ * x * g ∈ X := by
      have := conj_mem_conjSub (n := g⁻¹) hxX
      rwa [hXn g⁻¹ (Y.inv_mem hg), inv_inv] at this
    have h1 : g⁻¹ * x * g ∈ R ⊓ X := ⟨hxR, hxX'⟩
    rw [hRX, Subgroup.mem_bot] at h1
    rw [Subgroup.mem_bot]
    have : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
    rw [this, h1]
    group
  have hcard : Nat.card (conjSub g R) = Nat.card R :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hc1 : Nat.card (X ⊔ conjSub g R : Subgroup G) = Nat.card X * Nat.card (conjSub g R) :=
    card_sup_of_le_normalizer hR''N hR''X
  have hc2 : Nat.card (X ⊔ R : Subgroup G) = Nat.card X * Nat.card R :=
    card_sup_of_le_normalizer hRN (by rwa [inf_comm])
  have hle2 : X ⊔ conjSub g R ≤ X ⊔ R := sup_le le_sup_left (hle.trans hSH)
  have heq : X ⊔ conjSub g R = X ⊔ R :=
    Subgroup.eq_of_le_of_card_ge hle2 (by rw [hc1, hc2, hcard])
  have hF : Frame X (conjSub g R) :=
    ⟨hR''N, by rwa [inf_comm], isPGroup_conjSub g hR2⟩
  obtain ⟨a, ha, b, hb, hab⟩ := (hΩ.isQuatSub_of_mem_RSet hp hR).exists_not_commute
  apply hab
  have hamem : a ∈ X ⊔ conjSub g R := heq ▸ (le_sup_right : R ≤ X ⊔ R) ha
  obtain ⟨t, ht, c, hc, hr⟩ := hF.mem_sup_iff.mp hamem
  have hcdef : c = t⁻¹ * a := by rw [← hr]; group
  have hct : t⁻¹ * (a * b * a⁻¹) * t = a * b * a⁻¹ := by
    have := hcomm (a * b * a⁻¹) (R.mul_mem (R.mul_mem ha hb) (R.inv_mem ha)) t ht
    rw [mul_assoc, this]
    group
  have hw1 : a * b * a⁻¹ * b⁻¹ ∈ R := R.mul_mem (R.mul_mem (R.mul_mem ha hb) (R.inv_mem ha))
    (R.inv_mem hb)
  have hw2 : a * b * a⁻¹ * b⁻¹ ∈ X := by
    have e : a * b * a⁻¹ * b⁻¹ = c * (b * c⁻¹ * b⁻¹) := by
      calc a * b * a⁻¹ * b⁻¹ = (t⁻¹ * (a * b * a⁻¹) * t) * b⁻¹ := by rw [hct]
        _ = c * (b * c⁻¹ * b⁻¹) := by rw [hcdef]; group
    rw [e]
    refine X.mul_mem hc ?_
    have := conj_mem_conjSub (n := b) (X.inv_mem hc)
    rwa [hXn b (hRY hb)] at this
  have h1 : a * b * a⁻¹ * b⁻¹ ∈ R ⊓ X := ⟨hw1, hw2⟩
  rw [hRX, Subgroup.mem_bot] at h1
  calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
    _ = b * a := by rw [h1, one_mul]

theorem l6_13_on [Finite G] (hp : p ≠ 2) (hΩ : HypOmegaMod p f Ω) (h67 : L6_7On Ω) :
    ∀ R ∈ RSet Ω, ∀ Y X : Subgroup G, R ≤ Y → X ≤ Y → (∀ y ∈ Y, conjSub y X = X) →
      R ⊓ X = ⊥ →
        (⨆ R' ∈ {R' : Subgroup G | (∃ y ∈ Y, R' = conjSub y R) ∧ R' ≤ R ⊔ X}, R') ≤
            R ⊔ oddCoreOf X ∧
          ⁅R, X⁆ ≤ oddCoreOf X := by
  intro R hR Y X hRY hXY hXn hRX
  have hR2 : IsPGroup 2 R := (mem_RSet_iff.mp hR).choose_spec.2.2.1
  have hRN : R ≤ Subgroup.normalizer (X : Set G) := fun x hx =>
    mem_normalizer_of_normal_in hXn (hRY hx)
  have hHY : X ⊔ R ≤ Y := sup_le hXY hRY
  obtain ⟨S, hS, hRS⟩ := exists_isSylowOf_le hR2 (le_sup_right : R ≤ X ⊔ R)
  have hclosed : ∀ g ∈ Y, conjSub g R ≤ S → conjSub g R = R := fun g hg hle =>
    eq_of_conjSub_le_of_l6_7 hp h67 hΩ hR hRY hXn hRX hS.isPGroup hRS hS.le hg hle
  have h42 : Hyp42 X R S :=
    { frame := ⟨hRN, hRX, hR2⟩
      sylow := hS
      le := hRS
      closed := fun g hg hle => hclosed g⁻¹ (Y.inv_mem (hXY hg)) hle }
  have hcomm : ⁅X, R⁆ ≤ oddCoreOf X := lemma_4_2_oddCore h42
  have hcomm' : ⁅R, X⁆ ≤ oddCoreOf X := by
    rw [Subgroup.commutator_comm]
    exact hcomm
  refine ⟨?_, hcomm'⟩
  refine iSup₂_le fun R' hR' => ?_
  obtain ⟨⟨y, hy, hR'eq⟩, hR'le⟩ := hR'
  subst hR'eq
  have hR'2 : IsPGroup 2 (conjSub y R) := isPGroup_conjSub y hR2
  obtain ⟨S', hS', hR'S'⟩ := exists_isSylowOf_le hR'2 (sup_comm R X ▸ hR'le)
  obtain ⟨c, hcH, hconj⟩ := exists_rightConjugate_eq_of_isSylowOf hS' hS
  have hcY : c ∈ Y := hHY hcH
  have hle : conjSub (c * y) R ≤ S := by
    rw [conjSub_mul]
    have h1 : conjSub y R ≤ conjSub c⁻¹ S := by
      have : rightConjugate S c = conjSub c⁻¹ S := rfl
      rw [← this, hconj]
      exact hR'S'
    have h2 := conjSub_mono (n := c) h1
    rwa [conjSub_conjSub_inv] at h2
  have hceq : conjSub (c * y) R = R := hclosed _ (Y.mul_mem hcY hy) hle
  have hyR : conjSub y R = conjSub c⁻¹ R := by
    calc conjSub y R = conjSub (c⁻¹ * (c * y)) R := by rw [inv_mul_cancel_left]
      _ = conjSub c⁻¹ (conjSub (c * y) R) := conjSub_mul _ _ _
      _ = conjSub c⁻¹ R := by rw [hceq]
  have hF : Frame X R := ⟨hRN, hRX, hR2⟩
  obtain ⟨ρ, hρ, x, hx, hρx⟩ := hF.mem_sup_iff.mp (Subgroup.inv_mem _ hcH)
  have hinv : c⁻¹ = (ρ * x * ρ⁻¹) * ρ := by rw [← hρx]; group
  have hxX : ρ * x * ρ⁻¹ ∈ X := by
    have := conj_mem_conjSub (n := ρ) hx
    rwa [hXn ρ (hRY hρ)] at this
  rw [hyR, hinv, conjSub_mul, conjSub_eq_self_of_mem hρ]
  intro u hu
  rw [mem_conjSub_iff] at hu
  have hu' : u = ((ρ * x * ρ⁻¹) * ((ρ * x * ρ⁻¹)⁻¹ * u * (ρ * x * ρ⁻¹)) * (ρ * x * ρ⁻¹)⁻¹ *
      ((ρ * x * ρ⁻¹)⁻¹ * u * (ρ * x * ρ⁻¹))⁻¹) * ((ρ * x * ρ⁻¹)⁻¹ * u * (ρ * x * ρ⁻¹)) := by
    group
  rw [hu', sup_comm]
  refine Subgroup.mul_mem_sup (hcomm (Subgroup.commutator_mem_commutator hxX hu)) hu

theorem l6_13 (h67 : L6_7 p f) : L6_13 p f := by
  intro hp hq G _ _ Ω hΩ
  exact l6_13_on hp hΩ (l6_7On_of_l6_7 h67 hp hq hΩ)

end CFSG.ClassicalInvolution.Asc77
