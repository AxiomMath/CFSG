module

public import CFSG.ClassicalInvolution.Q3.Q3CPSix67

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
open CFSG.ComponentClassification.AschbacherTheorem3
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

theorem eq_of_conjSub_le_gen [Finite G] (hΩ : HypOmegaGen Ω) {R Y X S : Subgroup G}
    (hR : R ∈ RSet Ω) (hRY : R ≤ Y) (hXn : ∀ y ∈ Y, conjSub y X = X) (hRX : R ⊓ X = ⊥)
    (hS2 : IsPGroup 2 S) (hRS : R ≤ S) (hSH : S ≤ X ⊔ R) {g : G} (hg : g ∈ Y)
    (hle : conjSub g R ≤ S) : conjSub g R = R := by
  by_contra hne
  have hR2 : IsPGroup 2 R := (mem_RSet_iff.mp hR).choose_spec.2.2.1
  have hR'' : conjSub g R ∈ RSet Ω := RSet.conj hΩ.conjInvariant hR g
  obtain ⟨S₀, hS₀⟩ := IsPGroup.exists_le_sylow hS2
  have hcomm : Commutes R (conjSub g R) :=
    Q3CP.l67Gen G Ω hΩ S₀ R hR (conjSub g R) hR'' (hRS.trans hS₀) (hle.trans hS₀) (Ne.symm hne)
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
  obtain ⟨a, ha, b, hb, hab⟩ := (Disconnected.AschTight.Sec6Gen.isQuatSub_of_mem_RSet hΩ hR).exists_not_commute
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

theorem comm613Gen [Finite G] (hΩ : HypOmegaGen Ω) {R : Subgroup G} (hR : R ∈ RSet Ω)
    {Y X : Subgroup G} (hRY : R ≤ Y) (hXY : X ≤ Y) (hXn : ∀ y ∈ Y, conjSub y X = X)
    (hRX : R ⊓ X = ⊥) : ⁅R, X⁆ ≤ oddCoreOf X := by
  have hR2 : IsPGroup 2 R := (mem_RSet_iff.mp hR).choose_spec.2.2.1
  have hRN : R ≤ Subgroup.normalizer (X : Set G) := fun x hx =>
    mem_normalizer_of_normal_in hXn (hRY hx)
  obtain ⟨S, hS, hRS⟩ := exists_isSylowOf_le hR2 (le_sup_right : R ≤ X ⊔ R)
  have hclosed : ∀ g ∈ Y, conjSub g R ≤ S → conjSub g R = R := fun g hg hle =>
    eq_of_conjSub_le_gen hΩ hR hRY hXn hRX hS.isPGroup hRS hS.le hg hle
  have h42 : Hyp42 X R S :=
    { frame := ⟨hRN, hRX, hR2⟩
      sylow := hS
      le := hRS
      closed := fun g hg hle => hclosed g⁻¹ (Y.inv_mem (hXY hg)) hle }
  have hcomm : ⁅X, R⁆ ≤ oddCoreOf X := lemma_4_2_oddCore h42
  rw [Subgroup.commutator_comm]
  exact hcomm

theorem conjSub_eq_self_of_normal {X : Subgroup G} (hX : X.Normal) (y : G) : conjSub y X = X := by
  ext x
  rw [mem_conjSub_iff]
  constructor
  · intro h
    have := hX.conj_mem _ h y
    rwa [show y * (y⁻¹ * x * y) * y⁻¹ = x by group] at this
  · intro h
    have := hX.conj_mem _ h y⁻¹
    rwa [inv_inv] at this

theorem comm613Gen_normal [Finite G] (hΩ : HypOmegaGen Ω) {R : Subgroup G} (hR : R ∈ RSet Ω)
    {X : Subgroup G} (hX : X.Normal) (hRX : R ⊓ X = ⊥) : ⁅R, X⁆ ≤ oddCoreOf X :=
  comm613Gen hΩ hR le_top le_top (fun y _ => conjSub_eq_self_of_normal hX y) hRX

end CFSG.ClassicalInvolution.Q3
