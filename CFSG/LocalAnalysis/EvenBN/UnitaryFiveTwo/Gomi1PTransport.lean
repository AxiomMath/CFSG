module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Gomi1PReduction

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Gomi1P

open Subgroup
open scoped commutatorElement

structure FrobSylow {A : Type} [Group A] (f : A →* A) (U₀ : Subgroup A) : Prop where
  card : Nat.card U₀ = 2 ^ 8
  stable : ∀ u ∈ U₀, f u ∈ U₀
  class_two : ∀ x ∈ U₀, ∀ y ∈ U₀, ∀ z ∈ U₀, ⁅x, y⁆ * z = z * ⁅x, y⁆
  nonabelian : ∃ x ∈ U₀, ∃ y ∈ U₀, x * y ≠ y * x
  elem_abelian : ∃ E : Subgroup A, E ≤ U₀ ∧ Nat.card E = 2 ^ 6 ∧
    (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧ ∀ a ∈ E, a * a = 1
  big_abelian : ∀ x ∈ U₀, x * x = 1 → ∃ R : Subgroup A, R ≤ U₀ ∧ x ∈ R ∧
    (∀ a ∈ R, ∀ b ∈ R, a * b = b * a) ∧ Nat.card R = 2 ^ 6
  cocycle : ∀ u ∈ U₀, u * f u = 1 → ∃ v ∈ U₀, u = v * (f v)⁻¹
  card_fix : Nat.card (U₀ ⊓ f.eqLocus (MonoidHom.id A) : Subgroup A) = 2 ^ 4

variable {X : Type} [Group X] {Y : Subgroup X} {t : X} {A : Type} [Group A]

@[expose] def embed (ψ : A ≃* Y) : A →* X := Y.subtype.comp ψ.toMonoidHom

theorem embed_injective (ψ : A ≃* Y) : Function.Injective (embed ψ) := by
  intro a b h
  exact ψ.injective (Subtype.ext h)

theorem inf_centralizer_eq_map (ψ : A ≃* Y) (f : A →* A)
    (hact : ∀ a : A, t * (ψ a : X) * t⁻¹ = ψ (f a)) :
    Y ⊓ centralizer ({t} : Set X) = (f.eqLocus (MonoidHom.id A)).map (embed ψ) := by
  ext x
  constructor
  · rintro ⟨hxY, hxC⟩
    obtain ⟨a, ha⟩ := ψ.surjective ⟨x, hxY⟩
    have hx : (ψ a : X) = x := congrArg Subtype.val ha
    subst hx
    refine ⟨a, ?_, rfl⟩
    have h1 : t * (ψ a : X) = (ψ a : X) * t := (mem_centralizer_singleton_iff.mp hxC).symm
    have h2 : t * (ψ a : X) * t⁻¹ = (ψ a : X) := by rw [h1]; group
    rw [hact] at h2
    exact ψ.injective (Subtype.ext h2)
  · rintro ⟨a, ha, rfl⟩
    refine ⟨(ψ a).2, mem_centralizer_singleton_iff.mpr ?_⟩
    have h1 := hact a
    have h2 : f a = a := ha
    rw [h2] at h1
    exact (mul_inv_eq_iff_eq_mul.mp h1).symm

theorem card_inf_centralizer_eq (ψ : A ≃* Y) (f : A →* A)
    (hact : ∀ a : A, t * (ψ a : X) * t⁻¹ = ψ (f a)) :
    Nat.card (Y ⊓ centralizer ({t} : Set X) : Subgroup X) =
      Nat.card (f.eqLocus (MonoidHom.id A) : Subgroup A) := by
  rw [inf_centralizer_eq_map ψ f hact, Subgroup.card_map_of_injective (embed_injective ψ)]

theorem center_inf_centralizer_eq_bot (ψ : A ≃* Y) (f : A →* A)
    (hact : ∀ a : A, t * (ψ a : X) * t⁻¹ = ψ (f a))
    (hZ : ∀ a ∈ f.eqLocus (MonoidHom.id A), (∀ b ∈ f.eqLocus (MonoidHom.id A), a * b = b * a) →
      a = 1) :
    ∀ k ∈ Y ⊓ centralizer ({t} : Set X),
      (∀ k' ∈ Y ⊓ centralizer ({t} : Set X), k * k' = k' * k) → k = 1 := by
  intro k hk hkc
  rw [inf_centralizer_eq_map ψ f hact] at hk hkc
  obtain ⟨a, ha, rfl⟩ := hk
  have : a = 1 := hZ a ha fun b hb => embed_injective ψ (by
    rw [map_mul, map_mul]
    exact hkc _ ⟨b, hb, rfl⟩)
  rw [this, map_one]

theorem sylowData_of_frobSylow [Finite X] (ψ : A ≃* Y) (f : A →* A) {U₀ : Subgroup A}
    (hF : FrobSylow f U₀) (ht2 : t * t = 1) (htY : t ∉ Y)
    (hact : ∀ a : A, t * (ψ a : X) * t⁻¹ = ψ (f a)) :
    SylowData t Y (U₀.map (embed ψ)) := by
  have hinj := embed_injective ψ
  have hact' : ∀ a : A, t * embed ψ a * t⁻¹ = embed ψ (f a) := fun a => hact a
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨a, _, rfl⟩
    exact (ψ a).2
  · rw [Subgroup.card_map_of_injective hinj, hF.card]
  · rintro _ ⟨a, ha, rfl⟩
    exact ⟨f a, hF.stable a ha, (hact' a).symm⟩
  · rintro ⟨a, _, h⟩
    exact htY (h ▸ (ψ a).2)
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩
    rw [← map_commutatorElement, ← map_mul, ← map_mul, hF.class_two a ha b hb c hc]
  · obtain ⟨a, ha, b, hb, hab⟩ := hF.nonabelian
    exact ⟨embed ψ a, ⟨a, ha, rfl⟩, embed ψ b, ⟨b, hb, rfl⟩, fun h =>
      hab (hinj (by rw [map_mul, map_mul]; exact h))⟩
  · obtain ⟨E, hEU, hEc, hEab, hEexp⟩ := hF.elem_abelian
    refine ⟨E.map (embed ψ), Subgroup.map_mono hEU, ?_, ?_, ?_⟩
    · rw [Subgroup.card_map_of_injective hinj, hEc]
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [← map_mul, ← map_mul, hEab a ha b hb]
    · rintro _ ⟨a, ha, rfl⟩
      rw [← map_mul, hEexp a ha, map_one]
  · rintro _ ⟨a, ha, rfl⟩ hx2 -
    have haa : a * a = 1 := hinj (by rw [map_mul, map_one]; exact hx2)
    obtain ⟨R, hRU, haR, hRab, hRc⟩ := hF.big_abelian a ha haa
    refine ⟨R.map (embed ψ), Subgroup.map_mono hRU, ⟨a, haR, rfl⟩, ?_, ?_⟩
    · rintro _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩
      rw [← map_mul, ← map_mul, hRab b hb c hc]
    · rw [Subgroup.card_map_of_injective hinj, hRc]
  · rintro _ ⟨a, ha, rfl⟩ hsq
    have h1 : embed ψ a * embed ψ (f a) = 1 := by
      have : (embed ψ a * t) * (embed ψ a * t) = embed ψ a * (t * embed ψ a * t⁻¹) * (t * t) := by
        group
      rw [this, ht2, mul_one, hact'] at hsq
      exact hsq
    have h2 : a * f a = 1 := hinj (by rw [map_mul, map_one]; exact h1)
    obtain ⟨v, hv, hav⟩ := hF.cocycle a ha h2
    refine ⟨embed ψ v, ⟨v, hv, rfl⟩, ?_⟩
    rw [hav, map_mul, map_inv, ← hact' v]
    group
  · have : U₀.map (embed ψ) ⊓ centralizer ({t} : Set X) =
        (U₀ ⊓ f.eqLocus (MonoidHom.id A)).map (embed ψ) := by
      ext x
      constructor
      · rintro ⟨⟨a, ha, rfl⟩, hxC⟩
        have h1 : t * embed ψ a = embed ψ a * t := (mem_centralizer_singleton_iff.mp hxC).symm
        have h2 : t * embed ψ a * t⁻¹ = embed ψ a := by rw [h1]; group
        rw [hact'] at h2
        exact ⟨a, ⟨ha, hinj h2⟩, rfl⟩
      · rintro ⟨a, ⟨ha, haf⟩, rfl⟩
        refine ⟨⟨a, ha, rfl⟩, mem_centralizer_singleton_iff.mpr ?_⟩
        have h2 : f a = a := haf
        have h1 := hact' a
        rw [h2] at h1
        exact (mul_inv_eq_iff_eq_mul.mp h1).symm
    rw [this, Subgroup.card_map_of_injective hinj, hF.card_fix]

theorem FrobSylow.map_equiv {B : Type} [Group B] (e : A ≃* B) {f : A →* A} {g : B →* B}
    (hfg : ∀ a, e (f a) = g (e a)) {U₀ : Subgroup A} (h : FrobSylow f U₀) :
    FrobSylow g (U₀.map e.toMonoidHom) := by
  have hinj : Function.Injective e.toMonoidHom := e.injective
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective hinj, h.card]
  · rintro _ ⟨a, ha, rfl⟩
    exact ⟨f a, h.stable a ha, hfg a⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩
    rw [← map_commutatorElement, ← map_mul, ← map_mul, h.class_two a ha b hb c hc]
  · obtain ⟨a, ha, b, hb, hab⟩ := h.nonabelian
    exact ⟨e a, ⟨a, ha, rfl⟩, e b, ⟨b, hb, rfl⟩, fun hh =>
      hab (hinj (by rw [map_mul, map_mul]; exact hh))⟩
  · obtain ⟨E, hEU, hEc, hEab, hEexp⟩ := h.elem_abelian
    refine ⟨E.map e.toMonoidHom, Subgroup.map_mono hEU, ?_, ?_, ?_⟩
    · rw [Subgroup.card_map_of_injective hinj, hEc]
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [← map_mul, ← map_mul, hEab a ha b hb]
    · rintro _ ⟨a, ha, rfl⟩
      rw [← map_mul, hEexp a ha, map_one]
  · rintro _ ⟨a, ha, rfl⟩ hx2
    have haa : a * a = 1 := hinj (by
      rw [map_mul, map_one]
      exact hx2)
    obtain ⟨R, hRU, haR, hRab, hRc⟩ := h.big_abelian a ha haa
    refine ⟨R.map e.toMonoidHom, Subgroup.map_mono hRU, ⟨a, haR, rfl⟩, ?_, ?_⟩
    · rintro _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩
      rw [← map_mul, ← map_mul, hRab b hb c hc]
    · rw [Subgroup.card_map_of_injective hinj, hRc]
  · rintro _ ⟨a, ha, rfl⟩ hsq
    have h1 : e a * e (f a) = 1 := by rw [hfg a]; exact hsq
    have h2 : a * f a = 1 := hinj (by
      rw [map_mul, map_one]
      exact h1)
    obtain ⟨v, hv, hav⟩ := h.cocycle a ha h2
    refine ⟨e v, ⟨v, hv, rfl⟩, ?_⟩
    rw [hav, map_mul, map_inv]
    show e v * (e (f v))⁻¹ = e v * (g (e v))⁻¹
    rw [hfg v]
  · have hmap : U₀.map e.toMonoidHom ⊓ g.eqLocus (MonoidHom.id B) =
        (U₀ ⊓ f.eqLocus (MonoidHom.id A)).map e.toMonoidHom := by
      ext x
      constructor
      · rintro ⟨⟨a, ha, rfl⟩, hxg⟩
        have h1 : g (e a) = e a := hxg
        rw [← hfg a] at h1
        exact ⟨a, ⟨ha, (e.injective h1 : f a = a)⟩, rfl⟩
      · rintro ⟨a, ⟨ha, haf⟩, rfl⟩
        refine ⟨⟨a, ha, rfl⟩, ?_⟩
        have h2 : f a = a := haf
        show g (e a) = e a
        rw [← hfg a, h2]
    rw [hmap, Subgroup.card_map_of_injective hinj, h.card_fix]

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Gomi1P
