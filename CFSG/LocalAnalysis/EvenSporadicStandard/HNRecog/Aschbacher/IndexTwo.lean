module

public import CFSG.Monster.B.Recog.GenericIndexTwo

public section

namespace CFSG.EvenSporadicStandard.HNRecog

open Subgroup

theorem exists_mulEquiv_of_outer_involutions {C C' : Type*} [Group C] [Group C']
    {L : Subgroup C} {L' : Subgroup C'} [L.Normal] [L'.Normal] (hL : L.index = 2)
    (hL' : L'.index = 2) (α : L ≃* L') {t : C} {t' : C'} (ht : t ∉ L) (ht' : t' ∉ L')
    (ht2 : t ^ 2 = 1) (ht'2 : t' ^ 2 = 1)
    (h : ∀ l : L, ((α (MulAut.conjNormal t l) : L') : C') = t' * (α l : C') * t'⁻¹) :
    Nonempty (C ≃* C') := by
  let ι₁ : L →* C := L.subtype
  let ι₂ : L →* C' := L'.subtype.comp α.toMonoidHom
  have hι₁ : Function.Injective ι₁ := L.subtype_injective
  have hι₂ : Function.Injective ι₂ := L'.subtype_injective.comp α.injective
  have hr₁ : ι₁.range = L := L.range_subtype
  have hr₂ : ι₂.range = L' := by
    ext x
    constructor
    · rintro ⟨l, rfl⟩
      exact (α l).2
    · intro hx
      obtain ⟨l, hl⟩ := α.surjective ⟨x, hx⟩
      exact ⟨l, by simp [ι₂, hl]⟩
  have h₁ : ι₁.range.index = 2 := by rw [hr₁]; exact hL
  have h₂ : ι₂.range.index = 2 := by rw [hr₂]; exact hL'
  have hs₁ : t ∉ ι₁.range := by rw [hr₁]; exact ht
  have hs₂ : t' ∉ ι₂.range := by rw [hr₂]; exact ht'
  obtain ⟨e, -, -⟩ := CFSG.Monster.B.Recog.exists_mulEquiv_of_index_two_of_eq ι₁ ι₂ hι₁ hι₂ h₁ h₂
    hs₁ hs₂ (fun a => MulAut.conjNormal t a) 1
    (fun a => by simp [ι₁, MulAut.conjNormal_apply])
    (fun a => by simpa [ι₂] using (h a).symm)
    (by simpa [ι₁, ← pow_two] using ht2) (by simpa [ι₂, ← pow_two] using ht'2)
  exact ⟨e⟩

end CFSG.EvenSporadicStandard.HNRecog
