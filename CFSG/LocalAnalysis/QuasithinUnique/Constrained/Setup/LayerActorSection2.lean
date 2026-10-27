module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerActorSection
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilySuzukiComponent

public section

namespace CFSG.QuasithinUnique.Setup.Layer.Actor

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
  CFSG.QuasithinUnique.Setup.Family
open CFSG.Quasithin.B6 (conjSub mem_conjSub mem_normalizer_of_conjSub_le)

theorem sectionProductionProp : SectionProductionProp := by
  intro V _ _ hV G L A hL hA hne
  obtain ⟨hAN, -, ⟨S⟩⟩ := irreducibleSectionProp V hV G L A hL hA hne
  have hbin : ∀ w : S.W, w * w = 1 := by
    intro w
    obtain ⟨v, rfl⟩ := S.π_surjective w
    rw [← map_mul]
    have : v * v = 1 := Subtype.ext (hV _)
    rw [this, map_one]
  have hclos : ∀ a ∈ (S.τW.comp (Subgroup.inclusion (le_sup_right : A ≤ L ⊔ A))).range,
      ∀ g ∈ (S.τW.comp (Subgroup.inclusion (le_sup_left : L ≤ L ⊔ A))).range,
        a * g * a⁻¹ ∈ (S.τW.comp (Subgroup.inclusion (le_sup_left : L ≤ L ⊔ A))).range := by
    rintro _ ⟨y, rfl⟩ _ ⟨l, rfl⟩
    have hyl : (y : MulAut V) * (l : MulAut V) * (y : MulAut V)⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.1 (hAN y.2) l).1 l.2
    refine ⟨⟨(y : MulAut V) * (l : MulAut V) * (y : MulAut V)⁻¹, hyl⟩, ?_⟩
    show S.τW ⟨_, _⟩ = S.τW ⟨(y : MulAut V), _⟩ * S.τW ⟨(l : MulAut V), _⟩ *
      (S.τW ⟨(y : MulAut V), _⟩)⁻¹
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  refine ⟨S.W, S.commGroup, S.finite, S.τW.comp (Subgroup.inclusion le_sup_left),
    (S.τW.comp (Subgroup.inclusion le_sup_right)).range, hbin, S.nontrivial, S.lbar_ne_bot, ?_,
    S.abar_ne_bot, S.abar_elem, ?_, S.abar_offender⟩
  · intro U hU
    refine S.irreducible U fun x hx u hu => ?_
    exact hU (S.τW x) ⟨⟨x, hx⟩, rfl⟩ u hu
  · intro a ha
    refine mem_normalizer_of_conjSub_le ?_ ?_
    · intro x hx
      have h1 : a⁻¹ * x * a ∈ (S.τW.comp (Subgroup.inclusion
          (le_sup_left : L ≤ L ⊔ A))).range := mem_conjSub.1 hx
      have := hclos a ha _ h1
      simpa [mul_assoc] using this
    · intro x hx
      have h1 : a⁻¹⁻¹ * x * a⁻¹ ∈ (S.τW.comp (Subgroup.inclusion
          (le_sup_left : L ≤ L ⊔ A))).range := mem_conjSub.1 hx
      have := hclos a⁻¹ ((S.τW.comp (Subgroup.inclusion
        (le_sup_right : A ≤ L ⊔ A))).range.inv_mem ha) _ h1
      simpa [mul_assoc] using this

end CFSG.QuasithinUnique.Setup.Layer.Actor
