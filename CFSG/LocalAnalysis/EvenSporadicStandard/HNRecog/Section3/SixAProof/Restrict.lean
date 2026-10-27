module

public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Operations

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

theorem sixA_restrict_equiv {X M : Type*} [Group X] [Group M] (f : X →* M)
    (hf : Function.Injective f) {D : Subgroup X} {C : Subgroup M}
    (hrange : ∀ c ∈ C, ∃ x, f x = c) (hiff : ∀ x, f x ∈ C ↔ x ∈ D) :
    Nonempty (↥D ≃* ↥C) := by
  let g : ↥D →* ↥C := (f.comp D.subtype).codRestrict C (fun d => (hiff d.1).2 d.2)
  refine ⟨MulEquiv.ofBijective g ⟨?_, ?_⟩⟩
  · intro d d' hdd'
    apply Subtype.ext
    apply hf
    exact congrArg Subtype.val hdd'
  · rintro ⟨c, hc⟩
    obtain ⟨x, hx⟩ := hrange c hc
    have hxD : x ∈ D := (hiff x).1 (hx ▸ hc)
    exact ⟨⟨x, hxD⟩, Subtype.ext hx⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
