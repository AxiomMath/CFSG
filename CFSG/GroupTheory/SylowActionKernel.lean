module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG

universe u v

theorem injective_of_isPGroup_ker_of_sylow
    {G : Type u} {A : Type v} [Group G] [Group A]
    {p : ℕ} (S : Sylow p G) (f : G →* A) (hker : IsPGroup p f.ker)
    (hfaithful : ∀ g ∈ (S : Subgroup G), f g = 1 → g = 1) :
    Function.Injective f := by
  apply (MonoidHom.ker_eq_bot_iff f).mp
  apply le_antisymm _ bot_le
  intro g hg
  exact Subgroup.mem_bot.mpr (hfaithful g (hker.le_sylow_of_normal S hg) hg)

theorem injective_on_image_of_isPGroup_ker_of_sylow
    {G : Type u} {A : Type v} [Group G] [Finite G] [Group A]
    {B : Type*} [Group B] {p : ℕ} [Fact p.Prime]
    (S : Sylow p G) (f : G →* A) (q : A →* B)
    (hker : IsPGroup p q.ker)
    (hfaithful : ∀ g ∈ (S : Subgroup G), q (f g) = 1 → f g = 1) :
    Function.Injective (q.domRestrict f.range) := by
  let T : Sylow p f.range := S.mapSurjective f.rangeRestrict_surjective
  apply injective_of_isPGroup_ker_of_sylow T (q.domRestrict f.range)
  · exact hker.comap_of_injective f.range.subtype f.range.subtype_injective
  · intro a ha hqa
    change a ∈ (S : Subgroup G).map f.rangeRestrict at ha
    obtain ⟨g, hg, hga⟩ := Subgroup.mem_map.mp ha
    subst a
    apply Subtype.ext
    have hqg : q (f g) = 1 := by
      exact hqa
    exact hfaithful g hg hqg

end CFSG
