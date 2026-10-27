module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionDoubleTransitiveNormalizer

theorem prime_subgroup_normalizer_ne_top
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (p : ℕ) (hp : p.Prime)
    (A : Subgroup G) (hA : IsPGroup p A) (hAne : A ≠ ⊥) :
    Subgroup.normalizer (A : Set G) ≠ ⊤ := by
  intro hnormalizer
  let : A.Normal := Subgroup.normalizer_eq_top_iff.mp hnormalizer
  have hAtop : A = ⊤ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal A).resolve_left hAne
  have hG : IsPGroup p G := hA.of_surjective A.subtype (by
    intro g
    refine ⟨⟨g, ?_⟩, rfl⟩
    rw [hAtop]
    exact Subgroup.mem_top g)
  let : Fact p.Prime := ⟨hp⟩
  have hcenter_ne : Subgroup.center G ≠ ⊥ := hG.bot_lt_center.ne'
  have hcenter_top : Subgroup.center G = ⊤ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G)).resolve_left hcenter_ne
  obtain ⟨a, b, hab⟩ := hnonab
  have hb : b ∈ Subgroup.center G := by
    rw [hcenter_top]
    exact Subgroup.mem_top b
  exact hab (Subgroup.mem_center_iff.mp hb a)

end CFSG.ProperTwoGeneratedCore.LocalCriterionDoubleTransitiveNormalizer
