module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingLocalBetween
public import CFSG.LocalAnalysis.ComponentClassification.CentralTwoBInclusion

public section

namespace CFSG.ComponentClassification.CatalogueBAlternating

theorem normalizer_badSubgroup_eq_bot_of_between {G Ω : Type*} [Group G] [Finite G]
    [Fintype Ω] [DecidableEq Ω] (K : Subgroup (Equiv.Perm Ω))
    (hK : alternatingGroup Ω ≤ K) (e : G ≃* K)
    (S : Subgroup G) (hS : IsPGroup 2 S) :
    TwoComponents.badSubgroup (Subgroup.normalizer (S : Set G)) = ⊥ := by
  let f := normalizerEquiv e S
  apply (Subgroup.map_eq_bot_iff_of_injective
    (TwoComponents.badSubgroup (Subgroup.normalizer (S : Set G)))
    (f := f.toMonoidHom) f.injective).mp
  rw [BadComponents.equiv_invariant f]
  exact between_normalizer_badSubgroup_eq_bot K hK (S.map e.toMonoidHom)
    (hS.map e.toMonoidHom)

theorem generalizedFitting_normalizer_badSubgroup_eq_bot {G : Type*} [Group G] [Finite G]
    [IsSimpleGroup (GeneralizedFitting.subgroup G)]
    (hnonab : ∃ a b : GeneralizedFitting.subgroup G, a * b ≠ b * a)
    {n : ℕ} (hn : n = 5 ∨ 7 ≤ n)
    (θ : GeneralizedFitting.subgroup G ≃* alternatingGroup (Fin n))
    (S : Subgroup G) (hS : IsPGroup 2 S) :
    TwoComponents.badSubgroup (Subgroup.normalizer (S : Set G)) = ⊥ := by
  obtain ⟨K, hK, e, _⟩ := generalizedFitting_between_alternating_symmetric hnonab hn θ
  exact normalizer_badSubgroup_eq_bot_of_between K hK e S hS

theorem generalizedFitting_B_inclusion {G : Type*} [Group G] [Finite G]
    [IsSimpleGroup (GeneralizedFitting.subgroup G)]
    (hnonab : ∃ a b : GeneralizedFitting.subgroup G, a * b ≠ b * a)
    {n : ℕ} (hn : n = 5 ∨ 7 ≤ n)
    (θ : GeneralizedFitting.subgroup G ≃* alternatingGroup (Fin n)) :
    CentralTwoBInclusion.Property G := by
  intro S _ hS
  rw [generalizedFitting_normalizer_badSubgroup_eq_bot hnonab hn θ S hS,
    Subgroup.map_bot]
  exact bot_le

theorem alternating_generalizedFitting_B_inclusion {G : Type*} [Group G] [Finite G]
    [IsSimpleGroup (GeneralizedFitting.subgroup G)]
    (hnonab : ∃ a b : GeneralizedFitting.subgroup G, a * b ≠ b * a)
    {n : ℕ} (hn : n = 5 ∨ 7 ≤ n)
    (θ : GeneralizedFitting.subgroup G ≃* alternatingGroup (Fin n)) :
    (∀ S : Subgroup G, IsPGroup 2 S →
      TwoComponents.badSubgroup (Subgroup.normalizer (S : Set G)) = ⊥) ∧
      CentralTwoBInclusion.Property G :=
  ⟨fun S hS => generalizedFitting_normalizer_badSubgroup_eq_bot hnonab hn θ S hS,
    generalizedFitting_B_inclusion hnonab hn θ⟩

end CFSG.ComponentClassification.CatalogueBAlternating
