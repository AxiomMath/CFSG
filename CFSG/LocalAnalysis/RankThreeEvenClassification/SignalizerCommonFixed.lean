module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerSubgroups

public section

open CFSG.Open

namespace CFSG.RankThreeEvenClassification.Helpers

universe u

theorem signalizer_complete_iff_unique_maximal
    {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (actor plane : Subgroup G) (signalizer : G → Subgroup G)
    (hsignalizer : IsSolvableSignalizerFunctor prime actor signalizer)
    (hplaneLe : plane ≤ actor) (hpower : ∀ member : plane, member ^ prime = 1)
    (hplaneCard : Nat.card plane = prime ^ 2) :
    SignalizerComplete prime actor signalizer ↔
      ∃! maximal : Subgroup G, Maximal (SignalizerCompatible prime actor signalizer) maximal := by
  rw [signalizer_complete_iff_exists_greatest_compatible prime hprime actor plane signalizer
    hsignalizer hplaneLe hpower hplaneCard]
  constructor
  · rintro ⟨greatest, hcompatible, hgreatest⟩
    have hmaximal : Maximal (SignalizerCompatible prime actor signalizer) greatest :=
      ⟨hcompatible, fun _ hother _ => hgreatest _ hother⟩
    refine ⟨greatest, hmaximal, ?_⟩
    intro other hother
    exact hother.eq_of_le hcompatible (hgreatest other hother.1)
  · rintro ⟨maximal, hmaximal, hunique⟩
    refine ⟨maximal, hmaximal.1, ?_⟩
    intro subgroup hsubgroup
    obtain ⟨other, hle, hother⟩ := exists_maximal_signalizer_compatible_above prime actor signalizer
      subgroup hsubgroup
    exact hunique other hother ▸ hle

theorem SignalizerComplete.maximal_eq_generated
    {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (actor plane : Subgroup G) (signalizer : G → Subgroup G)
    (hcomplete : SignalizerComplete prime actor signalizer)
    (hplaneLe : plane ≤ actor) (hpower : ∀ member : plane, member ^ prime = 1)
    (hplaneCard : Nat.card plane = prime ^ 2)
    (maximal : Subgroup G) (hmaximal : Maximal (SignalizerCompatible prime actor signalizer) maximal) :
    maximal = signalizerGenerated actor signalizer := by
  exact hmaximal.eq_of_le hcomplete
    (SignalizerCompatible.le_generated prime hprime actor plane signalizer hplaneLe hpower hplaneCard
      maximal hmaximal.1)

@[expose] noncomputable def signalizerCommonFixed {G : Type u} [Group G]
    (subactor : Subgroup G) (signalizer : G → Subgroup G) : Subgroup G :=
  ⨅ (element : G) (_ : element ∈ subactor) (_ : element ≠ 1), signalizer element

theorem signalizerCommonFixed_le_value {G : Type u} [Group G]
    (subactor : Subgroup G) (signalizer : G → Subgroup G)
    (element : G) (hmem : element ∈ subactor) (hne : element ≠ 1) :
    signalizerCommonFixed subactor signalizer ≤ signalizer element := by
  exact iInf_le_of_le element (iInf_le_of_le hmem (iInf_le_of_le hne le_rfl))

theorem signalizerCommonFixed_le_centralizer {G : Type u} [Group G]
    (prime : ℕ) (actor subactor : Subgroup G) (signalizer : G → Subgroup G)
    (hsignalizer : IsSolvableSignalizerFunctor prime actor signalizer) (hle : subactor ≤ actor) :
    signalizerCommonFixed subactor signalizer ≤ Subgroup.centralizer (subactor : Set G) := by
  intro element helement
  apply Subgroup.mem_centralizer_iff.mpr
  intro member hmember
  by_cases hne : member = 1
  · rw [hne, one_mul, mul_one]
  · exact (Subgroup.mem_centralizer_singleton_iff.mp
      (hsignalizer.le_centralizer member (hle hmember) hne
        (signalizerCommonFixed_le_value subactor signalizer member hmember hne helement))).symm

theorem signalizerCommonFixed_eq_value_centralizer {G : Type u} [Group G]
    (prime : ℕ) (actor subactor : Subgroup G) (signalizer : G → Subgroup G)
    (hsignalizer : IsSolvableSignalizerFunctor prime actor signalizer) (hle : subactor ≤ actor)
    (element : G) (hmem : element ∈ subactor) (hne : element ≠ 1) :
    signalizerCommonFixed subactor signalizer =
      signalizer element ⊓ Subgroup.centralizer (subactor : Set G) := by
  apply le_antisymm
  · exact le_inf (signalizerCommonFixed_le_value subactor signalizer element hmem hne)
      (signalizerCommonFixed_le_centralizer prime actor subactor signalizer hsignalizer hle)
  · apply le_iInf
    intro member
    apply le_iInf
    intro hmember
    apply le_iInf
    intro hmemberNe
    exact (inf_le_inf le_rfl
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hmember))).trans
      (hsignalizer.balance element (hle hmem) hne member (hle hmember) hmemberNe)

theorem signalizerCommonFixed_compatible {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (actor subactor : Subgroup G) (signalizer : G → Subgroup G)
    (hsignalizer : IsSolvableSignalizerFunctor prime actor signalizer) (hle : subactor ≤ actor)
    (element : G) (hmem : element ∈ subactor) (hne : element ≠ 1) :
    SignalizerCompatible prime actor signalizer (signalizerCommonFixed subactor signalizer) := by
  apply SignalizerCompatible.of_le prime actor signalizer (signalizer element) _
    (signalizer_value_compatible prime hprime actor signalizer hsignalizer element (hle hmem) hne)
    (signalizerCommonFixed_le_value subactor signalizer element hmem hne)
  apply normalizes_iInf
  intro member
  apply normalizes_iInf
  intro hmember
  apply normalizes_iInf
  intro hmemberNe conjugator hconjugator
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    (hsignalizer.invariant member (hle hmember) hmemberNe conjugator hconjugator)

theorem signalizer_common_actor_fixed_eq {G : Type u} [Group G]
    (prime : ℕ) (actor : Subgroup G) (signalizer : G → Subgroup G)
    (hsignalizer : IsSolvableSignalizerFunctor prime actor signalizer)
    (first second : G) (hfirst : first ∈ actor) (hsecond : second ∈ actor)
    (hfirstNe : first ≠ 1) (hsecondNe : second ≠ 1) :
    signalizer first ⊓ Subgroup.centralizer (actor : Set G) =
      signalizer second ⊓ Subgroup.centralizer (actor : Set G) := by
  rw [← signalizerCommonFixed_eq_value_centralizer prime actor actor signalizer hsignalizer
    le_rfl first hfirst hfirstNe,
    ← signalizerCommonFixed_eq_value_centralizer prime actor actor signalizer hsignalizer
      le_rfl second hsecond hsecondNe]

end CFSG.RankThreeEvenClassification.Helpers
