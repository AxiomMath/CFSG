module

public import CFSG.LocalAnalysis.ComponentClassification.KProperRelativeBShell
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddLieAssembly
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddLieG2F4E8
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourIndexTwoLocalB

public section

namespace CFSG.ComponentClassification.KProperRelativeB

open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank

@[expose] def OddExceptionalFrontier : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup (GeneralizedFitting.subgroup G) →
    (∃ a b : GeneralizedFitting.subgroup G, a * b ≠ b * a) →
    (GeneralizedFitting.subgroup G).index ≤ 2 →
    ∀ (t : StatedLieTag) (p f : ℕ),
      (t = .E6 ∨ t = .E7 ∨ t = .twistedE6 ∨ t = .trialityD4) → p.Prime → p ≠ 2 →
      ChevalleyExceptionalModel (GeneralizedFitting.subgroup G) t p f →
      (∀ X : Subgroup G, X ≠ ⊤ → CentralTwoBInclusion.Property X) →
      CentralTwoBInclusion.Property G

@[expose] def HeldInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup (GeneralizedFitting.subgroup G) →
    (∃ a b : GeneralizedFitting.subgroup G, a * b ≠ b * a) →
    (GeneralizedFitting.subgroup G).index ≤ 2 →
    Nonempty (GeneralizedFitting.subgroup G ≃* NativeSporadic.He) →
    (∀ X : Subgroup G, X ≠ ⊤ → CentralTwoBInclusion.Property X) →
    CentralTwoBInclusion.Property G

theorem oddLieInput_of_frontier (hfront : OddExceptionalFrontier) : OddLieInput := by
  intro G _ _ hsimple hnonab hindex hodd hproper
  have : IsSimpleGroup (GeneralizedFitting.subgroup G) := hsimple
  refine CatalogueBOddLie.odd_Lie_index_two_B_of_exceptional hnonab hindex hodd hproper
    fun t p f ht hp hp2 hmodel => ?_
  simp only [chevalleyExceptionalTags, Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (CatalogueBOddLie.odd_G2_F4_E8_index_two_B_under_proper_subgroup_B hnonab hindex .G2
      (Or.inl rfl) p f hp2 hmodel hproper).2
  · exact (CatalogueBOddLie.odd_G2_F4_E8_index_two_B_under_proper_subgroup_B hnonab hindex .F4
      (Or.inr (Or.inl rfl)) p f hp2 hmodel hproper).2
  · exact hfront G hsimple hnonab hindex .E6 p f (Or.inl rfl) hp hp2 hmodel hproper
  · exact hfront G hsimple hnonab hindex .E7 p f (Or.inr (Or.inl rfl)) hp hp2 hmodel hproper
  · exact (CatalogueBOddLie.odd_G2_F4_E8_index_two_B_under_proper_subgroup_B hnonab hindex .E8
      (Or.inr (Or.inr rfl)) p f hp2 hmodel hproper).2
  · exact hfront G hsimple hnonab hindex .twistedE6 p f (Or.inr (Or.inr (Or.inl rfl))) hp hp2
      hmodel hproper
  · exact hfront G hsimple hnonab hindex .trialityD4 p f (Or.inr (Or.inr (Or.inr rfl))) hp hp2
      hmodel hproper

theorem exceptionalInput_of_held (hheld : HeldInput) : ExceptionalInput := by
  intro G _ _ hsimple hnonab hindex hmodel hproper
  rcases hmodel with hpsl | hhe
  · have : IsSimpleGroup (GeneralizedFitting.subgroup G) := hsimple
    have : (GeneralizedFitting.subgroup G).Normal := GeneralizedFitting.normal G
    obtain ⟨-, hbad⟩ := PSL3Four.index_two_local_B (GeneralizedFitting.subgroup G) hpsl hindex
    intro S hne htwo
    rw [hbad S hne htwo, Subgroup.map_bot]
    exact bot_le
  · exact hheld G hsimple hnonab hindex hhe hproper

theorem kProper_component_local_B_of_frontiers
    (hTits : ∀ (S : Type) [Group S] (p f : ℕ), ReeTitsModel S .Tits p f →
      Group.IsSolvable (OuterAutomorphisms.Outer S))
    (hspor : ∀ (S : Type) [Group S] [Finite S] [IsSimpleGroup S], (∃ a b : S, a * b ≠ b * a) →
      NativeSporadic.SporadicRep S → Group.IsSolvable (OuterAutomorphisms.Outer S))
    (hU : RelativeU Catalog) (hfront : OddExceptionalFrontier) (hheld : HeldInput) (G : Type)
    [Group G] [Finite G] [IsSimpleGroup G] (hK : KProper Catalog G)
    (hcomp : IsComponentType G) :
    oddCore G = ⊥ ∧ ComponentType.LocalBProperty G :=
  kProper_component_local_B_of_parts hTits hspor hU (oddLieInput_of_frontier hfront)
    (exceptionalInput_of_held hheld) G hK hcomp

end CFSG.ComponentClassification.KProperRelativeB
