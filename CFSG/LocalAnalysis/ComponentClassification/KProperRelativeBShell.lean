module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingInclusion
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalUnbalanced
public import CFSG.LocalAnalysis.ComponentClassification.AssemblyBLocalB
public import CFSG.LocalAnalysis.ComponentClassification.SimpleOddCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueRelativeBMinimal
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAssembly

public section

namespace CFSG.ComponentClassification.KProperRelativeB

open CFSG.Assembly CFSG.Blueprint
open LocalAnalysis.ComponentInitial (SchreierFor)

variable {C : GroupProp}

@[expose] def ReducedCounterexample (C : GroupProp) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], KProper C G →
    (∀ (X : Type) [Group X] [Finite X], KProper C X → Nat.card X < Nat.card G →
      CentralTwoBInclusion.Property X) →
    ¬ CentralTwoBInclusion.Property G →
    IsSimpleGroup (GeneralizedFitting.subgroup G) ∧
      (∃ a b : GeneralizedFitting.subgroup G, a * b ≠ b * a) ∧
      (GeneralizedFitting.subgroup G).index ≤ 2 ∧
      ∃ z : G, orderOf z = 2 ∧ CFSG.oddCore (Subgroup.centralizer ({z} : Set G)) ≠ ⊥

@[expose] def RelativeU (C : GroupProp) : Prop :=
  ∀ (X : Type) [Group X] [Finite X], KProper C X →
    IsSimpleGroup (GeneralizedFitting.subgroup X) →
    (∃ a b : GeneralizedFitting.subgroup X, a * b ≠ b * a) →
    (∃ z : X, orderOf z = 2 ∧ CFSG.oddCore (Subgroup.centralizer ({z} : Set X)) ≠ ⊥) →
    OutcomeLocal.UOutcome X

@[expose] def OddLieInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup (GeneralizedFitting.subgroup G) →
    (∃ a b : GeneralizedFitting.subgroup G, a * b ≠ b * a) →
    (GeneralizedFitting.subgroup G).index ≤ 2 → OddLieType (GeneralizedFitting.subgroup G) →
    (∀ X : Subgroup G, X ≠ ⊤ → CentralTwoBInclusion.Property X) →
    CentralTwoBInclusion.Property G

@[expose] def ExceptionalInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup (GeneralizedFitting.subgroup G) →
    (∃ a b : GeneralizedFitting.subgroup G, a * b ≠ b * a) →
    (GeneralizedFitting.subgroup G).index ≤ 2 →
    (LieModel (GeneralizedFitting.subgroup G) .PSL 3 2 2 ∨
      Nonempty (GeneralizedFitting.subgroup G ≃* NativeSporadic.He)) →
    (∀ X : Subgroup G, X ≠ ⊤ → CentralTwoBInclusion.Property X) →
    CentralTwoBInclusion.Property G

theorem kProper_B_inclusion_of_inputs
    (hC : ∀ {X Y : Type} [Group X] [Group Y], X ≃* Y → C Y → C X)
    (hred : ReducedCounterexample C) (hU : RelativeU C) (hodd : OddLieInput)
    (hexc : ExceptionalInput) :
    ∀ (G : Type) [Group G] [Finite G], KProper C G → CentralTwoBInclusion.Property G := by
  suffices h : ∀ n : ℕ, ∀ (G : Type) [Group G] [Finite G], Nat.card G = n →
      KProper C G → CentralTwoBInclusion.Property G from
    fun G _ _ hK => h _ G rfl hK
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro G _ _ hn hK
    have hsmall : ∀ (X : Type) [Group X] [Finite X], KProper C X →
        Nat.card X < Nat.card G → CentralTwoBInclusion.Property X :=
      fun X _ _ hX hlt => ih (Nat.card X) (hn ▸ hlt) X rfl hX
    have hproper : ∀ X : Subgroup G, X ≠ ⊤ → CentralTwoBInclusion.Property X := fun X hX =>
      hsmall X (LocalAnalysis.ComponentInitial.kProper_subgroup hC hK X) (by
        simpa only [Subgroup.card_top] using Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr hX))
    by_contra hfail
    obtain ⟨hsimple, hnonab, hindex, hz⟩ := hred G hK hsmall hfail
    have : IsSimpleGroup (GeneralizedFitting.subgroup G) := hsimple
    rcases hU G hK hsimple hnonab hz with hlie | ⟨m, -, hm, ⟨θ⟩, -⟩ | ⟨hexcmodel, -⟩
    · exact hfail (hodd G hsimple hnonab hindex hlie hproper)
    · exact hfail (CatalogueBAlternating.generalizedFitting_B_inclusion hnonab (Or.inr hm) θ)
    · exact hfail (hexc G hsimple hnonab hindex hexcmodel hproper)

theorem kProper_component_local_B_of_inputs
    (hC : ∀ {X Y : Type} [Group X] [Group Y], X ≃* Y → C Y → C X)
    (hred : ReducedCounterexample C) (hU : RelativeU C) (hodd : OddLieInput)
    (hexc : ExceptionalInput) (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hK : KProper C G) (hcomp : IsComponentType G) :
    oddCore G = ⊥ ∧ ComponentType.LocalBProperty G := by
  have hcore := ComponentType.oddCore_eq_bot_of_componentType G hcomp
  exact ⟨hcore, AssemblyBLocalB.of_corefree_and_inclusion hcore
    (kProper_B_inclusion_of_inputs hC hred hU hodd hexc G hK)⟩

theorem reducedCounterexample_of_schreier
    (hC : ∀ {X Y : Type} [Group X] [Group Y], X ≃* Y → C Y → C X)
    (hschreier : SchreierFor C) : ReducedCounterexample C := by
  intro G _ _ hK hsmall hfail
  obtain ⟨hsimple, hperfect, hF, hindex, z, hz, -, -, hcore⟩ :=
    CatalogueRelativeB.simple_unbalanced_section hC hK hsmall hfail hschreier
  let e : GeneralizedFitting.subgroup G ≃* commutator G := MulEquiv.subgroupCongr hF
  have hnonab : ∃ a b : commutator G, a * b ≠ b * a := by
    by_contra h
    refine Group.IsPerfect.not_isSolvable (commutator G) (Group.isSolvable_of_comm fun a b => ?_)
    by_contra hab
    exact h ⟨a, b, hab⟩
  obtain ⟨a, b, hab⟩ := hnonab
  exact ⟨e.isSimpleGroup, ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩,
    hF ▸ hindex, z, hz, hcore⟩

theorem kProper_component_local_B_of_schreier
    (hC : ∀ {X Y : Type} [Group X] [Group Y], X ≃* Y → C Y → C X)
    (hschreier : SchreierFor C) (hU : RelativeU C) (hodd : OddLieInput) (hexc : ExceptionalInput)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (hK : KProper C G)
    (hcomp : IsComponentType G) :
    oddCore G = ⊥ ∧ ComponentType.LocalBProperty G :=
  kProper_component_local_B_of_inputs hC (reducedCounterexample_of_schreier hC hschreier) hU hodd
    hexc G hK hcomp

theorem catalogueSchreier_of_native
    (hTits : ∀ (S : Type) [Group S] (p f : ℕ), ReeTitsModel S .Tits p f →
      Group.IsSolvable (OuterAutomorphisms.Outer S))
    (hspor : ∀ (S : Type) [Group S] [Finite S] [IsSimpleGroup S], (∃ a b : S, a * b ≠ b * a) →
      NativeSporadic.SporadicRep S → Group.IsSolvable (OuterAutomorphisms.Outer S)) :
    SchreierFor Catalog := fun X _ _ _ hnonab hX =>
  CatalogueSchreierAssembly.catalog_schreier_of_tits_sporadic hnonab (hTits X) (hspor X hnonab) hX

theorem kProper_component_local_B_of_parts
    (hTits : ∀ (S : Type) [Group S] (p f : ℕ), ReeTitsModel S .Tits p f →
      Group.IsSolvable (OuterAutomorphisms.Outer S))
    (hspor : ∀ (S : Type) [Group S] [Finite S] [IsSimpleGroup S], (∃ a b : S, a * b ≠ b * a) →
      NativeSporadic.SporadicRep S → Group.IsSolvable (OuterAutomorphisms.Outer S))
    (hU : RelativeU Catalog) (hodd : OddLieInput) (hexc : ExceptionalInput) (G : Type) [Group G]
    [Finite G] [IsSimpleGroup G] (hK : KProper Catalog G) (hcomp : IsComponentType G) :
    oddCore G = ⊥ ∧ ComponentType.LocalBProperty G :=
  kProper_component_local_B_of_schreier (fun e h => SectionRank.catalog_of_mulEquiv e h)
    (catalogueSchreier_of_native hTits hspor) hU hodd hexc G hK hcomp

end CFSG.ComponentClassification.KProperRelativeB
