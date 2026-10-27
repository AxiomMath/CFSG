module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueRelativeBSec
public import CFSG.LocalAnalysis.ComponentClassification.KProperRelativeBShell

public section

namespace CFSG.ComponentClassification.KProperRelativeB

open CFSG.Assembly CFSG.Blueprint
open LocalAnalysis.ComponentInitial (SchreierFor)
open CFSG.SignalizerFunctorTheorem (IsSectionOf)

variable {C : GroupProp}

@[expose] def RelativeUAt (C : GroupProp) (X : Type) [Group X] [Finite X] : Prop :=
  KProper C X →
    IsSimpleGroup (GeneralizedFitting.subgroup X) →
    (∃ a b : GeneralizedFitting.subgroup X, a * b ≠ b * a) →
    (∃ z : X, orderOf z = 2 ∧ CFSG.oddCore (Subgroup.centralizer ({z} : Set X)) ≠ ⊥) →
    OutcomeLocal.UOutcome X

@[expose] def ReducedCounterexampleSec (C : GroupProp) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], KProper C G →
    CatalogueRelativeB.InductionHypothesisSec C G →
    ¬ CentralTwoBInclusion.Property G →
    IsSimpleGroup (GeneralizedFitting.subgroup G) ∧
      (∃ a b : GeneralizedFitting.subgroup G, a * b ≠ b * a) ∧
      (GeneralizedFitting.subgroup G).index ≤ 2 ∧
      ∃ z : G, orderOf z = 2 ∧ CFSG.oddCore (Subgroup.centralizer ({z} : Set G)) ≠ ⊥

theorem reducedCounterexampleSec_of_schreier
    (hC : ∀ {X Y : Type} [Group X] [Group Y], X ≃* Y → C Y → C X)
    (hschreier : SchreierFor C) : ReducedCounterexampleSec C := by
  intro G _ _ hK hsmall hfail
  obtain ⟨hsimple, hperfect, hF, hindex, z, hz, -, -, hcore⟩ :=
    CatalogueRelativeB.simple_unbalanced_section_sec hC hK hsmall hfail hschreier
  let e : GeneralizedFitting.subgroup G ≃* commutator G := MulEquiv.subgroupCongr hF
  have hnonab : ∃ a b : commutator G, a * b ≠ b * a := by
    by_contra h
    refine Group.IsPerfect.not_isSolvable (commutator G) (Group.isSolvable_of_comm fun a b => ?_)
    by_contra hab
    exact h ⟨a, b, hab⟩
  obtain ⟨a, b, hab⟩ := hnonab
  exact ⟨e.isSimpleGroup, ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩,
    hF ▸ hindex, z, hz, hcore⟩

theorem kProper_B_inclusion_of_inputs_P
    (P : ∀ (X : Type) [Group X], Prop)
    (hP : ∀ (X Y : Type) [Group X] [Group Y], P Y → IsSectionOf X Y → P X)
    (hC : ∀ {X Y : Type} [Group X] [Group Y], X ≃* Y → C Y → C X)
    (hred : ReducedCounterexampleSec C)
    (hU : ∀ (X : Type) [Group X] [Finite X], P X → RelativeUAt C X) (hodd : OddLieInput)
    (hexc : ExceptionalInput) :
    ∀ (G : Type) [Group G] [Finite G], P G → KProper C G → CentralTwoBInclusion.Property G := by
  suffices h : ∀ n : ℕ, ∀ (G : Type) [Group G] [Finite G], Nat.card G = n → P G →
      KProper C G → CentralTwoBInclusion.Property G from
    fun G _ _ hPG hK => h _ G rfl hPG hK
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro G _ _ hn hPG hK
    have hsmall : CatalogueRelativeB.InductionHypothesisSec C G :=
      fun X _ _ hXG hX hlt => ih (Nat.card X) (hn ▸ hlt) X rfl (hP X G hPG hXG) hX
    have hproper : ∀ X : Subgroup G, X ≠ ⊤ → CentralTwoBInclusion.Property X := fun X hX =>
      CatalogueRelativeB.proper_subgroup_B_sec hC hK hsmall X hX
    by_contra hfail
    obtain ⟨hsimple, hnonab, hindex, hz⟩ := hred G hK hsmall hfail
    have : IsSimpleGroup (GeneralizedFitting.subgroup G) := hsimple
    rcases hU G hPG hK hsimple hnonab hz with hlie | ⟨m, -, hm, ⟨θ⟩, -⟩ | ⟨hexcmodel, -⟩
    · exact hfail (hodd G hsimple hnonab hindex hlie hproper)
    · exact hfail (CatalogueBAlternating.generalizedFitting_B_inclusion hnonab (Or.inr hm) θ)
    · exact hfail (hexc G hsimple hnonab hindex hexcmodel hproper)

end CFSG.ComponentClassification.KProperRelativeB
