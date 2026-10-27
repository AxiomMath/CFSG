module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X5aActor
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X5bFinal
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerActorComp
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerActorSection2

public section

namespace CFSG.QuasithinUnique.Setup.X5

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X35 CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial

theorem actorComponentSection : ActorComponentSection := by
  intro V _ _ H T M E hB hns L hL
  have hFF : Family.FFHyp V H T M E :=
    ⟨hB.elementary, hB.o2_trivial, hB.sylow, hB.not_normal, hB.max, hB.offender⟩
  have hlay := Layer.Actor.actorLayerProp V H T M E hFF hns
  have hL' : Family.IsComp L H := (Layer.Actor.isComp_iff L H).2 hL
  obtain ⟨A, hA, hAL⟩ := hlay.component_commutator L hL'
  have hqs : CFSG.IsQuasisimple ↥L :=
    (isQuasisimple_congr (Subgroup.subgroupOfEquivOfLe hL.1)).mp hL.2.1
  have hLne : L ≠ ⊥ := by
    have := CFSG.LocalCores.isQuasisimple_nontrivial hqs
    exact (Subgroup.nontrivial_iff_ne_bot L).1 this
  have hne : ⁅L, A⁆ ≠ ⊥ := by
    rw [hAL]
    exact hLne
  exact Layer.Actor.sectionProductionProp V hB.elementary H L A hL' hA hne

theorem no_unitary_three_at_three_component_unconditional {V : Type} [CommGroup V] [Finite V]
    {H T M E : Subgroup (MulAut V)} (hA : ActorBase V H T M E) (hns : ¬ Group.IsSolvable H)
    {L : Subgroup (MulAut V)} (hL : IsComponentIn L H) :
    ¬ CFSG.Blueprint.LieModel (L ⧸ Subgroup.center L) .PSU 3 3 1 :=
  no_unitary_three_at_three_component Layer.Actor.actorComponentTransfer hA hns hL

theorem no_even_unitary_three_component_unconditional
    {V : Type} [CommGroup V] [Finite V]
    {H T M E : Subgroup (MulAut V)} (hA : ActorBase V H T M E) (hns : ¬ Group.IsSolvable H)
    {L : Subgroup (MulAut V)} (hL : IsComponentIn L H) (f : ℕ) :
    ¬ StatedClassicalModel (L ⧸ Subgroup.center L) .PSU 3 2 f :=
  no_even_unitary_three_component_of_section actorComponentSection hA hns hL f

end CFSG.QuasithinUnique.Setup.X5
