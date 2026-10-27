module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyStatements
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyAlt7
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyLinearBinary
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Top

public section

namespace CFSG.QuasithinUnique.Setup.Family

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X35 CFSG.QuasithinUnique.Setup.X6

theorem FFHyp.toActorBase {V : Type} [CommGroup V] [Finite V] {H T M E : Subgroup (MulAut V)}
    (h : FFHyp V H T M E) : ActorBase V H T M E :=
  ⟨h.elementary, h.o2_trivial, h.sylow, h.not_normal, h.max, h.offender⟩

theorem isComponentIn_of_isComp {G : Type} [Group G] {L H : Subgroup G} (hL : IsComp L H) :
    IsComponentIn L H :=
  ⟨hL.1, (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hL.1).1
    ((CFSG.ComponentClassification.AssemblyBPredicates.isComponentOf_iff_open L H).2 hL)⟩

@[expose] def NoGL3ComponentProp : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (H T M E : Subgroup (MulAut V)),
    FFHyp V H T M E → ¬ Group.IsSolvable H → ∀ L : Subgroup (MulAut V), IsComp L H →
      ¬ Nonempty (CQ L ≃* GL (Fin 3) (ZMod 2))

theorem false_of_isComp_twoGeneratingSylowOvergroups (hT : ActorComponentTransfer) {V : Type}
    [CommGroup V] [Finite V] {H T M E : Subgroup (MulAut V)} (hFF : FFHyp V H T M E)
    (hns : ¬ Group.IsSolvable H) {L : Subgroup (MulAut V)} (hL : IsComp L H)
    (hX : TwoGeneratingSylowOvergroups (CQ L)) : False :=
  false_of_actorComponentTransfer hT hFF.toActorBase hns (isComponentIn_of_isComp hL) hX

theorem noAlt78BinaryLinear (hT : ActorComponentTransfer) (hGL3 : NoGL3ComponentProp) :
    NoAlt78BinaryLinearProp := by
  intro V _ _ H T M E hFF hns L hL
  refine ⟨?_, ?_⟩
  · rintro n (rfl | rfl) ⟨e⟩
    · exact false_of_isComp_twoGeneratingSylowOvergroups hT hFF hns hL
        (TwoGeneratingSylowOvergroups.of_mulEquiv e.symm twoGeneratingSylowOvergroups_alt_seven)
    · exact false_of_isComp_twoGeneratingSylowOvergroups hT hFF hns hL
        (TwoGeneratingSylowOvergroups.of_mulEquiv e.symm twoGeneratingSylowOvergroups_alt_eight)
  · intro n hn ⟨e⟩
    rcases (by omega : n = 3 ∨ 4 ≤ n) with rfl | h4
    · exact hGL3 V H T M E hFF hns L hL ⟨e.trans (slEquivGL 3)⟩
    · exact false_of_isComp_twoGeneratingSylowOvergroups hT hFF hns hL
        (TwoGeneratingSylowOvergroups.of_mulEquiv e.symm
          (twoGeneratingSylowOvergroups_binary_linear h4))

end CFSG.QuasithinUnique.Setup.Family
