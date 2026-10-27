module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.TopBlocks
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathGate7
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyTopL1b
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Final4
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyL3Top
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6TitsLattice
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3Final
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X5Final
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6TopB
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7SecTop
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7SecBTop

public section

namespace CFSG.QuasithinUnique.Setup.Top

open CFSG.Quasithin CFSG.SectionRank CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.QuasithinUnique.Setup CFSG.QuasithinUnique.Setup.Family CFSG.QuasithinUnique.Setup.Lift

theorem actorBase_of_ffHyp {V : Type} [CommGroup V] [Finite V] {H T M E : Subgroup (MulAut V)}
    (h : FFHyp V H T M E) : X35.ActorBase V H T M E :=
  ⟨h.elementary, h.o2_trivial, h.sylow, h.not_normal, h.max, h.offender⟩

theorem noAlt6Component_final
    : NoAlt6Component :=
  fun _ _ _ _ _ _ _ hFF hns hsqtk _ hL => X3.no_A6_component_final hFF hns hsqtk hL

theorem noPSU33Component_final : NoPSU33Component := by
  intro V _ _ H T M E hFF hns _ L hL hmodel
  exact X5.no_unitary_three_at_three_component_unconditional (actorBase_of_ffHyp hFF) hns
    ((Layer.Actor.isComp_iff L H).1 hL) (Or.inl ⟨by decide, hmodel⟩)

theorem noEvenUnitaryThreeComponent_final
    : NoEvenUnitaryThreeComponent := by
  intro V _ _ H T M E hFF hns _ L hL f _
  exact X5.no_even_unitary_three_component_unconditional (actorBase_of_ffHyp hFF) hns
    ((Layer.Actor.isComp_iff L H).1 hL) f

theorem noTrialityOrLargeReeComponent_final
    : NoTrialityOrLargeReeComponent := by
  intro V _ _ H T M E hFF hns _ L hL
  exact ⟨fun f _ => (X6.no_even_triality_or_large_Ree_component Layer.Actor.actorComponentTransfer
      (actorBase_of_ffHyp hFF) hns ((Layer.Actor.isComp_iff L H).1 hL) f).1,
    fun f _ _ => (X6.no_even_triality_or_large_Ree_component Layer.Actor.actorComponentTransfer
      (actorBase_of_ffHyp hFF) hns ((Layer.Actor.isComp_iff L H).1 hL) f).2⟩

theorem noG2OrTitsComponent_final
    (hTits : X6.TitsSylowOvergroupLattice) : NoG2OrTitsComponent := by
  intro V _ _ H T M E hFF hns _ L hL
  have h := X6.no_even_G2_or_Tits_component Layer.Actor.actorComponentTransfer hTits
    (actorBase_of_ffHyp hFF) hns ((Layer.Actor.isComp_iff L H).1 hL)
  exact ⟨fun f _ => h.1 f, h.2⟩

theorem nonsolvableActionSQT
    : NonsolvableActionSQT := by
  intro G _ _ S P h hns
  have hR := reducedAction_of_pushUpObstruction h
  obtain ⟨W, _, _, _, θ, ρ, hbin⟩ := Layer.exists_binModel hR.isElemAbelian hR.le_normalizer
  have hrange : ρ.range = (autOn P (reducedModule S P)).map (Layer.binPsi θ).toMonoidHom :=
    hbin.range_eq
  have hns' : ¬ Group.IsSolvable ↥ρ.range := by
    rw [hrange]
    exact not_isSolvable_map (Layer.binPsi θ) hns
  have hlay := (Layer.Final.original_nonsolvable_action oddKernelCentralization catalogStepHyp h
    hbin).2 hns'
  exact isStronglyQuasithin_of_mulEquiv
    ((Layer.Actor.mapEquiv (Layer.binPsi θ) (autOn P (reducedModule S P))).trans
      (MulEquiv.subgroupCongr hrange.symm)) hlay.sqtk.1.1

theorem familyRestriction_of_L1b
    (hspor : NoSporadicComponentProp)
    (hlin3 : PrimeLinearThreeExclusionProp) (huni3 : PrimeUnitaryThreeExclusionProp) :
    FamilyRestrictionProp := by
  have hlayer := Layer.Actor.actorLayerProp
  have hT := Layer.Actor.actorComponentTransfer
  have hTrans := Layer.Actor.componentTransferProp
  have hSec := Layer.Actor.irreducibleSectionProp
  have hsec : SectionProductionProp := sectionProductionProp_of_irreducibleSection hSec
  have hGL3 : NoGL3ComponentProp := noGL3Component hlayer hT hTrans gl3GraphNormalizerExclusion
  have hA78 : NoAlt78BinaryLinearProp := noAlt78BinaryLinear hT hGL3
  have hSuz : NoSuzukiComponentProp := noSuzukiComponent hlayer hsec
  have hodd : OddClassicalSmallProp :=
    oddClassicalSmall catalogStepHyp hlayer hTrans hSec hA78 hlin3 huni3 primeSquareExclusion
  exact familyRestriction hlayer hspor hSuz hA78 hodd

theorem noSporadicComponent_of_L1b
    (hHe : X1.SporadicExclusion .He)
    (hJ4 : X1.SporadicExclusion .J4) : NoSporadicComponentProp :=
  X1.noSporadicComponentHeJ4 Layer.Actor.actorLayerProp Layer.Actor.componentTransferProp
    Layer.Actor.irreducibleSectionProp hHe hJ4

theorem minParabolicBlocks_of_native
    (hNat : NaturalCanonicalLin2Blocks)
    (hDel : DeletedCanonicalAlt5Blocks) (hHe : X1.SporadicExclusion .He)
    (hJ4 : X1.SporadicExclusion .J4) (huni3 : PrimeUnitaryThreeExclusionProp) :
    MinParabolicBlocks := by
  have hspor : NoSporadicComponentProp := noSporadicComponent_of_L1b hHe hJ4
  exact minParabolicBlocks_of_canonical Wreath.solvableA3Family hNat hDel nonsolvableActionSQT
    (familyTop_of_L1b hspor primeLinearThreeExclusion huni3)
    (familyRestriction_of_L1b hspor primeLinearThreeExclusion huni3)
    noAlt6Component_final noPSU33Component_final noEvenUnitaryThreeComponent_final
    noTrialityOrLargeReeComponent_final (noG2OrTitsComponent_final X6.titsSylowOvergroupLattice)
    X7Sec.actualLinearThreeSelfDualSections X7Sec.actualSymplecticFourData

end CFSG.QuasithinUnique.Setup.Top
