module

public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups

namespace Up34Exc


@[expose] def UniEmbed : Prop :=
  ∀ (τ : Tag) {M : Type} [CommGroup M] (χ : Multiplicative (Fin τ.rank → ℤ) →* M)
    (i : KernelComponent χ) (K : Type) [Field K] [Finite K] (ℓ : ℕ) [Fact ℓ.Prime] [CharP K ℓ],
    ∃ V : Subgroup ↥(componentRootSpan K χ i), IsPGroup ℓ V ∧
      Nat.card V = Nat.card K ^ (posRoots (componentRoots χ i)).ncard ∧
      V ⊓ Subgroup.center ↥(componentRootSpan K χ i) = ⊥

end Up34Exc

end CFSG.HardMathSupport.Dickson.Sec6
