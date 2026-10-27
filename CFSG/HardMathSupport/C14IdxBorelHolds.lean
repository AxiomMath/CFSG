module

public import CFSG.HardMathSupport.C14IdxBorel
public import CFSG.HardMathSupport.C14IdxDerived
public import CFSG.HardMathSupport.C14IdxProduct
public import CFSG.LieType.AlgebraicGroups.CocharCurveConnected
public import CFSG.LieType.AlgebraicGroups.RootSpanConnected
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcLevi
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeDiag
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerFiveOrbit
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerFiveRigid
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerFiveTw
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerResiduals
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LangFrame
public import CFSG.LieType.SeitzGeneration.ExtSeitzReeF4Cyclic
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsCentModel
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFieldAut
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
public import CFSG.LocalAnalysis.StandardType.GGL45NtExcIdxRee
public import CFSG.LocalAnalysis.StandardType.GGL45NtExcRee
public import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
public import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
public import CFSG.RankThree.PartOne.BRANCH.RankRee
public import CFSG.RankThree.PartOne.CTP.StrongPBridgeRest
public import CFSG.RankThree.PartOne.KC.LinearCommutatorOdd
public import CFSG.RankThree.PartOne.KC.LinearDegreeFive
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessEven
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessOdd
public import CFSG.RankThree.PartOne.KC.UnitaryHigherCrossPrimeTorus
public import CFSG.RankThree.PartOne.KC.UnitaryPlaneEndpoints
public import CFSG.RankThree.PartOne.KD4T.Certs
public import CFSG.RankThree.PartOne.KE.E7FiveBlock
public import CFSG.RankThree.PartOne.N143.Weyl613Defs
public import CFSG.RankThree.PartOne.N143X.KF64WSimple
public import CFSG.RankThree.PartOne.S11d.OutExceptional
public import CFSG.RankThree.PartTwo.KFacts.KS14SzLie
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent

public section

open scoped CFSG.ConvolutionPoints

open CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.Torality

namespace CFSG.HardMathSupport.C14Idx

theorem isConnectedAlgebraicSubgroup_famZ {τ : Tag} {L : Type} [Field L] {ι : Type}
    [IsAlgClosed L]
    (a : ι → Fin τ.rank → Lˣ) :
    IsConnectedAlgebraicSubgroup L ((famZ a).map (modGLPoint τ L).toMonoidHom) := by
  have hgen : {g : ModGL τ L | ∃ (lam : Fin τ.rank → ℤ) (c : Lˣ),
        (∀ α ∈ familyKernel a, ∑ i, α i * lam i = 0) ∧ g = rootDiagUnit τ (cochar lam c)} =
      {g : ModGL τ L | ∃ lam ∈ {lam : Fin τ.rank → ℤ |
          ∀ α ∈ familyKernel a, ∑ i, α i * lam i = 0}, ∃ c : Lˣ,
        g = rootDiagUnit τ fun i => c ^ lam i} := by
    ext g
    simp only [Set.mem_setOf_eq, cochar]
    exact ⟨fun ⟨lam, c, hlam, hg⟩ => ⟨lam, hlam, c, hg⟩,
      fun ⟨lam, hlam, c, hg⟩ => ⟨lam, c, hlam, hg⟩⟩
  rw [famZ, hgen]
  exact isConnectedAlgebraicSubgroup_closure_cocharCurve _

theorem isConnectedAlgebraicSubgroup_famS {τ : Tag} {L : Type} [Field L] {ι : Type}
    [IsAlgClosed L]
    (a : ι → Fin τ.rank → Lˣ) :
    IsConnectedAlgebraicSubgroup L
      (((famS a).map (adjointGroup τ L).subtype).map (modGLPoint τ L).toMonoidHom) := by
  rw [map_famS_subtype_eq_rootSpan a]
  exact isConnectedAlgebraicSubgroup_rootSpan (familyKernel a)

theorem excBorelInput_holds :
    ExcBorelInput := by
  intro τ L _ _ ι a
  exact ⟨famZ_mem_adjointGroup_and_comm a, exists_famZ_mul_famS_eq a,
    finite_famZ_inter_famS a, isConnectedAlgebraicSubgroup_famZ a,
    isConnectedAlgebraicSubgroup_famS a⟩

end CFSG.HardMathSupport.C14Idx
