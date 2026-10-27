module

public import CFSG.LieType.Chevalley.E7Three.Fourier
public import CFSG.LieType.Chevalley.E7Three.BasisActions
public import CFSG.LieType.Chevalley.E7Three.TriangularActions
public import CFSG.LocalAnalysis.StandardType.GGAutomizerMap
public import CFSG.GH74.Generic.Certificates
public import CFSG.GH74.Statements
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerE8Five
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerResiduals
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwE6
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwF4
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwRigid
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSU
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialPoly
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.OuterField
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidField
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidNorm
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LangFrame
public import CFSG.LieType.AlgebraicGroups.ConnectedToralLang
public import CFSG.LieType.Chevalley.EvenTrialityOuterInvolutions
public import CFSG.LieType.Chevalley.OddTrialityCosetInvolutions
public import CFSG.LieType.SeitzGeneration.ExtSeitzReeF4Cyclic
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeTwo
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsCentModel
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFieldAut
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueUStatement
public import CFSG.LocalAnalysis.ComponentClassification.GSLitType
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfE7Three
public import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
public import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
public import CFSG.RankThree.Chevalley.SteinbergBTTwistedCosetDescent
public import CFSG.RankThree.Classical.SteinbergBJSymplecticSquareZeroCentralizer
public import CFSG.RankThree.PartOne.BRANCH.RankRee
public import CFSG.RankThree.PartOne.CTP.StrongPBridgeRest
public import CFSG.RankThree.PartOne.KC.LinearCommutatorOdd
public import CFSG.RankThree.PartOne.KC.LinearDegreeFive
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessEven
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessOdd
public import CFSG.RankThree.PartOne.KC.UnitaryHigherCrossPrimeTorus
public import CFSG.RankThree.PartOne.KC.UnitaryPlaneEndpoints
public import CFSG.RankThree.PartOne.KE.E7FiveBlock
public import CFSG.RankThree.PartOne.KE.E7FourLattice
public import CFSG.RankThree.PartOne.KE.E8D4Family
public import CFSG.RankThree.PartOne.KE.SLnShape
public import CFSG.RankThree.PartOne.KE.StabGeneral
public import CFSG.RankThree.PartOne.KE.ThreeA1Group
public import CFSG.RankThree.PartOne.N143.Weyl613Defs
public import CFSG.RankThree.PartOne.N143X.KF64WSimple
public import CFSG.RankThree.PartOne.S11d.OutExceptional
public import CFSG.RankThree.PartOne.S11d.OutLinear
public import CFSG.RankThree.PartTwo.KFacts.KS14SzLie
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic
public import CFSG.RankThree.SubgroupLists.CommutatorScalarBound
public import CFSG.RankThree.SubgroupLists.ExtraspecialNormal
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import CFSG.Sporadic.Th.Max3.Core
public import Certificates.Certificate1
public import Certificates.Certificate1953
public import Certificates.Certificate1954
public import Certificates.Certificate2
public import Certificates.Kernel.SporSch.Th.Plane2320

public noncomputable section

set_option autoImplicit false

namespace CFSG.LieType.Chevalley.E7Three.Automizer

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KA5L
  CFSG.StandardType
  CFSG.LieType.Chevalley.E7Three.Cube CFSG.LieType.Chevalley.E7Three.Fourier
  CFSG.LieType.Chevalley.E7Three.Multiplicity
  CFSG.LieType.Chevalley.E7Three.CoordinateActions CFSG.LieType.Chevalley.E7Three.BasisActions
  CFSG.LieType.Chevalley.E7Three.TriangularActions

variable {K : Type} [Field K] [CharP K 2]

@[expose] def cubeEquiv (ζ : Kˣ) (hζ : IsPrimitiveRoot ζ 3) :
    D ≃* (cubeHom ζ hζ.pow_eq_one).range := MonoidHom.ofInjective (cubeHom_injective ζ hζ)

theorem cubeHom_basis (ζ : Kˣ) (hζ : ζ ^ 3 = 1) (i : Fin 3) :
    cubeHom ζ hζ (basis i) = generators ζ i := by
  have h1 : (1 : ZMod 3).val = 1 := by decide +kernel
  fin_cases i <;> rw [cubeHom_apply] <;> simp [basis, generators, h1]

theorem u_eq_conj_a5Cycle (ζ : Kˣ) (hζ : IsPrimitiveRoot ζ 3) :
    MulAut.congr (cubeEquiv ζ hζ) u =
      ggConjAut (cubeHom ζ hζ.pow_eq_one).range
        (a5CycleElement_mem_normalizer ζ hζ.pow_eq_one) := by
  apply congr_eq_conjAut_of_basis _ (cubeEquiv ζ hζ) u
    (a5CycleElement (K := K)) (a5CycleElement_mem_normalizer ζ hζ.pow_eq_one)
  intro i
  change a5CycleElement * cubeHom ζ hζ.pow_eq_one (basis i) * a5CycleElement⁻¹ =
    cubeHom ζ hζ.pow_eq_one (u (basis i))
  rw [cubeHom_basis]
  fin_cases i
  all_goals dsimp only
  · change a5CycleElement * scalarWord ζ * a5CycleElement⁻¹ =
      cubeHom ζ hζ.pow_eq_one (u (basis 0))
    rw [u_basis_zero, cubeHom_basis]
    exact a5CycleElement_conj_scalarWord ζ hζ.pow_eq_one
  · change a5CycleElement * pairedWord ζ * a5CycleElement⁻¹ =
      cubeHom ζ hζ.pow_eq_one (u (basis 1))
    rw [u_basis_one, map_mul, map_pow, cubeHom_basis, cubeHom_basis]
    exact a5CycleElement_conj_pairedWord ζ hζ.pow_eq_one
  · change a5CycleElement * cyclic * a5CycleElement⁻¹ =
      cubeHom ζ hζ.pow_eq_one (u (basis 2))
    rw [u_basis_two, cubeHom_basis]
    exact a5CycleElement_conj_cyclic

theorem exists_fourier_eq_conj (ζ : Kˣ) (hζ : IsPrimitiveRoot ζ 3) :
    ∃ (n : adjointGroup .E7 K)
      (hn : n ∈ Subgroup.normalizer ((cubeHom ζ hζ.pow_eq_one).range : Set (adjointGroup .E7 K))),
      MulAut.congr (cubeEquiv ζ hζ) v = ggConjAut (cubeHom ζ hζ.pow_eq_one).range hn ∧
        n ^ 4 = 1 ∧ n * multiplicityWord ζ * n⁻¹ = multiplicityWord ζ := by
  have hζ1 : (ζ : K) ≠ 1 := by
    intro h
    have he : ζ = 1 := Units.ext h
    have hd : 3 ∣ 1 := hζ.dvd_of_pow_eq_one 1 (by simp [he])
    norm_num at hd
  obtain ⟨n, hn, hg, hb, hc, h4, hm⟩ :=
    exists_fourier_normalizer_and_multiplicity ζ hζ.pow_eq_one hζ1
  refine ⟨n, hn, ?_, h4, hm⟩
  apply congr_eq_conjAut_of_basis _ (cubeEquiv ζ hζ) v n hn
  intro i
  change n * cubeHom ζ hζ.pow_eq_one (basis i) * n⁻¹ =
    cubeHom ζ hζ.pow_eq_one (v (basis i))
  rw [cubeHom_basis]
  fin_cases i
  all_goals dsimp only
  · change n * scalarWord ζ * n⁻¹ = cubeHom ζ hζ.pow_eq_one (v (basis 0))
    rw [v_basis_zero, cubeHom_basis]
    exact hg
  · change n * pairedWord ζ * n⁻¹ = cubeHom ζ hζ.pow_eq_one (v (basis 1))
    rw [v_basis_one, map_pow, cubeHom_basis]
    exact hb
  · change n * cyclic * n⁻¹ = cubeHom ζ hζ.pow_eq_one (v (basis 2))
    rw [v_basis_two, cubeHom_basis]
    exact hc

theorem w_eq_conj_move (ζ : Kˣ) (hζ : IsPrimitiveRoot ζ 3) :
    MulAut.congr (cubeEquiv ζ hζ) w =
      ggConjAut (cubeHom ζ hζ.pow_eq_one).range
        (moveElement_mem_normalizer ζ hζ.pow_eq_one) := by
  have hsinv : (scalarWord ζ)⁻¹ = scalarWord ζ ^ 2 := by
    apply inv_eq_of_mul_eq_one_left
    simpa only [← pow_succ] using scalarWord_pow_three ζ hζ.pow_eq_one
  have hbinv : (pairedWord ζ)⁻¹ = pairedWord ζ ^ 2 := by
    apply inv_eq_of_mul_eq_one_left
    simpa only [← pow_succ] using pairedWord_pow_three ζ hζ.pow_eq_one
  apply congr_eq_conjAut_of_basis _ (cubeEquiv ζ hζ) w
    (moveElement (K := K)) (moveElement_mem_normalizer ζ hζ.pow_eq_one)
  intro i
  change moveElement * cubeHom ζ hζ.pow_eq_one (basis i) * moveElement⁻¹ =
    cubeHom ζ hζ.pow_eq_one (w (basis i))
  rw [cubeHom_basis]
  fin_cases i
  all_goals dsimp only
  · change moveElement * scalarWord ζ * moveElement⁻¹ =
      cubeHom ζ hζ.pow_eq_one (w (basis 0))
    rw [w_basis_zero, map_pow, cubeHom_basis]
    change moveElement * scalarWord ζ * moveElement⁻¹ = pairedWord ζ ^ 2
    simpa only [hsinv, hbinv] using moveElement_conj_scalarWord ζ hζ.pow_eq_one
  · change moveElement * pairedWord ζ * moveElement⁻¹ =
      cubeHom ζ hζ.pow_eq_one (w (basis 1))
    rw [w_basis_one, map_pow, cubeHom_basis]
    change moveElement * pairedWord ζ * moveElement⁻¹ = scalarWord ζ ^ 2
    simpa only [hsinv, hbinv] using moveElement_conj_pairedWord ζ hζ.pow_eq_one
  · change moveElement * cyclic * moveElement⁻¹ =
      cubeHom ζ hζ.pow_eq_one (w (basis 2))
    rw [w_basis_two, map_pow, cubeHom_basis]
    exact moveElement_conj_cyclic

end CFSG.LieType.Chevalley.E7Three.Automizer
