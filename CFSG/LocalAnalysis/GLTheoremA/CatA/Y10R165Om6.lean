module

public import CFSG.RankThree.PartOne.KC.OrthogonalEvenMinusFourExtract
public import CFSG.RankThree.PartOne.KC.OrthogonalEvenMinusSixExtract
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.Classical2.OrthogonalIsotropicUnipotent
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical2 QuadraticMap

namespace OmEngine

variable {K W : Type} [Field K] [Finite K] [CharP K 2] [AddCommGroup W] [Module K W]
  [FiniteDimensional K W] {Q : QuadraticForm K W}

theorem mem_orthDerived_of_odd_of_finrank_four
    (hQ : (polarBilin Q).Nondegenerate) (hdim : Module.finrank K W = 4)
    (hns : ∀ U : Submodule K W, Module.finrank K U = 2 → ∃ u ∈ U, Q u ≠ 0)
    {g : W ≃ₗ[K] W} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hodd : Odd (orderOf g)) :
    g ∈ orthDerived Q := by
  obtain ⟨E, _, _, D, ψ, ρ, -, -, -, -, hcomm, -, -, -, -, -, -, hoddmem⟩ :=
    CFSG.RankThree.PartOne.even_minus_four_actual_derived_extraction Q hQ hdim hns
  have hEq : orthDerived Q = ρ.range := hcomm
  exact hEq.ge (hoddmem g hg hodd)

theorem mem_orthDerived_of_odd_of_finrank_six
    (hQ : (polarBilin Q).Nondegenerate) (hdim : Module.finrank K W = 6)
    (hts : ∀ U : Submodule K W, Module.finrank K U = 3 → ∃ u ∈ U, Q u ≠ 0)
    {g : W ≃ₗ[K] W} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hodd : Odd (orderOf g)) :
    g ∈ orthDerived Q := by
  obtain ⟨E, _, _, D, ψ, ρ, -, -, -, -, hcomm, -, -, -, -, -, -, hoddmem⟩ :=
    CFSG.RankThree.PartOne.even_minus_six_actual_derived_extraction Q hQ hdim hts
  have hEq : orthDerived Q = ρ.range := hcomm
  exact hEq.ge (hoddmem g hg hodd)

end OmEngine

end CFSG.LocalAnalysis.GLTheoremA.Y10F
