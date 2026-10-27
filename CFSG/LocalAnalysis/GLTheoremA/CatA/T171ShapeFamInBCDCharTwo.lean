module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeSpModelSelfDualMain
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeOrthPairMain
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeSpBlock
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeCompDescIndSymp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeOrthModelAnalysis
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeOrthCatCatalogue
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeOrthAsmPlus
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeOrthAsmMinus
import CFSG.LocalAnalysis.ComponentInitial.ProjectiveOrthogonalLocalComponent

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Yardstones.Md0ec50421ce4
open CFSG.LieType.Universal.Spin (quadPlus quadMinus)

theorem orthComponentBlockAnalysis_holds {K V : Type} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] (Q : QuadraticForm K V)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hQne : ∃ v, Q v ≠ 0) :
    OrthComponentBlockAnalysis Q :=
  orthComponentBlockAnalysis_holds_of_residuals orthPairedBlockModel_holds orthSelfDualCatalogue
    Q hQ hQne

theorem orthComponentBlockAnalysisPlus_holds : OrthComponentBlockAnalysisPlus :=
  orthComponentBlockAnalysisPlus_of_generic fun m K _ _ _ hm => by
    haveI : Nonempty (Fin m ⊕ Fin m) := ⟨Sum.inl ⟨0, by omega⟩⟩
    have hQ := CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus m K
    exact @orthComponentBlockAnalysis_holds _ _ _ _ _ _ _ _ _ hQ
      (CFSG.LocalAnalysis.ComponentInitial.ProjectiveOrthogonal.exists_ne_zero_of_nondegenerate hQ)

theorem orthComponentBlockAnalysisMinus_holds : OrthComponentBlockAnalysisMinus :=
  orthComponentBlockAnalysisMinus_of_generic fun m K _ _ _ b₀ c₀ _ hbc => by
    haveI : Nonempty (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) := ⟨Sum.inr (Sum.inr 0)⟩
    have hQ := CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite m K hbc
    exact @orthComponentBlockAnalysis_holds _ _ _ _ _ _ _ _ _ hQ
      (CFSG.LocalAnalysis.ComponentInitial.ProjectiveOrthogonal.exists_ne_zero_of_nondegenerate hQ)

theorem innerCompNonShape_classicalBCD_charTwo_of_halves
    (hS : InnerCompNonShape fun i => isSympBCIdx i ∧ i.characteristic = 2)
    (hO : InnerCompNonShape fun i => isOrthDIdx i ∧ i.characteristic = 2) :
    InnerCompNonShape fun i => KD264Lie.isClassicalBCDIdx i ∧ i.characteristic = 2 := by
  intro G _ _ p L J A d b hSet hcat hshape hin
  obtain ⟨i, hi, e⟩ := hcat
  cases i with
  | lie dd =>
    obtain ⟨d0, hv⟩ := dd
    have hc := hi.2
    cases d0 with
    | B n q => exact hS p L J A d b hSet ⟨.lie ⟨.B n q, hv⟩, ⟨trivial, hc⟩, e⟩ hshape hin
    | C n q => exact hS p L J A d b hSet ⟨.lie ⟨.C n q, hv⟩, ⟨trivial, hc⟩, e⟩ hshape hin
    | D n q => exact hO p L J A d b hSet ⟨.lie ⟨.D n q, hv⟩, ⟨trivial, hc⟩, e⟩ hshape hin
    | twistedD n q =>
      exact hO p L J A d b hSet ⟨.lie ⟨.twistedD n q, hv⟩, ⟨trivial, hc⟩, e⟩ hshape hin
    | _ => simp [onLie, KD264Lie.isClassicalBCDIdx] at hi
  | cyclic _ _ => simp [onLie] at hi
  | alternating _ _ => simp [onLie] at hi
  | sporadic _ => simp [onLie] at hi


theorem innerCompNonShape_symp_charTwo_holds :
    InnerCompNonShape fun i => isSympBCIdx i ∧ i.characteristic = 2 :=
  innerCompNonShape_symp_charTwo (sympCompMatrixAnalysis_of sympComponentDescent_holds
    unitaryBlockInnAutDerived_holds sympComponentBlockAnalysis_holds)

theorem innerCompNonShape_orth_charTwo_holds :
    InnerCompNonShape fun i => isOrthDIdx i ∧ i.characteristic = 2 :=
  innerCompNonShape_orth_charTwo_of_matrixAnalysis
    (orthCompMatrixAnalysisPlus_of componentDescentIndAut_holds unitaryBlockInnAutDerived_holds
      orthComponentBlockAnalysisPlus_holds)
    (orthCompMatrixAnalysisMinus_of componentDescentIndAut_holds unitaryBlockInnAutDerived_holds
      orthComponentBlockAnalysisMinus_holds)

theorem innerCompNonShape_classicalBCD_charTwo_holds :
    InnerCompNonShape fun i => KD264Lie.isClassicalBCDIdx i ∧ i.characteristic = 2 :=
  innerCompNonShape_classicalBCD_charTwo_of_halves innerCompNonShape_symp_charTwo_holds
    innerCompNonShape_orth_charTwo_holds

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
