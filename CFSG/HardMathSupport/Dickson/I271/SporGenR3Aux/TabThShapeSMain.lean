module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabThCensus
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabThCentSInputs
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabThShapeS
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabThG2Rec
public import CFSG.HardMathSupport.Dickson.Sec6.Up34SporAux.ThThree
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThThreeClose
public import Certificates.Certificate17308
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.ConstrainedGen
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.SporRec
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR1Basic
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2Layer
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.BorelTitsConstrained
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.RadicalQuot
public import CFSG.LocalAnalysis.RankThreeTheoremC.InvariantTwoBalanceThree
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3Transitive
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294Inputs
public import CFSG.LocalAnalysis.RankThreeTheoremC.PlaneTransvection
public import CFSG.RankThree.Native.ONSevenDefs
public import CFSG.RankThree.Native.ONSevenRestrict
public import CFSG.RankThree.PartOne.SPOR.OuterSimple
public import CFSG.Sporadic.SuzOddCore.GraphData
public import CFSG.Sporadic.SuzOddCore.SmallActionData
public import CFSG.Walter.Bender1970.S1
public import CFSG.Walter.Bender1970.S2
public import CFSG.Walter.PSL2Facts
public import Certificates.Certificate16041
public import Certificates.Certificate2098
public import Certificates.Certificate2103
public import Certificates.Certificate2108
public import Certificates.Certificate2109
public import Certificates.Certificate2274
public import Certificates.Certificate8137
public import Certificates.Certificate8138
public import Certificates.Certificate8139
public import Certificates.Certificate8140
public import Certificates.Certificate8141
public import Certificates.Certificate8145
public import Certificates.Certificate8146

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.Sporadic.Th CFSG.Blueprint CFSG.Sporadic.Th.Native CFSG.SectionRank.Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlp
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlpNative
  CFSG.HardMathSupport.Dickson.Sec6.Up34Th.ThThreeNative
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThCent
  CFSG.RankThree.PartTwo.Sec4.Item434SporTh CFSG.HardMathSupport.Dickson.Sec6
  CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest
open CFSG.GH74.QTGen4.Recog.G23 (g23Words SatisfiesG23Words)

section Letters


@[expose] noncomputable def thEps (i : Fin 6) : ↥J :=
  slpJ a b TabThNative.progE (TabThNative.eIdx i.val)


theorem th_letters_spec :
    (∀ r ∈ g23Words, evalW thEps r = 1) ∧ (∀ i, thS * thEps i = thEps i * thS) ∧ thEps 0 ≠ 1 := by
  obtain ⟨hrel, hcomm, hne⟩ := Certificates.certificate17308
  exact ⟨fun r hr => (lift_mk_eq_evalW thEps r).symm.trans (hrel r hr), hcomm, hne⟩

end Letters

section Shape


theorem leaf_closure_of_six {X : Type} [Group X] (ε : Fin 6 → X) (hε : SatisfiesG23Words ε)
    (hne : ε 0 ≠ 1) :
    LeafType 3 ↥(Subgroup.closure (Set.range ε)) ∧ IsSimpleGroup ↥(Subgroup.closure (Set.range ε)) ∧
      (∃ a b : ↥(Subgroup.closure (Set.range ε)), a * b ≠ b * a) ∧
      Nat.card ↥(Subgroup.closure (Set.range ε)) = 4245696 := by
  obtain ⟨e⟩ := nonempty_mulEquiv_adjointG2_of_six ε hε ⟨0, hne⟩
  exact leafType_three_of_equiv_adjointG2 e

theorem th_shape_S : ShapeRkAt 3 (LeafType 3) (fun _ _ => True) thS := by
  haveI : Finite ↥J := finite_J
  obtain ⟨hrel, hcomm, hne⟩ := th_letters_spec
  have hε : SatisfiesG23Words thEps := fun r hr => (lift_mk_eq_evalW _ r).trans (hrel r hr)
  obtain ⟨hleaf, hsimp, hnab, hcard⟩ := leaf_closure_of_six thEps hε hne
  have hEC : Subgroup.closure (Set.range thEps) ≤ Subgroup.centralizer ({thS} : Set ↥J) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.2 (hcomm i).symm
  have hs3 : orderOf thS = 3 := th_orderOf.1
  have hO : GLAPPrimeCoreOf 3 (Subgroup.centralizer ({thS} : Set ↥J)) = ⊥ :=
    oPrimeCoreTrivialAt_Th_three_of_residual thThreeResidual_holds thS hs3
  have hC : Nat.card ↥(Subgroup.centralizer ({thS} : Set ↥J)) ≤ 63685439 :=
    th3_facts.2.2.2.2.2
  refine shapeRkAt_of_simple_small_index hs3 hO _ hEC hsimp hnab ?_ ?_ ?_ hleaf
  · rw [hcard]; norm_num
  · rw [hcard]
    intro n hn
    interval_cases n <;> decide
  · rw [hcard]; omega

end Shape

end CFSG.HardMathSupport.Dickson.I271
