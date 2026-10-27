module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.BRowsOf
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicDataRest
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.BFiveCheck
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.KlingenIdentSporAux
public import CFSG.Sporadic.Bridge.BTc

public section

namespace CFSG.AGLEmbedding

open CFSG.Blueprint CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary

theorem coverWeakGen_of_kernelTrivialAt {X : Type} [Group X] {p : ℕ} [Fact p.Prime]
    (hkt : KernelTrivialAt X p) : CoverWeakGen X p := by
  intro K _ _ π hπ hker hperf hZ hZp _ T
  exfalso
  apply hZ
  rw [← hker]
  exact @hkt K _ _ hperf π hπ hker.le (by rw [hker]; exact hZp)

section

theorem kernelTrivialAt_B_five :
    KernelTrivialAt NativeSporadic.B 5 := by
  intro E _ _ _ π hπ hC hpg
  exact BScal.bKernelTrivial E π hπ hC hpg

theorem sporadicCaseThreeData_B_of_tc_kt (htc : TCGenDatum NativeSporadic.B 5)
    (hkt : KernelTrivialAt NativeSporadic.B 5) :
    SporadicCaseThreeData (NativeSporadic.Carrier .B) :=
  sporadicCaseThreeData_B_of fun {_ _} =>
    Or.inr (Or.inr ⟨fun T => Or.inl (weakCoreOfTC _ 5 htc T), Or.inl hkt⟩)

theorem sporadicCaseThreeData_B_of_tc_scal
    (htc : TCGenDatum NativeSporadic.B 5) : SporadicCaseThreeDataRest :=
  sporadicCaseThreeData_B_of_tc_kt htc kernelTrivialAt_B_five

end

end CFSG.AGLEmbedding

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.KlingenIdentSporAux

open CFSG.Blueprint CFSG.AGLEmbedding

theorem genData_of_tc_kt {X : Type} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    (htc : TCGenDatum X p) (hkt : KernelTrivialAt X p) : GenData X p :=
  ⟨fun T => weakCoreOfTC X p htc T, coverWeakGen_of_kernelTrivialAt hkt⟩

theorem genData_B_five_of_scal
    [Finite (NativeSporadic.Carrier .B)] [Fact (Nat.Prime 5)] :
    GenData (NativeSporadic.Carrier .B) 5 :=
  genData_of_tc_kt (X := NativeSporadic.B) CFSG.Sporadic.Bridge.B.tcGenDatum_B_five
    kernelTrivialAt_B_five

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.KlingenIdentSporAux
