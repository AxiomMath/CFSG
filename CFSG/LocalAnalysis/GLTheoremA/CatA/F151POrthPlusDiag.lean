module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.F151DiagDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeOrthAsmPlus

public section

namespace CFSG.LocalAnalysis.GLTheoremA.F151

open CFSG.Yardstones.Md0ec50421ce4 (catalogIs onLie)
open CFSG.RankThree.Classical2 (ProjOrthDerived)
open CFSG.LieType.Universal.Spin (quadPlus)
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp.OmegaAux.C
  (exists_mulEquiv_catalogue_statedProj_plus)

private theorem catalogIs_projOrthDerived_plus (n m : ℕ) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ m) (hn : 4 ≤ n) :
    catalogIs (ProjOrthDerived (quadPlus n K)) (onLie fun d => d.characteristic = 2) := by
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := CFSG.RankThree.PartOne.charP_two_of_card_eq_pow hK
  have hring : ringChar K = 2 := ringChar.eq K 2
  obtain ⟨q, hv, -, hqp, ⟨iso⟩⟩ := exists_mulEquiv_catalogue_statedProj_plus (K := K) n hn
  refine ⟨TauCeti.CFSGIndex.lie ⟨.D n q, hv⟩, ?_,
    ⟨(T171Sh.orthModelEquivPlus n K).symm.trans iso⟩⟩
  show (TauCeti.LieTypeIndex.D n q).characteristic = 2
  exact (TauCeti.LieTypeIndex.characteristic_D n q).trans (hqp.trans hring)

theorem orthPlusDiag_of_block (hL : CatLayer) (hC : CatChevComps) (hB : DiagOfBlock)
    (hT : MarkTransport) (hI : ShapeModelDiagIso)
    (hM : T171Sh.OrthComponentBlockAnalysisPlus) : OrthPlusDiag := by
  intro n m K _ _ hn hKcard p hp hp2
  haveI : Finite (ProjOrthDerived (quadPlus n K)) :=
    Finite.of_injective (T171Sh.orthModelEquivPlus n K).symm
      (T171Sh.orthModelEquivPlus n K).symm.injective
  have hcat : catalogIs (ProjOrthDerived (quadPlus n K))
      (onLie fun d => d.characteristic = 2) :=
    catalogIs_projOrthDerived_plus n m K hKcard hn
  have hblock : BlockAnalysisAt (ProjOrthDerived (quadPlus n K)) p :=
    hM hKcard hn hp hp2
  have hdiag : ShapeModelDiagAt (ProjOrthDerived (quadPlus n K)) p :=
    hB (ProjOrthDerived (quadPlus n K)) p hp hp2
      (hL (ProjOrthDerived (quadPlus n K)) p hp hp2 hcat)
      (hC (ProjOrthDerived (quadPlus n K)) p hp hp2 hcat)
      hblock
  exact hI hT _ _ (T171Sh.orthModelEquivPlus n K).symm p hdiag

end CFSG.LocalAnalysis.GLTheoremA.F151

end
