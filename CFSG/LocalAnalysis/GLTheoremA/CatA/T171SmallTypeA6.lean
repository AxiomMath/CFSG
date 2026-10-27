module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171SmallTypeDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ChevTwoInn
import CFSG.LocalAnalysis.GLTheoremA.CatB.I1430LieTwoInnRed
import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTSp8

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171S

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived)

theorem a6InnField_of_inputs (hL : LieSemisimpleCent) (hB : LieOrderBridge)
    (hI : ∀ d : TauCeti.ValidLieTypeIndex, d.1.characteristic = 2 →
      CompIdxAt 3 d.1 (TauCeti.CFSGIndex.lie d).Group) : A6InnField := by
  intro S _ _ hS hnc d hd hSd α hα hP
  obtain ⟨e⟩ := hSd
  obtain ⟨hα3, hα1, hC⟩ := hP
  obtain ⟨i, J, hrel, ⟨φ⟩, hcat⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.H1431c.lieSInn_component_index hL hS hnc d hd e
      (hI d hd) hα hα3 hα1 hC
  exact CFSG.LocalAnalysis.GLTheoremA.S8.L84.ClsRed.i1430_fieldSize hB d hd i hrel φ
    (CFSG.LocalAnalysis.GLTheoremA.HSubT.card_of_catalogIs_alt6 hcat)

theorem a6InnField_holds :
    A6InnField :=
  a6InnField_of_inputs LieSemisimple.lieSemisimpleCent lieOrderBridge_holds
    (CFSG.LocalAnalysis.GLTheoremA.I1431C2.compIdxAt_three_of_families
      lieCompIdx_linear lieCompIdx_unitary lieCompIdx_classicalBCD lieCompIdx_triality
      lieCompIdx_excUntwisted lieCompIdx_excTwisted)

end CFSG.LocalAnalysis.GLTheoremA.T171S

end
