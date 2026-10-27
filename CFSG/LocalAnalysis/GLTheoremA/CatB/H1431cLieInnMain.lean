module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieInn

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1431c

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived)

theorem lieSInn_of_inputs (hL : LieSemisimpleCent) (hB : LieOrderBridge)
    (hI : ∀ d : TauCeti.ValidLieTypeIndex, d.1.characteristic = 2 →
      CompIdxAt 3 d.1 (TauCeti.CFSGIndex.lie d).Group) : LieSInn := by
  intro S _ _ hS hnc d hd hSd α hα hα3 hα1
  obtain ⟨e⟩ := hSd
  refine ⟨fun hC => ?_, fun hC => ?_⟩
  · obtain ⟨i, J, hrel, ⟨φ⟩, hT⟩ :=
      lieSInn_component_index hL hS hnc d hd e (hI d hd) hα hα3 hα1 hC
    exact (lieSInn_fieldSize hB d hd i hrel φ (lieSInn_card_sp6 hB hT) (Or.inl rfl)).1 rfl
  · obtain ⟨i, J, hrel, ⟨φ⟩, hT⟩ :=
      lieSInn_component_index hL hS hnc d hd e (hI d hd) hα hα3 hα1 hC
    exact (lieSInn_fieldSize hB d hd i hrel φ (lieSInn_card_sp48 hB hT) (Or.inr rfl)).2 rfl

theorem lieSInn_holds :
    LieSInn :=
  lieSInn_of_inputs LieSemisimple.lieSemisimpleCent lieOrderBridge_holds
    (I1431C2.compIdxAt_three_of_families lieCompIdx_linear lieCompIdx_unitary
      lieCompIdx_classicalBCD lieCompIdx_triality lieCompIdx_excUntwisted lieCompIdx_excTwisted)

end CFSG.LocalAnalysis.GLTheoremA.H1431c

end
