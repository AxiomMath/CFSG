module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.DResE81Half

public section

namespace CFSG.EvenSporadicStandard.M24Std.DRes

open Subgroup CFSG.Open

@[expose] def Ega81CSideHalf : Prop :=
  Ega81Sit fun G _ _ L z A _ C _ =>
    Nonempty (egaLayer (egQD C ⧸ fusionOddCore (egQD C)) ≃*
      alternatingGroup (Fin 6) × alternatingGroup (Fin 6)) →
    ∃ E : Subgroup G, CSideHalf L A z E

theorem residue_cStruct_of_half
    (h : Ega81CSideHalf) :
    Ega81Sit fun _ _ _ _ _ _ _ C D =>
      Nonempty (egaLayer (egQD C ⧸ fusionOddCore (egQD C)) ≃*
        alternatingGroup (Fin 6) × alternatingGroup (Fin 6)) →
      HasElemAbThree81 (egQD D ⧸ fusionOddCore (egQD D)) := by
  intro G _ _ L z hZ hstd hs A B C D hF hE
  obtain ⟨E, hE'⟩ := h G L z hZ hstd hs A B C D hF hE
  obtain ⟨X, Q1, T1, hdata⟩ := e81Data_of_half hs hF (DResH.lem17_of_pair hF.pair) hE'
  exact hdata.hasElemAbThree81

end CFSG.EvenSporadicStandard.M24Std.DRes
