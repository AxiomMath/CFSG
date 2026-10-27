module

public import CFSG.HardMathSupport.Foote.Coordinator.CoverThree.Assembly
public import CFSG.HardMathSupport.Malle.Coordinator.CoverThree.RankTwo
public import CFSG.HardMathSupport.Malle.Coordinator.CoverThree.GenToral

public section

namespace CFSG.HardMathSupport.Foote.Coordinator

open CFSG.ComponentClassification.TBLit (GriessMultipliersAllModels)

theorem p1OffCharCoverThree (hGA : GriessMultipliersAllModels) :
    CFSG.AGLEmbedding.P1OffCharCoverThree :=
  p1OffCharCoverThree_of hGA
    (fun d hd hchar A hA => CFSG.HardMathSupport.Malle.Coordinator.CoverThree.coverThree_rank_le_two d hd hchar A hA)
    (fun K _ _ hK d h9 _ hchar e hz P hPc hP hPZ hP3 =>
      CFSG.HardMathSupport.Malle.Coordinator.CoverThree.coverThree_gen_toral hGA hK d h9 e
        (Nat.dvd_of_factorization_pos (show (Nat.card (Subgroup.center K)).factorization 3 ≠ 0 by rw [hz]; exact one_ne_zero)) P hPc hP hPZ hP3)

end CFSG.HardMathSupport.Foote.Coordinator
