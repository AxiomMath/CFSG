module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291DefCharChev
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291DefCharSU
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291DefCharOrth

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open KD291DC

theorem inUni : InUni := fun p n f hp _ hn G _ _ hm => by
  haveI : Fact p.Prime := ⟨hp⟩
  exact rankThreeCent_psu hn hm

theorem kd291DefCharL_of_g2Prime
    (hG2 : InG2Prime) : KD291DefCharL :=
  kd291DefCharL_of_inputs
    { uni := inUni
      omegaOdd := inOmegaOdd
      omegaPlus := inOmegaPlus
      omegaMinus := inOmegaMinus
      f4 := inExc_f4
      e6 := inExc_e6
      e7 := inExc_e7
      e8 := inExc_e8
      twistedE6 := inExc_twistedE6
      trialityD4 := inExc_trialityD4
      g2Two := inG2Two
      g2Prime := hG2 }

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
