module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxLinear
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxUnitary
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxClassical
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxExc2

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie


theorem lieCompIdx_all : LieCompIdx fun _ => True := by
  rintro ⟨d, hv⟩ p hp hp2 hpc -
  cases d with
  | A n q => exact lieCompIdx_linear ⟨_, hv⟩ p hp hp2 hpc trivial
  | twistedA n q => exact lieCompIdx_unitary ⟨_, hv⟩ p hp hp2 hpc trivial
  | B n q => exact lieCompIdx_classicalBCD ⟨_, hv⟩ p hp hp2 hpc trivial
  | C n q => exact lieCompIdx_classicalBCD ⟨_, hv⟩ p hp hp2 hpc trivial
  | D n q => exact lieCompIdx_classicalBCD ⟨_, hv⟩ p hp hp2 hpc trivial
  | twistedD n q => exact lieCompIdx_classicalBCD ⟨_, hv⟩ p hp hp2 hpc trivial
  | E6 q => exact lieCompIdx_excUntwisted ⟨_, hv⟩ p hp hp2 hpc trivial
  | E7 q => exact lieCompIdx_excUntwisted ⟨_, hv⟩ p hp hp2 hpc trivial
  | E8 q => exact lieCompIdx_excUntwisted ⟨_, hv⟩ p hp hp2 hpc trivial
  | F4 q => exact lieCompIdx_excUntwisted ⟨_, hv⟩ p hp hp2 hpc trivial
  | G2 q => exact lieCompIdx_excUntwisted ⟨_, hv⟩ p hp hp2 hpc trivial
  | twistedE6 q => exact lieCompIdx_excTwisted ⟨_, hv⟩ p hp hp2 hpc trivial
  | trialityD4 q => exact lieCompIdx_triality ⟨_, hv⟩ p hp hp2 hpc trivial
  | suzuki k => exact lieCompIdx_excTwisted ⟨_, hv⟩ p hp hp2 hpc trivial
  | reeG2 k => exact lieCompIdx_excTwisted ⟨_, hv⟩ p hp hp2 hpc trivial
  | reeF4 k => exact lieCompIdx_excTwisted ⟨_, hv⟩ p hp hp2 hpc trivial
  | tits => exact lieCompIdx_excTwisted ⟨_, hv⟩ p hp hp2 hpc trivial

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
