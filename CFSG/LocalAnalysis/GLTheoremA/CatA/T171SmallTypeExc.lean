module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171SmallTypeExcF4
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171SmallTypeExcTE6
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171SmallTypeExcE678
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171SmallTypeExcD4
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171SmallTypeExcTits

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171S

open CFSG.Open


theorem excNoSmall_holds : ExcNoSmall := by
  intro d hd
  obtain ⟨i, hv⟩ := d
  cases i with
  | E6 q => exact noSmall_lie_E6 q hv hd
  | E7 q => exact noSmall_lie_E7 q hv hd
  | E8 q => exact noSmall_lie_E8 q hv hd
  | F4 q => exact noSmall_lie_F4 q hv hd
  | twistedE6 q => exact noSmall_lie_twistedE6 q hv hd
  | trialityD4 q => exact noSmall_lie_trialityD4 q hv hd
  | tits => exact noSmall_lie_tits hv
  | A n q => exact hd.elim
  | twistedA n q => exact hd.elim
  | B n q => exact hd.elim
  | C n q => exact hd.elim
  | D n q => exact hd.elim
  | twistedD n q => exact hd.elim
  | G2 q => exact hd.elim
  | suzuki m => exact hd.elim
  | reeG2 a => exact hd.elim
  | reeF4 m => exact hd.elim

end CFSG.LocalAnalysis.GLTheoremA.T171S

end
