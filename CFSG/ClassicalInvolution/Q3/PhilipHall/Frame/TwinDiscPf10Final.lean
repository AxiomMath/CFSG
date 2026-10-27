module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf10U5
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf6Q8
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf10U4
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf9N

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Uniform

namespace TwinDisc

structure TwinDiscInputsPf10 (n : ℕ) : Prop where
  thmE : TwinThmE n
  base : TwinDiscBase n
  normCent : DiscNormCent n
  zt : DiscZT n
  thm4 : Thm4RTwinBelow 3 n
  cit : CIT3Below n
  pkg : TL4.TightBelowRPlus 3 n
  exit : DStarExitQ8 n

theorem TwinDiscInputsPf10.toPf6 {n : ℕ} (I : TwinDiscInputsPf10 n) : TwinDiscInputsPf6 n where
  thmE := I.thmE
  base := I.base
  c13Exc := fun Y _ _ R S t₀ K K' z u J t W s _ =>
    disc13N_of_thm4 I.base I.thm4 (dstarConnectedTwinQ8Below_of_exit I.cit I.pkg I.exit)
      Y R S t₀ K K' z u J t W s
  c14Exc := fun Y _ _ R S t₀ K K' z u J t W s _ =>
    disc14N_of_zt I.base I.thm4 I.zt Y R S t₀ K K' z u J t W s
  c14AltExc := disc14AltExc_of_zt I.base I.thm4 I.zt I.normCent
    (discTqTz_of_conn I.base
      (discSecConnTz_of I.thm4 (dstarConnectedTwinQ8Below_of_exit I.cit I.pkg I.exit)))
  normCent := I.normCent
  thm4 := I.thm4
  cit := I.cit
  pkg := I.pkg
  exit := I.exit

end TwinDisc

theorem twinCoreDiscPerp_of_inputsPf10 {n : ℕ} (I : TwinDisc.TwinDiscInputsPf10 n) :
    TwinCoreDiscPerp n :=
  twinCoreDiscPerp_of_inputsPf5 I.toPf6.toPf5

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
