module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8L1Uni
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8L1U3Rank
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8L1FourU3
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8L1CardU3

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.L1

open CFSG.GH74.GLS.Stage2.Signalizer.Odd87

theorem cellAbs_FU3 : CellAbs FU3 :=
  cellAbs_of_uniform (fun _ _ _ hY => fu3_elemAbelian_le_eight hY)
    (fun _ _ _ hY => exists_four_of_FU3 hY) (fun _ _ _ hY => not_card_sq_dvd_factorial_of_FU3 hY)

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.L1
