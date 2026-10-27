module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8S12Norm
public import Certificates.Certificate5244

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu
  CFSG.Sporadic.Th CFSG.Sporadic.Th.Native

theorem not_sylCfgOf_M12
    {Y : Type} [Group Y] (hY : NativeSporadic.IsSporadic Y .M12) : ¬ SylCfgOf Y := by
  obtain ⟨e⟩ := hY
  exact not_sylCfgOf_of_noThree NativeSporadic.M12 (m := 1485) (by rw [m12_card]; norm_num) (by decide)
    Certificates.certificate5244 e m12_center_eq_bot' m12_mulAut_card

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
