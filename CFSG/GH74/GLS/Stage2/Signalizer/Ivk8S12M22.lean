module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8S12Norm
public import CFSG.Sporadic.Schreier.MathieuOddCoreM22
public import Certificates.Certificate5245

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu
  CFSG.Sporadic.Th CFSG.Sporadic.Th.Native

theorem not_sylCfgOf_M22
    {Y : Type} [Group Y] (hY : NativeSporadic.IsSporadic Y .M22) : ¬ SylCfgOf Y := by
  obtain ⟨e⟩ := hY
  exact not_sylCfgOf_of_noThree NativeSporadic.M22 (m := 3465) (by rw [m22_card]; norm_num) (by decide)
    Certificates.certificate5245 e m22_center_eq_bot' m22_mulAut_card

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
