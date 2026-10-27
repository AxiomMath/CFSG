module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8S12Weak
public import Certificates.Data.GH74.Ivk8Weak
public import CFSG.Certificates.Kernel.ThDemp.OrbCent
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55MN1
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55MNoP
public import Certificates.Certificate5253
public import CFSG.Sporadic.Schreier.MathieuOddCoreM12
public import CFSG.Sporadic.Schreier.PairJ2Cert
public import CFSG.Sporadic.Schreier.PairJ3Cert

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu
  CFSG.Sporadic.Th CFSG.Sporadic.Th.Native

theorem noN1_M12
    {Y : Type} [Group Y] (hY : NativeSporadic.IsSporadic Y .M12) {p : ℕ} {b : MulAut Y}
    {R₀ : Subgroup Y} : ¬ N1Config Y p b R₀ := by
  obtain ⟨e⟩ := hY
  exact noN1_of_noP (e : Y ≃* ↥NativeSporadic.M12) m12_center_eq_bot' m12_mulAut_card (k := 6)
    (by rw [m12_card]; norm_num) (by rw [m12_card]; norm_num) Certificates.certificate5253.1

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
