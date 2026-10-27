module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8S12Weak
public import Certificates.Data.GH74.Ivk8Weak
public import CFSG.Certificates.Kernel.ThDemp.OrbCent
public import CFSG.Sporadic.SmallOddCore.CentSpec
public import Certificates.Data.CFSGNative.SmallOddCore.Check
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55MN1
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55MNoP
public import Certificates.Certificate5253
public import CFSG.Sporadic.Schreier.MathieuOddCoreM23
public import CFSG.Sporadic.Schreier.PairJ2Cert
public import CFSG.Sporadic.Schreier.PairJ3Cert

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu
  CFSG.Sporadic.Th CFSG.Sporadic.Th.Native

theorem noN1_M23
    {Y : Type} [Group Y] (hY : NativeSporadic.IsSporadic Y .M23) {p : ℕ} {b : MulAut Y}
    {R₀ : Subgroup Y} : ¬ N1Config Y p b R₀ := by
  obtain ⟨e⟩ := hY
  exact noN1_of_noP (e : Y ≃* ↥NativeSporadic.M23) m23_center_eq_bot'
    (by have := m23_mulAut_card; omega) (k := 7) (by rw [m23_card]; norm_num)
    (by rw [m23_card]; norm_num) Certificates.certificate5253.2.2.2.1

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
