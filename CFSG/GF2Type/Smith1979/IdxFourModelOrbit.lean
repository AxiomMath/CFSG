
module

public import CFSG.GF2Type.Smith1979.IdxFourModelOrbitBase

public import CFSG.GF2Type.Smith1979.IdxFourModelBasic
public import Certificates.Certificate17603

public section

namespace CFSG.GF2Type.Smith1979.IdxFour

open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA
open CFSG.GF2Type.Smith1979.GammaU.Viol CFSG.GF2Type.Smith1979.GammaU.Enum
open CFSG.GF2Type.Smith1979.IdxFour.Orb

theorem inO378_invariant {U : V12 ≃ₗ[ZMod 2] V12} (hU : U ∈ M0)
    {v : V12} (hv : inO378 v) : inO378 (U v) :=
  Certificates.certificate17603.1 U hU v hv

theorem inO1701_invariant {U : V12 ≃ₗ[ZMod 2] V12} (hU : U ∈ M0)
    {v : V12} (hv : inO1701 v) : inO1701 (U v) :=
  Certificates.certificate17603.2.1 U hU v hv

theorem inO378_trans_E0 {v w : V12} (hv : inO378 v)
    (hw : inO378 w) : ∃ U ∈ E0, U v = w :=
  exists_E0_of_images (Certificates.certificate17603.2.2.1 v hv)
    (Certificates.certificate17603.2.2.1 w hw)

theorem inO1701_trans_E0 {v w : V12} (hv : inO1701 v)
    (hw : inO1701 w) : ∃ U ∈ E0, U v = w :=
  exists_E0_of_images (Certificates.certificate17603.2.2.2 v hv)
    (Certificates.certificate17603.2.2.2 w hw)

theorem inO378_trans {v w : V12} (hv : inO378 v) (hw : inO378 w) :
    ∃ U ∈ M0, U v = w := by
  obtain ⟨U, hU, h⟩ := inO378_trans_E0 hv hw
  exact ⟨U, E0_le_M0 hU, h⟩

theorem inO1701_trans {v w : V12} (hv : inO1701 v)
    (hw : inO1701 w) : ∃ U ∈ M0, U v = w := by
  obtain ⟨U, hU, h⟩ := inO1701_trans_E0 hv hw
  exact ⟨U, E0_le_M0 hU, h⟩

end CFSG.GF2Type.Smith1979.IdxFour
