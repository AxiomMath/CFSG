module

public import Certificates.Certificate17640
public import CFSG.GF2Type.Smith1979.IdxFourModelLemma5Base

public section

namespace CFSG.GF2Type.Smith1979.IdxFour

open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.Viol

theorem orbitC_ncard
    {v : V12} (hv : inO1701 v) (hf : f0 v w0 = 0) :
    64 ≤ Set.ncard {u : V12 | ∃ s ∈ stabIn E0 w0, s v = u} := by
  refine le_trans (Certificates.certificate17640 v hv hf) (Set.ncard_le_ncard ?_ (Set.toFinite _))
  rintro u ⟨U, hU, rfl⟩
  exact ⟨U, genGrp_pGens_le hU, rfl⟩

end CFSG.GF2Type.Smith1979.IdxFour
