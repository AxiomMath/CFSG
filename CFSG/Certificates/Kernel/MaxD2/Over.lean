module

public import CFSG.Certificates.Kernel.MaxD2.Max
public import Certificates.Data.OverD2Perm

public section

namespace CFSG.KS.MaxD2

open CFSG.PSL3Four.Native Certificates.MaxD2Perm

theorem checkMaximal_of {D : Data} {K : Pk} (H : HypsM D K) :
    Certificates.OverD2Perm.checkMaximal D = true := by
  unfold Certificates.OverD2Perm.checkMaximal
  rw [checkInv_of H, checkN_of H, checkMax_of H]
  have hs : (nGens D).size = K.kN := (ngens H).1
  unfold invsOK
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.true_and, Bool.and_true]
  refine ⟨by simp [nGensI], allBelow_iff'.2 fun k hk => ?_⟩
  rw [hs] at hk
  rw [ngi_get H hk, ng_get H hk, H.hDn, inv_comp (H.hNI k hk)]
  simp [size_u]

end CFSG.KS.MaxD2

end
