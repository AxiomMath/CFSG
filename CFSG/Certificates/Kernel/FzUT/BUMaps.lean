module

public import CFSG.Certificates.Kernel.FzUT.Codes
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL319Spec
public import Certificates.Data.Kernel.FzUT.BU

public section

namespace CFSG.KC.FzUT

open CFSG.OddStandard.SmallF3.FritzII

theorem rhoBP_eq : ∀ x : FzUT, rhoBP (enc x) = enc (fzRho0 (fzRho0 x)) := by decide +kernel

theorem eW_eq : fzEW = fzRho0 (fzRho0 fzE1) := by decide +kernel

theorem fW_eq : fzFW = fzRho0 (fzRho0 fzF1) := by decide +kernel

theorem enc_e1 : enc fzE1 = 1 := by decide +kernel

theorem enc_eW : enc fzEW = 2 := by decide +kernel

theorem enc_f1 : enc fzF1 = 4 := by decide +kernel

theorem enc_fW : enc fzFW = 8 := by decide +kernel

theorem cfP_of_comm (σ : MulAut FzUT)
    (h : ∀ x, σ (fzRho0 (fzRho0 x)) = fzRho0 (fzRho0 (σ x))) (x : FzUT) :
    enc (σ x) = cfP (enc (σ fzE1)) (enc (σ fzF1)) (enc x) := by
  have e := hom_evN σ.toMonoidHom x
  simp only [MulEquiv.coe_toMonoidHom] at e
  rw [e, eW_eq, fW_eq, h, h, ← rhoBP_eq, ← rhoBP_eq]
  rfl

theorem yfP_of_inv (σ : MulAut FzUT)
    (h : ∀ x, σ (fzRho0 (fzRho0 x)) = fzRho0 (fzRho0 (fzRho0 (fzRho0 (σ x))))) (x : FzUT) :
    enc (σ x) = yfP (enc (σ fzE1)) (enc (σ fzF1)) (enc x) := by
  have e := hom_evN σ.toMonoidHom x
  simp only [MulEquiv.coe_toMonoidHom] at e
  rw [e, eW_eq, fW_eq, h, h, ← rhoBP_eq, ← rhoBP_eq, ← rhoBP_eq, ← rhoBP_eq]
  rfl

end CFSG.KC.FzUT
