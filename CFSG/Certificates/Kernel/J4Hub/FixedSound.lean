module

public import CFSG.Certificates.Kernel.Fam.CentSound
import all CFSG.Certificates.Kernel.Spor.OrdSound

public section

namespace CFSG.KS.J4Hub

open CFSG.KC.Ord CFSG.KS.Ord Matrix

variable {p d w S T L H CM RM ONE LV HV nb : Nat}

private theorem andT_fb {a b : Bool} (h : andB a b = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all [andB]

theorem fixed_sound' (hc : constsOK p w S d T L H CM RM ONE LV HV = true) (hnb : nb = d * S)
    {RB : Nat → Nat} {nreg v r : Nat} (hr : validM p nb L H (RB r) = true)
    (h : CFSG.KC.Fam.fixedOK RB (vecR p w S d T LV HV RM) (validM p S LV HV) nreg v r = true) :
    ordVec p d w v ᵥ* ordMat p d w S (RB r) = ordVec p d w v := by
  obtain ⟨-, h⟩ := andT_fb h
  obtain ⟨hv, h⟩ := andT_fb h
  have hvc := validV_canon hc hv
  have hRc : Canon p d w (RB r) := by
    subst hnb
    exact validM_canon hc hr
  obtain ⟨-, e⟩ := CFSG.KC.LQT.SecS.vecR_sound hc hvc hRc
  have h' : vecR p w S d T LV HV RM v (RB r) = v := Nat.eq_of_beq_eq_true h
  rw [h'] at e
  exact e.symm

theorem basis_sound' (hc : constsOK p w S d T L H CM RM ONE LV HV = true) (hnb : nb = d * S)
    {V : Nat → Nat} {Ri : Nat}
    (h : CFSG.KC.Fam.rowsBasis V (mulR p w S d T L H CM RM) (validM p nb L H) (validM p S LV HV) S d
      ONE Ri = true) (M : Matrix (Fin d) (Fin d) (ZMod p))
    (hM : ∀ k < d, ordVec p d w (V k) ᵥ* M = ordVec p d w (V k)) : M = 1 := by
  obtain ⟨-, hR⟩ := CFSG.KS.Cent.rowsBasis_sound' hc hnb h
  set R : Matrix (Fin d) (Fin d) (ZMod p) :=
    Matrix.of (fun i j : Fin d => CFSG.KC.LQT.SecS.toVec p d w (V i.val) j) with hRdef
  have hRM : R * M = R := by
    funext i j
    have := congrFun (hM i.val i.isLt) j
    simpa [hRdef, Matrix.mul_apply, Matrix.vecMul, dotProduct, ordVec, CFSG.KC.LQT.SecS.toVec,
      CFSG.KS.Ord.lane] using this
  have hL : ordMat p d w S Ri * R = 1 := mul_eq_one_comm.1 hR
  calc M = (ordMat p d w S Ri * R) * M := by rw [hL, Matrix.one_mul]
    _ = ordMat p d w S Ri * (R * M) := by rw [Matrix.mul_assoc]
    _ = 1 := by rw [hRM, hL]

end CFSG.KS.J4Hub

end
