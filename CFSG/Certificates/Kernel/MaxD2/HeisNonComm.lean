module

public import CFSG.Certificates.Kernel.MaxD2.Heis
public import Certificates.Data.MaxD2NonComm

public section

namespace CFSG.KS.MaxD2

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KS.PEnum CFSG.KS.Row CFSG.PSL3Four.Native
open Certificates.MaxD2Perm Certificates.MaxD2Heis

variable {D : Data} {K : Pk} {ZP ZX CZ : Nat → Nat}

theorem checkHNonComm_of (H : HypsH D K ZP ZX CZ) {i j : Nat} (hi : i < K.kN) (hj : j < K.kN)
    (h : notInK K.rcnt K.RT (pcomp K.n K.w (mask K.w) (pcomp K.n K.w (mask K.w)
      (pcomp K.n K.w (mask K.w) (K.NG i) (K.NG j)) (K.NGI i)) (K.NGI j)) = true) :
    checkHNonComm D = true := by
  have HC := H.toHypsBC.toHypsC
  obtain ⟨e, -⟩ := h_rEnum_eq H
  have hs : (nGens D).size = K.kN := (c_ngens HC).1
  unfold checkHNonComm
  simp only []
  rw [e, anyBelow_iff]
  refine ⟨i, by rw [hs]; exact hi, ?_⟩
  rw [anyBelow_iff]
  refine ⟨j, by rw [hs]; exact hj, ?_⟩
  rw [Bool.not_eq_true', Bool.eq_false_iff]
  intro hf
  have pi : Cn K.n K.w (K.NG i) ∧ Cn K.n K.w (K.NGI i) := perm_canon (HC.hNI i hi) HC.hn
  have pj : Cn K.n K.w (K.NG j) ∧ Cn K.n K.w (K.NGI j) := perm_canon (HC.hNI j hj) HC.hn
  rw [c_ng_get HC hi, c_ng_get HC hj, c_ngi_get HC hi, c_ngi_get HC hj, HC.hDn] at hf
  unfold commTab at hf
  rw [comp_u pi.1 pj.1, comp_u (cc pi.1 pj.1) pi.2, comp_u (cc (cc pi.1 pj.1) pi.2) pj.2,
    h_foundR H (cc (cc (cc pi.1 pj.1) pi.2) pj.2)] at hf
  obtain ⟨r, hr, er⟩ := hf
  have hm := (PK.allN_iff.1 h) r hr
  rw [er, Nat.beq_refl] at hm
  exact absurd hm (by decide)

end CFSG.KS.MaxD2

end
