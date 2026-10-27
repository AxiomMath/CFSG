module

public import CFSG.CGT.A8S.L2FD
public import CFSG.CGT.A8S.L2GModel
public import CFSG.CGT.A8S.L2FA
public import CFSG.CGT.A8S.L2FB
public import CFSG.CGT.A8S.L2FC2

public section

namespace CFSG.CGT.A8S.L2

open CFSG.CosetTable CFSG.CGT.A8S.N0

@[expose] noncomputable def l2ModelA8 :
    T1ModelA8 (PG 5 relsN0A8) where
  T0 := T0
  B0 := B0
  b0 := b0
  d := dE
  theta := thE
  alpha := alphaA8
  tau := tGenA8 2
  beta := beta1
  b0_mem := Subgroup.subset_closure (by simp)
  d_mem := dE_mem
  theta_mem := thE_mem
  alpha_T := mem_T0_iff_alpha
  alpha_alpha := alphaA8_alphaA8
  inv_class := inv_classA8
  klein_eq := klein_eqA8
  swap := swapA8
  center := centerA8
  theta_sq := ⟨wTh, theta_wordsA8⟩
  tau_mem := Subgroup.subset_closure ⟨2, rfl⟩
  tau_not := tau_not_mem
  beta_mem := Subgroup.subset_closure (by simp)
  beta_ne := beta1_ne
  comm_mem := by
    change commTB ∈ T0
    rw [commTB_eq]
    exact Subgroup.subset_closure ⟨1, rfl⟩
  comm_norm := commTB_mem_D0
  comm_ne := commTB_ne
  sig_beta := sig_beta1
  sig_comm := sig_commTB
  sig_fix := sig_fix

end CFSG.CGT.A8S.L2
