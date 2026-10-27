module

public import CFSG.CGT.Foote81L6.Bridge.Centralizer

public section

namespace CFSG.CGT.Foote81L6.Bridge

open Subgroup

variable {n : ℕ}

@[expose] noncomputable def footeCoreModel (hn : 3 ≤ n) : FooteCore (TM n) ⊤ (n - 1) n where
  A := AT hn
  B := BT hn
  B₀ := B₀T hn
  B₁ := B₁T hn
  t := tT n
  s := sT n
  a := aT n
  b₀ := b₀T hn
  b₁ := b₁T hn
  T_eq := top_eq hn
  A_inf_B := AT_inf_BT hn
  A_comm_B := AT_comm_BT hn
  conj_t_A := conj_tT_AT hn
  conj_t_B := conj_tT_BT hn
  t_sq := by rw [pow_two, tT_mul_tT hn]
  two_le_m := by omega
  A_iso := by
    rw [show n - 1 - 1 = n - 2 by omega]
    exact ⟨(MonoidHom.ofInjective (fA_injective hn)).symm⟩
  At_iso := by
    rw [AT_sup_tT hn]
    exact ⟨(MonoidHom.ofInjective (fAt_injective hn)).symm⟩
  B_eq := rfl
  B₀_inf_B₁ := B₀T_inf_B₁T hn
  B₀_comm_B₁ := B₀T_comm_B₁T hn
  m_lt_n := by omega
  B₀_iso := ⟨(MonoidHom.ofInjective (f₀_injective hn)).symm⟩
  B₁_iso := ⟨(MonoidHom.ofInjective (f₁_injective hn)).symm⟩
  s_sq := by rw [pow_two, sT_mul_sT hn]
  conj_s_B₀ := map_conj_sT_B₀T hn
  Bt_conj := Bt_conj hn
  CBt_iso := CBt_iso hn
  a_mem := aT_mem_AT hn
  a_order := orderOf_aT hn
  a_comm := aT_comm hn
  b₀_mem := b₀T_mem hn
  b₀_order := orderOf_b₀T hn
  b₀_comm := b₀T_comm hn
  b₁_mem := b₁T_mem hn
  b₁_order := orderOf_b₁T hn
  b₁_comm := b₁T_comm hn

end CFSG.CGT.Foote81L6.Bridge
