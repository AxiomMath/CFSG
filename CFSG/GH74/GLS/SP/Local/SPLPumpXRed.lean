module

public import CFSG.GH74.GLS.SP.Local.SPLPumpX
public import CFSG.GH74.GLS.SP.Local.SPLStdCt
public import CFSG.GH74.GLS.SP.Local.SPLPumpXOrd

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.BNPair
open CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS.SP
open scoped commutatorElement

theorem splInPumpStd_of_X (hX : SPLPumpX) : SPLInPumpStd := by
  intro G _ _ hS D hs hset
  have hct := splCt0 D hs
  obtain ⟨T₁, hT₁le, hT₁p, hT₁max, hT₁dih⟩ := hct.T₁ex
  have hq5 := hs.q_ge
  have hz2 : orderOf D.z = 2 := hs.syl.z_inv
  have ht2 : orderOf D.t = 2 := hs.syl.t_ord
  have hn : 1 ≤ D.n := by
    unfold SPLNot0.n
    omega
  have hT₁card : Nat.card ↥T₁ = 2 ^ (D.n - 1) := CtW.card_of_isDihedralOrder hT₁dih
  refine hX G hS.kps D.q D.z D.t D.Ict D.F₀ ?_
  refine
    { odd_q := ?_
      q_ge := hq5
      gen4 := hS.gen4
      comp := fun L hL => hS.lb2.1 D.t ht2 L hL
      z_ord := hz2
      t_ord := ht2
      zt_comm := (hs.syl.comm_z hs.syl.t_mem).symm
      z_ne_t := fun h => hs.syl.t_nconj (h ▸ IsConj.refl _)
      cen := hct.CCt
      I_L2 := hct.I_L2
      I_perf := hct.I_perf
      F₀_norm := hct.F₀_norm
      F₀_inf := hct.F₀_inf
      F₀_faith := hct.F₀_faith
      F₀_odd := hct.F₀_odd
      O2 := hct.O2
      T₁ex := ⟨T₁, hT₁le.trans inf_le_left, hT₁p, ?_, ?_⟩ }
  · obtain ⟨k, hk, hqk⟩ := hs.q_pow
    rw [hqk]
    exact (hs.prime.eq_two_or_odd'.resolve_left hs.p_ne_two).pow
  · intro P hP hPI hT
    exact hT₁max P hP hPI hT
  · intro P hP hPt
    have h1 := sp_card_two_subgroup_le hs hP hPt
    rw [hT₁card, ← pow_mul]
    have : 2 * 2 ^ ((D.n - 1) * 2) = 2 ^ (2 * D.n - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    omega

theorem sp_compat_Std_of_X
    (hM : SPModelLeaf) (h11 : IVK.Proofs2.IVK_11_1b_nat) (hX : SPLPumpX) :
    S_stage5_SP_compat_Std :=
  sp_compat_Std_of_K1Std hM h11 (splInPumpStd_of_X hX)

end CFSG.GH74.GLS.SP.Local
