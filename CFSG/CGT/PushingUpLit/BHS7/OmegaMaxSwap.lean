module

public import CFSG.CGT.PushingUpLit.BHS7.OmegaSL
public import CFSG.CGT.PushingUpLit.BHS7.OmegaMaxSwapCore

public section

namespace CFSG.CGT.PushingUpLit.BHS7

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6

variable {Γ : Type} [Group Γ] [Finite Γ] {G T : Subgroup Γ}

theorem omegaMaxSwap_holds (h : MinCex G T) : OmegaMaxSwap G T := by
  intro E hE m hm2 hn
  have hG : CharTwo G := h.charTwo
  have hT : IsSylowOf 2 T G := h.sylow
  have hT2 : IsSylowTwoOf T G := isSylowTwoOf_of_isSylowOf hT
  have hEb : IsBTBlock G T E := omega_isBTBlock h hE
  have hchar : CharTwo E := charTwo_of_isBTBlock hG hT hEb
  have hS : IsSylowTwoOf (T ⊓ E) E := isSylowTwoOf_inf_of_isSubnormal hE.2 hT2
  have hBE : baum T ≤ Subgroup.normalizer (E : Set Γ) := baum_le_normalizer_of_isBTBlock hEb
  have hBT : baum T ≤ T := inf_le_left
  have hB2 : IsPGroup 2 ↥(baum T) := hT2.2.1.to_le hBT
  exact card_autOn_baum_of_isSylowTwoOf hG hT hEb hm2 hn hS fun c hc hcW =>
    exists_pow_two_eq_one_of_centralizes hchar hEb.elemAbelian.1 hB2 hBE hc hcW

end CFSG.CGT.PushingUpLit.BHS7
