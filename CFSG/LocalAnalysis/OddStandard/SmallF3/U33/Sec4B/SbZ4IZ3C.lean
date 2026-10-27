module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4IZ3B
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4IZ3E

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped commutatorElement

variable {H : Type} [Group H] [Finite H]

namespace ZEData

variable {Q Y V V' B K : Subgroup H} {ρ t τ l : H}

theorem Qf_Vc (h : ZEData Q Y V V' B K ρ t τ l) : z4iQf (z4iVc K t τ l) = Q := by
  have hV : z4iVf (z4iVc K t τ l) = V := h.D_comm_eq_V
  have hF : z4iFf (z4iVc K t τ l) = z4iF K t τ := by
    unfold z4iFf
    rw [hV]
    exact h.Vc_inf_cent_V
  have hC : z4iVc K t τ l ⊓ centralizer ((z4iD (z4iVc K t τ l) : Subgroup H) : Set H) = Y :=
    h.Vc_inf_cent_D
  unfold z4iQf
  rw [hF, hC]
  exact h.F_comm_sup_Y

end ZEData

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
