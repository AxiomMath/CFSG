module

public import CFSG.CGT.PushingUpLit.CGT6.Diag.Defs
public import CFSG.CGT.PushingUpLit.CGT6.Diag.BoundBasic

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG.Quasithin

theorem diagBoundSL_holds : DiagBoundSL := by
  intro V _ _ hV Y n hn hnat y hy hodd
  obtain ⟨-, θ, β, -, hβk, -⟩ := hnat
  have h := Diag.Bound.card_commV_zpowers_le hV hy hodd (inf_le_right) β hβk
  rw [card_sl_model (by omega)] at h
  exact h

end CFSG.CGT.PushingUpLit.CGT6
