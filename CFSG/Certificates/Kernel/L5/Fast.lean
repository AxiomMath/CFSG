module

public import CFSG.Certificates.Kernel.PermCent.CVSound
public import CFSG.GH74.GLS.C3.Layer2.L5C0Inputs

public section

namespace CFSG.Certificates.Kernel.PkCV

instance : Small 16 := ⟨by decide⟩

variable {n : Nat} [Small n]

theorem map_cOf_ev (L : List (Equiv.Perm (Fin n))) : (L.map cOf).map ev = L := by
  rw [List.map_map]
  conv_rhs => rw [← List.map_id L]
  congr 1
  funext σ
  exact ev_cOf σ

theorem closureStep_map_ev (gs l : List (CV n)) :
    CFSG.GH74.GLS.C3.Layer2.Model.closureStep (gs.map ev) (l.map ev) =
      (CFSG.GH74.GLS.C3.Layer2.Model.closureStep gs l).map ev := by
  unfold CFSG.GH74.GLS.C3.Layer2.Model.closureStep
  rw [← dedup_map_ev]
  congr 1
  simp only [List.map_append, List.flatMap_map, List.map_flatMap, List.map_map]
  congr 1
  congr 1
  funext g
  congr 1
  funext h
  simp only [Function.comp_apply, ev_mul]

theorem closureList_map_ev (gs : List (CV n)) (k : Nat) :
    CFSG.GH74.GLS.C3.Layer2.Model.closureList (gs.map ev) k =
      (CFSG.GH74.GLS.C3.Layer2.Model.closureList gs k).map ev := by
  unfold CFSG.GH74.GLS.C3.Layer2.Model.closureList
  induction k with
  | zero => simp [ev_one]
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, closureStep_map_ev]

theorem mulClosedChkP_map_ev (L : List (CV n)) :
    CFSG.GH74.GLS.C3.Layer2.L5.mulClosedChkP (L.map ev) =
      CFSG.GH74.GLS.C3.Layer2.L5.mulClosedChkP L := by
  unfold CFSG.GH74.GLS.C3.Layer2.L5.mulClosedChkP
  simp only [List.all_map, Function.comp_def, ← ev_mul, mem_map_ev]
  congr!

theorem invClosedChkP_map_ev (L : List (CV n)) :
    CFSG.GH74.GLS.C3.Layer2.L5.invClosedChkP (L.map ev) =
      CFSG.GH74.GLS.C3.Layer2.L5.invClosedChkP L := by
  unfold CFSG.GH74.GLS.C3.Layer2.L5.invClosedChkP
  simp only [List.all_map, Function.comp_def, ← ev_inv, mem_map_ev]
  congr!

end CFSG.Certificates.Kernel.PkCV

end
