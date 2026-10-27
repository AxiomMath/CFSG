module

public import Certificates.Data.Kernel.GH74Tab.Pos
public import CFSG.Certificates.Kernel.GH74Tab.Transport
public import CFSG.GH74.GLS.C3.Layer2.L4ModelGen
public import CFSG.GH74.GLS.C3.Prop121.FinPosCheckInputs

public section

namespace CFSG.KC.GH74Tab

open CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model

theorem claimPosB_eq {n : ℕ} [NeZero n] (t : Tab n) : t.claimPosB = t.claimG (posP t) := rfl

theorem posOK_sound {n : ℕ} [NeZero n] {D : Dat} {S2 : Nat} {L : List (Nat × Nat)}
    (ht : transOK D n = true) (hs : s2OK n S2 = true) (hp : posOK D S2 L = true)
    {p : Nat × Nat} (hpL : p ∈ L) (u : Fin 64) : posP (mkTab n) (tblOf p.1) u = true := by
  simp only [posP, List.all_eq_true, List.mem_finRange, true_implies, imp_eq_true]
  intro i hq
  simp only [s2OK, List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at hs
  simp only [posOK, List.all_eq_true, r64, List.mem_range, Bool.or_eq_true,
    Bool.not_eq_true'] at hp
  rw [isQ_eq D ht] at hq
  have h1 := hp p hpL i i.isLt
  rw [hq] at h1
  simp only [Bool.true_eq_false, false_or] at h1
  rw [tblOf, vget_ofFn, hs]
  simpa only [f64, g6, Nat.mod_mod] using h1

end CFSG.KC.GH74Tab

end
