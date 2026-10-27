module

public import CFSG.Certificates.Kernel.Spor.ONVecLib

public section

namespace CFSG.KC.D43

open CFSG.KS CFSG.KS.ON CFSG.F3.Native CFSG.Sporadic.Fi23.Native CFSG.Sporadic.ON.Native

theorem combW_trunc (Y : Array W) {r : V} {e : Nat} (hr : VB e r) :
    ∀ {d : Nat}, e ≤ d → d ≤ 256 → combW d Y (ofV r) = combW e Y (ofV r)
  | 0, h1, _ => by
    have : e = 0 := by omega
    subst this
    rfl
  | d + 1, h1, h2 => by
    rcases Nat.lt_or_ge d e with h | h
    · have : e = d + 1 := by omega
      subst this
      rfl
    · have ih := combW_trunc Y hr (d := d) h (by omega)
      unfold combW at ih ⊢
      rw [Nat.fold_succ, ih, (bit_ofV r (by omega : d < 256)).1, (bit_ofV r (by omega : d < 256)).2,
        (hr d h).1, (hr d h).2]
      simp

theorem mulVecT_mv {M : Array W} {L : List Nat} (hl : L.length = 84)
    (hc : ∀ j < 84, M[j]! = ofV (vOf (L.getD j 0)) ∧ canon (L.getD j 0) = true) {X : Nat}
    (hX : VB 84 (vOf X)) : mulVecT M (ofV (vOf X)) = ofV (vOf (mv L X)) := by
  rw [mulVecT, combW_trunc M hX (by omega) (by omega),
    vOf_mv (by rw [hl]; exact fun j hj => (hc j hj).2), hl]
  exact combW_ofV _ (by omega) fun j hj => by rw [map_vOf_get (by omega), (hc j hj).1]

end CFSG.KC.D43

end
