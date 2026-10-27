
module

public import Certificates.Data.Kernel.J4FixCE
public import CFSG.Certificates.Kernel.J4FixCSoundBase

public section

namespace CFSG.KC.J4FixCE

open CFSG.KC.J4Q (vecJ)
open CFSG.KC.J4FixC (nth notK bAnd_eq notK_eq)

theorem fixAllJ_spec {rm M : Nat} {L : List Nat} (h : fixAllJ rm M L = true) :
    ∀ p ∈ L, p < 2 ^ 112 ∧ vecJ rm p M = p := by
  induction L with
  | nil => intro p hp; simp at hp
  | cons q t ih =>
    change bAnd(Nat.blt q (Nat.pow 2 112), bAnd(Nat.beq (vecJ rm q M) q, fixAllJ rm M t)) = true
      at h
    rw [bAnd_eq, bAnd_eq, Bool.and_eq_true, Bool.and_eq_true] at h
    intro p hp
    rcases List.mem_cons.1 hp with rfl | hp
    · exact ⟨Nat.le_of_ble_eq_true h.1, Nat.eq_of_beq_eq_true h.2.1⟩
    · exact ih h.2.2 p hp

theorem nodupK_spec {L : List Nat} (h : nodupK L = true) : L.Nodup := by
  induction L with
  | nil => exact List.nodup_nil
  | cons p t ih =>
    change bAnd(List.rec (motive := fun _ => Bool) true
      (fun q _ ih' => bAnd(notK (Nat.beq p q), ih')) t, nodupK t) = true at h
    rw [bAnd_eq, Bool.and_eq_true] at h
    refine List.nodup_cons.2 ⟨fun hp => ?_, ih h.2⟩
    have h1 := h.1
    clear h ih
    induction t with
    | nil => simp at hp
    | cons q t ih2 =>
      change bAnd(notK (Nat.beq p q), _) = true at h1
      rw [bAnd_eq, Bool.and_eq_true, notK_eq, Bool.not_eq_true'] at h1
      rcases List.mem_cons.1 hp with rfl | hp
      · rw [Nat.beq_refl] at h1
        exact Bool.noConfusion h1.1
      · exact ih2 hp h1.2

theorem eqB_spec {x y : Bool} (h : eqB x y = true) : x = y := by
  cases x <;> cases y <;> first | rfl | exact absurd h (by decide)

theorem treeAt_spec {rm : Nat} {GM PT : List Nat} {PAR : List (Nat × Nat)} {i : Nat}
    (h : treeAt rm GM PT PAR i = true) (h0 : i ≠ 0) (h77 : i ≠ 77) :
    (nth (0, 0) PAR i).1 < i ∧ (nth (0, 0) PAR i).2 < 2 ∧
      ((nth (0, 0) PAR i).1 < 77 ↔ i < 77) ∧
      vecJ rm (nth 0 PT (nth (0, 0) PAR i).1) (nth 0 GM (nth (0, 0) PAR i).2) = nth 0 PT i := by
  have e0 : Nat.beq i 0 = false := Bool.eq_false_iff.2 fun e => h0 (Nat.eq_of_beq_eq_true e)
  have e77 : Nat.beq i 77 = false := Bool.eq_false_iff.2 fun e => h77 (Nat.eq_of_beq_eq_true e)
  unfold treeAt at h
  rw [e0, e77] at h
  change Prod.rec (motive := fun _ => Bool) (fun p g => bAnd(Nat.blt p i, bAnd(Nat.blt g 2,
      bAnd(eqB (Nat.blt p 77) (Nat.blt i 77),
        Nat.beq (vecJ rm (nth 0 PT p) (nth 0 GM g)) (nth 0 PT i))))) (nth (0, 0) PAR i) = true at h
  generalize nth (0, 0) PAR i = q at h ⊢
  obtain ⟨p, g⟩ := q
  change bAnd(Nat.blt p i, bAnd(Nat.blt g 2, bAnd(eqB (Nat.blt p 77) (Nat.blt i 77),
    Nat.beq (vecJ rm (nth 0 PT p) (nth 0 GM g)) (nth 0 PT i)))) = true at h
  rw [bAnd_eq, bAnd_eq, bAnd_eq, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  have e3 := eqB_spec h3
  refine ⟨Nat.le_of_ble_eq_true h1, Nat.le_of_ble_eq_true h2, ?_, Nat.eq_of_beq_eq_true h4⟩
  rw [← Nat.blt_eq, ← Nat.blt_eq, e3]

end CFSG.KC.J4FixCE

end
