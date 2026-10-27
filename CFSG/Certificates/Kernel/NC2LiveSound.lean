module

public import Certificates.Data.Kernel.NC2L

public section

namespace CFSG.KC.NC2L

open CFSG.KC.LQT CFSG.KC.OpsLayK CFSG.SectionRank.Native

variable {c : Lay} {P : Nat → Prop}

private theorem strictN_eq (y : Nat) (k : Nat → Nat) : CFSG.KC.Loop.strictN y k = k y := by
  cases y <;> rfl

private theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

private theorem eq_of_eqL : ∀ {a b : List Nat}, eqL a b = true → a = b
  | [], [], _ => rfl
  | x :: xs, y :: ys, h => by
    simp only [eqL, Bool.and_eq_true] at h
    rw [Nat.eq_of_beq_eq_true h.1, eq_of_eqL h.2]
  | [], _ :: _, h => by simp [eqL] at h
  | _ :: _, [], h => by simp [eqL] at h

theorem powN_mem (hone : P c.ONE) (hmul : ∀ x y, P x → P y → P (c.mul x y)) :
    ∀ (f X e : Nat), P X → P (powN c f X e) := by
  intro f
  induction f with
  | zero => intro X e _; exact hone
  | succ f ih =>
    intro X e hX
    have hY := ih (c.mul X X) (Nat.div e 2) (hmul _ _ hX hX)
    change P (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat)
      (CFSG.KC.Loop.strictN (c.mul X X) fun X2 =>
        CFSG.KC.Loop.strictN (powN c f X2 (Nat.div e 2)) fun Y =>
          Bool.rec (motive := fun _ => Nat) Y (c.mul X Y) (Nat.beq (Nat.mod e 2) 1))
      X (Nat.beq e 1)) c.ONE (Nat.beq e 0))
    rw [strictN_eq, strictN_eq]
    cases Nat.beq e 0 <;> cases Nat.beq e 1 <;> cases Nat.beq (Nat.mod e 2) 1 <;>
      first | exact hone | exact hX | exact hY | exact hmul _ _ hX hY

theorem getD_mem {d : Nat} (hd : P d) : ∀ (R : List Nat) (i : Nat), (∀ x ∈ R, P x) →
    P (R.getD i d)
  | [], _, _ => by simpa using hd
  | a :: _, 0, h => by simpa using h a List.mem_cons_self
  | _ :: l, i + 1, h => by
    simpa using getD_mem hd l i fun x hx => h x (List.mem_cons_of_mem _ hx)

theorem stepV_mem (hone : P c.ONE) (hmul : ∀ x y, P x → P y → P (c.mul x y)) {R : List Nat}
    (hR : ∀ x ∈ R, P x) : ∀ o : Op, P (stepV c R o)
  | .mul i j _ => hmul _ _ (getD_mem hone R i hR) (getD_mem hone R j hR)
  | .pow e i _ => powN_mem hone hmul 17 _ e (getD_mem hone R i hR)

theorem runC_mem (hone : P c.ONE) (hmul : ∀ x y, P x → P y → P (c.mul x y)) :
    ∀ (prog : List Op) (R : List Nat) (k : List Nat → Bool), runC c prog R k = true →
      (∀ x ∈ R, P x) → ∃ R', k R' = true ∧ ∀ x ∈ R', P x
  | [], R, _, h, hR => ⟨R, h, hR⟩
  | o :: prog, R, k, h, hR => by
    change strictB (stepV c R o) (fun v => runC c prog (R.set (Op.tgt o) v) k) = true at h
    rw [strictB_eq] at h
    refine runC_mem hone hmul prog _ k h fun x hx => ?_
    rcases List.mem_or_eq_of_mem_set hx with hx | hx
    · exact hR x hx
    · rw [hx]
      exact stepV_mem hone hmul hR o

theorem liveL_mem (hone : P c.ONE) (hmul : ∀ x y, P x → P y → P (c.mul x y)) {C : LiveChunk}
    {R S : List Nat} (h : liveL c C R S = true) (hR : ∀ x ∈ R, P x) : ∀ x ∈ S, P x := by
  have hpad : ∀ x ∈ padR c R C.n, P x := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hR x hx
    · rw [List.eq_of_mem_replicate hx]
      exact hone
  obtain ⟨R', hk, hR'⟩ := runC_mem hone hmul C.prog _ _ h hpad
  rw [← eq_of_eqL hk]
  intro x hx
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
  exact getD_mem hone R' i hR'

theorem liveL_chain (hone : P c.ONE) (hmul : ∀ x y, P x → P y → P (c.mul x y))
    {C : Nat → LiveChunk} {S : Nat → List Nat} {m : Nat} (h0 : ∀ x ∈ S 0, P x)
    (hch : ∀ i < m, liveL c (C i) (S i) (S (i + 1)) = true) : ∀ x ∈ S m, P x := by
  induction m with
  | zero => exact h0
  | succ m ih =>
    exact liveL_mem hone hmul (hch m (Nat.lt_succ_self m))
      (ih fun i hi => hch i (Nat.lt_succ_of_lt hi))

end CFSG.KC.NC2L

end
