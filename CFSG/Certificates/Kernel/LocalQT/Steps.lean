module

public import Init

public section

namespace CFSG.KC.LQT

def StepsTo (f : Nat → Bool) (N : Nat) : Prop := ∀ n, 3 ≤ n → n < N → f n = true

theorem steps_three (f : Nat → Bool) : StepsTo f 3 := fun _ h h' => absurd h' (by omega)

theorem steps_succ (f : Nat → Bool) (N : Nat) (h : StepsTo f N) (hN : f N = true) :
    StepsTo f (Nat.succ N) := fun n h3 hn => by
  rcases Nat.lt_succ_iff_lt_or_eq.1 hn with hn | rfl
  · exact h n h3 hn
  · exact hN

end CFSG.KC.LQT

end
