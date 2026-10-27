module

public import Certificates.Data.Kernel.A45Cls.Outer

public section

namespace CFSG.KC.A45Cls

open CFSG.KC.Enum CFSG.KS

theorem anyL_spec {f : Nat → Bool} : ∀ {L : List Nat}, anyL L f = true → ∃ x ∈ L, f x = true
  | [], h => absurd h Bool.false_ne_true
  | x :: L, h => by
    change Bool.rec (motive := fun _ => Bool) (anyL L f) true (f x) = true at h
    cases hx : f x
    · rw [hx] at h
      obtain ⟨y, hy, e⟩ := anyL_spec h
      exact ⟨y, List.mem_cons_of_mem _ hy, e⟩
    · exact ⟨x, List.mem_cons_self, hx⟩

theorem anyL_of {f : Nat → Bool} {x : Nat} (hf : f x = true) :
    ∀ {L : List Nat}, x ∈ L → anyL L f = true
  | [], h => absurd h List.not_mem_nil
  | y :: L, h => by
    change Bool.rec (motive := fun _ => Bool) (anyL L f) true (f y) = true
    rcases List.mem_cons.1 h with rfl | h
    · rw [hf]
    · cases f y
      · exact anyL_of hf h
      · rfl

theorem allL_of {f : Nat → Bool} : ∀ {L : List Nat}, (∀ x ∈ L, f x = true) → allL L f = true
  | [], _ => rfl
  | y :: L, h => by
    change Bool.rec (motive := fun _ => Bool) false (allL L f) (f y) = true
    rw [h y List.mem_cons_self]
    exact allL_of fun x hx => h x (List.mem_cons_of_mem _ hx)

theorem allNL_spec {f : Nat → Bool} : ∀ {N : Nat}, allNL N f = true → ∀ i < N, f i = true
  | 0, _ => fun _ h => absurd h (Nat.not_lt_zero _)
  | N + 1, h => by
    change Bool.rec (motive := fun _ => Bool) false (allNL N f) (f N) = true at h
    cases hN : f N
    · rw [hN] at h
      exact absurd h Bool.false_ne_true
    · rw [hN] at h
      intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact allNL_spec h i hi
      · exact hN

theorem outL_spec {N : Nat} {T : Nat → Nat} {BL : List Nat} (h : outL N T BL = true) {i : Nat}
    (hi : i < N) (hn : nrmInvL (T i) BL = true) : witL (T i) BL = true := by
  have := allNL_spec h i hi
  rw [hn] at this
  exact this

end CFSG.KC.A45Cls

end
