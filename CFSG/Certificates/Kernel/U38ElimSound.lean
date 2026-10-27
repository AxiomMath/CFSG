module

public import Certificates.Data.Kernel.U38ElimK

public section

namespace CFSG.KC.U38Elim

theorem eAll_iff (f : Nat → Bool) : ∀ L : List Nat, eAll f L = true ↔ ∀ x ∈ L, f x = true
  | [] => ⟨fun _ x hx => absurd hx List.not_mem_nil, fun _ => rfl⟩
  | x :: L => by
    have e : eAll f (x :: L) = (f x && eAll f L) := by
      change Bool.rec (motive := fun _ => Bool) false (eAll f L) (f x) = _
      cases f x <;> rfl
    rw [e, Bool.and_eq_true, eAll_iff f L, List.forall_mem_cons]

theorem eAny_iff (f : Nat → Bool) : ∀ L : List Nat, eAny f L = true ↔ ∃ x ∈ L, f x = true
  | [] => ⟨fun h => absurd h Bool.false_ne_true, fun ⟨_, hx, _⟩ => absurd hx List.not_mem_nil⟩
  | x :: L => by
    have e : eAny f (x :: L) = (f x || eAny f L) := by
      change Bool.rec (motive := fun _ => Bool) (eAny f L) true (f x) = _
      cases f x <;> rfl
    rw [e, Bool.or_eq_true, eAny_iff f L]
    simp

theorem eAnyN_iff (f : Nat → Bool) : ∀ n : Nat, eAnyN n f = true ↔ ∃ i < n, f i = true
  | 0 => ⟨fun h => absurd h Bool.false_ne_true, fun ⟨_, hi, _⟩ => absurd hi (Nat.not_lt_zero _)⟩
  | n + 1 => by
    have e : eAnyN (n + 1) f = (f n || eAnyN n f) := by
      change Bool.rec (motive := fun _ => Bool) (eAnyN n f) true (f n) = _
      cases f n <;> rfl
    rw [e, Bool.or_eq_true, eAnyN_iff f n]
    constructor
    · rintro (h | ⟨i, hi, h⟩)
      · exact ⟨n, Nat.lt_succ_self n, h⟩
      · exact ⟨i, Nat.lt_succ_of_lt hi, h⟩
    · rintro ⟨i, hi, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact Or.inr ⟨i, hi, h⟩
      · exact Or.inl h

theorem eMem_iff (x : Nat) (L : List Nat) : eMem x L = true ↔ x ∈ L := by
  unfold eMem
  rw [eAny_iff]
  constructor
  · rintro ⟨y, hy, h⟩
    rwa [← Nat.eq_of_beq_eq_true h]
  · intro h
    exact ⟨x, h, Nat.beq_refl x⟩

theorem eBit_eq (M x : Nat) : eBit M x = M.testBit x := by
  unfold eBit
  rw [Nat.testBit_eq_decide_div_mod_eq, ← Nat.shiftRight_eq_div_pow]
  change Nat.beq ((M >>> x) &&& 1) 1 = _
  rw [Nat.and_one_is_mod]
  apply Bool.eq_iff_iff.2
  rw [decide_eq_true_iff]
  exact ⟨Nat.eq_of_beq_eq_true, fun h => h ▸ Nat.beq_refl 1⟩

theorem eBit_land (a b x : Nat) : eBit (a &&& b) x = (eBit a x && eBit b x) := by
  rw [eBit_eq, eBit_eq, eBit_eq, Nat.testBit_and]

end CFSG.KC.U38Elim

end
