module

public import Certificates.Data.Kernel.HMathieu.Pred24

public section

namespace CFSG.KC.HMathieu

open CFSG.Quasithin.H.Mathieu CFSG.Quasithin.AppendixH.H14

theorem testBit_foldr_mask (f : Nat → Bool) (k : Nat) : ∀ L : List Nat,
    (L.foldr (fun j acc => if f j then acc ||| 1 <<< j else acc) 0).testBit k =
      L.any fun j => j == k && f j
  | [] => by simp
  | j :: L => by
    rw [List.foldr_cons, List.any_cons, ← testBit_foldr_mask f k L]
    by_cases hf : f j
    · rw [if_pos hf, Nat.testBit_or, Nat.testBit_shiftLeft, hf, Bool.and_true]
      by_cases hjk : j = k
      · subst hjk
        simp
      · have h0 : (decide (j ≤ k) && Nat.testBit 1 (k - j)) = false := by
          by_cases hle : j ≤ k
          · have hlt : 1 < 2 ^ (k - j) :=
              Nat.one_lt_two_pow (by omega)
            rw [Nat.testBit_eq_false_of_lt hlt, Bool.and_false]
          · simp [hle]
        rw [h0, Bool.or_false]
        simp [hjk]
    · rw [if_neg hf]
      simp [hf]

theorem testBit_maskOf (n : Nat) (f : Nat → Bool) {k : Nat} (hk : k < n) :
    (maskOf n f).testBit k = f k := by
  unfold maskOf
  rw [testBit_foldr_mask, Bool.eq_iff_iff, List.any_eq_true]
  constructor
  · rintro ⟨j, -, h⟩
    rw [Bool.and_eq_true, beq_iff_eq] at h
    rw [← h.1]
    exact h.2
  · intro h
    exact ⟨k, List.mem_range.2 hk, by simp [h]⟩

theorem c1Comp_eq (a b : Array Nat) : c1Comp a b = c1CompL a b := by
  apply Array.ext (by simp [c1Comp, c1CompL])
  intro i h1 h2
  simp [c1Comp, c1CompL]

theorem c1Conj_eq (a t : Array Nat) : c1Conj a t = c1ConjL a t := by
  rw [c1Conj, c1Comp_eq, c1Comp_eq]
  rfl

end CFSG.KC.HMathieu

end
