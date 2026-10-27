module

public import CFSG.Certificates.Kernel.Census.ConjSound

public section

namespace CFSG.KC.Census

theorem pinvRest_blocks {n w : Nat} {xs : List Nat} {L : Nat} {f : Nat → List Nat} :
    ∀ (bs : List (List Nat)) (m : Nat), (∀ b ∈ bs, b.length = L) →
      (∀ c < bs.length, pinvRest n w xs (m + L * c) (f (m + L * c)) bs[c]! =
        some (f (m + L * (c + 1)))) →
      pinvRest n w xs m (f m) bs.flatten = some (f (m + L * bs.length))
  | [], m, _, _ => by simp [pinvRest]
  | b :: bs, m, hl, h => by
    rw [List.flatten_cons]
    have h0 := h 0 (by simp)
    simp only [Nat.mul_zero, Nat.add_zero, Nat.zero_add, Nat.mul_one] at h0
    rw [pinvRest_append_of (hl b (by simp)) rfl (by simpa using h0)]
    have ih := pinvRest_blocks (f := f) bs (m + L) (fun b' hb' => hl b' (by simp [hb']))
      fun c hc => by
        have := h (c + 1) (by simpa using hc)
        rw [show m + L + L * c = m + L * (c + 1) by simp only [Nat.mul_add, Nat.mul_one]; omega,
          show m + L + L * (c + 1) = m + L * (c + 1 + 1) by simp only [Nat.mul_add, Nat.mul_one]; omega]
        simpa using this
    rw [ih, List.length_cons, show m + L + L * bs.length = m + L * (bs.length + 1) by
      simp only [Nat.mul_add, Nat.mul_one]; omega]

end CFSG.KC.Census
