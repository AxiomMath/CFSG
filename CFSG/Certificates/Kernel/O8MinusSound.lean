module

public import CFSG.Certificates.Kernel.O8ListProved

public section

namespace CFSG.KC.O8

open CFSG.EvenSmallLie.OmegaEight.Stage2

theorem all_of_getD {l : List ℕ} {n : ℕ} {f : ℕ → Bool} (hl : l.length = n)
    (h : ∀ i < n, f (l.getD i 0) = true) : l.all f = true := by
  rw [List.all_eq_true]
  intro r hr
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hr
  have := h i (hl ▸ hi)
  rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] at this

theorem all_range_of_blocks {m s nb : ℕ} {f : ℕ → Bool} (hm : m ≤ nb * 2 ^ s)
    (h : ∀ b < nb, ((List.range (2 ^ s)).all fun c =>
      !(decide (b * 2 ^ s + c < m)) || f (b * 2 ^ s + c)) = true) :
    (List.range m).all f = true := by
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not] at h ⊢
  intro i hi
  have h2 : 0 < 2 ^ s := by positivity
  have hb : i / 2 ^ s < nb := by
    rw [Nat.div_lt_iff_lt_mul h2]
    omega
  rcases h (i / 2 ^ s) hb (i % 2 ^ s) (Nat.mod_lt _ h2) with h1 | h1
  · rw [Nat.div_add_mod' i (2 ^ s)] at h1
    exact absurd hi h1
  · rwa [Nat.div_add_mod' i (2 ^ s)] at h1

theorem commCount_eq (E : Enum) (s : ℕ) : commCount E s =
    ((List.range E.keys.size).filter fun i =>
      mulK (E.keys.getD i 0) s == mulK s (E.keys.getD i 0)).length := by
  apply commCount_eq_proved

end CFSG.KC.O8

end
