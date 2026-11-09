module


public section

namespace CFSG.KC.AllChunks

theorem all_of_chunks {α : Type} (L : List α) (f : α → Bool) (n K : Nat) (hK : L.length ≤ K * n)
    (h : ∀ k < K, ((L.drop (k * n)).take n).all f = true) : L.all f = true := by
  rw [List.all_eq_true]
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0
      have : L.length = 0 := by simpa using hK
      omega
    · exact h0
  have hk : i / n < K := by
    rw [Nat.div_lt_iff_lt_mul hn]
    omega
  have hc := h (i / n) hk
  rw [List.all_eq_true] at hc
  have hlt : i % n < ((L.drop (i / n * n)).take n).length := by
    rw [List.length_take, List.length_drop]
    have := Nat.mod_lt i hn
    have e := Nat.div_add_mod i n
    refine Nat.lt_min.2 ⟨this, ?_⟩
    rw [Nat.mul_comm] at e
    omega
  have := hc _ (List.getElem_mem hlt)
  rw [List.getElem_take, List.getElem_drop] at this
  have e : i / n * n + i % n = i := by
    have := Nat.div_add_mod i n
    rw [Nat.mul_comm] at this
    omega
  simp only [e] at this
  exact this

end CFSG.KC.AllChunks

end
