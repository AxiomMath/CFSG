module

public import CFSG.Certificates.Kernel.SporSch.RuDistSound

public section

namespace CFSG.KS.SporSch

open CFSG.Sporadic.RuSchreier.RuB1

theorem pickBy_length_idx {α : Type} {r : α → α → Bool} {m : Nat} {g : Nat → α} {K : Nat → Nat}
    (h : ∀ i < m, ∀ j < m, r (g i) (g j) = Nat.beq (K i) (K j)) :
    (pickBy r ((List.range m).map g)).length = distNL ((List.range m).map K) := by
  classical
  let key : α → Nat := fun p => if hp : ∃ i, i < m ∧ g i = p then K (Nat.find hp) else 0
  have hkey : ∀ i < m, key (g i) = K i := fun i hi => by
    have hp : ∃ i', i' < m ∧ g i' = g i := ⟨i, hi, rfl⟩
    simp only [key, dite_eq_left hp]
    obtain ⟨hj, hg⟩ := Nat.find_spec hp
    have e := h (Nat.find hp) hj i hi
    rw [hg, h i hi i hi, Nat.beq_refl] at e
    exact Nat.eq_of_beq_eq_true e.symm
  rw [pickBy_length (key := key), List.map_map]
  · exact congrArg distNL (List.map_congr_left fun i hi => hkey i (List.mem_range.1 hi))
  · intro p hp p' hp'
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hp
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hp'
    rw [hkey i (List.mem_range.1 hi), hkey j (List.mem_range.1 hj)]
    exact h i (List.mem_range.1 hi) j (List.mem_range.1 hj)

theorem beq_pair {N x y x' y' : Nat} (hy : y < 2 ^ N) (hy' : y' < 2 ^ N) :
    Nat.beq (x * 2 ^ N + y) (x' * 2 ^ N + y') = (Nat.beq x x' && Nat.beq y y') := by
  have hp : 0 < 2 ^ N := Nat.two_pow_pos N
  by_cases hx : x = x'
  · subst hx
    by_cases hyy : y = y'
    · subst hyy
      simp [Nat.beq_refl]
    · have h1 : Nat.beq (x * 2 ^ N + y) (x * 2 ^ N + y') = false := by
        cases e : Nat.beq (x * 2 ^ N + y) (x * 2 ^ N + y')
        · rfl
        · exact absurd (by have := Nat.eq_of_beq_eq_true e; omega) hyy
      have h2 : Nat.beq y y' = false := by
        cases e : Nat.beq y y'
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true e) hyy
      rw [h1, h2, Nat.beq_refl]
      rfl
  · have h1 : Nat.beq (x * 2 ^ N + y) (x' * 2 ^ N + y') = false := by
      cases e : Nat.beq (x * 2 ^ N + y) (x' * 2 ^ N + y')
      · rfl
      · have he := Nat.eq_of_beq_eq_true e
        have d1 : (x * 2 ^ N + y) / 2 ^ N = x := by
          rw [Nat.add_comm, Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt hy, Nat.zero_add]
        have d2 : (x' * 2 ^ N + y') / 2 ^ N = x' := by
          rw [Nat.add_comm, Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt hy', Nat.zero_add]
        exact absurd (by rw [← d1, ← d2, he]) hx
    have h2 : Nat.beq x x' = false := by
      cases e : Nat.beq x x'
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true e) hx
    rw [h1, h2]
    rfl

end CFSG.KS.SporSch

end
