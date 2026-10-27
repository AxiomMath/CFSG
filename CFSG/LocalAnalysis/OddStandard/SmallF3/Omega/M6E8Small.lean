module

public import CFSG.GroupTheory.NonabelianSimpleOrderSixty

public section

namespace CFSG.OddStandard.SmallF3.Omega

theorem m6e8_not_simple_dvd_234 {Q : Type*} [Group Q] [Finite Q] (hs : IsSimpleGroup Q)
    (hnab : ∃ a b : Q, a * b ≠ b * a) : ¬ Nat.card Q ∣ 234 := by
  intro hd
  have h60 := CFSG.GroupTheory.nonabelian_simple_order_at_least_sixty hs hnab
  have hle : Nat.card Q ≤ 234 := Nat.le_of_dvd (by norm_num) hd
  have key : ∀ n : ℕ, 60 ≤ n → n ≤ 234 → n ∣ 234 → n = 78 ∨ n = 117 ∨ n = 234 := by
    intro n h1 h2 h3
    interval_cases n <;> omega
  obtain ⟨m, hm, hQ⟩ : ∃ m : ℕ, (m = 6 ∨ m = 9 ∨ m = 18) ∧ Nat.card Q = 13 ^ 1 * m := by
    rcases key _ h60 hle hd with h | h | h
    · exact ⟨6, Or.inl rfl, by omega⟩
    · exact ⟨9, Or.inr (Or.inl rfl), by omega⟩
    · exact ⟨18, Or.inr (Or.inr rfl), by omega⟩
  have hp : Nat.Prime 13 := by norm_num
  have hpm : ¬ 13 ∣ m := by omega
  obtain ⟨hdvd, hmod, h5⟩ := CFSG.GroupTheory.nonabelian_simple_Sylow_count_minimum hs hnab hp
    (by rw [hQ]; exact Dvd.intro _ (by ring)) (le_refl 1) hpm hQ
  have hmd : m ∣ 18 := by rcases hm with rfl | rfl | rfl <;> norm_num
  have hn18 : Nat.card (Sylow 13 Q) ∣ 18 := hdvd.trans hmd
  have hle18 : Nat.card (Sylow 13 Q) ≤ 18 := Nat.le_of_dvd (by norm_num) hn18
  have hmod' : Nat.card (Sylow 13 Q) % 13 = 1 := hmod
  have h14 : Nat.card (Sylow 13 Q) = 14 := by omega
  rw [h14] at hn18
  omega

end CFSG.OddStandard.SmallF3.Omega
