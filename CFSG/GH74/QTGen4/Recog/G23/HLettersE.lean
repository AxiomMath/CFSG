module

public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.Algebra.Group.Subgroup.Finite

public section

namespace CFSG.GH74.QTGen4.Recog.G23

theorem closure_eq_of_index_two {G : Type*} [Group G] [Finite G] {H K L : Subgroup G}
    (hLH : L ≤ H) (hKL : K ≤ L) {w : G} (hwL : w ∈ L) (hwK : w ∉ K)
    (hcard : Nat.card H = 2 * Nat.card K) : L = H := by
  have : Nonempty ↥K := ⟨1⟩
  have hKpos : 0 < Nat.card K := Nat.card_pos
  have hlt : Nat.card K < Nat.card L := by
    by_contra h
    have h' : Nat.card L ≤ Nat.card K := not_lt.mp h
    have hKeq : K = L := Subgroup.eq_of_le_of_card_ge hKL h'
    exact hwK (by rw [hKeq]; exact hwL)
  have hLdvd : Nat.card L ∣ Nat.card H := Subgroup.card_dvd_of_le hLH
  obtain ⟨m, hm⟩ : Nat.card K ∣ Nat.card L := Subgroup.card_dvd_of_le hKL
  have h2 : Nat.card K * m ∣ Nat.card K * 2 := by
    rw [← hm, mul_comm (Nat.card K) 2, ← hcard]
    exact hLdvd
  have hm2 : m ∣ 2 := Nat.dvd_of_mul_dvd_mul_left hKpos h2
  have hmle : m ≤ 2 := Nat.le_of_dvd (by decide) hm2
  have hm3 : m = 0 ∨ m = 1 ∨ m = 2 := by omega
  rcases hm3 with rfl | rfl | rfl
  · omega
  · omega
  · have hHle : Nat.card H ≤ Nat.card L := by omega
    exact Subgroup.eq_of_le_of_card_ge hLH hHle

end CFSG.GH74.QTGen4.Recog.G23
