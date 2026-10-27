module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.GH74.QTGen4.U42

open Subgroup

theorem exists_card_nine_sup_eq_top {K : Type*} [Group K] [Finite K] (S : Subgroup K) (n : ℕ)
    (hS : Nat.card S = 2 ^ n) (hK : Nat.card K = 9 * Nat.card S) :
    ∃ P : Subgroup K, Nat.card P = 9 ∧ P ⊔ S = ⊤ := by
  have h9 : 3 ^ 2 ∣ Nat.card K := ⟨Nat.card S, by rw [hK]; norm_num⟩
  obtain ⟨P, hP⟩ := Sylow.exists_subgroup_card_pow_prime 3 h9
  have hP9 : Nat.card P = 9 := by rw [hP]; norm_num
  have hPi : P.index = Nat.card S := by
    have h : Nat.card P * P.index = Nat.card K := Subgroup.card_mul_index P
    rw [hP9, hK] at h
    omega
  have hSi : S.index = 9 := by
    have h : Nat.card S * S.index = Nat.card K := Subgroup.card_mul_index S
    rw [hK] at h
    have hpos : 0 < Nat.card S := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hpos (h.trans (Nat.mul_comm 9 (Nat.card S)))
  have hcop : Nat.Coprime (Nat.card S) 9 := by
    rw [hS]
    exact Nat.Coprime.pow_left n (by norm_num)
  have h1 : (P ⊔ S).index ∣ P.index := Subgroup.index_dvd_of_le le_sup_left
  have h2 : (P ⊔ S).index ∣ S.index := Subgroup.index_dvd_of_le le_sup_right
  rw [hPi] at h1
  rw [hSi] at h2
  have hQ : (P ⊔ S).index = 1 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
  exact ⟨P, hP9, Subgroup.index_eq_one.mp hQ⟩

end CFSG.GH74.QTGen4.U42

end
