module

public import Mathlib.GroupTheory.Sylow

public section

open Subgroup

namespace CFSG.EvenSporadicStandard.TwoHS.GH312

variable {X : Type*} [Group X]

theorem mul_card_dvd_card_of_card_centralizer_eq [Finite X] {T : Subgroup X} (hT : T.Normal)
    {u : X} {m : ℕ}
    (h : Nat.card ↥(centralizer ({u} : Set X)) =
      m * Nat.card ↥(T ⊓ centralizer ({u} : Set X))) :
    m * Nat.card ↥T ∣ Nat.card X := by
  haveI := hT
  have h1 : T.relIndex (centralizer ({u} : Set X)) *
      Nat.card ↥(T ⊓ centralizer ({u} : Set X)) = Nat.card ↥(centralizer ({u} : Set X)) :=
    Subgroup.relIndex_mul_card T _
  have hpos : 0 < Nat.card ↥(T ⊓ centralizer ({u} : Set X)) := Nat.card_pos
  have hm : T.relIndex (centralizer ({u} : Set X)) = m :=
    Nat.eq_of_mul_eq_mul_right hpos (h1.trans h)
  have h2 : T.relIndex (centralizer ({u} : Set X)) ∣ T.index :=
    Subgroup.relIndex_dvd_index_of_normal T _
  rw [hm] at h2
  calc m * Nat.card ↥T ∣ T.index * Nat.card ↥T := Nat.mul_dvd_mul_right h2 _
    _ = Nat.card X := Subgroup.index_mul_card T

theorem false_of_four_mul_card_dvd [Finite X] (P : Sylow 2 X)
    (hP : Nat.card ↥(P : Subgroup X) = 2 ^ 7) {T : Subgroup X} (hT6 : 2 ^ 6 ∣ Nat.card ↥T)
    (h : 4 * Nat.card ↥T ∣ Nat.card X) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h8 : 2 ^ 8 ∣ Nat.card X := by
    refine dvd_trans ?_ h
    obtain ⟨k, hk⟩ := hT6
    rw [hk]
    exact ⟨k, by ring⟩
  have h8P : 2 ^ 8 ∣ Nat.card ↥(P : Subgroup X) := P.pow_dvd_card_of_pow_dvd_card h8
  rw [hP] at h8P
  have := Nat.le_of_dvd (by norm_num) h8P
  omega

theorem false_of_card_centralizer_eq_four_mul [Finite X] {T : Subgroup X} (hT : T.Normal)
    (hT6 : 2 ^ 6 ∣ Nat.card ↥T) {u : X} (P : Sylow 2 X)
    (hP : Nat.card ↥(P : Subgroup X) = 2 ^ 7)
    (h : Nat.card ↥(centralizer ({u} : Set X)) =
      4 * Nat.card ↥(T ⊓ centralizer ({u} : Set X))) : False :=
  false_of_four_mul_card_dvd P hP hT6 (mul_card_dvd_card_of_card_centralizer_eq hT h)

end CFSG.EvenSporadicStandard.TwoHS.GH312
