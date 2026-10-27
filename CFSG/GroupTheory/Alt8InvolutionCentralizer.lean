module

public import CFSG.CGT.A8S.TopPerm

public section

namespace CFSG.GroupTheory

open Equiv Equiv.Perm CFSG.CGT.A8S.Perm8

theorem card_centralizer_dvd_one_ninety_two {σ : alternatingGroup (Fin 8)} (h2 : σ ^ 2 = 1)
    (h1 : σ ≠ 1) : Nat.card (Subgroup.centralizer {σ}) ∣ 192 := by
  have h2' : (σ : Perm (Fin 8)) ^ 2 = 1 := by rw [← Subgroup.coe_pow, h2]; rfl
  have h1' : (σ : Perm (Fin 8)) ≠ 1 := fun h => h1 (Subtype.ext h)
  obtain ⟨k, hk, hk1, hk4⟩ := cycleType_eq_replicate h2' h1'
  obtain ⟨j, rfl⟩ := even_of_sign_eq_one hk σ.2
  have hc := two_mul_card_centralizer h2 h1
  rw [card_centralizer_perm hk (by omega)] at hc
  have hj : j = 1 ∨ j = 2 := by omega
  rcases hj with rfl | rfl
  · norm_num [Nat.factorial] at hc
    have : Nat.card (Subgroup.centralizer {σ}) = 96 := by omega
    rw [this]
    norm_num
  · norm_num [Nat.factorial] at hc
    have : Nat.card (Subgroup.centralizer {σ}) = 192 := by omega
    rw [this]

theorem card_centralizer_dvd_one_ninety_two_of_mulEquiv {X : Type} [Group X]
    (e : X ≃* alternatingGroup (Fin 8)) {α : X} (h2 : α * α = 1) (h1 : α ≠ 1) :
    Nat.card (Subgroup.centralizer ({α} : Set X)) ∣ 192 := by
  rw [card_centralizer_mulEquiv e α]
  refine card_centralizer_dvd_one_ninety_two ?_ ?_
  · rw [pow_two, ← map_mul, h2, map_one]
  · intro h
    exact h1 (e.injective (by rw [h, map_one]))

end CFSG.GroupTheory
