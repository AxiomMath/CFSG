module

public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Group

public section

namespace CFSG.KC.HeChain

open Subgroup

theorem class_count {G : Type*} [Group G] (C : Subgroup G) [Finite C] (s : G) {N : ℕ}
    (c : ℕ → G) (hc : ∀ i < N, c i ∈ C)
    (hd : ∀ i < N, ∀ j < N, c i * s * (c i)⁻¹ = c j * s * (c j)⁻¹ → i = j) :
    N * Nat.card (C ⊓ centralizer {s} : Subgroup G) ≤ Nat.card C ∧
      (N * Nat.card (C ⊓ centralizer {s} : Subgroup G) = Nat.card C →
        ∀ z ∈ C, ∃ i < N, (c i)⁻¹ * z ∈ C ⊓ centralizer {s}) := by
  set K : Subgroup G := C ⊓ centralizer {s} with hK
  have hKC : K ≤ C := inf_le_left
  let φ : Fin N × K → C := fun p => ⟨c p.1 * p.2, C.mul_mem (hc _ p.1.2) (hKC p.2.2)⟩
  have hinj : Function.Injective φ := by
    rintro ⟨i, k⟩ ⟨j, k'⟩ h
    have e : c i * k = c j * k' := congrArg Subtype.val h
    have hx : (c j)⁻¹ * c i ∈ centralizer {s} := by
      have : (c j)⁻¹ * c i = (k' : G) * (k : G)⁻¹ := by
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← e, mul_inv_cancel_right]
      rw [this]
      exact (centralizer {s}).mul_mem (inf_le_right (a := C) k'.2)
        ((centralizer {s}).inv_mem (inf_le_right (a := C) k.2))
    rw [mem_centralizer_singleton_iff] at hx
    have hij : (i : ℕ) = j := hd i i.2 j j.2 (by
      have e2 : c i = c j * ((c j)⁻¹ * c i) := by group
      calc c i * s * (c i)⁻¹ = c j * ((c j)⁻¹ * c i * s) * ((c j)⁻¹ * c i)⁻¹ * (c j)⁻¹ := by
            group
        _ = c j * (s * ((c j)⁻¹ * c i)) * ((c j)⁻¹ * c i)⁻¹ * (c j)⁻¹ := by rw [hx]
        _ = c j * s * (c j)⁻¹ := by group)
    have hij' : i = j := Fin.ext hij
    subst hij'
    have : (k : G) = k' := mul_left_cancel e
    rw [Subtype.ext this]
  have hcard : Nat.card (Fin N × K) = N * Nat.card K := by
    rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin N), Fintype.card_fin]
  have hle := Nat.card_le_card_of_injective φ hinj
  rw [hcard] at hle
  refine ⟨hle, fun heq z hz => ?_⟩
  have hbij := hinj.bijective_of_nat_card_le (by rw [hcard, heq])
  obtain ⟨⟨i, k⟩, hik⟩ := hbij.2 ⟨z, hz⟩
  have e : c i * k = z := congrArg Subtype.val hik
  refine ⟨i, i.2, ?_⟩
  rw [← e, inv_mul_cancel_left]
  exact k.2

end CFSG.KC.HeChain

end
