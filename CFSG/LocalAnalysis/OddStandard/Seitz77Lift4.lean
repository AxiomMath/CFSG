module

public import CFSG.LocalAnalysis.OddStandard.Seitz77U

public section

namespace CFSG.OddStandard.Seitz77

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial.FieldFourCover

section Lift4

variable {F : Type} [Field F] [CharP F 2]

theorem aut_apply_apply_of_coords (ρ : MulAut (unipAll F))
    (hA : ∀ y, coordA (ρ y) = coordA y) (hB : ∀ y, coordB (ρ y) = coordB y)
    (hZ : ∀ c, ρ (uelt 0 0 c) = uelt 0 0 c) (x : unipAll F) : ρ (ρ x) = x := by
  obtain ⟨z, hz⟩ : ∃ z, z = x⁻¹ * ρ x := ⟨_, rfl⟩
  have hz0 : coordA z = 0 ∧ coordB z = 0 := by
    rw [hz, coordA_mul, coordB_mul, coordA_inv, coordB_inv, hA, hB]
    constructor <;> ring
  have hzc : z = uelt 0 0 (coordC z) := by
    have h := uelt_coords z
    rw [hz0.1, hz0.2] at h
    exact h.symm
  have hρz : ρ z = z := by
    calc ρ z = ρ (uelt 0 0 (coordC z)) := by rw [← hzc]
      _ = uelt 0 0 (coordC z) := hZ _
      _ = z := hzc.symm
  have hzz : z * z = 1 := by
    rw [hzc, uelt_mul_self, mul_zero, uelt_zero]
  have hx : ρ x = x * z := by rw [hz, mul_inv_cancel_left]
  calc ρ (ρ x) = ρ (x * z) := by rw [← hx]
    _ = ρ x * ρ z := map_mul ρ x z
    _ = x * (z * z) := by rw [hx, hρz, mul_assoc]
    _ = x := by rw [hzz, mul_one]

theorem lift4_of_charP [Finite F] (ρ : MulAut (unipAll F)) (v : unipAll F)
    (hρ : ρ * ρ = MulAut.conj v) (hv : ρ v = v) :
    ∃ s : unipAll F, (ρ s * v * s) ^ 2 = 1 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have key : ∀ s : unipAll F, coordA (ρ s * v * s) = 0 → (ρ s * v * s) ^ 2 = 1 := fun s hs => by
    rw [sq]
    exact (sq_eq_one_iff _).2 (Or.inr ((mem_radTwo _).2 hs))
  have hρy : ∀ y, ρ (ρ y) = v * y * v⁻¹ := fun y => by
    have := congrArg (fun γ : MulAut (unipAll F) => γ y) hρ
    simpa using this
  obtain ⟨σ, l, m, sw, h⟩ := aut_data ρ
  cases sw
  ·
    have hA : ∀ y, coordA (ρ y) = (l : F) * σ (coordA y) := fun y => by
      simpa using h.coordA_eq y
    have hB : ∀ y, coordB (ρ y) = (m : F) * σ (coordB y) := fun y => by
      simpa using h.coordB_eq y
    have hcA : ∀ y, coordA (ρ (ρ y)) = coordA y := fun y => by
      rw [hρy, coordA_mul, coordA_mul, coordA_inv]
      ring
    have hcB : ∀ y, coordB (ρ (ρ y)) = coordB y := fun y => by
      rw [hρy, coordB_mul, coordB_mul, coordB_inv]
      ring
    have hl : (l : F) * σ l = 1 := by
      have e := hcA (uelt 1 0 0)
      rw [hA, hA, coordA_uelt] at e
      simpa using e
    have hm : (m : F) * σ m = 1 := by
      have e := hcB (uelt 0 1 0)
      rw [hB, hB, coordB_uelt] at e
      simpa using e
    have hσσ : ∀ a, σ (σ a) = a := fun a => by
      have e := hcA (uelt a 0 0)
      rw [hA, hA, coordA_uelt, map_mul] at e
      linear_combination e - (σ (σ a)) * hl
    have hva : (l : F) * σ (coordA v) = coordA v := by
      have e := hA v
      rw [hv] at e
      exact e.symm
    by_cases hne : ∃ x, σ x ≠ x
    ·
      obtain ⟨p, hp⟩ := exists_add_twisted_eq σ hσσ hne l hl (coordA v) hva
      refine ⟨uelt p 0 0, key _ ?_⟩
      rw [coordA_mul, coordA_mul, hA, coordA_uelt]
      linear_combination hp + ((l : F) * σ p + p) * h2
    ·
      push Not at hne
      have sq1 : ∀ u : F, u * σ u = 1 → u = 1 := fun u hu => by
        rw [hne] at hu
        have h0 : (u - 1) * (u - 1) = 0 := by linear_combination hu + (1 - u) * h2
        exact sub_eq_zero.1 (mul_self_eq_zero.1 h0)
      have hl1 := sq1 l hl
      have hm1 := sq1 m hm
      have hρ1 : ∀ x, ρ (ρ x) = x := aut_apply_apply_of_coords ρ
        (fun y => by rw [hA, hl1, hne, one_mul]) (fun y => by rw [hB, hm1, hne, one_mul])
        (fun c => by rw [h.2 c, hl1, hm1, hne]; simp)
      have hcomm : ∀ y, v * y = y * v := fun y => by
        have e := hρy y
        rw [hρ1 y] at e
        exact mul_inv_eq_iff_eq_mul.1 e.symm
      refine ⟨1, key _ ?_⟩
      rw [map_one, one_mul, mul_one]
      exact (coords_eq_zero_of_commute hcomm).1
  ·
    refine ⟨uelt (coordA v) 0 0, key _ ?_⟩
    have e := h.coordA_eq (uelt (coordA v) 0 0)
    simp only [ite_true, coordB_uelt, map_zero, mul_zero] at e
    rw [coordA_mul, coordA_mul, e, coordA_uelt]
    linear_combination (coordA v) * h2

end Lift4

section CardFour

private theorem charP_two_of_card_four_aux {F : Type} [Field F] (hF : Nat.card F = 4) :
    CharP F 2 := by
  have : Finite F := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype F := Fintype.ofFinite F
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact charP_of_card_eq_prime_pow (p := 2) (f := 2)
    (by rw [← Nat.card_eq_fintype_card, hF]; norm_num)

theorem lift4 {F : Type} [Field F] (hF : Nat.card F = 4) (ρ : MulAut (unipAll F))
    (v : unipAll F) (hρ : ρ * ρ = MulAut.conj v) (hv : ρ v = v) :
    ∃ s : unipAll F, (ρ s * v * s) ^ 2 = 1 := by
  have := charP_two_of_card_four_aux hF
  have : Finite F := Nat.finite_of_card_ne_zero (by omega)
  exact lift4_of_charP ρ v hρ hv

end CardFour

end CFSG.OddStandard.Seitz77
