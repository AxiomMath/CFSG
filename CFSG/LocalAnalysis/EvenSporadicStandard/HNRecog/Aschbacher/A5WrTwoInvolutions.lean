module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.A5WrTwoFacts

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HNRecog

open Subgroup

private theorem coord_cases (q : Multiplicative (ZMod 2)) :
    q = 1 ∨ q = Multiplicative.ofAdd 1 := by
  rcases (show ∀ e : ZMod 2, e = 0 ∨ e = 1 by decide) (Multiplicative.toAdd q) with h | h
  · left
    rw [← ofAdd_toAdd q, h]
    rfl
  · right
    rw [← ofAdd_toAdd q, h]

private theorem sigmaC2_ne_one : (Multiplicative.ofAdd (1 : ZMod 2)) ≠ 1 := by decide

private theorem sigmaC2_inv :
    (Multiplicative.ofAdd (1 : ZMod 2))⁻¹ = Multiplicative.ofAdd (1 : ZMod 2) := by decide

private theorem sigmaC2_mul_self :
    (Multiplicative.ofAdd (1 : ZMod 2)) * Multiplicative.ofAdd (1 : ZMod 2) = 1 := by decide

theorem A5WrTwo.exists_conj_of_outer_involutions {u v : A5WrTwo}
    (hu : u ∉ commutator A5WrTwo) (hv : v ∉ commutator A5WrTwo) (hu2 : u ^ 2 = 1)
    (hv2 : v ^ 2 = 1) : ∃ b ∈ commutator A5WrTwo, b * u * b⁻¹ = v := by
  have hu_ne : u.right ≠ 1 := by
    intro h
    exact hu (by rw [A5WrTwo.commutator_eq_ker]; exact h)
  have hv_ne : v.right ≠ 1 := by
    intro h
    exact hv (by rw [A5WrTwo.commutator_eq_ker]; exact h)
  have hur : u.right = Multiplicative.ofAdd (1 : ZMod 2) := by
    rcases coord_cases u.right with h | h
    · exact absurd h hu_ne
    · exact h
  have hvr : v.right = Multiplicative.ofAdd (1 : ZMod 2) := by
    rcases coord_cases v.right with h | h
    · exact absurd h hv_ne
    · exact h
  have hu_sq : ∀ x, u.left x * u.left (Multiplicative.ofAdd (1 : ZMod 2) * x) = 1 := by
    intro x
    have h : (u ^ 2).left x = (1 : A5WrTwo).left x :=
      congrArg (fun w : A5WrTwo => w.left x) hu2
    rw [pow_two, RegularWreathProduct.mul_left, Pi.mul_apply] at h
    simpa [hur, sigmaC2_inv] using h
  have hv_sq : ∀ x, v.left x * v.left (Multiplicative.ofAdd (1 : ZMod 2) * x) = 1 := by
    intro x
    have h : (v ^ 2).left x = (1 : A5WrTwo).left x :=
      congrArg (fun w : A5WrTwo => w.left x) hv2
    rw [pow_two, RegularWreathProduct.mul_left, Pi.mul_apply] at h
    simpa [hvr, sigmaC2_inv] using h
  have hu_sqσ : u.left (Multiplicative.ofAdd (1 : ZMod 2)) * u.left 1 = 1 := by
    have h := hu_sq (Multiplicative.ofAdd (1 : ZMod 2))
    simpa [sigmaC2_mul_self] using h
  have hv_sqσ : v.left (Multiplicative.ofAdd (1 : ZMod 2)) * v.left 1 = 1 := by
    have h := hv_sq (Multiplicative.ofAdd (1 : ZMod 2))
    simpa [sigmaC2_mul_self] using h
  have hu_rel : u.left (Multiplicative.ofAdd (1 : ZMod 2)) = (u.left 1)⁻¹ :=
    eq_inv_of_mul_eq_one_left hu_sqσ
  have hv_rel : v.left (Multiplicative.ofAdd (1 : ZMod 2)) = (v.left 1)⁻¹ :=
    eq_inv_of_mul_eq_one_left hv_sqσ
  let g : Multiplicative (ZMod 2) → alternatingGroup (Fin 5) :=
    fun x => if x = 1 then v.left 1 * (u.left 1)⁻¹ else 1
  have hg1 : g 1 = v.left 1 * (u.left 1)⁻¹ := by
    dsimp only [g]
    rw [if_pos rfl]
  have hgσ : g (Multiplicative.ofAdd (1 : ZMod 2)) = 1 := by
    dsimp only [g]
    rw [if_neg sigmaC2_ne_one]
  refine ⟨⟨g, 1⟩, ?_, ?_⟩
  · rw [A5WrTwo.commutator_eq_ker]
    rfl
  · apply RegularWreathProduct.ext
    · funext x
      rcases coord_cases x with rfl | rfl
      · simp only [RegularWreathProduct.mul_left, RegularWreathProduct.mul_right,
          RegularWreathProduct.inv_left, RegularWreathProduct.inv_right, Pi.mul_apply,
          Pi.inv_apply, one_mul, mul_one, inv_one, hur, sigmaC2_inv, hg1, hgσ, hu_rel,
          hv_rel]
        group
      · simp only [RegularWreathProduct.mul_left, RegularWreathProduct.mul_right,
          RegularWreathProduct.inv_left, RegularWreathProduct.inv_right, Pi.mul_apply,
          Pi.inv_apply, one_mul, mul_one, inv_one, hur, sigmaC2_inv, sigmaC2_mul_self, hg1,
          hgσ, hu_rel, hv_rel]
        group
    · simp only [RegularWreathProduct.mul_right, RegularWreathProduct.inv_right, one_mul,
        mul_one, inv_one, hur, hvr]

end CFSG.EvenSporadicStandard.HNRecog
