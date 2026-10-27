module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailModelCoordinates
public import CFSG.Timmesfeld.Orders.ClassicalAnisotropic

public section

namespace CFSG.AGLEmbedding.LeviBlock

open QuadraticMap CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
open scoped commutatorElement

variable {K : Type*} [Field K] {b c : K}

@[expose] noncomputable def minusOmegaMul (b c : K) : Module.End K (Fin 2 → K) :=
  Matrix.toLin' !![0, c; 1, b]

theorem minusOmegaMul_apply_zero (a : Fin 2 → K) : minusOmegaMul b c a 0 = c * a 1 := by
  simp [minusOmegaMul, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem minusOmegaMul_apply_one (a : Fin 2 → K) : minusOmegaMul b c a 1 = a 0 + b * a 1 := by
  simp [minusOmegaMul, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

variable (b c) in
@[expose] def IsOmegaTwisted (g : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) (e : K) : Prop :=
  (g : Module.End K (Fin 2 → K)) * minusOmegaMul b c = (minusOmegaMul b c + e • 1) * g

theorem IsOmegaTwisted.mul {g h : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)} {e e' : K}
    (hg : IsOmegaTwisted b c g e) (hh : IsOmegaTwisted b c h e') :
    IsOmegaTwisted b c (g * h) (e + e') := by
  unfold IsOmegaTwisted at *
  rw [LinearEquiv.coe_toLinearMap_mul, mul_assoc, hh, ← mul_assoc, mul_add, hg]
  simp only [add_mul, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, mul_assoc, add_smul]
  abel

theorem IsOmegaTwisted.inv {g : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)} {e : K}
    (hg : IsOmegaTwisted b c g e) : IsOmegaTwisted b c g⁻¹ (-e) := by
  unfold IsOmegaTwisted at *
  have h1 : ((g⁻¹ : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) : Module.End K (Fin 2 → K)) * g = 1 := by
    rw [← LinearEquiv.coe_toLinearMap_mul, inv_mul_cancel]
    rfl
  have h2 : (g : Module.End K (Fin 2 → K)) * ((g⁻¹ : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) :
      Module.End K (Fin 2 → K)) = 1 := by
    rw [← LinearEquiv.coe_toLinearMap_mul, mul_inv_cancel]
    rfl
  set g' : Module.End K (Fin 2 → K) :=
    ((g⁻¹ : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) : (Fin 2 → K) →ₗ[K] (Fin 2 → K))
  set G : Module.End K (Fin 2 → K) := (g : Module.End K (Fin 2 → K))
  set J := minusOmegaMul b c
  have h3 : J * g' = g' * J + e • g' := by
    calc J * g' = g' * (G * J) * g' := by rw [← mul_assoc, h1, one_mul]
      _ = g' * ((J + e • 1) * G) * g' := by rw [hg]
      _ = g' * J * (G * g') + e • (g' * (G * g')) := by
        simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_assoc]
      _ = g' * J + e • g' := by rw [h2, mul_one, mul_one]
  rw [add_mul, h3, smul_mul_assoc, one_mul, add_assoc, ← add_smul, add_neg_cancel, zero_smul,
    add_zero]

theorem IsOmegaTwisted.commutator {g h : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)} {e e' : K}
    (hg : IsOmegaTwisted b c g e) (hh : IsOmegaTwisted b c h e') :
    IsOmegaTwisted b c ⁅g, h⁆ 0 := by
  have := ((hg.mul hh).mul hg.inv).mul hh.inv
  rwa [show e + e' + -e + -e' = 0 by ring, ← commutatorElement_def] at this

theorem minusPlane_ext {f f' : Module.End K (Fin 2 → K)}
    (h0 : f (Pi.single 0 1) = f' (Pi.single 0 1)) (h1 : f (Pi.single 1 1) = f' (Pi.single 1 1)) :
    f = f' := by
  refine LinearMap.pi_ext fun i x => ?_
  rw [show (Pi.single i x : Fin 2 → K) = x • Pi.single i 1 by rw [← Pi.single_smul, smul_eq_mul,
    mul_one], map_smul, map_smul]
  fin_cases i
  · exact congrArg _ h0
  · exact congrArg _ h1

theorem minusOmegaMul_single_zero : minusOmegaMul b c (Pi.single 0 1) = Pi.single 1 1 := by
  funext j
  fin_cases j <;> simp [minusOmegaMul_apply_zero, minusOmegaMul_apply_one]

theorem minusPlane_eq_or_eq [CharP K 2] (hb : b ≠ 0)
    {g : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (minusTailForm K b c)) :
    ∃ l : K, (l = 0 ∨ l = b) ∧
      g (Pi.single 1 1) 0 = c * g (Pi.single 0 1) 1 + l * g (Pi.single 0 1) 0 ∧
      g (Pi.single 1 1) 1 = g (Pi.single 0 1) 0 + b * g (Pi.single 0 1) 1 +
        l * g (Pi.single 0 1) 1 := by
  have h2' : (2 : K) = 0 := CharTwo.two_eq_zero
  set x := g (Pi.single 0 1)
  set z := g (Pi.single 1 1)
  have hq := fun a => TauCeti.QuadraticMap.mem_orthogonalGroup_iff.1 hg a
  have h1 : x 0 ^ 2 + b * x 0 * x 1 + c * x 1 ^ 2 = 1 := by
    have := hq (Pi.single 0 1)
    rw [minusTailForm_apply, minusTailForm_apply] at this
    simpa using this
  have h2 : z 0 ^ 2 + b * z 0 * z 1 + c * z 1 ^ 2 = c := by
    have := hq (Pi.single 1 1)
    rw [minusTailForm_apply, minusTailForm_apply] at this
    simpa using this
  have hp : (x 0 + z 0) ^ 2 + b * (x 0 + z 0) * (x 1 + z 1) + c * (x 1 + z 1) ^ 2 =
      1 + b + c := by
    have := hq (Pi.single 0 1 + Pi.single 1 1)
    rw [minusTailForm_apply, minusTailForm_apply, map_add] at this
    simpa using this
  have h3 : x 0 * z 1 + x 1 * z 0 = 1 := by
    have : b * (x 0 * z 1 + x 1 * z 0 - 1) = 0 := by
      linear_combination hp - h1 - h2 - (x 0 * z 0 + x 1 * z 1 * c) * h2'
    linear_combination (mul_eq_zero.1 this).resolve_left hb
  obtain ⟨l, hl0, hl1⟩ : ∃ l : K, z 0 = c * x 1 + l * x 0 ∧ z 1 = x 0 + b * x 1 + l * x 1 := by
    by_cases hx0 : x 0 = 0
    · have hx1 : x 1 ≠ 0 := by
        rintro h
        rw [hx0, h] at h1
        simp at h1
      refine ⟨(z 1 - x 0 - b * x 1) / x 1, ?_, by field_simp; ring⟩
      rw [hx0, mul_zero, add_zero]
      have : x 1 * (z 0 - c * x 1) = 0 := by
        rw [hx0] at h3 h1
        linear_combination h3 - h1
      linear_combination (mul_eq_zero.1 this).resolve_left hx1
    · refine ⟨(z 0 - c * x 1) / x 0, by field_simp; ring, ?_⟩
      have : x 0 * (z 1 - x 0 - b * x 1 - (z 0 - c * x 1) / x 0 * x 1) = 0 := by
        field_simp
        linear_combination h3 - h1 - (x 1 * z 0 - c * x 1 ^ 2) * h2'
      linear_combination (mul_eq_zero.1 this).resolve_left hx0
  have hl : l * (l + b) = 0 := by
    rw [hl0, hl1] at h2
    linear_combination h2 - (c + l ^ 2 + l * b) * h1 -
      (l * b * c * x 1 ^ 2 + 2 * l * c * x 0 * x 1 + b * c * x 0 * x 1 + b ^ 2 * c * x 1 ^ 2) * h2'
  refine ⟨l, ?_, hl0, hl1⟩
  rcases mul_eq_zero.1 hl with h | h
  · exact Or.inl h
  · exact Or.inr (by linear_combination h - b * h2')

theorem minusOmegaMul_single_one : minusOmegaMul b c (Pi.single 1 1) =
    c • Pi.single 0 1 + b • Pi.single 1 1 := by
  funext j
  fin_cases j <;> simp [minusOmegaMul_apply_zero, minusOmegaMul_apply_one]

theorem isOmegaTwisted_of_mem_orthogonalGroup [CharP K 2] (hb : b ≠ 0)
    {g : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (minusTailForm K b c)) :
    ∃ l : K, (l = 0 ∨ l = b) ∧ IsOmegaTwisted b c g l := by
  have h2' : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨l, hl, hl0, hl1⟩ := minusPlane_eq_or_eq hb hg
  have hlb : l * (l + b) = 0 := by
    rcases hl with h | h <;> rw [h]
    · ring
    · linear_combination b ^ 2 * h2'
  refine ⟨l, hl, minusPlane_ext ?_ ?_⟩
  · rw [Module.End.mul_apply, Module.End.mul_apply, minusOmegaMul_single_zero]
    funext j
    fin_cases j
    · simp [minusOmegaMul_apply_zero, hl0]
    · simp [minusOmegaMul_apply_one, hl1]
  · rw [Module.End.mul_apply, Module.End.mul_apply, minusOmegaMul_single_one]
    funext j
    fin_cases j
    · simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
        Module.End.one_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, LinearEquiv.coe_coe,
        Fin.zero_eta, Fin.isValue, minusOmegaMul_apply_zero]
      rw [hl0, hl1]
      linear_combination (-(g (Pi.single 0 1) 0)) * hlb +
        (g (Pi.single 0 1) 0 * b * l - l * c * g (Pi.single 0 1) 1) * h2'
    · simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
        Module.End.one_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, LinearEquiv.coe_coe,
        Fin.mk_one, Fin.isValue, minusOmegaMul_apply_one]
      rw [hl0, hl1]
      linear_combination (-(g (Pi.single 0 1) 1)) * hlb - (g (Pi.single 0 1) 0 * l) * h2'

theorem eq_of_isOmegaTwisted_zero {g : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)}
    (hg : IsOmegaTwisted b c g 0) :
    (g : Module.End K (Fin 2 → K)) =
      g (Pi.single 0 1) 0 • (1 : Module.End K (Fin 2 → K)) +
        g (Pi.single 0 1) 1 • minusOmegaMul b c := by
  unfold IsOmegaTwisted at hg
  rw [zero_smul, add_zero] at hg
  set R : Module.End K (Fin 2 → K) := g (Pi.single 0 1) 0 • (1 : Module.End K (Fin 2 → K)) +
    g (Pi.single 0 1) 1 • minusOmegaMul b c
  have h0 : (g : Module.End K (Fin 2 → K)) (Pi.single 0 1) = R (Pi.single 0 1) := by
    funext j
    fin_cases j <;> simp [R, minusOmegaMul_single_zero]
  have hRJ : R * minusOmegaMul b c = minusOmegaMul b c * R := by
    simp only [R, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  refine minusPlane_ext h0 ?_
  rw [← minusOmegaMul_single_zero (b := b) (c := c), ← Module.End.mul_apply, hg,
    Module.End.mul_apply, h0, ← Module.End.mul_apply, ← hRJ, Module.End.mul_apply]

theorem commute_of_isOmegaTwisted_zero {g h : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)}
    (hg : IsOmegaTwisted b c g 0) (hh : IsOmegaTwisted b c h 0) : g * h = h * g := by
  apply LinearEquiv.toLinearMap_injective
  rw [LinearEquiv.coe_toLinearMap_mul, LinearEquiv.coe_toLinearMap_mul,
    eq_of_isOmegaTwisted_zero hg, eq_of_isOmegaTwisted_zero hh]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  module

variable (b c) in
@[expose] def omegaRotations : Subgroup ((Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) where
  carrier := {g | IsOmegaTwisted b c g 0}
  mul_mem' {g h} hg hh := by
    have := IsOmegaTwisted.mul hg hh
    rwa [add_zero] at this
  one_mem' := by
    change ((1 : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) : Module.End K (Fin 2 → K)) * _ = _
    rw [zero_smul, add_zero]
    rfl
  inv_mem' {g} hg := by
    have := IsOmegaTwisted.inv hg
    rwa [neg_zero] at this

theorem minusPlane_b_ne_zero [Finite K] [CharP K 2] (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    b ≠ 0 := by
  rintro rfl
  obtain ⟨s, hs⟩ := CFSG.Timmesfeld.ClassicalOrders.exists_sq_eq_of_charTwo c
  apply hirr s
  rw [zero_mul, add_zero, ← hs, ← two_mul, CharTwo.two_eq_zero, zero_mul]

theorem commute_of_mem_commutator_minusTailForm [Finite K] [CharP K 2]
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {g h : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)}
    (hg : g ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup (minusTailForm K b c),
      TauCeti.QuadraticMap.orthogonalGroup (minusTailForm K b c)⁆)
    (hh : h ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup (minusTailForm K b c),
      TauCeti.QuadraticMap.orthogonalGroup (minusTailForm K b c)⁆) : g * h = h * g := by
  have hb := minusPlane_b_ne_zero hirr
  have hle : ⁅TauCeti.QuadraticMap.orthogonalGroup (minusTailForm K b c),
      TauCeti.QuadraticMap.orthogonalGroup (minusTailForm K b c)⁆ ≤ omegaRotations b c := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    obtain ⟨l, -, hl⟩ := isOmegaTwisted_of_mem_orthogonalGroup hb hx
    obtain ⟨l', -, hl'⟩ := isOmegaTwisted_of_mem_orthogonalGroup hb hy
    exact hl.commutator hl'
  exact commute_of_isOmegaTwisted_zero (hle hg) (hle hh)

end CFSG.AGLEmbedding.LeviBlock
