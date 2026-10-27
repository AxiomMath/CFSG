module

public import CFSG.LieType.Steinberg.Minuscule.Valid
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Dynkin
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116

public section

namespace CFSG.LieType.Steinberg.Minuscule

open CFSG.Blueprint.Chevalley MinData

variable {τ : Tag} (hpd : (τ.cartan.map (Int.cast : ℤ → ℚ)).PosDef)
include hpd

theorem cartan_symm (i j : Fin τ.rank) : τ.cartan i j = τ.cartan j i := by
  have h := congrFun (congrFun hpd.isHermitian i) j
  simp only [Matrix.conjTranspose_apply, Matrix.map_apply, star_trivial] at h
  exact_mod_cast h.symm

theorem form_comm (x y : Fin τ.rank → ℤ) : toWeight x ⬝ᵥ y = toWeight y ⬝ᵥ x := by
  simp only [dotProduct, toWeight_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  rw [cartan_symm hpd]
  ring

theorem form_pos {x : Fin τ.rank → ℤ} (hx : x ≠ 0) : 0 < toWeight x ⬝ᵥ x := by
  have hx' : (fun k => (x k : ℚ)) ≠ 0 := fun h =>
    hx (funext fun k => by have := congrFun h k; simpa using this)
  have h := hpd.dotProduct_mulVec_pos hx'
  have e : star (fun k => (x k : ℚ)) ⬝ᵥ Matrix.mulVec (τ.cartan.map (Int.cast : ℤ → ℚ))
      (fun k => (x k : ℚ)) = ((toWeight x ⬝ᵥ x : ℤ) : ℚ) := by
    simp only [star_trivial, dotProduct, Matrix.mulVec, Matrix.map_apply, toWeight_apply,
      Int.cast_sum, Int.cast_mul]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  rw [e] at h
  exact_mod_cast h

theorem form_single_left (i : Fin τ.rank) (y : Fin τ.rank → ℤ) :
    toWeight (Pi.single i 1) ⬝ᵥ y = toWeight y i := by
  rw [form_comm hpd, dotProduct_single, mul_one]

omit hpd in
theorem form_single_single (i : Fin τ.rank) :
    toWeight (Pi.single i 1) ⬝ᵥ (Pi.single i 1 : Fin τ.rank → ℤ) = 2 := by
  rw [dotProduct_single, mul_one, toWeight_single, Tag.cartan_self]

theorem form_reflect (i : Fin τ.rank) (x y : Fin τ.rank → ℤ) :
    toWeight (reflect τ i x) ⬝ᵥ reflect τ i y = toWeight x ⬝ᵥ y := by
  rw [toWeight_reflect, reflectWeight, reflect_eq, sub_dotProduct, dotProduct_sub, dotProduct_sub,
    smul_dotProduct, smul_dotProduct, dotProduct_smul, dotProduct_smul, dotProduct_single,
    mul_one, form_single_left hpd, form_single_single]
  simp only [smul_eq_mul]
  ring

theorem form_self_root {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) : toWeight γ ⬝ᵥ γ = 2 := by
  induction hγ with
  | basis j => exact form_single_single j
  | reflect i _ ih => rw [form_reflect hpd, ih]

theorem form_sub_self (x y : Fin τ.rank → ℤ) :
    toWeight (x - y) ⬝ᵥ (x - y) = toWeight x ⬝ᵥ x - 2 * (toWeight x ⬝ᵥ y) + toWeight y ⬝ᵥ y := by
  rw [toWeight_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub, form_comm hpd y x]
  ring

theorem form_add_self (x y : Fin τ.rank → ℤ) :
    toWeight (x + y) ⬝ᵥ (x + y) = toWeight x ⬝ᵥ x + 2 * (toWeight x ⬝ᵥ y) + toWeight y ⬝ᵥ y := by
  rw [toWeight_add, add_dotProduct, dotProduct_add, dotProduct_add, form_comm hpd y x]
  ring

theorem form_le_one {γ δ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (hδ : IsRoot τ δ) (hne : γ ≠ δ) :
    toWeight γ ⬝ᵥ δ ≤ 1 := by
  have := form_pos hpd (sub_ne_zero.2 hne)
  rw [form_sub_self hpd, form_self_root hpd hγ, form_self_root hpd hδ] at this
  omega

theorem neg_one_le_form {γ δ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (hδ : IsRoot τ δ)
    (hne : γ + δ ≠ 0) : -1 ≤ toWeight γ ⬝ᵥ δ := by
  have := form_pos hpd hne
  rw [form_add_self hpd, form_self_root hpd hγ, form_self_root hpd hδ] at this
  omega

theorem toWeight_injective : Function.Injective (toWeight : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ) := by
  intro x y h
  by_contra hne
  have := form_pos hpd (sub_ne_zero.2 hne)
  rw [toWeight_sub, h, sub_self, zero_dotProduct] at this
  exact lt_irrefl 0 this

theorem eq_one_of_isRoot_nsmul_add_nsmul {γ δ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    (hδ : IsRoot τ δ) (hne : γ + δ ≠ 0) {i j : ℕ} (hi : 0 < i) (hj : 0 < j)
    (h : IsRoot τ (i • γ + j • δ)) : i = 1 ∧ j = 1 := by
  by_cases hγδ : γ = δ
  · subst hγδ
    have e : i • γ + j • γ = ((i + j : ℕ) : ℤ) • γ := by
      rw [← add_smul, natCast_zsmul]
    rw [e] at h
    rcases h.eq_one_or_neg_one_of_eq_smul rfl with h1 | h1 <;> omega
  have hp1 := form_le_one hpd hγ hδ hγδ
  have hp2 := neg_one_le_form hpd hγ hδ hne
  have hε := form_self_root hpd h
  have e : toWeight (i • γ + j • δ) ⬝ᵥ (i • γ + j • δ) =
      2 * (i : ℤ) ^ 2 + 2 * (i * j) * (toWeight γ ⬝ᵥ δ) + 2 * (j : ℤ) ^ 2 := by
    rw [← natCast_zsmul, ← natCast_zsmul, form_add_self hpd, toWeight_smul, toWeight_smul,
      smul_dotProduct, dotProduct_smul, smul_dotProduct, dotProduct_smul, smul_dotProduct,
      dotProduct_smul, form_self_root hpd hγ, form_self_root hpd hδ]
    simp only [smul_eq_mul]
    ring
  rw [e] at hε
  have hi' : (1 : ℤ) ≤ i := by exact_mod_cast hi
  have hj' : (1 : ℤ) ≤ j := by exact_mod_cast hj
  have hprod : 0 ≤ (i : ℤ) * j * (toWeight γ ⬝ᵥ δ + 1) :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  constructor
  · by_contra h1
    have : (2 : ℤ) ≤ i := by omega
    nlinarith [sq_nonneg ((i : ℤ) - j)]
  · by_contra h1
    have : (2 : ℤ) ≤ j := by omega
    nlinarith [sq_nonneg ((i : ℤ) - j)]

omit hpd

theorem cartan_E6 : Tag.cartan .E6 = CartanMatrix.E 6 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem cartan_E7 : Tag.cartan .E7 = CartanMatrix.E 7 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem posDef_cartan_E6 : ((Tag.cartan .E6).map (Int.cast : ℤ → ℚ)).PosDef := by
  rw [cartan_E6]
  exact TauCeti.posDef_map_intCast_cartanMatrix_E6

theorem posDef_cartan_E7 : ((Tag.cartan .E7).map (Int.cast : ℤ → ℚ)).PosDef := by
  rw [cartan_E7]
  exact TauCeti.posDef_map_intCast_cartanMatrix_E7

end CFSG.LieType.Steinberg.Minuscule
