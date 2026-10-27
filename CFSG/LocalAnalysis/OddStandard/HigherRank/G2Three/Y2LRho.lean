module

public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Algebra.Module.ZMod

public section

namespace CFSG.OddStandard.HigherRank.G2Three.Sec2

open Subgroup Matrix

variable {X : Type} [Group X] {M : Subgroup X} (τ : M ≃* Multiplicative (Fin 3 → ZMod 4))

@[expose] def y2l_el (c : Fin 3 → ZMod 4) : X := ((τ.symm (Multiplicative.ofAdd c) : M) : X)

theorem y2l_el_mem (c : Fin 3 → ZMod 4) : y2l_el τ c ∈ M := (τ.symm _).2

theorem y2l_el_add (c d : Fin 3 → ZMod 4) : y2l_el τ (c + d) = y2l_el τ c * y2l_el τ d := by
  simp only [y2l_el, ofAdd_add, map_mul, Subgroup.coe_mul]

theorem y2l_el_zero : y2l_el τ 0 = 1 := by
  simp only [y2l_el, ofAdd_zero, map_one, OneMemClass.coe_one]

theorem y2l_el_neg (c : Fin 3 → ZMod 4) : y2l_el τ (-c) = (y2l_el τ c)⁻¹ := by
  simp only [y2l_el, ofAdd_neg, map_inv, Subgroup.coe_inv]

theorem y2l_el_nsmul (k : ℕ) (c : Fin 3 → ZMod 4) : y2l_el τ (k • c) = y2l_el τ c ^ k := by
  simp only [y2l_el, ofAdd_nsmul, map_pow, Subgroup.coe_pow]

theorem y2l_el_injective : Function.Injective (y2l_el τ) := fun _ _ h =>
  Multiplicative.ofAdd.injective (τ.symm.injective (Subtype.ext h))

theorem y2l_el_eq_one_iff (c : Fin 3 → ZMod 4) : y2l_el τ c = 1 ↔ c = 0 := by
  rw [← y2l_el_zero τ]
  exact (y2l_el_injective τ).eq_iff

theorem y2l_el_toAdd (m : M) : y2l_el τ (Multiplicative.toAdd (τ m)) = m := by
  simp only [y2l_el, ofAdd_toAdd, MulEquiv.symm_apply_apply]

theorem y2l_exists_el {x : X} (hx : x ∈ M) : ∃ c, y2l_el τ c = x :=
  ⟨Multiplicative.toAdd (τ ⟨x, hx⟩), y2l_el_toAdd τ ⟨x, hx⟩⟩

include τ in
theorem y2l_comm {a b : X} (ha : a ∈ M) (hb : b ∈ M) : a * b = b * a := by
  obtain ⟨c, rfl⟩ := y2l_exists_el τ ha
  obtain ⟨d, rfl⟩ := y2l_exists_el τ hb
  rw [← y2l_el_add, ← y2l_el_add, add_comm]

variable [M.Normal]

@[expose] def y2l_conjAdd (x : X) : (Fin 3 → ZMod 4) →+ (Fin 3 → ZMod 4) where
  toFun c := Multiplicative.toAdd (τ (MulAut.conjNormal x⁻¹ (τ.symm (Multiplicative.ofAdd c))))
  map_zero' := by simp
  map_add' c d := by simp only [ofAdd_add, map_mul, toAdd_mul]

theorem y2l_el_conjAdd (x : X) (c : Fin 3 → ZMod 4) :
    y2l_el τ (y2l_conjAdd τ x c) = x⁻¹ * y2l_el τ c * x := by
  change y2l_el τ (Multiplicative.toAdd (τ _)) = _
  rw [y2l_el_toAdd, MulAut.conjNormal_apply, inv_inv]
  rfl

@[expose] noncomputable def y2l_rhoMat (x : X) : Matrix (Fin 3) (Fin 3) (ZMod 4) :=
  (LinearMap.toMatrix' ((y2l_conjAdd τ x).toZModLinearMap 4))ᵀ

theorem y2l_conj_el' (x : X) (c : Fin 3 → ZMod 4) :
    x⁻¹ * y2l_el τ c * x = y2l_el τ (c ᵥ* y2l_rhoMat τ x) := by
  rw [y2l_rhoMat, Matrix.vecMul_transpose, LinearMap.toMatrix'_mulVec,
    AddMonoidHom.coe_toZModLinearMap, y2l_el_conjAdd]

theorem y2l_mat_ext {A B : Matrix (Fin 3) (Fin 3) (ZMod 4)} (h : ∀ c, c ᵥ* A = c ᵥ* B) :
    A = B := by
  ext i j
  have := congrFun (h (Pi.single i 1)) j
  simpa only [Matrix.single_one_vecMul, Matrix.row_apply] using this

theorem y2l_rhoMat_eq_of {x : X} {N : Matrix (Fin 3) (Fin 3) (ZMod 4)}
    (h : ∀ c, x⁻¹ * y2l_el τ c * x = y2l_el τ (c ᵥ* N)) : y2l_rhoMat τ x = N :=
  y2l_mat_ext fun c => y2l_el_injective τ (by rw [← y2l_conj_el', h])

@[expose] noncomputable def y2l_rho : X →* Matrix (Fin 3) (Fin 3) (ZMod 4) where
  toFun := y2l_rhoMat τ
  map_one' := y2l_rhoMat_eq_of τ fun c => by rw [inv_one, one_mul, mul_one, Matrix.vecMul_one]
  map_mul' x y := y2l_rhoMat_eq_of τ fun c => by
    rw [← Matrix.vecMul_vecMul, ← y2l_conj_el', ← y2l_conj_el']
    group

theorem y2l_conj_el (x : X) (c : Fin 3 → ZMod 4) :
    x⁻¹ * y2l_el τ c * x = y2l_el τ (c ᵥ* y2l_rho τ x) :=
  y2l_conj_el' τ x c

theorem y2l_rho_eq_of {x : X} {N : Matrix (Fin 3) (Fin 3) (ZMod 4)}
    (h : ∀ c, x⁻¹ * y2l_el τ c * x = y2l_el τ (c ᵥ* N)) : y2l_rho τ x = N :=
  y2l_rhoMat_eq_of τ h

theorem y2l_rho_of_mem {x : X} (hx : x ∈ M) : y2l_rho τ x = 1 :=
  y2l_rho_eq_of τ fun c => by
    rw [Matrix.vecMul_one, y2l_comm τ (inv_mem hx) (y2l_el_mem τ c), inv_mul_cancel_right]

theorem y2l_rho_eq_one_iff (hC : centralizer (M : Set X) = M) {x : X} :
    y2l_rho τ x = 1 ↔ x ∈ M := by
  refine ⟨fun h => ?_, y2l_rho_of_mem τ⟩
  rw [← hC, Subgroup.mem_centralizer_iff]
  intro m hm
  obtain ⟨c, rfl⟩ := y2l_exists_el τ hm
  have h1 := y2l_conj_el τ x c
  rw [h, Matrix.vecMul_one] at h1
  calc y2l_el τ c * x = x * (x⁻¹ * y2l_el τ c * x) := by group
    _ = x * y2l_el τ c := by rw [h1]

@[expose] def y2l_rowAut (K : Matrix (Fin 3) (Fin 3) (ZMod 4)) (hK : K * K = 1) :
    Multiplicative (Fin 3 → ZMod 4) ≃* Multiplicative (Fin 3 → ZMod 4) where
  toFun c := Multiplicative.ofAdd (Multiplicative.toAdd c ᵥ* K)
  invFun c := Multiplicative.ofAdd (Multiplicative.toAdd c ᵥ* K)
  left_inv c := by simp [Matrix.vecMul_vecMul, hK]
  right_inv c := by simp [Matrix.vecMul_vecMul, hK]
  map_mul' c d := by simp [Matrix.add_vecMul]

theorem y2l_el_trans (K : Matrix (Fin 3) (Fin 3) (ZMod 4)) (hK : K * K = 1)
    (c : Fin 3 → ZMod 4) : y2l_el (τ.trans (y2l_rowAut K hK)) c = y2l_el τ (c ᵥ* K) :=
  rfl

theorem y2l_rho_trans (K : Matrix (Fin 3) (Fin 3) (ZMod 4)) (hK : K * K = 1) (x : X) :
    y2l_rho (τ.trans (y2l_rowAut K hK)) x = K * y2l_rho τ x * K :=
  y2l_rho_eq_of _ fun c => by
    rw [y2l_el_trans, y2l_el_trans, y2l_conj_el]
    congr 1
    simp only [Matrix.vecMul_vecMul, mul_assoc, hK, mul_one]

end CFSG.OddStandard.HigherRank.G2Three.Sec2
