module

public import CFSG.LieType.Ree.SuzukiLocalData
public import CFSG.LieType.Ree.SuzukiMatrixIdentities

public section

namespace CFSG.LieType.Ree

open CFSG.Blueprint Matrix
open scoped LinearAlgebra.Projectivization

variable {a : ℕ} {K : Type} [Field K]

theorem exists_mulVec_eq_of_smul_mk_eq (A : GL (Fin 4) K) {w : Fin 4 → K} (hw : w ≠ 0)
    (h : A • Projectivization.mk K w hw = Projectivization.mk K w hw) :
    ∃ k : K, ∀ i, (A : Matrix (Fin 4) (Fin 4) K) i 0 * w 0 +
      (A : Matrix (Fin 4) (Fin 4) K) i 1 * w 1 + (A : Matrix (Fin 4) (Fin 4) K) i 2 * w 2 +
        (A : Matrix (Fin 4) (Fin 4) K) i 3 * w 3 = k * w i := by
  rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff] at h
  obtain ⟨k, hk⟩ := h
  refine ⟨k, fun i => ?_⟩
  have hi := congrFun hk i
  change (k : K) * w i = ((A : Matrix (Fin 4) (Fin 4) K) *ᵥ w) i at hi
  rw [hi, mulVec, dotProduct, Fin.sum_univ_four]

theorem exists_pow_theta_ne (ha : 1 ≤ a) [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ∃ x : K, x ^ 2 ^ (a + 1) ≠ x := by
  obtain ⟨-, -, hθθ⟩ := suzuki_frob_data a hK
  by_contra h
  push Not at h
  have h01 : ∀ x : K, x = 0 ∨ x = 1 := fun x => by
    have hx : x * (x - 1) = 0 := by
      have : x ^ 2 = x := by rw [← hθθ x, h x, h x]
      linear_combination this
    rcases mul_eq_zero.1 hx with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.1 h)
  have hsurj : Function.Surjective fun b : Bool => if b then (1 : K) else 0 := fun x => by
    rcases h01 x with rfl | rfl
    · exact ⟨false, by simp⟩
    · exact ⟨true, by simp⟩
  have hle : Nat.card K ≤ 2 := by
    simpa using Nat.card_le_card_of_surjective _ hsurj
  have h8 : 2 ^ 3 ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem suzuki_ovoid_scalar_kernel (ha : 1 ≤ a) [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1))
    (A : GL (Fin 4) K) (hA : ∀ x ∈ suzukiOmega a K, A • x = x) :
    ∃ c : K, (A : Matrix (Fin 4) (Fin 4) K) = Matrix.scalar (Fin 4) c := by
  have hθ0 : 2 ^ (a + 1) ≠ 0 := pow_ne_zero _ two_ne_zero
  obtain ⟨x, hx⟩ := exists_pow_theta_ne ha hK
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hx (zero_pow hθ0)
  have hx1 : x - 1 ≠ 0 := by
    intro h
    rw [sub_eq_zero.1 h, one_pow] at hx
    exact hx rfl
  have hxθ : x - x ^ 2 ^ (a + 1) ≠ 0 := fun h => hx (sub_eq_zero.1 h).symm
  have hfix := fun u v =>
    exists_mulVec_eq_of_smul_mk_eq A _ (hA _ (suzukiLine_mem_suzukiOmega a K u v))
  obtain ⟨k4, h4⟩ := exists_mulVec_eq_of_smul_mk_eq A _ (hA _ (suzukiInfty_mem_suzukiOmega a K))
  obtain ⟨k1, h1⟩ := hfix 0 0
  obtain ⟨k3, h3⟩ := hfix 0 1
  obtain ⟨k3', h3'⟩ := hfix 0 x
  obtain ⟨k2, h2⟩ := hfix 1 0
  obtain ⟨k2', h2'⟩ := hfix x 0
  set M := (A : Matrix (Fin 4) (Fin 4) K)
  have hN : ∀ v : K, suzukiN a 0 v = v ^ 2 ^ (a + 1) := fun v => by
    simp [suzukiN]
  have hN' : ∀ u : K, suzukiN a u 0 = u ^ (2 ^ (a + 1) + 2) := fun u => by
    simp [suzukiN, zero_pow hθ0]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons, Fin.isValue] at h4 h1 h3 h3' h2 h2'
  have e03 := h4 0
  have e13 := h4 1
  have e23 := h4 2
  have e33 := h4 3
  have e00 := h1 0
  have e10 := h1 1
  have e20 := h1 2
  have e30 := h1 3
  simp [hN] at e03 e13 e23 e33 e00 e10 e20 e30
  have f0 := h3 0
  have f1 := h3 1
  have f2 := h3 2
  have f3 := h3 3
  have g0 := h3' 0
  have g2 := h3' 2
  have g3 := h3' 3
  simp [hN, e03, e13, e23, e33, e00, e10, e20, e30] at f0 f1 f2 f3 g0 g2 g3
  have hk3' : k3' = M 2 2 := (g2.resolve_right hx0).symm
  have h02 : M 0 2 = 0 := by
    have : M 0 2 * (x - 1) = 0 := by linear_combination g0 - f0 + hk3' + f2
    exact (mul_eq_zero.1 this).resolve_right hx1
  have h22 : M 2 2 = k1 := by linear_combination -f0 + f2 + h02
  have h33 : k4 = k1 := by
    have : (k1 - k4) * (x - x ^ 2 ^ (a + 1)) = 0 := by
      linear_combination g3 - x * f3 + x ^ 2 ^ (a + 1) * hk3' + x ^ 2 ^ (a + 1) * h22 +
        x * f2 - x * h22
    exact (sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hxθ)).symm
  have h32 : M 3 2 = 0 := by linear_combination f3 - f2 + h22 - h33
  have p0 := h2 0
  have p1 := h2 1
  have p2 := h2 2
  have p3 := h2 3
  have q0 := h2' 0
  have q1 := h2' 1
  simp [hN', e03, e13, e23, e33, e00, e10, e20, e30] at p0 p1 p2 p3 q0 q1
  have hk2' : k2' = M 1 1 := (q1.resolve_right hx0).symm
  have h01 : M 0 1 = 0 := by
    have : M 0 1 * (x - 1) = 0 := by linear_combination q0 - p0 + hk2' + p1
    exact (mul_eq_zero.1 this).resolve_right hx1
  have h11 : M 1 1 = k1 := by linear_combination -p0 + p1 + h01
  have h31 : M 3 1 = 0 := by linear_combination p3 - p1 + h11 - h33
  refine ⟨k1, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.scalar_apply, e03, e13, e23, e33, e00, e10, e20, e30, f1, p2, h02, h22, h33, h32,
      h01, h11, h31]

end CFSG.LieType.Ree
