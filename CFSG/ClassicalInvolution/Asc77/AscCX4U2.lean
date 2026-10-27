module

public import CFSG.ClassicalInvolution.Asc77.AscCX4L1
public import CFSG.ClassicalInvolution.ModelFacts.Orth15OuterU4

public section

namespace CFSG.ClassicalInvolution.Asc77.CX.CX4.U4

open Matrix CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.ModelFacts.UnitaryAut CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.ClassicalInvolution.ModelFacts.Orth15.ChainU
  CFSG.ClassicalGroups.Unitary CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterU4

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem sq_eq_one_of_norm (hq1 : p ^ f % 4 = 1) {t : K}
    (hN : unitaryInvolution K p f t * t = 1) : ∀ {k : ℕ}, t ^ (2 ^ k) = 1 → t ^ 2 = 1
  | 0, h => by
    rw [pow_zero, pow_one] at h
    rw [h, one_pow]
  | k + 1, h => by
    have hN2 : unitaryInvolution K p f (t ^ 2) * t ^ 2 = 1 := by
      rw [map_pow, ← mul_pow, hN, one_pow]
    have h' : (t ^ 2) ^ (2 ^ k) = 1 := by
      rw [← pow_mul, ← pow_succ']
      exact h
    have h4 : (t ^ 2) ^ 2 = 1 := sq_eq_one_of_norm hq1 hN2 h'
    have hq : t ^ (p ^ f + 1) = 1 := by
      rw [pow_succ, ← unitaryInvolution_apply]
      exact hN
    obtain ⟨j, hj⟩ : ∃ j, p ^ f + 1 = 4 * j + 2 := ⟨p ^ f / 4, by omega⟩
    rw [hj, pow_add, pow_mul, show t ^ 4 = (t ^ 2) ^ 2 by ring, h4, one_pow, one_mul] at hq
    exact hq

omit [Finite K] in
theorem diag_pow (a b : K) (N : ℕ) :
    (!![a, 0, 0, 0; 0, a, 0, 0; 0, 0, b, 0; 0, 0, 0, b] : Matrix (Fin 4) (Fin 4) K) ^ N =
      !![a ^ N, 0, 0, 0; 0, a ^ N, 0, 0; 0, 0, b ^ N, 0; 0, 0, 0, b ^ N] := by
  rw [L4.diag4_eq, L4.diag4_eq, Matrix.diagonal_pow]
  congr 1
  ext i
  fin_cases i <;> rfl

theorem lift_pow {X : Type} [Group X] (θ : Su K p f 4 →* X) (s : MulAut X)
    (α : Monoid.End (Su K p f 4)) (hα : ∀ x, θ (α x) = s (θ x)) (N : ℕ) :
    ∀ x, θ ((α ^ N) x) = (s ^ N) (θ x) := by
  induction N with
  | zero => intro x; rfl
  | succ N ih =>
    intro x
    rw [pow_succ, pow_succ]
    show θ ((α ^ N) (α x)) = (s ^ N * s) (θ x)
    rw [ih, hα]
    rfl

omit [Finite K] in
theorem diag_mul_diag (a b c d : K) :
    (!![a, 0, 0, 0; 0, a, 0, 0; 0, 0, b, 0; 0, 0, 0, b] : Matrix (Fin 4) (Fin 4) K) *
      !![c, 0, 0, 0; 0, c, 0, 0; 0, 0, d, 0; 0, 0, 0, d] =
        !![a * c, 0, 0, 0; 0, a * c, 0, 0; 0, 0, b * d, 0; 0, 0, 0, b * d] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]

theorem suMat_pow_diag (α : Monoid.End (Su K p f 4)) {a b : K}
    (hα : ∀ x, suMat (α x) = !![a, 0, 0, 0; 0, a, 0, 0; 0, 0, b, 0; 0, 0, 0, b] * suMat x *
      !![a⁻¹, 0, 0, 0; 0, a⁻¹, 0, 0; 0, 0, b⁻¹, 0; 0, 0, 0, b⁻¹]) (N : ℕ) :
    ∀ x, suMat ((α ^ N) x) = !![a ^ N, 0, 0, 0; 0, a ^ N, 0, 0; 0, 0, b ^ N, 0; 0, 0, 0, b ^ N] *
      suMat x * !![(a ^ N)⁻¹, 0, 0, 0; 0, (a ^ N)⁻¹, 0, 0; 0, 0, (b ^ N)⁻¹, 0;
        0, 0, 0, (b ^ N)⁻¹] := by
  induction N with
  | zero =>
    intro x
    simp only [pow_zero, inv_one]
    rw [show (!![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] : Matrix (Fin 4) (Fin 4) K) = 1
      by ext i j; fin_cases i <;> fin_cases j <;> rfl, Matrix.one_mul, Matrix.mul_one]
    rfl
  | succ N ih =>
    intro x
    rw [pow_succ]
    show suMat ((α ^ N) (α x)) = _
    rw [ih, hα]
    calc !![a ^ N, 0, 0, 0; 0, a ^ N, 0, 0; 0, 0, b ^ N, 0; 0, 0, 0, b ^ N] *
          (!![a, 0, 0, 0; 0, a, 0, 0; 0, 0, b, 0; 0, 0, 0, b] * suMat x *
            !![a⁻¹, 0, 0, 0; 0, a⁻¹, 0, 0; 0, 0, b⁻¹, 0; 0, 0, 0, b⁻¹]) *
          !![(a ^ N)⁻¹, 0, 0, 0; 0, (a ^ N)⁻¹, 0, 0; 0, 0, (b ^ N)⁻¹, 0; 0, 0, 0, (b ^ N)⁻¹]
        = (!![a ^ N, 0, 0, 0; 0, a ^ N, 0, 0; 0, 0, b ^ N, 0; 0, 0, 0, b ^ N] *
            !![a, 0, 0, 0; 0, a, 0, 0; 0, 0, b, 0; 0, 0, 0, b]) * suMat x *
          (!![a⁻¹, 0, 0, 0; 0, a⁻¹, 0, 0; 0, 0, b⁻¹, 0; 0, 0, 0, b⁻¹] *
            !![(a ^ N)⁻¹, 0, 0, 0; 0, (a ^ N)⁻¹, 0, 0; 0, 0, (b ^ N)⁻¹, 0;
              0, 0, 0, (b ^ N)⁻¹]) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [diag_mul_diag, diag_mul_diag, ← pow_succ, ← pow_succ, ← mul_inv,
          ← mul_inv, ← pow_succ', ← pow_succ']

theorem diag_two_elem (hK : Nat.card K = (p ^ f) ^ 2) (hq1 : p ^ f % 4 = 1) {X : Type}
    [Group X] (θ : Su K p f 4 →* X) (hθ : Function.Surjective θ)
    (hker : θ.ker ≤ Subgroup.center (Su K p f 4)) (s : MulAut X) (α : Su K p f 4 →* Su K p f 4)
    (hα : ∀ x, θ (α x) = s (θ x)) {a b : K} (ha : a ≠ 0) (hb : b ≠ 0)
    (hNa : unitaryInvolution K p f a * a = 1) (hNb : unitaryInvolution K p f b * b = 1)
    (hαM : ∀ x, suMat (α x) = !![a, 0, 0, 0; 0, a, 0, 0; 0, 0, b, 0; 0, 0, 0, b] * suMat x *
      !![a⁻¹, 0, 0, 0; 0, a⁻¹, 0, 0; 0, 0, b⁻¹, 0; 0, 0, 0, b⁻¹]) {k : ℕ} (hk : s ^ (2 ^ k) = 1) :
    s = 1 ∨ s = MulAut.conj (θ (rootInvSU K p f (show 2 ≤ 4 by norm_num))) := by
  have hσ : IsUnitaryInvolution (unitaryInvolution K p f) :=
    isUnitaryInvolution_unitaryInvolution hK
  set α' : Monoid.End (Su K p f 4) := α with hα'
  have hlift := lift_pow θ s α' hα (2 ^ k)
  have hmat := suMat_pow_diag α' hαM (2 ^ k)
  have hc : (α' ^ (2 ^ k)) (mixSU K p f) * (mixSU K p f)⁻¹ ∈ Subgroup.center (Su K p f 4) :=
    hker (by rw [MonoidHom.mem_ker, map_mul, map_inv, hlift, hk, MulAut.one_apply,
      mul_inv_cancel])
  obtain ⟨u, hu⟩ := Phan.exists_scalar_of_mem_center hσ (by norm_num : 3 ≤ 4) hc
  have h1 : suMat ((α' ^ (2 ^ k)) (mixSU K p f)) = (u : K) • suMat (mixSU K p f) := by
    calc suMat ((α' ^ (2 ^ k)) (mixSU K p f)) =
          suMat ((α' ^ (2 ^ k)) (mixSU K p f) * (mixSU K p f)⁻¹) * suMat (mixSU K p f) := by
          rw [suMat_mul, Matrix.mul_assoc, suMat_inv_mul_suMat, Matrix.mul_one]
      _ = (u : K) • suMat (mixSU K p f) := by
          show ((_ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * _ = _
          rw [hu, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul,
            Matrix.one_mul]
  rw [hmat, suMat_mixSU] at h1
  have e11 := congrFun (congrFun h1 1) 1
  have e02 := congrFun (congrFun h1 0) 2
  simp [Matrix.mul_apply, Fin.sum_univ_four] at e11 e02
  have haN : a ^ 2 ^ k ≠ 0 := pow_ne_zero _ ha
  have hbN : b ^ 2 ^ k ≠ 0 := pow_ne_zero _ hb
  rw [mul_inv_cancel₀ haN] at e11
  have hab : (a / b) ^ (2 ^ k) = 1 := by
    rw [div_pow, ← e11] at *
    rw [div_eq_mul_inv]
    exact e02
  have hNab : unitaryInvolution K p f (a / b) * (a / b) = 1 := by
    rw [map_div₀, div_mul_div_comm, hNa, hNb, div_one]
  have ht := sq_eq_one_of_norm hq1 hNab hab
  have h' : (a / b - 1) * (a / b + 1) = 0 := by linear_combination ht
  rcases mul_eq_zero.mp h' with h | h
  · left
    have hab' : a = b := by
      have := sub_eq_zero.mp h
      rwa [div_eq_one_iff_eq hb] at this
    subst hab'
    ext y
    obtain ⟨x, rfl⟩ := hθ y
    rw [← hα, MulAut.one_apply]
    congr 1
    apply suMat_injective
    rw [hαM x]
    exact conj_scalar4 ha (suMat x)
  · right
    have hab' : b = -a := by
      have h3 : a / b = -1 := by linear_combination h
      rw [div_eq_iff hb] at h3
      linear_combination h3
    subst hab'
    ext y
    obtain ⟨x, rfl⟩ := hθ y
    rw [← hα, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
    congr 1
    apply suMat_injective
    rw [hαM x, suMat_mul, suMat_mul, suMat_rootInvSU_inv_four, suMat_rootInvSU_four, inv_neg]
    exact conj_neg4 ha (suMat x)

end CFSG.ClassicalInvolution.Asc77.CX.CX4.U4
