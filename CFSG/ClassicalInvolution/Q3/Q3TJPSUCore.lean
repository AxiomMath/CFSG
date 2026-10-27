module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherOrthogonality
public import CFSG.LocalAnalysis.ComponentInitial.FieldFiniteAutomorphism
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherSemilinearData
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {K : Type} [Field K] {r ε : ℕ}

theorem ringEquiv_sq_eq_one_of_card_nine (hK : Nat.card K = 9) (σ : K ≃+* K) : σ ^ 2 = 1 := by
  obtain ⟨-, -, -, -, hcard, -⟩ := finite_field_automorphism_fixed_field_cardinality (F := K)
    Nat.prime_three (n := 2) (by norm_num) (by rw [hK]; norm_num)
  have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  rw [← hcard]
  exact pow_card_eq_one'

theorem semiGL_pow_of_right_eq_one {ι : Type} [Fintype ι] [DecidableEq ι] (y : SemiGL ι K)
    (hy : y.right = 1) (k : ℕ) : (y ^ k).left = y.left ^ k ∧ (y ^ k).right = 1 := by
  induction k with
  | zero => exact ⟨rfl, rfl⟩
  | succ k ih =>
    refine ⟨?_, ?_⟩
    · rw [pow_succ, SemidirectProduct.mul_left, ih.1, ih.2, map_one, MulAut.one_apply, pow_succ]
    · rw [pow_succ, SemidirectProduct.mul_right, ih.2, hy, one_mul]

theorem similitude_pow {ι : Type} [Fintype ι] [DecidableEq ι] (bar : K →+* K)
    (J : Matrix ι ι K) {B : GL ι K} {μ : K}
    (hB : ((B : Matrix ι ι K).map bar)ᵀ * J * (B : Matrix ι ι K) = μ • J) (k : ℕ) :
    (((B ^ k : GL ι K) : Matrix ι ι K).map bar)ᵀ * J * ((B ^ k : GL ι K) : Matrix ι ι K) =
      μ ^ k • J := by
  induction k with
  | zero =>
    simp only [pow_zero, Units.val_one, Matrix.map_one _ (map_zero bar) (map_one bar),
      transpose_one, Matrix.one_mul, Matrix.mul_one, one_smul]
  | succ k ih =>
    rw [pow_succ, Units.val_mul, Matrix.map_mul, transpose_mul]
    calc ((B : Matrix ι ι K).map bar)ᵀ * (((B ^ k : GL ι K) : Matrix ι ι K).map bar)ᵀ * J *
          (((B ^ k : GL ι K) : Matrix ι ι K) * (B : Matrix ι ι K))
        = ((B : Matrix ι ι K).map bar)ᵀ * ((((B ^ k : GL ι K) : Matrix ι ι K).map bar)ᵀ * J *
          ((B ^ k : GL ι K) : Matrix ι ι K)) * (B : Matrix ι ι K) := by
          simp only [Matrix.mul_assoc]
      _ = μ ^ k • (((B : Matrix ι ι K).map bar)ᵀ * J * (B : Matrix ι ι K)) := by
          rw [ih, Matrix.mul_smul, Matrix.smul_mul]
      _ = μ ^ (k + 1) • J := by rw [hB, smul_smul, pow_succ]

theorem semilinearPointAction_pow_sixteen_mem {h : UnitaryFieldData 3 1 K}
    (x : semilinearSimilitudes h r ε) :
    semilinearPointAction h r ε x ^ 16 ∈ (hypProjLineAction h r ε).range := by
  have hK : Nat.card K = 9 := by rw [h.card]; norm_num
  have : Finite K := h.finite
  have : Fintype K := Fintype.ofFinite K
  set y : semilinearSimilitudes h r ε := x ^ 2 with hy
  have hyr : (y : SemiGL (HypIndex r ε) K).right = 1 := by
    rw [hy, SubgroupClass.coe_pow, ← SemidirectProduct.rightHom_eq_right, map_pow,
      SemidirectProduct.rightHom_eq_right]
    exact ringEquiv_sq_eq_one_of_card_nine hK _
  obtain ⟨μ, hμ0, hμ, hsim⟩ := y.2
  have hμ2 : μ ^ 2 = 1 := by
    have h3 : μ ^ 3 = μ := by
      have := hμ
      rwa [UnitaryFieldData.bar_apply, pow_one] at this
    exact mul_left_cancel₀ hμ0 (by rw [← pow_succ', h3, mul_one])
  set B := (y : SemiGL (HypIndex r ε) K).left with hB
  have hB8 : (B ^ 8 : GL (HypIndex r ε) K) ∈ hypSU h r ε := by
    rw [mem_hypSU]
    refine ⟨?_, ?_⟩
    · rw [similitude_pow h.bar (hypGram r ε K) hsim 8]
      rw [show μ ^ 8 = (μ ^ 2) ^ 4 by ring, hμ2, one_pow, one_smul]
    · rw [Units.val_pow_eq_pow_val, Matrix.det_pow]
      have hd : (B : Matrix (HypIndex r ε) (HypIndex r ε) K).det ≠ 0 :=
        (Matrix.GeneralLinearGroup.det B).ne_zero
      have h8 := FiniteField.pow_card_sub_one_eq_one _ hd
      rwa [← Nat.card_eq_fintype_card, hK] at h8
  have hpow := semiGL_pow_of_right_eq_one (y : SemiGL (HypIndex r ε) K) hyr 8
  refine ⟨hypProj h r ε ⟨_, hB8⟩, ?_⟩
  have hx16 : x ^ 16 = y ^ 8 := by rw [hy, ← pow_mul]
  rw [← map_pow, hx16]
  refine Equiv.ext fun L => Subtype.ext ?_
  rw [hypProjLineAction_hypProj_apply, semilinearPointAction_apply, SubgroupClass.coe_pow,
    hpow.1, hpow.2, coordImage_one]
  rfl

end CFSG.ClassicalInvolution.Q3.Q3T
