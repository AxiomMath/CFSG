module

public import CFSG.CGT.Timmesfeld75.ListWCLinMain
import CFSG.RankThree.GF2n.Stroth80.Sec93TransvAlgebra

public section

namespace CFSG.ClassicalGroups.SpecialLinear

open Matrix CFSG.CGT.Timmesfeld75
open scoped MatrixGroups

variable {K : Type} [Field K]

private theorem eq_one_of_eq_smul_one_add_vecMulVec_of_mul_self [CharP K 2] {m : ℕ}
    (hm : 0 < m) {X : Matrix (Fin m) (Fin m) K} {μ : K} {c b : Fin m → K} (hb : b ⬝ᵥ c = 0)
    (hX : X = μ • (1 : Matrix (Fin m) (Fin m) K) + vecMulVec c b) (h2 : X * X = 1) : μ = 1 := by
  have h3 : (μ • (1 : Matrix (Fin m) (Fin m) K) + vecMulVec c b) *
      (μ • (1 : Matrix (Fin m) (Fin m) K) + vecMulVec c b) = 1 := by
    rw [← hX, h2]
  have h4 : (μ • (1 : Matrix (Fin m) (Fin m) K) + vecMulVec c b) *
      (μ • (1 : Matrix (Fin m) (Fin m) K) + vecMulVec c b) = (μ * μ) •
        (1 : Matrix (Fin m) (Fin m) K) := by
    rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.smul_mul, Matrix.one_mul,
      Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one,
      Matrix.vecMulVec_mul_vecMulVec, hb, zero_smul, vecMulVec_zero,
      smul_smul, add_zero, add_assoc, ← add_smul, CharTwo.add_self_eq_zero, zero_smul, add_zero]
  have h5 : μ * μ = 1 := by
    let i : Fin m := ⟨0, hm⟩
    have h6 := congrFun (congrFun (h4.symm.trans h3) i) i
    simpa [Matrix.smul_apply, Matrix.one_apply] using h6
  exact CFSG.CGT.Timmesfeld75.eq_one_of_mul_self_eq_one_char_two h5

theorem exists_eq_one_add_smul_vecMulVec_of_commute [CharP K 2] {m : ℕ}
    (hm : 2 ≤ m) {c a : Fin m → K} (hc : c ≠ 0) (ha : a ≠ 0) {u : SL(m, K)} (hu : u * u = 1)
    (hcen : ∀ x ∈ tvCenterSL c, Commute u x) (hax : ∀ x ∈ tvAxisSL a, Commute u x) :
    ∃ s : K, (u : Matrix (Fin m) (Fin m) K) = 1 + s • Matrix.vecMulVec c a := by
  have huM : (u : Matrix (Fin m) (Fin m) K) * (u : Matrix (Fin m) (Fin m) K) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, hu, Matrix.SpecialLinearGroup.coe_one]
  have hcommC : ∀ b : Fin m → K, b ⬝ᵥ c = 0 →
      (u : Matrix (Fin m) (Fin m) K) * (1 + Matrix.vecMulVec c b) =
        (1 + Matrix.vecMulVec c b) * (u : Matrix (Fin m) (Fin m) K) := by
    intro b hb
    have h := hcen (CFSG.CGT.Timmesfeld75.tvSL c b hb) ⟨b, hb, rfl⟩
    exact congrArg (fun t : SL(m, K) => (t : Matrix (Fin m) (Fin m) K)) h.eq
  have hcommA : ∀ v : Fin m → K, a ⬝ᵥ v = 0 →
      (u : Matrix (Fin m) (Fin m) K) * (1 + Matrix.vecMulVec v a) =
        (1 + Matrix.vecMulVec v a) * (u : Matrix (Fin m) (Fin m) K) := by
    intro v hv
    have h := hax (CFSG.CGT.Timmesfeld75.tvSL v a hv) ⟨v, hv, rfl⟩
    exact congrArg (fun t : SL(m, K) => (t : Matrix (Fin m) (Fin m) K)) h.eq
  obtain ⟨μ, b, hb, hU⟩ :=
    CFSG.RankThree.GF2n.Stroth80.eq_smul_one_add_vecMulVec_of_commute_center hm hc hcommC
  obtain ⟨μ', w, hw, hU'⟩ :=
    CFSG.RankThree.GF2n.Stroth80.eq_smul_one_add_vecMulVec_of_commute_axis hm ha hcommA
  have hμ : μ = 1 := eq_one_of_eq_smul_one_add_vecMulVec_of_mul_self (by omega) hb hU huM
  have hμ' : μ' = 1 := eq_one_of_eq_smul_one_add_vecMulVec_of_mul_self (by omega) hw hU' huM
  rw [hμ, one_smul] at hU
  rw [hμ', one_smul] at hU'
  have hA : Matrix.vecMulVec c b = Matrix.vecMulVec w a :=
    add_left_cancel (hU.symm.trans hU')
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hc
  have hj' : c j ≠ 0 := by simpa using hj
  have hb_eq : b = (w j / c j) • a := by
    funext k
    have h1 := congrFun₂ hA j k
    simp only [Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul] at h1 ⊢
    rw [div_mul_eq_mul_div, eq_div_iff hj']
    rw [mul_comm (b k), h1]
  refine ⟨w j / c j, ?_⟩
  rw [hU, hb_eq, Matrix.vecMulVec_smul]

end CFSG.ClassicalGroups.SpecialLinear
