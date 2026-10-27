module

public import CFSG.Open.StatedDefs

public section

open Matrix CFSG.Open

namespace CFSG.ClassicalGroups.Symplectic

namespace TransvectionCentralizer

variable {K : Type} [Field K] {m : ℕ}

private theorem dot_apply_of_isometry {ι : Type} [Fintype ι] [DecidableEq ι]
    {J A : Matrix ι ι K} (h : Aᵀ * J * A = J) (x y : ι → K) :
    (A *ᵥ x) ⬝ᵥ J *ᵥ (A *ᵥ y) = x ⬝ᵥ J *ᵥ y := by
  calc (A *ᵥ x) ⬝ᵥ J *ᵥ (A *ᵥ y) = (A *ᵥ x) ⬝ᵥ (J * A) *ᵥ y := by rw [Matrix.mulVec_mulVec]
    _ = ((A *ᵥ x) ᵥ* (J * A)) ⬝ᵥ y := Matrix.dotProduct_mulVec _ _ _
    _ = (x ᵥ* (Aᵀ * (J * A))) ⬝ᵥ y := by rw [← Matrix.vecMul_transpose, Matrix.vecMul_vecMul]
    _ = (x ᵥ* J) ⬝ᵥ y := by rw [← Matrix.mul_assoc, h]
    _ = x ⬝ᵥ J *ᵥ y := (Matrix.dotProduct_mulVec _ _ _).symm

end TransvectionCentralizer

open TransvectionCentralizer

theorem mulVec_eq_of_commute_transvection {K : Type} [Field K] [CharP K 2] {ι : Type}
    [Fintype ι] [DecidableEq ι] {J t g : Matrix ι ι K} (hJa : ∀ v, v ⬝ᵥ J *ᵥ v = 0)
    (hJn : ∀ x, (∀ y, x ⬝ᵥ J *ᵥ y = 0) → x = 0) (ht : tᵀ * J * t = J)
    (hg : gᵀ * J * g = J) (hrk : (t - 1).rank = 1) (hcomm : g * t = t * g)
    (x : ι → K) : g *ᵥ ((t - 1) *ᵥ x) = (t - 1) *ᵥ x := by
  set N : Matrix ι ι K := t - 1 with hN
  have htN : ∀ y, t *ᵥ y = y + N *ᵥ y := fun y => by
    rw [hN, Matrix.sub_mulVec, Matrix.one_mulVec]; abel
  obtain ⟨u, hu0, hu⟩ : ∃ u : ι → K, u ≠ 0 ∧ ∀ y, ∃ c : K, N *ᵥ y = c • u := by
    unfold Matrix.rank at hrk
    obtain ⟨v, hv0, hv⟩ := finrank_eq_one_iff'.mp hrk
    refine ⟨(v : ι → K), fun h => hv0 (Subtype.ext h), fun y => ?_⟩
    obtain ⟨c, hc⟩ := hv ⟨N *ᵥ y, ⟨y, rfl⟩⟩
    exact ⟨c, (congrArg Subtype.val hc).symm⟩
  choose a ha using hu
  have hβneg : ∀ x y : ι → K, x ⬝ᵥ J *ᵥ y = -(y ⬝ᵥ J *ᵥ x) := fun x y => by
    have h1 := hJa (x + y)
    simp only [Matrix.mulVec_add, dotProduct_add, add_dotProduct, hJa x, hJa y] at h1
    linear_combination h1
  have hrel : ∀ x y : ι → K, a y * (x ⬝ᵥ J *ᵥ u) + a x * (u ⬝ᵥ J *ᵥ y) = 0 := fun x y => by
    have h1 := dot_apply_of_isometry ht x y
    rw [htN x, htN y, Matrix.mulVec_add, ha x, ha y] at h1
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, add_dotProduct,
      smul_dotProduct, dotProduct_smul, smul_eq_mul, hJa u] at h1
    linear_combination h1
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, x₀ ⬝ᵥ J *ᵥ u ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hu0 (hJn u fun y => by rw [hβneg, hcon y, neg_zero])
  have hform : ∀ y, a y = -(a x₀ / (x₀ ⬝ᵥ J *ᵥ u)) * (u ⬝ᵥ J *ᵥ y) := fun y => by
    have h1 := hrel x₀ y
    field_simp
    linear_combination h1
  obtain ⟨y₁, hy₁⟩ : ∃ y₁, a y₁ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hall : ∀ y, N *ᵥ y = 0 := fun y => by rw [ha y, hcon y, zero_smul]
    have hN0 : N = 0 := by
      ext i j
      have := congrFun (hall (Pi.single j 1)) i
      simpa [Matrix.mulVec_single_one] using this
    rw [hN0, Matrix.rank_zero] at hrk
    exact absurd hrk (by norm_num)
  have hc'0 : -(a x₀ / (x₀ ⬝ᵥ J *ᵥ u)) ≠ 0 := fun h => hy₁ (by rw [hform y₁, h, zero_mul])
  have hβ1 : u ⬝ᵥ J *ᵥ y₁ ≠ 0 := fun h => hy₁ (by rw [hform y₁, h, mul_zero])
  have hgN : g * N = N * g := by
    rw [hN, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, hcomm]
  have hcommvec : ∀ y, g *ᵥ (N *ᵥ y) = N *ᵥ (g *ᵥ y) := fun y => by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hgN]
  obtain ⟨μ, hμ⟩ : ∃ μ : K, g *ᵥ u = μ • u := by
    refine ⟨a (g *ᵥ y₁) / a y₁, ?_⟩
    have h1 := hcommvec y₁
    rw [ha y₁, ha, Matrix.mulVec_smul] at h1
    calc g *ᵥ u = (a y₁)⁻¹ • (a y₁ • (g *ᵥ u)) := by rw [smul_smul, inv_mul_cancel₀ hy₁, one_smul]
      _ = (a y₁)⁻¹ • (a (g *ᵥ y₁) • u) := by rw [h1]
      _ = (a (g *ᵥ y₁) / a y₁) • u := by rw [smul_smul, div_eq_inv_mul]
  have hag : ∀ y, a (g *ᵥ y) = μ * a y := fun y => by
    have h1 := hcommvec y
    rw [ha y, ha, Matrix.mulVec_smul, hμ, smul_smul] at h1
    have h2 := smul_left_injective K hu0 h1
    rw [← h2]; ring
  have hβg : ∀ y, u ⬝ᵥ J *ᵥ (g *ᵥ y) = μ * (u ⬝ᵥ J *ᵥ y) := fun y => by
    have h1 := hag y
    rw [hform (g *ᵥ y), hform y] at h1
    have h2 : (-(a x₀ / (x₀ ⬝ᵥ J *ᵥ u))) * (u ⬝ᵥ J *ᵥ (g *ᵥ y)) =
        (-(a x₀ / (x₀ ⬝ᵥ J *ᵥ u))) * (μ * (u ⬝ᵥ J *ᵥ y)) := by rw [h1]; ring
    exact mul_left_cancel₀ hc'0 h2
  have hμ2 : μ * μ = 1 := by
    have h1 := dot_apply_of_isometry hg u y₁
    rw [hμ, smul_dotProduct, smul_eq_mul, hβg] at h1
    have h2 : (μ * μ) * (u ⬝ᵥ J *ᵥ y₁) = 1 * (u ⬝ᵥ J *ᵥ y₁) := by linear_combination h1
    exact mul_right_cancel₀ hβ1 h2
  have hμ1 : μ = 1 := by
    rcases mul_self_eq_one_iff.1 hμ2 with h | h
    · exact h
    · rw [h, CharTwo.neg_eq]
  rw [ha x, Matrix.mulVec_smul, hμ, hμ1, one_smul]

end CFSG.ClassicalGroups.Symplectic
