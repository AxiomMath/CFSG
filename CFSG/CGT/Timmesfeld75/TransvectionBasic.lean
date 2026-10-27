module

public import CFSG.CGT.Timmesfeld75.Defs

public section

namespace CFSG.CGT.Timmesfeld75

open Matrix
open scoped MatrixGroups

variable {m : ℕ}

section General

variable {K : Type*} [Field K]

@[expose] def dotLK (a : Fin m → K) : (Fin m → K) →ₗ[K] K where
  toFun x := a ⬝ᵥ x
  map_add' := dotProduct_add a
  map_smul' c x := by simp [dotProduct_smul]

theorem exists_dot_eq_one_K {a : Fin m → K} (ha : a ≠ 0) : ∃ x, a ⬝ᵥ x = 1 := by
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
    by_contra hc
    push Not at hc
    exact ha (funext hc)
  refine ⟨Pi.single i (a i)⁻¹, ?_⟩
  rw [dotProduct_single, mul_inv_cancel₀ hi]

theorem finrank_ker_dotLK {a : Fin m → K} (ha : a ≠ 0) :
    Module.finrank K (LinearMap.ker (dotLK a)) + 1 = m := by
  have hr : LinearMap.range (dotLK a) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro c
    obtain ⟨x, hx⟩ := exists_dot_eq_one_K ha
    exact ⟨c • x, by simp [dotLK, hx]⟩
  have h1 := LinearMap.finrank_range_add_finrank_ker (dotLK a)
  rw [hr, finrank_top, Module.finrank_self, Module.finrank_fin_fun] at h1
  omega

end General

theorem exists_sl_of_linearEquiv (g : (Fin m → ZMod 2) ≃ₗ[ZMod 2] (Fin m → ZMod 2)) :
    ∃ s : SL(m, ZMod 2), ∀ x, (s : Matrix (Fin m) (Fin m) (ZMod 2)) *ᵥ x = g x := by
  let M := LinearMap.toMatrix' (g : (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2))
  have hM : M * LinearMap.toMatrix'
      (g.symm : (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2)) = 1 := by
    rw [← LinearMap.toMatrix'_comp]
    have : (g : (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2)) ∘ₗ
        (g.symm : (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2)) = LinearMap.id := by
      ext x
      simp
    rw [this, LinearMap.toMatrix'_id]
  have hdet : M.det = 1 := by
    have h := congrArg Matrix.det hM
    rw [Matrix.det_mul, Matrix.det_one] at h
    have key : ∀ d e : ZMod 2, d * e = 1 → d = 1 := by decide
    exact key _ _ h
  exact ⟨⟨M, hdet⟩, fun x => by simp [M]⟩

end CFSG.CGT.Timmesfeld75
