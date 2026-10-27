module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddQuadraticWitt

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalSixSimilarity

open QuadraticMap CatalogueBOddQuadratic

universe u v w

variable {K : Type u} [Field K]

theorem singular_subspace_of_hyperbolic_isometry
    {V : Type v} [AddCommGroup V] [Module K V]
    {W : Type w} [AddCommGroup W] [Module K W]
    {Q : QuadraticForm K V} {R : QuadraticForm K W} {m : ℕ}
    (e : Q.IsometryEquiv ((hyperbolicSumForm K m).prod R))
    (r : ℕ) (hr : r ≤ m) :
    ∃ S : Submodule K V, Module.finrank K S = r ∧ ∀ x ∈ S, Q x = 0 := by
  let f : (Fin r → K) →ₗ[K] V :=
    { toFun := fun x => e.symm
        (fun i => (if h : i.val < r then x ⟨i.val, h⟩ else 0, 0), 0)
      map_add' := by
        intro x y
        rw [← map_add]
        congr 1
        apply Prod.ext
        · funext i
          apply Prod.ext
          · by_cases h : i.val < r <;> simp [h]
          · simp
        · simp
      map_smul' := by
        intro a x
        rw [← map_smul]
        congr 1
        apply Prod.ext
        · funext i
          apply Prod.ext
          · by_cases h : i.val < r <;> simp [h]
          · simp
        · simp }
  have hf : Function.Injective f := by
    intro x y h
    funext i
    have hi := congrArg (fun v => ((e v).1 (Fin.castLE hr i)).1) h
    simpa [f, Fin.castLE] using hi
  refine ⟨f.range, ?_, ?_⟩
  · rw [LinearMap.finrank_range_of_inj hf]
    simp
  · rintro _ ⟨x, rfl⟩
    change Q (e.symm _) = 0
    rw [e.symm.map_app, QuadraticMap.prod_apply, map_zero, add_zero,
      hyperbolicSumForm_apply]
    simp

variable [Finite K] {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem exists_two_planes_binary_isometry (hodd : Odd (Nat.card K))
    (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (hdim : Module.finrank K V = 6)
    (hno : ¬ ∃ S : Submodule K V, Module.finrank K S = 3 ∧ ∀ x ∈ S, Q x = 0) :
    ∃ w : Fin 2 → Kˣ, (weightedSumSquares K w).Anisotropic ∧
      Nonempty (Q.IsometryEquiv
        ((hyperbolicSumForm K 2).prod (weightedSumSquares K w))) := by
  obtain ⟨m, k, w, hk, ha, hrank, ⟨e⟩⟩ := exists_hyperbolic_decomposition hodd Q hQ
  have hm : m < 3 := by
    by_contra h
    exact hno (singular_subspace_of_hyperbolic_isometry e 3 (by omega))
  have hm' : m = 2 := by omega
  have hk' : k = 2 := by omega
  subst m
  subst k
  exact ⟨w, ha, ⟨e⟩⟩

end CFSG.ComponentClassification.CatalogueBOrthogonalSixSimilarity
