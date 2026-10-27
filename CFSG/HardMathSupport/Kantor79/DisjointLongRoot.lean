module

public import CFSG.HardMathSupport.Kantor79.LongRootGroup

public section

namespace CFSG.HardMathSupport.Kantor79

open CFSG.HardMathSupport.GuralnickMalle QuadraticMap LinearMap Module

variable {K E : Type*} [Field K] [CharP K 2] [AddCommGroup E] [Module K E]

theorem siegelEquiv_toLin_eq_one_add_smul_rootEnd {Q : QuadraticForm K E} {a b : E}
    (ha : Q a = 0) (hb : Q b = 0) (hab : QuadraticMap.polarBilin Q a b = 0) (c : K) :
    (siegelEquiv Q a b ha hb hab c : E →ₗ[K] E) = 1 + c • rootEnd Q a b := by
  ext x
  change siegelLin Q a b c x = x + c • rootEnd Q a b x
  rw [siegelLin_apply, rootEnd_apply, smul_add]
  change x + c • polar Q x b • a + c • polar Q x a • b =
    x + (c • polar Q x b • a + c • polar Q x a • b)
  abel

theorem rootEnd_comp_eq_zero_of_orthogonal {Q : QuadraticForm K E} {a b a' b' : E}
    (horth : ∀ x ∈ Submodule.span K ({a, b} : Set E),
      ∀ y ∈ Submodule.span K ({a', b'} : Set E), polar Q x y = 0) :
    rootEnd Q a b * rootEnd Q a' b' = 0 := by
  ext x
  rw [Module.End.mul_apply, rootEnd_apply]
  have hy : rootEnd Q a' b' x ∈ Submodule.span K ({a', b'} : Set E) :=
    range_rootEnd_le_span Q a' b' ⟨x, rfl⟩
  have hb0 : polar Q (rootEnd Q a' b' x) b = 0 := by
    rw [polar_comm]
    exact horth b (Submodule.subset_span (by simp)) _ hy
  have ha0 : polar Q (rootEnd Q a' b' x) a = 0 := by
    rw [polar_comm]
    exact horth a (Submodule.subset_span (by simp)) _ hy
  rw [hb0, ha0]
  simp

theorem rootEnd_comp_eq_zero_of_orthogonal' {Q : QuadraticForm K E} {a b a' b' : E}
    (horth : ∀ x ∈ Submodule.span K ({a, b} : Set E),
      ∀ y ∈ Submodule.span K ({a', b'} : Set E), polar Q x y = 0) :
    rootEnd Q a' b' * rootEnd Q a b = 0 := by
  ext x
  rw [Module.End.mul_apply, rootEnd_apply]
  have hx : rootEnd Q a b x ∈ Submodule.span K ({a, b} : Set E) :=
    range_rootEnd_le_span Q a b ⟨x, rfl⟩
  have hb0 : polar Q (rootEnd Q a b x) b' = 0 :=
    horth _ hx b' (Submodule.subset_span (by simp))
  have ha0 : polar Q (rootEnd Q a b x) a' = 0 :=
    horth _ hx a' (Submodule.subset_span (by simp))
  rw [hb0, ha0]
  simp

theorem siegelEquiv_mul_comm_of_orthogonal {Q : QuadraticForm K E} {a b a' b' : E}
    (ha : Q a = 0) (hb : Q b = 0) (hab : QuadraticMap.polarBilin Q a b = 0)
    (ha' : Q a' = 0) (hb' : Q b' = 0) (hab' : QuadraticMap.polarBilin Q a' b' = 0)
    (horth : ∀ x ∈ Submodule.span K ({a, b} : Set E),
      ∀ y ∈ Submodule.span K ({a', b'} : Set E), polar Q x y = 0) (c d : K) :
    siegelEquiv Q a b ha hb hab c * siegelEquiv Q a' b' ha' hb' hab' d =
      siegelEquiv Q a' b' ha' hb' hab' d * siegelEquiv Q a b ha hb hab c := by
  have hpq := rootEnd_comp_eq_zero_of_orthogonal (Q := Q) (a := a) (b := b) horth
  have hqp := rootEnd_comp_eq_zero_of_orthogonal' (Q := Q) (a := a) (b := b) horth
  have hp := siegelEquiv_toLin_eq_one_add_smul_rootEnd ha hb hab c
  have hq := siegelEquiv_toLin_eq_one_add_smul_rootEnd ha' hb' hab' d
  have hL : ((siegelEquiv Q a b ha hb hab c * siegelEquiv Q a' b' ha' hb' hab' d :
      E ≃ₗ[K] E) : E →ₗ[K] E) = 1 + c • rootEnd Q a b + d • rootEnd Q a' b' := by
    change (siegelEquiv Q a b ha hb hab c : E →ₗ[K] E) *
      (siegelEquiv Q a' b' ha' hb' hab' d : E →ₗ[K] E) = _
    rw [hp, hq]
    simp only [mul_add, add_mul, one_mul, mul_one, smul_mul_smul, hpq, smul_zero, zero_add,
      add_zero]
  have hR : ((siegelEquiv Q a' b' ha' hb' hab' d * siegelEquiv Q a b ha hb hab c :
      E ≃ₗ[K] E) : E →ₗ[K] E) = 1 + c • rootEnd Q a b + d • rootEnd Q a' b' := by
    change (siegelEquiv Q a' b' ha' hb' hab' d : E →ₗ[K] E) *
      (siegelEquiv Q a b ha hb hab c : E →ₗ[K] E) = _
    rw [hp, hq]
    simp only [mul_add, add_mul, one_mul, mul_one, smul_mul_smul, hqp, smul_zero, zero_add,
      add_zero]
    abel
  ext x
  exact congrArg (fun f : E →ₗ[K] E => f x) (hL.trans hR.symm)

theorem longRootGroup_comm_of_orthogonal {Q : QuadraticForm K E} {a b a' b' : E}
    (ha : Q a = 0) (hb : Q b = 0) (hab : QuadraticMap.polarBilin Q a b = 0)
    (ha' : Q a' = 0) (hb' : Q b' = 0) (hab' : QuadraticMap.polarBilin Q a' b' = 0)
    (horth : ∀ x ∈ Submodule.span K ({a, b} : Set E),
      ∀ y ∈ Submodule.span K ({a', b'} : Set E), polar Q x y = 0) {g h : E ≃ₗ[K] E}
    (hg : g ∈ longRootGroup Q a b ha hb hab) (hh : h ∈ longRootGroup Q a' b' ha' hb' hab') :
    g * h = h * g := by
  obtain ⟨c, rfl⟩ := mem_longRootGroup_iff.mp hg
  obtain ⟨d, rfl⟩ := mem_longRootGroup_iff.mp hh
  exact siegelEquiv_mul_comm_of_orthogonal ha hb hab ha' hb' hab' horth c d

end CFSG.HardMathSupport.Kantor79
