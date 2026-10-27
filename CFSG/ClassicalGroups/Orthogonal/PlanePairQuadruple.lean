module

public import CFSG.ClassicalGroups.Orthogonal.SiegelRT1Pair

public section

namespace CFSG.ClassicalGroups.Orthogonal

open CFSG.ClassicalGroups.Orthogonal.SiegelRT1 QuadraticMap

private theorem polar_ne_zero_of_not_orthogonal {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] {Qf : QuadraticForm K V} {A A' : Submodule K V}
    (hAs : ∀ w ∈ A, Qf w = 0) (hA's : ∀ w ∈ A', Qf w = 0)
    (hno : ¬ A ≤ LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Qf) A')
    {v₂ w₁ e : V} (hv₂A : v₂ ∈ A) (hv₂A' : v₂ ∈ A') (hw₁A : w₁ ∈ A)
    (hspan : Submodule.span K ({v₂, w₁} : Set V) = A)
    (hspan' : Submodule.span K ({v₂, e} : Set V) = A') :
    QuadraticMap.polar Qf w₁ e ≠ 0 := by
  intro h0
  have h0' : QuadraticMap.polar Qf e w₁ = 0 := by
    rw [QuadraticMap.polar_comm]
    exact h0
  apply hno
  rw [← hspan]
  refine Submodule.span_le.mpr ?_
  intro x hx
  rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with hx | hx
  · rw [hx]
    exact mem_orthogonal_iff_polar.mpr fun y hy =>
      polar_eq_zero_of_totallySingular hA's hy hv₂A'
  · rw [hx]
    exact mem_orthogonal_iff_polar.mpr fun y hy => by
      have hy' : y ∈ Submodule.span K ({v₂, e} : Set V) := by rw [hspan']; exact hy
      obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp hy'
      rw [polar_add_left, polar_smul_left, polar_smul_left, smul_eq_mul, smul_eq_mul,
        polar_eq_zero_of_totallySingular hAs hv₂A hw₁A, h0', mul_zero, mul_zero, add_zero]

private theorem exists_polar_eq_one {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {Qf : QuadraticForm K V} (hnd : ∀ x : V, (∀ y, QuadraticMap.polar Qf x y = 0) → x = 0)
    {v : V} (hv : v ≠ 0) : ∃ u : V, QuadraticMap.polar Qf u v = 1 := by
  obtain ⟨u₀, hu₀⟩ : ∃ u : V, QuadraticMap.polar Qf u v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hv (hnd v fun y => by rw [QuadraticMap.polar_comm]; exact hcon y)
  exact ⟨(QuadraticMap.polar Qf u₀ v)⁻¹ • u₀, by
    rw [polar_smul_left, smul_eq_mul, inv_mul_cancel₀ hu₀]⟩

private theorem exists_polar_of_pair_orthogonal {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] {Qf : QuadraticForm K V} {u v₁ w₁ v₂ : V}
    (h11 : QuadraticMap.polar Qf v₁ w₁ = 1) (h12 : QuadraticMap.polar Qf v₁ v₂ = 0)
    (h21 : QuadraticMap.polar Qf v₂ w₁ = 0) (h₁₁ : QuadraticMap.polar Qf v₁ v₁ = 0)
    (h₂₂ : QuadraticMap.polar Qf w₁ w₁ = 0) (hu : QuadraticMap.polar Qf u v₂ = 1) :
    ∃ w₂ : V, QuadraticMap.polar Qf v₂ w₂ = 1 ∧ QuadraticMap.polar Qf v₁ w₂ = 0 ∧
      QuadraticMap.polar Qf w₁ w₂ = 0 := by
  have h12' : QuadraticMap.polar Qf v₂ v₁ = 0 := by
    rw [QuadraticMap.polar_comm]
    exact h12
  have hw₁v₁ : QuadraticMap.polar Qf w₁ v₁ = 1 := by
    rw [QuadraticMap.polar_comm]
    exact h11
  refine ⟨u - QuadraticMap.polar Qf u v₁ • w₁ - QuadraticMap.polar Qf u w₁ • v₁, ?_, ?_, ?_⟩
  · simp only [polar_sub_right, polar_smul_right, smul_eq_mul, h21, h12', mul_zero, sub_zero]
    rw [QuadraticMap.polar_comm]
    exact hu
  · simp only [polar_sub_right, polar_smul_right, smul_eq_mul, h11, h₁₁, mul_zero, sub_zero]
    rw [QuadraticMap.polar_comm]
    ring
  · simp only [polar_sub_right, polar_smul_right, smul_eq_mul, h₂₂, hw₁v₁, mul_zero, sub_zero]
    rw [QuadraticMap.polar_comm]
    ring

theorem exists_hyperbolic_quadruple_of_planes {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {Qf : QuadraticForm K V}
    (hnd : ∀ x : V, (∀ y, QuadraticMap.polar Qf x y = 0) → x = 0) {A A' : Submodule K V}
    (hA : Module.finrank K A = 2) (hA' : Module.finrank K A' = 2)
    (hAs : ∀ w ∈ A, Qf w = 0) (hA's : ∀ w ∈ A', Qf w = 0)
    (h1 : Module.finrank K ↥(A ⊓ A') = 1)
    (hno : ¬ A ≤ LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Qf) A') :
    ∃ v₁ v₂ w₁ w₂ : V, QuadraticMap.polar Qf v₁ w₁ = 1 ∧ QuadraticMap.polar Qf v₂ w₂ = 1 ∧
      QuadraticMap.polar Qf v₁ w₂ = 0 ∧ QuadraticMap.polar Qf v₂ w₁ = 0 ∧
      QuadraticMap.polar Qf v₁ v₂ = 0 ∧ QuadraticMap.polar Qf w₁ w₂ = 0 ∧
      Submodule.span K ({w₁, v₂} : Set V) = A ∧ Submodule.span K ({v₂, v₁} : Set V) = A' := by
  classical
  have hne : A ⊓ A' ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at h1
    omega
  obtain ⟨v₂, hv₂, hv₂0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨hv₂A, hv₂A'⟩ := Submodule.mem_inf.mp hv₂
  obtain ⟨w₁, hw₁A, -, hspan⟩ := exists_pair_of_mem_of_finrank_eq_two hA hv₂A hv₂0
  obtain ⟨e, heA', -, hspan'⟩ := exists_pair_of_mem_of_finrank_eq_two hA' hv₂A' hv₂0
  have hpol := polar_ne_zero_of_not_orthogonal hAs hA's hno hv₂A hv₂A' hw₁A hspan hspan'
  set c : K := QuadraticMap.polar Qf e w₁ with hc
  have hc0 : c ≠ 0 := by rw [hc, QuadraticMap.polar_comm]; exact hpol
  set v₁ : V := c⁻¹ • e with hv₁
  have hv₁A' : v₁ ∈ A' := by
    rw [hv₁]
    exact A'.smul_mem c⁻¹ heA'
  have hQv₁ : Qf v₁ = 0 := by
    rw [hv₁, QuadraticMap.map_smul, hA's e heA', smul_zero]
  have h11 : QuadraticMap.polar Qf v₁ w₁ = 1 := by
    rw [hv₁, polar_smul_left, smul_eq_mul, ← hc, inv_mul_cancel₀ hc0]
  have hv₂w₁ : QuadraticMap.polar Qf v₂ w₁ = 0 :=
    polar_eq_zero_of_totallySingular hAs hv₂A hw₁A
  have hv₁v₂ : QuadraticMap.polar Qf v₁ v₂ = 0 :=
    polar_eq_zero_of_totallySingular hA's hv₁A' hv₂A'
  have hpolv₁ : QuadraticMap.polar Qf v₁ v₁ = 0 := by
    rw [polar_self, hQv₁, smul_zero]
  have hpolw₁ : QuadraticMap.polar Qf w₁ w₁ = 0 := by
    rw [polar_self, hAs w₁ hw₁A, smul_zero]
  obtain ⟨u, hu⟩ := exists_polar_eq_one hnd hv₂0
  obtain ⟨w₂, h22, h12, hw₂⟩ :=
    exists_polar_of_pair_orthogonal h11 hv₁v₂ hv₂w₁ hpolv₁ hpolw₁ hu
  refine ⟨v₁, v₂, w₁, w₂, h11, h22, h12, hv₂w₁, hv₁v₂, hw₂, ?_, ?_⟩
  · rw [Set.pair_comm]
    exact hspan
  · rw [← hspan']
    have hsub₁ : Submodule.span K ({v₂, v₁} : Set V) ≤ Submodule.span K ({v₂, e} : Set V) := by
      refine Submodule.span_le.mpr ?_
      intro x hx
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with hx | hx
      · rw [hx]
        exact Submodule.subset_span (by simp)
      · rw [hx, hv₁]
        exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
    have hsub₂ : Submodule.span K ({v₂, e} : Set V) ≤ Submodule.span K ({v₂, v₁} : Set V) := by
      refine Submodule.span_le.mpr ?_
      intro x hx
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with hx | hx
      · rw [hx]
        exact Submodule.subset_span (by simp)
      · have he : e = c • v₁ := by rw [hv₁, smul_smul, mul_inv_cancel₀ hc0, one_smul]
        rw [hx, he]
        exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
    exact le_antisymm hsub₁ hsub₂

end CFSG.ClassicalGroups.Orthogonal
