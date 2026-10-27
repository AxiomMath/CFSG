module

public import CFSG.HardMathSupport.Kantor79.CommutatorSpace
public import CFSG.HardMathSupport.GuralnickMalle.LongRootGroup
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Basic

public section

open LinearMap Module QuadraticMap

namespace CFSG.HardMathSupport.Kantor79

open CFSG.HardMathSupport.GuralnickMalle

variable {K E : Type*} [Field K] [CharP K 2] [AddCommGroup E] [Module K E]

@[expose] noncomputable def rootEnd (Q : QuadraticForm K E) (a b : E) : E →ₗ[K] E :=
  siegelLin Q a b 1 - 1

theorem rootEnd_apply (Q : QuadraticForm K E) (a b x : E) :
    rootEnd Q a b x = polar Q x b • a + polar Q x a • b := by
  rw [rootEnd, LinearMap.sub_apply, siegelLin_apply, Module.End.one_apply, one_smul, one_smul]
  abel

theorem rootEnd_self_adjoint (Q : QuadraticForm K E) (a b x y : E) :
    polar Q (rootEnd Q a b x) y = polar Q x (rootEnd Q a b y) := by
  simp only [rootEnd_apply, polar_add_left, polar_smul_left, polar_add_right, polar_smul_right,
    smul_eq_mul, QuadraticMap.polarBilin_apply_apply]
  rw [polar_comm Q a y, polar_comm Q b y]
  ring

theorem polar_self_rootEnd (Q : QuadraticForm K E) (a b x : E) :
    polar Q x (rootEnd Q a b x) = 0 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  simp only [rootEnd_apply, polar_add_right, polar_smul_right, smul_eq_mul]
  calc polar Q x b * polar Q x a + polar Q x a * polar Q x b
      = 2 * (polar Q x b * polar Q x a) := by ring
    _ = 0 := by rw [h2, zero_mul]

theorem rootEnd_sq_eq_zero (Q : QuadraticForm K E) (a b : E) (hQa : Q a = 0) (hQb : Q b = 0)
    (hab : polar Q a b = 0) : rootEnd Q a b * rootEnd Q a b = 0 := by
  have haa : polar Q a a = 0 := by
    rw [polar_self, hQa]; exact CharTwo.two_nsmul _
  have hbb : polar Q b b = 0 := by
    rw [polar_self, hQb]; exact CharTwo.two_nsmul _
  ext x
  change rootEnd Q a b (rootEnd Q a b x) = 0
  rw [rootEnd_apply, rootEnd_apply]
  simp only [polar_add_left, polar_smul_left, smul_eq_mul, hab, hbb, haa, polar_comm Q b a,
    mul_zero, zero_mul, zero_smul, add_zero]

theorem rootEnd_isometry (Q : QuadraticForm K E) (a b x : E) (hQa : Q a = 0) (hQb : Q b = 0)
    (hab : polar Q a b = 0) : Q (x + rootEnd Q a b x) = Q x := by
  have hx : x + rootEnd Q a b x = siegelLin Q a b 1 x := by
    rw [rootEnd_apply, siegelLin_apply, one_smul, one_smul]
    abel
  rw [hx]
  exact siegelLin_isometry Q a b hQa hQb hab 1 x

@[expose] noncomputable def rootEquiv (Q : QuadraticForm K E) (a b : E) (hQa : Q a = 0) (hQb : Q b = 0)
    (hab : polar Q a b = 0) : E ≃ₗ[K] E :=
  siegelEquiv Q a b hQa hQb hab 1

theorem rootEquiv_apply (Q : QuadraticForm K E) (a b : E) (hQa : Q a = 0) (hQb : Q b = 0)
    (hab : polar Q a b = 0) (x : E) :
    rootEquiv Q a b hQa hQb hab x = x + polar Q x b • a + polar Q x a • b := by
  change siegelLin Q a b 1 x = x + polar Q x b • a + polar Q x a • b
  rw [siegelLin_apply, one_smul, one_smul]
  abel

theorem movedSpace_rootEquiv (Q : QuadraticForm K E) (a b : E) (hQa : Q a = 0) (hQb : Q b = 0)
    (hab : polar Q a b = 0) :
    movedSpace (rootEquiv Q a b hQa hQb hab) = LinearMap.range (rootEnd Q a b) := rfl

theorem range_rootEnd_le_span (Q : QuadraticForm K E) (a b : E) :
    LinearMap.range (rootEnd Q a b) ≤ Submodule.span K ({a, b} : Set E) := by
  rintro _ ⟨x, rfl⟩
  rw [rootEnd_apply]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

@[expose] def IsLongRootElement (Q : QuadraticForm K E) (x : E ≃ₗ[K] E) : Prop :=
  ∃ a b : E, Q a = 0 ∧ Q b = 0 ∧ polar Q a b = 0 ∧ a ≠ 0 ∧ b ≠ 0 ∧
    LinearIndependent K ![a, b] ∧
    ∀ v : E, x v = v + polar Q v b • a + polar Q v a • b

theorem IsLongRootElement.mem_orthogonalGroup {Q : QuadraticForm K E} {x : E ≃ₗ[K] E}
    (h : IsLongRootElement Q x) :
    x ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
  obtain ⟨a, b, hQa, hQb, hab, -, -, -, hx⟩ := h
  refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => ?_
  rw [hx]
  have hv : v + polar Q v b • a + polar Q v a • b = v + rootEnd Q a b v := by
    rw [rootEnd_apply, add_assoc]
  rw [hv]
  exact rootEnd_isometry Q a b v hQa hQb hab

theorem IsLongRootElement.movedSpace_le_span {Q : QuadraticForm K E} {x : E ≃ₗ[K] E}
    (h : IsLongRootElement Q x) :
    ∃ a b : E, movedSpace x ≤ Submodule.span K ({a, b} : Set E) := by
  obtain ⟨a, b, hQa, hQb, hab, -, -, -, hx⟩ := h
  refine ⟨a, b, ?_⟩
  have hxeq : x = rootEquiv Q a b hQa hQb hab := by
    ext v
    rw [rootEquiv_apply, hx]
  rw [hxeq, movedSpace_rootEquiv]
  exact range_rootEnd_le_span Q a b

theorem IsLongRootElement.finrank_movedSpace_le_two [FiniteDimensional K E]
    {Q : QuadraticForm K E} {x : E ≃ₗ[K] E}
    (h : IsLongRootElement Q x) : finrank K ↥(movedSpace x) ≤ 2 := by
  obtain ⟨a, b, hle⟩ := h.movedSpace_le_span
  exact (Submodule.finrank_mono hle).trans (finrank_span_pair_le_two a b)

theorem IsLongRootElement.conj {Q : QuadraticForm K E} {x g : E ≃ₗ[K] E}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hx : IsLongRootElement Q x) :
    IsLongRootElement Q (g * x * g⁻¹) := by
  obtain ⟨a, b, hQa, hQb, hab, ha, hb, hli, hxform⟩ := hx
  have hQa' : Q (g a) = 0 := by
    rw [TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hg, hQa]
  have hQb' : Q (g b) = 0 := by
    rw [TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hg, hQb]
  have hab' : polar Q (g a) (g b) = 0 := by
    rw [TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hg, hab]
  have ha' : g a ≠ 0 := fun h => ha (g.injective (by simpa using h))
  have hb' : g b ≠ 0 := fun h => hb (g.injective (by simpa using h))
  have hli' : LinearIndependent K ![g a, g b] := by
    have h : LinearIndependent K (fun i => g (![a, b] i)) :=
      hli.map' g.toLinearMap (by
        rw [LinearMap.ker_eq_bot]
        exact g.injective)
    convert h using 1
    ext i
    fin_cases i <;> simp
  have hform : ∀ v : E, (g * x * g⁻¹) v =
      v + polar Q v (g b) • g a + polar Q v (g a) • g b := by
    intro v
    have h1 : polar Q (g⁻¹ v) b = polar Q v (g b) := by
      have h := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hg (g⁻¹ v) b
      rw [show g (g⁻¹ v) = v by simp] at h
      exact h.symm
    have h2 : polar Q (g⁻¹ v) a = polar Q v (g a) := by
      have h := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hg (g⁻¹ v) a
      rw [show g (g⁻¹ v) = v by simp] at h
      exact h.symm
    calc (g * x * g⁻¹) v = g (x (g⁻¹ v)) := by simp [LinearEquiv.mul_apply]
      _ = g (g⁻¹ v + polar Q (g⁻¹ v) b • a + polar Q (g⁻¹ v) a • b) := by rw [hxform]
      _ = v + polar Q v (g b) • g a + polar Q v (g a) • g b := by
        rw [map_add, map_add, map_smul, map_smul, h1, h2]
        simp
  exact ⟨g a, g b, hQa', hQb', hab', ha', hb', hli', hform⟩

theorem isLongRootElement_siegelEquiv (Q : QuadraticForm K E) (a b : E) (hQa : Q a = 0)
    (hQb : Q b = 0) (hab : polar Q a b = 0)
    (hnd : ∀ x, (∀ y, polar Q x y = 0) → x = 0) (hli : LinearIndependent K ![a, b])
    {c : K} (hc : c ≠ 0) :
    IsLongRootElement Q (siegelEquiv Q a b hQa hQb hab c) ∧
      movedSpace (siegelEquiv Q a b hQa hQb hab c) =
        Submodule.span K ({a, b} : Set E) := by
  have hab' : QuadraticMap.polarBilin Q a b = 0 := hab
  have hnd' : ∀ x, (∀ y, QuadraticMap.polarBilin Q x y = 0) → x = 0 := hnd
  have ha : a ≠ 0 := by
    have := hli.ne_zero (0 : Fin 2)
    simpa using this
  have hb : b ≠ 0 := by
    have := hli.ne_zero (1 : Fin 2)
    simpa using this
  have hli' : LinearIndependent K ![c • a, b] := by
    rw [LinearIndependent.pair_iff] at hli ⊢
    intro s t hst
    have h : (s * c) • a + t • b = 0 := by
      rw [← hst, smul_smul]
    obtain ⟨h1, h2⟩ := hli (s * c) t h
    exact ⟨(mul_eq_zero.mp h1).resolve_right hc, h2⟩
  refine ⟨⟨c • a, b, ?_, hQb, ?_, ?_, hb, hli', ?_⟩, ?_⟩
  · rw [QuadraticMap.map_smul Q, hQa, smul_zero]
  · rw [polar_smul_left, hab, smul_zero]
  · exact smul_ne_zero hc ha
  · intro v
    change siegelLin Q a b c v = v + polar Q v b • c • a + polar Q v (c • a) • b
    have e1 : ((QuadraticMap.polarBilin Q) v) b = polar Q v b := rfl
    have e2 : ((QuadraticMap.polarBilin Q) v) a = polar Q v a := rfl
    rw [siegelLin_apply, polar_smul_right, e1, e2]
    module
  · change LinearMap.range (siegelLin Q a b c - 1) = Submodule.span K ({a, b} : Set E)
    exact siegelLin_sub_one_range Q a b hnd' hli c hc

theorem IsLongRootElement.polar_apply_self {Q : QuadraticForm K E} {x : E ≃ₗ[K] E}
    (h : IsLongRootElement Q x) (y : E) : polar Q y (x y) = 0 := by
  obtain ⟨a, b, -, -, -, -, -, -, hx⟩ := h
  rw [hx]
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hyy : polar Q y y = 0 := by rw [polar_self, CharTwo.two_nsmul]
  simp only [polar_add_right, polar_smul_right, smul_eq_mul, hyy, zero_add]
  calc polar Q y b * polar Q y a + polar Q y a * polar Q y b
      = 2 * (polar Q y b * polar Q y a) := by ring
    _ = 0 := by rw [h2, zero_mul]

theorem not_isLongRootElement_one {Q : QuadraticForm K E}
    (hnd : ∀ x, (∀ y, polar Q x y = 0) → x = 0) : ¬ IsLongRootElement Q 1 := by
  rintro ⟨a, b, -, -, -, -, hb, hli, hform⟩
  have hbpol : ∀ v, polar Q v b = 0 := by
    intro v
    have hzero : polar Q v b • a + polar Q v a • b = 0 := by
      have h : v = v + (polar Q v b • a + polar Q v a • b) := by
        have h1 := hform v
        rw [LinearEquiv.coe_one, add_assoc] at h1
        exact h1
      have h' : v + (polar Q v b • a + polar Q v a • b) - v = 0 := by
        rw [← h, sub_self]
      simpa using h'
    exact (LinearIndependent.eq_zero_of_pair hli hzero).1
  exact hb (hnd b fun v => by rw [polar_comm]; exact hbpol v)

end CFSG.HardMathSupport.Kantor79
