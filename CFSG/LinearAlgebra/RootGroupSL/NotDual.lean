module

public import CFSG.LinearAlgebra.RootGroupSL.TransvecSL
public import CFSG.LinearAlgebra.RootGroupSL.ModelDefs

public section

namespace CFSG.LinearAlgebra.RootGroupSL

variable {k E VJ : Type} [Field k] [Field E] [Algebra k E]
  [AddCommGroup VJ] [Module k VJ] [Module E VJ] [IsScalarTower k E VJ]
  [Module.Finite k E] [Module.Finite E VJ] [Module.Finite k VJ]

private lemma exists_form_vanishing_on_pair (u e₁ : VJ) (hm : 3 ≤ Module.finrank E VJ) :
    ∃ φ : VJ →ₗ[E] E, φ u = 0 ∧ φ e₁ = 0 ∧ ∃ v : VJ, φ v = 1 := by
  classical
  have hcard : ({u, e₁} : Set VJ).toFinset.card ≤ 2 := by
    have hfin : ({u, e₁} : Set VJ).toFinset = ({u, e₁} : Finset VJ) := by
      ext x
      simp
    rw [hfin]
    exact Finset.card_le_two
  have hspan : Submodule.span E ({u, e₁} : Set VJ) < ⊤ := by
    apply Submodule.lt_top_of_finrank_lt_finrank
    have hle : Module.finrank E (Submodule.span E ({u, e₁} : Set VJ)) ≤ 2 := by
      calc Module.finrank E (Submodule.span E ({u, e₁} : Set VJ))
          ≤ ({u, e₁} : Set VJ).toFinset.card := finrank_span_le_card _
        _ ≤ 2 := hcard
    omega
  obtain ⟨φ, hφne, hφker⟩ :=
    Submodule.exists_le_ker_of_lt_top (Submodule.span E ({u, e₁} : Set VJ)) hspan
  have hφu : φ u = 0 := hφker (Submodule.subset_span (by simp))
  have hφe : φ e₁ = 0 := hφker (Submodule.subset_span (by simp))
  obtain ⟨v, hv⟩ : ∃ v : VJ, φ v ≠ 0 := by
    by_contra h
    exact hφne (LinearMap.ext fun x => not_not.mp (not_exists.mp h x))
  refine ⟨(φ v)⁻¹ • φ, ?_, ?_, v, ?_⟩
  · rw [LinearMap.smul_apply, hφu, smul_eq_mul, mul_zero]
  · rw [LinearMap.smul_apply, hφe, smul_eq_mul, mul_zero]
  · rw [LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hv]

private lemma form_eq_zero_of_fixed (e₁ : VJ) (hm : 3 ≤ Module.finrank E VJ)
    (f : Module.Dual k VJ)
    (hf : ∀ (B : SpecialLinearGroup E VJ), B e₁ = e₁ → ∀ x : VJ, f (B x) = f x) :
    f = 0 := by
  ext u
  obtain ⟨φ, hφu, hφe, v, hφv⟩ := exists_form_vanishing_on_pair (E := E) u e₁ hm
  let B : SpecialLinearGroup E VJ := transvecSL u φ
  have hBe : B e₁ = e₁ := by
    change transvecSL u φ e₁ = e₁
    rw [transvecSL_apply hφu, hφe, zero_smul, add_zero]
  have hBv : B v = v + u := by
    change transvecSL u φ v = v + u
    rw [transvecSL_apply hφu, hφv, one_smul]
  have h1 : f (B v) = f v := hf B hBe v
  rw [hBv, map_add] at h1
  have h1' : f v + f u = f v + 0 := by simpa using h1
  simpa using add_left_cancel h1'

private lemma dual_apply_inv_eq_self (T : Module.Dual k VJ ≃+ VJ)
    (hT : ∀ (B : SpecialLinearGroup E VJ) (f : Module.Dual k VJ),
      T (f ∘ₗ (SpecialLinearGroup.toLinearEquiv (restrictSL k B⁻¹)).toLinearMap) = B (T f))
    (f₀ : Module.Dual k VJ) (e₁ : VJ) (hf₀ : T f₀ = e₁)
    {B : SpecialLinearGroup E VJ} (hB : B e₁ = e₁) (x : VJ) :
    f₀ (B⁻¹ x) = f₀ x := by
  have h1 : T (f₀ ∘ₗ (SpecialLinearGroup.toLinearEquiv (restrictSL k B⁻¹)).toLinearMap) = e₁ := by
    rw [hT B f₀, hf₀, hB]
  have h2 : f₀ ∘ₗ (SpecialLinearGroup.toLinearEquiv (restrictSL k B⁻¹)).toLinearMap = f₀ :=
    T.injective (by rw [h1, hf₀])
  have h3 := congrArg (fun g : Module.Dual k VJ => g x) h2
  have hLx : (SpecialLinearGroup.toLinearEquiv (restrictSL k B⁻¹)).toLinearMap x = B⁻¹ x := rfl
  rw [LinearMap.comp_apply, hLx] at h3
  exact h3

theorem not_exists_equivariant_dual_addEquiv (hm : 3 ≤ Module.finrank E VJ)
    (T : Module.Dual k VJ ≃+ VJ)
    (hT : ∀ (B : SpecialLinearGroup E VJ) (f : Module.Dual k VJ),
      T (f ∘ₗ (SpecialLinearGroup.toLinearEquiv (restrictSL k B⁻¹)).toLinearMap) = B (T f)) :
    False := by
  haveI : Nontrivial VJ := Module.nontrivial_of_finrank_pos (R := E) (M := VJ) (by omega)
  obtain ⟨e₁, he₁⟩ := exists_ne (0 : VJ)
  let f₀ : Module.Dual k VJ := T.symm e₁
  have hf₀ : T f₀ = e₁ := T.apply_symm_apply e₁
  have hfix : ∀ (B : SpecialLinearGroup E VJ), B e₁ = e₁ → ∀ x : VJ, f₀ (B x) = f₀ x := by
    intro B hB x
    have h3 := dual_apply_inv_eq_self (k := k) (E := E) (VJ := VJ) T hT f₀ e₁ hf₀
      (B := B) hB (B x)
    have hBinvx : B⁻¹ (B x) = x := by
      change (B⁻¹ : VJ ≃ₗ[E] VJ) ((B : VJ ≃ₗ[E] VJ) x) = x
      exact LinearEquiv.symm_apply_apply (B : VJ ≃ₗ[E] VJ) x
    rw [hBinvx] at h3
    exact h3.symm
  have hzero : f₀ = 0 := form_eq_zero_of_fixed (k := k) (E := E) (VJ := VJ) e₁ hm f₀ hfix
  have : e₁ = 0 := by rw [← hf₀, hzero, map_zero]
  exact he₁ this

end CFSG.LinearAlgebra.RootGroupSL
