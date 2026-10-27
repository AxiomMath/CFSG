module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Transvection.Basic
import Mathlib.LinearAlgebra.SpecialLinearGroup

public section

namespace CFSG.LinearAlgebra

variable {ι F : Type*} [Fintype ι] [DecidableEq ι] [Field F] [CharP F 2]

theorem range_ker_eq_of_finrank_range_eq_two (hF : ∀ a : F, a = 0 ∨ a = 1)
    {W E : Submodule F (ι → F)} (hWE : IsCompl W E) (hW : Module.finrank F W = 4)
    {r₀ v : Matrix.SpecialLinearGroup ι F}
    (hrW : ∀ w ∈ W, (r₀ : Matrix ι ι F).mulVec w ∈ W)
    (hrE : ∀ e ∈ E, (r₀ : Matrix ι ι F).mulVec e = e) (hsq : r₀ * r₀ = 1)
    (hrank : Module.finrank F (LinearMap.range (Matrix.toLin' ((r₀ : Matrix ι ι F) - 1))) = 2)
    (hvW : ∀ w ∈ W, (v : Matrix ι ι F).mulVec w ∈ W)
    (hvE : ∀ e ∈ E, (v : Matrix ι ι F).mulVec e = e) (hvr : v * r₀ = r₀ * v)
    (hconj : ∃ j : Matrix.SpecialLinearGroup ι F, v = j * r₀ * j⁻¹)
    (hcomm : ∀ y : Matrix.SpecialLinearGroup ι F,
      (∀ x, Matrix.toLin' ((y : Matrix ι ι F) - 1) x ∈
        LinearMap.range (Matrix.toLin' ((r₀ : Matrix ι ι F) - 1))) →
      (∀ u ∈ LinearMap.range (Matrix.toLin' ((r₀ : Matrix ι ι F) - 1)),
        Matrix.toLin' ((y : Matrix ι ι F) - 1) u = 0) →
      (∀ e ∈ E, Matrix.toLin' ((y : Matrix ι ι F) - 1) e = 0) →
      v * y * v⁻¹ * y⁻¹ = 1 ∨ v * y * v⁻¹ * y⁻¹ = r₀) :
    LinearMap.range (Matrix.toLin' ((v : Matrix ι ι F) - 1)) =
        LinearMap.range (Matrix.toLin' ((r₀ : Matrix ι ι F) - 1)) ∧
      LinearMap.ker (Matrix.toLin' ((v : Matrix ι ι F) - 1)) =
        LinearMap.ker (Matrix.toLin' ((r₀ : Matrix ι ι F) - 1)) := by
  classical
  let N : (ι → F) →ₗ[F] (ι → F) := Matrix.toLin' ((r₀ : Matrix ι ι F) - 1)
  let U : Submodule F (ι → F) := LinearMap.range N
  let V : (ι → F) ≃ₗ[F] (ι → F) := Matrix.SpecialLinearGroup.toLin' v
  let R : (ι → F) ≃ₗ[F] (ι → F) := Matrix.SpecialLinearGroup.toLin' r₀
  have hN_apply : ∀ x : ι → F, N x = (r₀ : Matrix ι ι F).mulVec x - x := by
    intro x
    change Matrix.toLin' ((r₀ : Matrix ι ι F) - 1) x = _
    rw [Matrix.toLin'_apply, Matrix.sub_mulVec, Matrix.one_mulVec]
  have hV_apply : ∀ x : ι → F, V x = (v : Matrix ι ι F).mulVec x := by
    intro x
    change (V : (ι → F) →ₗ[F] (ι → F)) x = _
    rw [show (V : (ι → F) →ₗ[F] (ι → F)) = Matrix.toLin' (v : Matrix ι ι F) from
      Matrix.SpecialLinearGroup.toLin'_to_linearMap v]
    rw [Matrix.toLin'_apply]
  have hR_apply : ∀ x : ι → F, R x = (r₀ : Matrix ι ι F).mulVec x := by
    intro x
    change (R : (ι → F) →ₗ[F] (ι → F)) x = _
    rw [show (R : (ι → F) →ₗ[F] (ι → F)) = Matrix.toLin' (r₀ : Matrix ι ι F) from
      Matrix.SpecialLinearGroup.toLin'_to_linearMap r₀]
    rw [Matrix.toLin'_apply]
  have hNW : ∀ w ∈ W, N w ∈ W := by
    intro w hw
    rw [hN_apply]
    exact Submodule.sub_mem W (hrW w hw) hw
  have hNE : ∀ e ∈ E, N e = 0 := by
    intro e he
    rw [hN_apply, hrE e he, sub_self]
  have hVW : ∀ w ∈ W, V w ∈ W := by
    intro w hw
    rw [hV_apply]
    exact hvW w hw
  have hVE : ∀ e ∈ E, V e = e := by
    intro e he
    rw [hV_apply, hvE e he]
  have hrr : (r₀ : Matrix ι ι F) * (r₀ : Matrix ι ι F) = 1 := by
    simpa [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] using
      congrArg (fun g : Matrix.SpecialLinearGroup ι F => (g : Matrix ι ι F)) hsq
  have h2F : (2 : F) = 0 := CharTwo.two_eq_zero
  have hRR : (R : (ι → F) →ₗ[F] (ι → F)) * (R : (ι → F) →ₗ[F] (ι → F)) = 1 := by
    rw [Module.End.mul_eq_comp,
      show (R : (ι → F) →ₗ[F] (ι → F)) = Matrix.toLin' (r₀ : Matrix ι ι F) from
        Matrix.SpecialLinearGroup.toLin'_to_linearMap r₀,
      ← Matrix.toLin'_mul, hrr, Matrix.toLin'_one]
    rfl
  have hRN : N = (R : (ι → F) →ₗ[F] (ι → F)) - 1 := by
    rw [show N = Matrix.toLin' ((r₀ : Matrix ι ι F) - 1) from rfl, map_sub,
      Matrix.toLin'_one]
    rw [show Matrix.toLin' (r₀ : Matrix ι ι F) = (R : (ι → F) →ₗ[F] (ι → F)) from
      (Matrix.SpecialLinearGroup.toLin'_to_linearMap r₀).symm]
    rfl
  have hNN : N * N = 0 := by
    rw [hRN]
    have hR2 : (R : (ι → F) →ₗ[F] (ι → F)) + (R : (ι → F) →ₗ[F] (ι → F)) = 0 := by
      rw [← two_smul F (R : (ι → F) →ₗ[F] (ι → F)), h2F, zero_smul]
    have h12 : (1 : (ι → F) →ₗ[F] (ι → F)) + 1 = 0 := by
      rw [← two_smul F (1 : (ι → F) →ₗ[F] (ι → F)), h2F, zero_smul]
    have hexp : ((R : (ι → F) →ₗ[F] (ι → F)) - 1) * ((R : (ι → F) →ₗ[F] (ι → F)) - 1)
        = (1 - (R : (ι → F) →ₗ[F] (ι → F))) - ((R : (ι → F) →ₗ[F] (ι → F)) - 1) := by
      rw [sub_mul, mul_sub, mul_sub, mul_one, one_mul, hRR]
      rfl
    rw [hexp]
    have hsub : (1 - (R : (ι → F) →ₗ[F] (ι → F)))
        - ((R : (ι → F) →ₗ[F] (ι → F)) - 1) = (1 + 1)
        - ((R : (ι → F) →ₗ[F] (ι → F)) + (R : (ι → F) →ₗ[F] (ι → F))) := by
      abel
    rw [hsub, h12, hR2, sub_self]
  have hUker : U ≤ LinearMap.ker N := by
    rintro x ⟨y, rfl⟩
    refine LinearMap.mem_ker.mpr ?_
    have h : (N * N) y = 0 := by rw [hNN, LinearMap.zero_apply]
    rwa [Module.End.mul_apply] at h
  have hUmap : LinearMap.range N = Submodule.map N W := by
    apply le_antisymm
    · rintro y ⟨x, rfl⟩
      have hx : x ∈ W ⊔ E := by rw [hWE.sup_eq_top]; exact Submodule.mem_top
      rcases Submodule.mem_sup.mp hx with ⟨w, hw, e, he, rfl⟩
      refine Submodule.mem_map.mpr ⟨w, hw, ?_⟩
      rw [map_add, hNE e he, add_zero]
    · rintro y ⟨w, hw, rfl⟩
      exact ⟨w, rfl⟩
  have hUW : U ≤ W := by
    intro x hx
    change x ∈ LinearMap.range N at hx
    rw [hUmap] at hx
    rcases Submodule.mem_map.mp hx with ⟨w, hw, rfl⟩
    exact hNW w hw
  have hUle : U ≤ W ⊓ LinearMap.ker N := le_inf hUW hUker
  have hfinM : Module.finrank F (ι → F) = 4 + Module.finrank F E := by
    have h := Submodule.finrank_add_eq_of_isCompl hWE
    omega
  have hkerN : Module.finrank F (LinearMap.ker N) = 2 + Module.finrank F E := by
    have h := LinearMap.finrank_range_add_finrank_ker N
    have hU2 : Module.finrank F (LinearMap.range N) = 2 := hrank
    omega
  have hEker : E ≤ LinearMap.ker N := by
    intro e he
    exact LinearMap.mem_ker.mpr (hNE e he)
  have hsup : W ⊔ LinearMap.ker N = ⊤ := by
    rw [eq_top_iff, ← hWE.sup_eq_top]
    exact sup_le_sup_left hEker W
  have hWker : Module.finrank F ↥(W ⊓ LinearMap.ker N) = 2 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq (s := W) (t := LinearMap.ker N)
    rw [hsup, finrank_top, hW, hkerN] at h
    omega
  have hWkerU : W ⊓ LinearMap.ker N = U := by
    refine (Submodule.eq_of_le_of_finrank_eq hUle ?_).symm
    rw [hWker, hrank]
  have hker_eq : LinearMap.ker N = U ⊔ E := by
    apply le_antisymm
    · intro x hx
      have hx' : N x = 0 := LinearMap.mem_ker.mp hx
      have hxmem : x ∈ W ⊔ E := by rw [hWE.sup_eq_top]; exact Submodule.mem_top
      rcases Submodule.mem_sup.mp hxmem with ⟨w, hw, e, he, rfl⟩
      have hNw : N w = 0 := by
        have h := hx'
        rw [map_add, hNE e he, add_zero] at h
        exact h
      have hwker : w ∈ W ⊓ LinearMap.ker N := ⟨hw, LinearMap.mem_ker.mpr hNw⟩
      rw [hWkerU] at hwker
      exact Submodule.mem_sup.mpr ⟨w, hwker, e, he, rfl⟩
    · intro x hx
      rcases Submodule.mem_sup.mp hx with ⟨u, hu, e, he, rfl⟩
      exact Submodule.add_mem _ (hUker hu) (hEker he)
  have hvrM : (v : Matrix ι ι F) * (r₀ : Matrix ι ι F)
      = (r₀ : Matrix ι ι F) * (v : Matrix ι ι F) := by
    simpa [Matrix.SpecialLinearGroup.coe_mul] using
      congrArg (fun g : Matrix.SpecialLinearGroup ι F => (g : Matrix ι ι F)) hvr
  have hVN : (V : (ι → F) →ₗ[F] (ι → F)) * N = N * (V : (ι → F) →ₗ[F] (ι → F)) := by
    have hm : (v : Matrix ι ι F) * ((r₀ : Matrix ι ι F) - 1)
        = ((r₀ : Matrix ι ι F) - 1) * (v : Matrix ι ι F) := by
      rw [mul_sub, sub_mul, mul_one, one_mul, hvrM]
    have h := congrArg Matrix.toLin' hm
    rw [Matrix.toLin'_mul, Matrix.toLin'_mul, ← Matrix.SpecialLinearGroup.toLin'_to_linearMap v]
      at h
    exact h
  have hVN_apply : ∀ x : ι → F, V (N x) = N (V x) := by
    intro x
    have := congrArg (fun f : (ι → F) →ₗ[F] (ι → F) => f x) hVN
    simpa [Module.End.mul_apply] using this
  have hVU_le : Submodule.map (V : (ι → F) →ₗ[F] (ι → F)) U ≤ U := by
    rintro x ⟨u, hu, rfl⟩
    change u ∈ LinearMap.range N at hu
    rcases hu with ⟨y, rfl⟩
    change V (N y) ∈ U
    rw [hVN_apply y]
    exact ⟨V y, rfl⟩
  have hVU_eq : Submodule.map (V : (ι → F) →ₗ[F] (ι → F)) U = U := by
    refine Submodule.eq_of_le_of_finrank_eq hVU_le ?_
    exact LinearEquiv.finrank_map_eq V U
  have hVinvU : Submodule.map (V.symm : (ι → F) →ₗ[F] (ι → F)) U ≤ U := by
    intro x hx
    rcases Submodule.mem_map.mp hx with ⟨y, hy, hyx⟩
    have hy' : y ∈ Submodule.map (V : (ι → F) →ₗ[F] (ι → F)) U := by rw [hVU_eq]; exact hy
    rcases Submodule.mem_map.mp hy' with ⟨z, hz, hzy⟩
    rw [← hyx, ← hzy]
    change V.symm (V z) ∈ U
    rw [LinearEquiv.symm_apply_apply]
    exact hz
  have h2M : ∀ y : ι → F, y + y = 0 := by
    intro y
    rw [← two_smul F y, h2F, zero_smul]
  have hVU : ∀ u ∈ U, V u = u := by
    intro u hu
    by_cases hu0 : u = 0
    · rw [hu0, map_zero]
    · have hu_range : u ∈ LinearMap.range N := hu
      obtain ⟨y, hy⟩ := hu_range
      have hy_mem : y ∈ W ⊔ E := by rw [hWE.sup_eq_top]; exact Submodule.mem_top
      rcases Submodule.mem_sup.mp hy_mem with ⟨w, hw, e, he, rfl⟩
      have hNw : N w = u := by
        have h := hy
        rw [map_add, hNE e he, add_zero] at h
        exact h
      have hwU : w ∉ U := by
        intro hwU'
        have h0 : N w = 0 := LinearMap.mem_ker.mp (hUker hwU')
        rw [hNw] at h0
        exact hu0 h0
      let p : Submodule F (ι → F) := U ⊔ Submodule.span F {w} ⊔ E
      have hUwW : U ⊔ Submodule.span F {w} ≤ W :=
        sup_le hUW (Submodule.span_le.mpr (by simpa using hw))
      have hUw_fin : Module.finrank F ↥(U ⊔ Submodule.span F {w}) = 3 := by
        rw [Submodule.finrank_sup_span_singleton hwU, hrank]
      have hdisj : (U ⊔ Submodule.span F {w}) ⊓ E = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        have hxW : x ∈ W := hUwW hx.1
        have hxE : x ∈ E := hx.2
        have hxWE : x ∈ W ⊓ E := ⟨hxW, hxE⟩
        rwa [hWE.inf_eq_bot] at hxWE
      have hpfin : Module.finrank F ↥p = 3 + Module.finrank F E := by
        have h := Submodule.finrank_sup_add_finrank_inf_eq
          (s := U ⊔ Submodule.span F {w}) (t := E)
        rw [hdisj, finrank_bot, hUw_fin, add_zero] at h
        exact h
      have hp : p < ⊤ := by
        rw [lt_top_iff_ne_top]
        intro hp_top
        have hlt : Module.finrank F ↥p < Module.finrank F (ι → F) := by
          rw [hpfin, hfinM]
          omega
        rw [hp_top, finrank_top] at hlt
        exact lt_irrefl _ hlt
      obtain ⟨f, hfne, hpker⟩ := Submodule.exists_le_ker_of_lt_top p hp
      have hf_mem : ∀ x ∈ p, f x = 0 := fun x hx => LinearMap.mem_ker.mp (hpker hx)
      have hu_p : u ∈ p := Submodule.mem_sup_left (Submodule.mem_sup_left hu)
      have hfu : f u = 0 := hf_mem u hu_p
      have hfw_u : f w = 0 :=
        hf_mem w (Submodule.mem_sup_left
          (Submodule.mem_sup_right (Submodule.mem_span_singleton_self w)))
      have hfE : ∀ e ∈ E, f e = 0 := fun e he => hf_mem e (Submodule.mem_sup_right he)
      have hex : ∃ x, f x ≠ 0 := by
        by_contra h
        push Not at h
        exact hfne (LinearMap.ext h)
      obtain ⟨x, hx⟩ := hex
      have hxmem : x ∈ W ⊔ E := by rw [hWE.sup_eq_top]; exact Submodule.mem_top
      rcases Submodule.mem_sup.mp hxmem with ⟨w₀, hw₀, e₀, he₀, rfl⟩
      have hfw₀ : f w₀ ≠ 0 := by
        have hfe₀ : f e₀ = 0 := hfE e₀ he₀
        simpa [map_add, hfe₀] using hx
      have hfw₁ : f w₀ = 1 := by
        rcases hF (f w₀) with h | h
        · exact absurd h hfw₀
        · exact h
      let S : (ι → F) →ₗ[F] (ι → F) := LinearMap.transvection f u - 1
      let Y : (ι → F) ≃ₗ[F] (ι → F) := LinearEquiv.transvection hfu
      let Ysl : SpecialLinearGroup F (ι → F) :=
        ⟨Y, LinearEquiv.transvection.det_eq_one hfu⟩
      let y : Matrix.SpecialLinearGroup ι F :=
        Matrix.SpecialLinearGroup.toLin'_equiv.symm Ysl
      have hS_apply : ∀ x : ι → F, S x = f x • u := by
        intro x
        rw [show S = LinearMap.transvection f u - 1 from rfl, LinearMap.sub_apply,
          LinearMap.transvection.apply]
        change (x + f x • u) - x = f x • u
        rw [add_sub_cancel_left]
      have hY_apply : ∀ x : ι → F, Y x = x + f x • u := by
        intro x
        rw [show Y = LinearEquiv.transvection hfu from rfl,
          LinearEquiv.transvection.apply]
      have hYlin : (Y : (ι → F) →ₗ[F] (ι → F)) = 1 + S := by
        rw [show (Y : (ι → F) →ₗ[F] (ι → F)) = LinearMap.transvection f u from
          LinearEquiv.transvection.coe_toLinearMap hfu]
        rw [show S = LinearMap.transvection f u - 1 from rfl]
        abel
      have hS2 : S * S = 0 := by
        apply LinearMap.ext
        intro x
        rw [Module.End.mul_apply, hS_apply, hS_apply, map_smul, hfu, smul_zero, zero_smul,
          LinearMap.zero_apply]
      have hS_ker : ∀ x ∈ U, S x = 0 := by
        intro x hx
        rw [hS_apply]
        have hx_p : x ∈ p := Submodule.mem_sup_left (Submodule.mem_sup_left hx)
        rw [hf_mem x hx_p, zero_smul]
      have hYinv : Y⁻¹ = Y := by
        have hYY : Y * Y = 1 := by
          apply LinearEquiv.ext
          intro x
          rw [LinearEquiv.mul_apply, hY_apply, hY_apply, map_add,
            map_smul, hfu, smul_zero, add_zero]
          change x + f x • u + f x • u = x
          rw [add_assoc, h2M, add_zero]
        exact inv_eq_of_mul_eq_one_right hYY
      have hVinv_eq : (V⁻¹ : (ι → F) ≃ₗ[F] (ι → F)) = V.symm := rfl
      have hVVsymm : (V : (ι → F) →ₗ[F] (ι → F)) *
          (V.symm : (ι → F) →ₗ[F] (ι → F)) = 1 := by
        rw [← LinearEquiv.coe_toLinearMap_mul, LinearEquiv.mul_eq_trans,
          LinearEquiv.symm_trans_self, LinearEquiv.refl_toLinearMap]
        rfl
      let T : (ι → F) →ₗ[F] (ι → F) :=
        (V : (ι → F) →ₗ[F] (ι → F)) * S * (V.symm : (ι → F) →ₗ[F] (ι → F))
      have hTS : T * S = 0 := by
        apply LinearMap.ext
        intro x
        rw [Module.End.mul_apply, LinearMap.zero_apply]
        rw [show T = (V : (ι → F) →ₗ[F] (ι → F)) * S *
          (V.symm : (ι → F) →ₗ[F] (ι → F)) from rfl,
          Module.End.mul_apply, Module.End.mul_apply]
        have hSxU : S x ∈ U := by
          rw [hS_apply]
          exact Submodule.smul_mem U (f x) hu
        have hVS : V.symm (S x) ∈ U :=
          hVinvU (Submodule.mem_map.mpr ⟨S x, hSxU, rfl⟩)
        change V (S (V.symm (S x))) = 0
        rw [hS_ker (V.symm (S x)) hVS, map_zero]
      have hA_lin : ((V * Y * V⁻¹ * Y⁻¹ : (ι → F) ≃ₗ[F] (ι → F)) :
          (ι → F) →ₗ[F] (ι → F)) = 1 + (T + S) := by
        rw [hYinv, hVinv_eq]
        simp only [LinearEquiv.coe_toLinearMap_mul]
        rw [hYlin]
        have hstep : (V : (ι → F) →ₗ[F] (ι → F)) * (1 + S) *
            (V.symm : (ι → F) →ₗ[F] (ι → F)) = 1 + T := by
          rw [mul_add, mul_one, add_mul, hVVsymm]
        rw [hstep, mul_add, mul_one, add_mul, one_mul, hTS, add_zero]
        abel
      have hy : Matrix.SpecialLinearGroup.toLin' y = Y := by
        have h := MulEquiv.apply_symm_apply Matrix.SpecialLinearGroup.toLin'_equiv Ysl
        exact congrArg (fun e : SpecialLinearGroup F (ι → F) =>
          (e : (ι → F) ≃ₗ[F] (ι → F))) h
      have hy_mat : Matrix.toLin' (y : Matrix ι ι F) = (Y : (ι → F) →ₗ[F] (ι → F)) := by
        rw [← Matrix.SpecialLinearGroup.toLin'_to_linearMap, hy]
      have hS_mat : Matrix.toLin' ((y : Matrix ι ι F) - 1) = S := by
        rw [map_sub, hy_mat, Matrix.toLin'_one, hYlin]
        exact add_sub_cancel_left _ _
      have h1 : ∀ x : ι → F, Matrix.toLin' ((y : Matrix ι ι F) - 1) x ∈ U := by
        intro x
        rw [hS_mat, hS_apply]
        exact Submodule.smul_mem U (f x) hu
      have h2 : ∀ u' ∈ U, Matrix.toLin' ((y : Matrix ι ι F) - 1) u' = 0 := by
        intro u' hu'
        rw [hS_mat, hS_ker u' hu']
      have h3 : ∀ e ∈ E, Matrix.toLin' ((y : Matrix ι ι F) - 1) e = 0 := by
        intro e he
        rw [hS_mat, hS_apply, hfE e he, zero_smul]
      have hgrp := hcomm y h1 h2 h3
      have hgrp' : V * Y * V⁻¹ * Y⁻¹ = 1 ∨ V * Y * V⁻¹ * Y⁻¹ = R := by
        rcases hgrp with h | h
        · left
          have hh := congrArg Matrix.SpecialLinearGroup.toLin' h
          simpa [V, R, hy, map_mul, map_inv] using hh
        · right
          have hh := congrArg Matrix.SpecialLinearGroup.toLin' h
          simpa [V, R, hy, map_mul, map_inv] using hh
      have hmem : V u ∈ Submodule.span F {u} := by
        rcases hgrp' with h | h
        · have hTS0 : T + S = 0 := by
            have h1eq : (1 : (ι → F) →ₗ[F] (ι → F)) = 1 + (T + S) := by
              rw [h] at hA_lin
              rwa [LinearEquiv.coe_toLinearMap_one] at hA_lin
            have h' : (1 : (ι → F) →ₗ[F] (ι → F)) + (T + S)
                = (1 : (ι → F) →ₗ[F] (ι → F)) + 0 := by
              rw [h1eq.symm, add_zero]
            exact add_left_cancel h'
          have h2S : S + S = 0 := by
            apply LinearMap.ext
            intro x
            simpa [LinearMap.add_apply, hS_apply] using h2M (f x • u)
          have hTS_eq : T = S := by
            calc T = T + 0 := (add_zero T).symm
              _ = T + (S + S) := by rw [h2S]
              _ = (T + S) + S := (add_assoc T S S).symm
              _ = 0 + S := by rw [hTS0]
              _ = S := zero_add S
          have hS_eq : V (S w₀) = S (V w₀) := by
            have h := congrArg (fun f : (ι → F) →ₗ[F] (ι → F) => f (V w₀)) hTS_eq
            have hT : T (V w₀) = V (S w₀) := by
              rw [show T = (V : (ι → F) →ₗ[F] (ι → F)) * S *
                (V.symm : (ι → F) →ₗ[F] (ι → F)) from rfl,
                Module.End.mul_apply, Module.End.mul_apply]
              change V (S (V.symm (V w₀))) = V (S w₀)
              rw [LinearEquiv.symm_apply_apply]
            rw [hT] at h
            exact h
          have hVuw₀ : V u = f (V w₀) • u := by
            rw [← hS_apply (V w₀), ← hS_eq, hS_apply, hfw₁, one_smul]
          exact Submodule.mem_span_singleton.mpr ⟨f (V w₀), hVuw₀.symm⟩
        · have hR1 : (R : (ι → F) →ₗ[F] (ι → F)) = 1 + N := by
            rw [hRN]
            abel
          have hTSN : T + S = N := by
            have h1eq : (1 : (ι → F) →ₗ[F] (ι → F)) + (T + S)
                = (1 : (ι → F) →ₗ[F] (ι → F)) + N := by
              rw [h] at hA_lin
              exact hA_lin.symm.trans hR1
            exact add_left_cancel h1eq
          have hTapp : T (V w) = 0 := by
            rw [show T = (V : (ι → F) →ₗ[F] (ι → F)) * S *
              (V.symm : (ι → F) →ₗ[F] (ι → F)) from rfl,
              Module.End.mul_apply, Module.End.mul_apply]
            change V (S (V.symm (V w))) = 0
            rw [LinearEquiv.symm_apply_apply, hS_apply, hfw_u, zero_smul, map_zero]
          have hNapp : N (V w) = V u := by
            rw [← hVN_apply w, hNw]
          have hTSapp := congrArg (fun f : (ι → F) →ₗ[F] (ι → F) => f (V w)) hTSN
          rw [LinearMap.add_apply, hTapp, hNapp] at hTSapp
          rw [hS_apply, zero_add] at hTSapp
          exact Submodule.mem_span_singleton.mpr ⟨f (V w), hTSapp⟩
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
      have hcne : c ≠ 0 := by
        intro hc0
        have h : V u = V 0 := by rw [← hc, hc0, zero_smul, map_zero]
        exact hu0 (V.injective h)
      have hc1 : c = 1 := by
        rcases hF c with h | h
        · exact absurd h hcne
        · exact h
      rw [← hc, hc1, one_smul]
  let D : (ι → F) →ₗ[F] (ι → F) := Matrix.toLin' ((v : Matrix ι ι F) - 1)
  have hD_apply : ∀ x : ι → F, D x = V x - x := by
    intro x
    change Matrix.toLin' ((v : Matrix ι ι F) - 1) x = _
    rw [Matrix.toLin'_apply, Matrix.sub_mulVec, Matrix.one_mulVec, ← hV_apply]
  have hD : D = (V : (ι → F) →ₗ[F] (ι → F)) - 1 := LinearMap.ext hD_apply
  have hDU : ∀ u ∈ U, D u = 0 := by
    intro u hu
    rw [hD_apply, hVU u hu, sub_self]
  have hDE : ∀ e ∈ E, D e = 0 := by
    intro e he
    rw [hD_apply, hVE e he, sub_self]
  have hrangeDU : LinearMap.range D ≤ U := by
    rintro y ⟨x, rfl⟩
    have hxmem : x ∈ W ⊔ E := by rw [hWE.sup_eq_top]; exact Submodule.mem_top
    rcases Submodule.mem_sup.mp hxmem with ⟨w, hw, e, he, rfl⟩
    rw [map_add, hDE e he, add_zero]
    have hDw : D w ∈ U := by
      rw [← hWkerU]
      refine ⟨?_, ?_⟩
      · rw [hD_apply]
        exact Submodule.sub_mem W (hVW w hw) hw
      · refine LinearMap.mem_ker.mpr ?_
        rw [hD_apply, map_sub, ← hVN_apply w]
        have hNw : N w ∈ U := ⟨w, rfl⟩
        rw [hVU (N w) hNw, sub_self]
    exact hDw
  have hker_le : LinearMap.ker N ≤ LinearMap.ker D := by
    rw [hker_eq]
    intro x hx
    rcases Submodule.mem_sup.mp hx with ⟨u, hu, e, he, rfl⟩
    refine LinearMap.mem_ker.mpr ?_
    rw [map_add, hDU u hu, hDE e he, add_zero]
  obtain ⟨j, hj⟩ := hconj
  let J : (ι → F) ≃ₗ[F] (ι → F) := Matrix.SpecialLinearGroup.toLin' j
  have hJinvmul : ((J⁻¹ : (ι → F) ≃ₗ[F] (ι → F)) : (ι → F) →ₗ[F] (ι → F))
      * (J : (ι → F) →ₗ[F] (ι → F)) = 1 := by
    rw [← LinearEquiv.coe_toLinearMap_mul, inv_mul_cancel, LinearEquiv.coe_toLinearMap_one]
    rfl
  have hVJ : (V : (ι → F) →ₗ[F] (ι → F))
      = (J : (ι → F) →ₗ[F] (ι → F)) * (R : (ι → F) →ₗ[F] (ι → F))
        * ((J⁻¹ : (ι → F) ≃ₗ[F] (ι → F)) : (ι → F) →ₗ[F] (ι → F)) := by
    have h := congrArg Matrix.SpecialLinearGroup.toLin' hj
    have h' : V = J * R * J⁻¹ := by
      simpa [V, R, J, map_mul, map_inv] using h
    have h'' := congrArg (fun e : (ι → F) ≃ₗ[F] (ι → F) =>
      (e : (ι → F) →ₗ[F] (ι → F))) h'
    rwa [LinearEquiv.coe_toLinearMap_mul, LinearEquiv.coe_toLinearMap_mul] at h''
  have hDJ : D * (J : (ι → F) →ₗ[F] (ι → F))
      = (J : (ι → F) →ₗ[F] (ι → F)) * N := by
    have hVJ' : (V : (ι → F) →ₗ[F] (ι → F)) * (J : (ι → F) →ₗ[F] (ι → F))
        = (J : (ι → F) →ₗ[F] (ι → F)) * (R : (ι → F) →ₗ[F] (ι → F)) := by
      rw [hVJ, mul_assoc, hJinvmul, mul_one]
    rw [hD, hRN, sub_mul, mul_sub, mul_one, one_mul, hVJ']
  have hrangeD : LinearMap.range D
      = (LinearMap.range N).map (J : (ι → F) →ₗ[F] (ι → F)) := by
    apply le_antisymm
    · rintro y ⟨x, rfl⟩
      have hx : x ∈ LinearMap.range (J : (ι → F) →ₗ[F] (ι → F)) := by
        rw [LinearMap.range_eq_top.mpr (LinearEquiv.surjective J)]
        exact Submodule.mem_top
      rcases hx with ⟨z, rfl⟩
      refine Submodule.mem_map.mpr ⟨N z, ⟨z, rfl⟩, ?_⟩
      have h := congrArg (fun f : (ι → F) →ₗ[F] (ι → F) => f z) hDJ
      simpa [Module.End.mul_apply] using h.symm
    · rintro y ⟨z, ⟨x, rfl⟩, rfl⟩
      refine ⟨J x, ?_⟩
      have h := congrArg (fun f : (ι → F) →ₗ[F] (ι → F) => f x) hDJ
      simpa [Module.End.mul_apply] using h
  have hfinrangeD : Module.finrank F (LinearMap.range D) = 2 := by
    rw [hrangeD, LinearEquiv.finrank_map_eq, hrank]
  have hrangeD_eq : LinearMap.range D = U := by
    refine Submodule.eq_of_le_of_finrank_eq hrangeDU ?_
    rw [hfinrangeD, hrank]
  have hkerfin : Module.finrank F (LinearMap.ker D) = Module.finrank F (LinearMap.ker N) := by
    have hD := LinearMap.finrank_range_add_finrank_ker D
    have hN := LinearMap.finrank_range_add_finrank_ker N
    have hrange : Module.finrank F (LinearMap.range D) = Module.finrank F (LinearMap.range N) := by
      rw [hfinrangeD, hrank]
    omega
  have hkerD_eq : LinearMap.ker D = LinearMap.ker N := by
    refine (Submodule.eq_of_le_of_finrank_eq hker_le ?_).symm
    rw [hkerfin]
  change LinearMap.range (Matrix.toLin' ((v : Matrix ι ι F) - 1)) = U ∧
    LinearMap.ker (Matrix.toLin' ((v : Matrix ι ι F) - 1)) = LinearMap.ker N
  exact ⟨hrangeD_eq, hkerD_eq⟩

end CFSG.LinearAlgebra
