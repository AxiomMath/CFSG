module

public import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.A2Heis.Spread
public import CFSG.HardMathSupport.Malle.Coordinator.SeitzA2Three.Assembly
public import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.A2Heis.Root

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.A2Heis

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.HardMathSupport.Malle.Coordinator.SeitzA2Three
open CFSG.HardMathSupport.Foote.ModuleExclusions (fixF mem_fixF tbar)
open scoped MatrixGroups

variable {F : Type} [Field F] [Finite F]

theorem fixed_primitive_cube_root {σ : F ≃+* F} (hσ : orderOf σ = 3) {ω : F}
    (hω : IsPrimitiveRoot ω 3) : σ ω = ω := by
  have h3 : σ ^ 3 = 1 := hσ ▸ pow_orderOf_eq_one σ
  have hσ3 : σ (σ (σ ω)) = ω := by
    have := congrArg (fun τ : F ≃+* F => τ ω) h3
    simpa [pow_succ] using this
  have hpow : (σ ω) ^ 3 = 1 := by rw [← map_pow, hω.pow_eq_one, map_one]
  obtain ⟨i, hi, hiω⟩ := hω.eq_pow_of_pow_eq_one hpow
  interval_cases i
  · exfalso
    rw [pow_zero] at hiω
    have : ω = 1 := σ.injective (by rw [← hiω, map_one])
    exact hω.ne_one (by norm_num) this
  · rw [pow_one] at hiω; exact hiω.symm
  · exfalso
    have h1 : σ (σ ω) = ω := by
      rw [← hiω, map_pow, ← hiω, ← pow_mul, show 2 * 2 = 3 + 1 by rfl, pow_succ, hω.pow_eq_one,
        one_mul]
    rw [h1, ← hiω] at hσ3
    have hne : ω ^ 2 ≠ ω := by
      intro h
      have hω0 : ω ≠ 0 := hω.ne_zero (by norm_num)
      have : ω = 1 := by
        have h' : ω * ω = ω * 1 := by rw [mul_one, ← sq]; exact h
        exact mul_left_cancel₀ hω0 h'
      exact hω.ne_one (by norm_num) this
    exact hne hσ3

theorem perm_conj_tbar {i j i' j' : Fin 3} (hij : i ≠ j) (hij' : i' ≠ j') (y : F)
    (hm : (!![0, 0, 1; 1, 0, 0; 0, 1, 0] : Matrix (Fin 3) (Fin 3) F) * (1 + Matrix.single i j y) *
      !![0, 1, 0; 0, 0, 1; 1, 0, 0] = 1 + Matrix.single i' j' y) :
    proj 3 F permSL * tbar hij y * (proj 3 F permSL)⁻¹ = tbar hij' y := by
  have h := conjAut_toGL (n := 3) (K := F) permSL
  rw [← MulAut.conj_apply, ← h]
  unfold tbar
  rw [conjAut_proj]
  congr 1
  apply Subtype.ext
  rw [coe_slConjugation]
  have hinv : (((Matrix.SpecialLinearGroup.toGL permSL)⁻¹ : GL (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) = !![0, 1, 0; 0, 0, 1; 1, 0, 0] := by
    rw [Matrix.coe_units_inv, Matrix.inv_eq_left_inv]
    change !![0, 1, 0; 0, 0, 1; 1, 0, 0] * ((permSL : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = 1
    rw [coe_permSL]
    ext a b
    fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  rw [hinv]
  change ((permSL : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) * (1 + Matrix.single i j y) * _ = _
  rw [coe_permSL]
  exact hm

theorem perm_conj_01 (y : F) :
    proj 3 F permSL * tbar h01 y * (proj 3 F permSL)⁻¹ =
      tbar (show (1 : Fin 3) ≠ 2 by decide) y := by
  refine perm_conj_tbar _ _ y ?_
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply, Matrix.one_apply,
      Matrix.vecMul, dotProduct]

theorem perm_conj_12 (y : F) :
    proj 3 F permSL * tbar (show (1 : Fin 3) ≠ 2 by decide) y * (proj 3 F permSL)⁻¹ =
      tbar (show (2 : Fin 3) ≠ 0 by decide) y := by
  refine perm_conj_tbar _ _ y ?_
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply, Matrix.one_apply,
      Matrix.vecMul, dotProduct]

theorem a2ThreeHeisGen_holds : A2ThreeHeisGen := by
  intro F _ _ σ hσ h3 h4 lam ω hl hω
  have hω3 : ω ^ 3 = 1 := by
    apply Units.ext; rw [Units.val_pow_eq_pow_val, hω.pow_eq_one, Units.val_one]
  have h : HeisHyp σ lam ω := ⟨hσ, hω3, hl, fixed_primitive_cube_root hσ hω⟩
  set M := Subgroup.closure (hyperFix σ lam ω)
  have : Fact (1 < Nat.card (fixF σ)) := ⟨by omega⟩
  obtain ⟨u, hu⟩ : ∃ u : (fixF σ)ˣ, u ^ 3 ≠ 1 :=
    exists_pow_ne_one_of_isCyclic (by norm_num) (by rw [Nat.card_units]; omega)
  set γ : F := ((u : fixF σ) : F)
  have hγ0 : γ ≠ 0 := fun h0 => u.ne_zero (Subtype.ext h0)
  have hγσ : σ γ = γ := mem_fixF.1 (u : fixF σ).2
  have hγ3 : γ ^ 3 ≠ 1 := by
    intro h1
    apply hu
    apply Units.ext
    apply Subtype.ext
    simpa [γ] using h1
  obtain ⟨α, hα0, hασ, hΔ⟩ : ∃ α : F, α ≠ 0 ∧ σ α = α ∧ α ^ 3 + (lam : F) ≠ 0 := by
    by_cases h1 : (1 : F) ^ 3 + lam ≠ 0
    · exact ⟨1, one_ne_zero, map_one σ, h1⟩
    · push_neg at h1
      refine ⟨γ, hγ0, hγσ, fun h2 => hγ3 ?_⟩
      linear_combination h2 - h1
  have hΔσ : σ (α ^ 3 + (lam : F))⁻¹ = (α ^ 3 + (lam : F))⁻¹ := by
    rw [map_inv₀, map_add, map_pow, hασ, hl]
  obtain ⟨μ', hμ'⟩ := exists_cube_root_of_fixed hσ h3 (inv_ne_zero hΔ) hΔσ
  have hμ'0 : μ' ≠ 0 := by
    rintro rfl
    have : (α ^ 3 + (lam : F))⁻¹ = 0 := by rw [← hμ']; ring
    exact hΔ (inv_eq_zero.1 this)
  have hμ : ((Units.mk0 μ' hμ'0 : Fˣ) : F) ^ 3 * (α ^ 3 + lam) = 1 := by
    rw [Units.val_mk0, hμ', inv_mul_cancel₀ hΔ]
  have hc := tbar_mem_closure_hyperFix h hασ hγσ hγ0 hΔ _ hμ
  have hc0 := nc_mul_ne_zero (lam := lam) hα0 hγ0 hΔ hγ3
  have h01y : ∀ y : F, tbar h01 y ∈ M := fun y => rootSet_eq_univ h h3 hc0 hc y
  have hP := Subgroup.subset_closure (mem_hyperFix_perm h)
  have h12y : ∀ y : F, tbar (show (1 : Fin 3) ≠ 2 by decide) y ∈ M := by
    intro y
    rw [← perm_conj_01]
    exact M.mul_mem (M.mul_mem hP (h01y y)) (M.inv_mem hP)
  have h20y : ∀ y : F, tbar (show (2 : Fin 3) ≠ 0 by decide) y ∈ M := by
    intro y
    rw [← perm_conj_12]
    exact M.mul_mem (M.mul_mem hP (h12y y)) (M.inv_mem hP)
  have hcomm : ∀ {i j l : Fin 3} (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l),
      (∀ y : F, tbar hij y ∈ M) → (∀ y : F, tbar hjl y ∈ M) → ∀ y : F, tbar hil y ∈ M := by
    intro i j l hij hjl hil hi hj y
    have hc := Matrix.SpecialLinearGroup.commutatorElement_transvection hij hjl hil y (1 : F)
    rw [mul_one] at hc
    unfold tbar at hi hj ⊢
    rw [← hc, map_commutatorElement, commutatorElement_def]
    exact M.mul_mem (M.mul_mem (M.mul_mem (hi y) (hj 1)) (M.inv_mem (hi y))) (M.inv_mem (hj 1))
  have h02y := hcomm h01 (show (1 : Fin 3) ≠ 2 by decide) (show (0 : Fin 3) ≠ 2 by decide) h01y h12y
  have h10y := hcomm (show (1 : Fin 3) ≠ 2 by decide) (show (2 : Fin 3) ≠ 0 by decide)
    (show (1 : Fin 3) ≠ 0 by decide) h12y h20y
  have h21y := hcomm (show (2 : Fin 3) ≠ 0 by decide) h01 (show (2 : Fin 3) ≠ 1 by decide) h20y h01y
  have hall : ∀ {i j : Fin 3} (hij : i ≠ j) (y : F), tbar hij y ∈ M := by
    intro i j hij y
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact h01y y
    · exact h02y y
    · exact h10y y
    · exact absurd rfl hij
    · exact h12y y
    · exact h20y y
    · exact h21y y
    · exact absurd rfl hij
  rw [modelHyperGen_iff, eq_top_iff]
  intro p _
  obtain ⟨g, rfl⟩ := proj_surjective 3 F p
  have hg : g ∈ Subgroup.closure (CFSG.LinearGroups.elementarySet 3 F) := by
    rw [CFSG.LinearGroups.special_linear_elementary_generation]; trivial
  refine Subgroup.closure_induction (p := fun g _ => proj 3 F g ∈ M) ?_ ?_ ?_ ?_ hg
  · rintro _ ⟨i, j, hij, c, rfl⟩
    exact hall hij c
  · rw [map_one]; exact M.one_mem
  · intro x y _ _ hx hy
    rw [map_mul]; exact M.mul_mem hx hy
  · intro x _ hx
    rw [map_inv]; exact M.inv_mem hx

end CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.A2Heis
