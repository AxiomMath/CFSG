module

public import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.A2Heis.FieldFacts
public import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.A2Heis.Elements

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.A2Heis

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.HardMathSupport.Malle.Coordinator.SeitzA2Three
open CFSG.HardMathSupport.Foote.ModuleExclusions (fixF mem_fixF tbar)
open scoped MatrixGroups

variable {F : Type} [Field F] [Finite F] {σ : F ≃+* F} {lam ω : Fˣ}

theorem h01 : (0 : Fin 3) ≠ 1 := by decide

@[expose] def rootSet (σ : F ≃+* F) (lam ω : Fˣ) : Set F :=
  {y | tbar h01 y ∈ Subgroup.closure (hyperFix σ lam ω)}

theorem mem_rootSet {y : F} :
    y ∈ rootSet σ lam ω ↔ tbar h01 y ∈ Subgroup.closure (hyperFix σ lam ω) := Iff.rfl

theorem rootSet_add {y y' : F} (hy : y ∈ rootSet σ lam ω) (hy' : y' ∈ rootSet σ lam ω) :
    y + y' ∈ rootSet σ lam ω := by
  rw [mem_rootSet] at hy hy' ⊢
  rw [CFSG.HardMathSupport.Foote.ModuleExclusions.tbar_add]
  exact Subgroup.mul_mem _ hy hy'

theorem zero_mem_rootSet : (0 : F) ∈ rootSet σ lam ω := by
  rw [mem_rootSet, CFSG.HardMathSupport.Foote.ModuleExclusions.tbar_zero]
  exact Subgroup.one_mem _

theorem rootSet_mul_fixed (h : HeisHyp σ lam ω) {u : F} (hu : σ u = u) {y : F}
    (hy : y ∈ rootSet σ lam ω) : u * y ∈ rootSet σ lam ω := by
  by_cases hu0 : u = 0
  · rw [hu0, zero_mul]; exact zero_mem_rootSet
  set v : Fˣ := Units.mk0 u hu0
  have hD : proj 3 F (CFSG.HardMathSupport.Foote.ModuleExclusions.Dsl h01 v) ∈
      hyperFix σ lam ω := by
    refine mem_hyperFix_diag h _ (CFSG.HardMathSupport.Foote.ModuleExclusions.Dsl_offdiag h01 v)
      fun i => ?_
    simp only [CFSG.HardMathSupport.Foote.ModuleExclusions.Dsl, Matrix.diagonal_apply_eq,
      CFSG.HardMathSupport.Foote.ModuleExclusions.dvec]
    fin_cases i <;> simp [v, hu, map_inv₀]
  have := CFSG.HardMathSupport.Foote.ModuleExclusions.Dsl_conj_tbar h01 v y
  rw [mem_rootSet] at hy ⊢
  rw [show u = (v : F) from rfl, ← this]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.subset_closure hD) hy)
    (Subgroup.inv_mem _ (Subgroup.subset_closure hD))

theorem toGL_twistSL (a μ : Fˣ) (hμ : (μ : F) ^ 3 * ((a : F) * σ a * σ (σ a)) = 1) :
    Matrix.SpecialLinearGroup.toGL (twistSL σ a μ hμ) =
      CFSG.HardMathSupport.Foote.ModuleExclusions.diagGL
        ![μ * a, μ * Units.map (σ : F →* F) a,
          μ * Units.map (σ : F →* F) (Units.map (σ : F →* F) a)] := by
  apply Units.ext
  change ((twistSL σ a μ hμ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = _
  rw [coe_twistSL, CFSG.HardMathSupport.Foote.ModuleExclusions.coe_diagGL]
  congr 1
  funext k
  fin_cases k <;> simp

theorem rootSet_mul_ratio (h : HeisHyp σ lam ω) (h3 : 3 ∣ Nat.card F - 1) (a : Fˣ) {y : F}
    (hy : y ∈ rootSet σ lam ω) : (a : F) / σ a * y ∈ rootSet σ lam ω := by
  have hσ3 : ∀ x : F, σ (σ (σ x)) = x := by
    intro x
    have := congrArg (fun τ : F ≃+* F => τ x) h.pow3
    simpa [pow_succ] using this
  set N : F := (a : F) * σ a * σ (σ a) with hN
  have hN0 : N ≠ 0 := by
    have : (a : F) ≠ 0 := a.ne_zero
    simp [hN, this]
  have hNσ : σ N⁻¹ = N⁻¹ := by
    rw [map_inv₀, hN, map_mul, map_mul, hσ3]; ring_nf
  obtain ⟨μ', hμ'⟩ := exists_cube_root_of_fixed h.ord h3 (inv_ne_zero hN0) hNσ
  have hμ'0 : μ' ≠ 0 := by
    rintro rfl
    have : N⁻¹ = 0 := by rw [← hμ']; ring
    exact hN0 (inv_eq_zero.1 this)
  set μ : Fˣ := Units.mk0 μ' hμ'0
  have hμ : (μ : F) ^ 3 * ((a : F) * σ a * σ (σ a)) = 1 := by
    change μ' ^ 3 * N = 1
    rw [hμ', inv_mul_cancel₀ hN0]
  have hT := Subgroup.subset_closure (mem_hyperFix_twisted h a μ hμ)
  have hconj := CFSG.HardMathSupport.Foote.ModuleExclusions.conjAut_diagGL_tbar
    ![μ * a, μ * Units.map (σ : F →* F) a,
      μ * Units.map (σ : F →* F) (Units.map (σ : F →* F) a)] h01 y
  rw [← toGL_twistSL a μ hμ, conjAut_toGL, MulAut.conj_apply] at hconj
  have hcoef : ((μ * a : Fˣ) : F) * y * (((μ * Units.map (σ : F →* F) a)⁻¹ : Fˣ) : F) =
      (a : F) / σ a * y := by
    have hμ0 : (μ : F) ≠ 0 := μ.ne_zero
    have hσa : σ (a : F) ≠ 0 := by simp
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.coe_map, MonoidHom.coe_coe]
    field_simp
  rw [mem_rootSet] at hy ⊢
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at hconj
  rw [← hcoef, ← hconj]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hT hy) (Subgroup.inv_mem _ hT)

theorem rootSet_eq_univ (h : HeisHyp σ lam ω) (h3 : 3 ∣ Nat.card F - 1) {c : F} (hc0 : c ≠ 0)
    (hc : c ∈ rootSet σ lam ω) (y : F) : y ∈ rootSet σ lam ω := by
  classical
  set K₁ : Set F := {x | ∃ a : Fˣ, x = (a : F) / σ a}
  have hact : ∀ r ∈ Algebra.adjoin (fixF σ) K₁, ∀ z ∈ rootSet σ lam ω, r * z ∈ rootSet σ lam ω := by
    intro r hr
    induction hr using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      exact fun z hz => rootSet_mul_ratio h h3 a hz
    | algebraMap f =>
      intro z hz
      exact rootSet_mul_fixed h (mem_fixF.1 f.2) hz
    | add r s _ _ hr hs =>
      intro z hz
      rw [add_mul]
      exact rootSet_add (hr z hz) (hs z hz)
    | mul r s _ _ hr hs =>
      intro z hz
      rw [mul_assoc]
      exact hr _ (hs z hz)
  have hprime : (Module.finrank (fixF σ) F).Prime := by
    rw [finrank_fixF h.ord]; exact Nat.prime_three
  have : IsSimpleOrder (IntermediateField (fixF σ) F) :=
    IntermediateField.isSimpleOrder_of_finrank_prime _ _ hprime
  have hE : IntermediateField.adjoin (fixF σ) K₁ = ⊤ := by
    rcases IsSimpleOrder.eq_bot_or_eq_top (IntermediateField.adjoin (fixF σ) K₁) with hb | ht
    · exfalso
      obtain ⟨a, ha⟩ := exists_ratio_not_fixed h.ord
      have hmem : (a : F) / σ a ∈ IntermediateField.adjoin (fixF σ) K₁ :=
        IntermediateField.subset_adjoin _ _ ⟨a, rfl⟩
      rw [hb, IntermediateField.mem_bot] at hmem
      obtain ⟨f, hf⟩ := hmem
      apply ha
      rw [← hf]
      exact mem_fixF.1 f.2
    · exact ht
  have hA : Algebra.adjoin (fixF σ) K₁ = ⊤ := by
    have halg : ∀ x ∈ K₁, IsAlgebraic (fixF σ) x := fun x _ => Algebra.IsAlgebraic.isAlgebraic x
    rw [← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic halg, hE,
      IntermediateField.top_toSubalgebra]
  have hyc : y * c⁻¹ ∈ Algebra.adjoin (fixF σ) K₁ := by rw [hA]; trivial
  have := hact _ hyc c hc
  rwa [mul_assoc, inv_mul_cancel₀ hc0, mul_one] at this

end CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.A2Heis
