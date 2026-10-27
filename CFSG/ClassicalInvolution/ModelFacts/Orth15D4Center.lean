module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15D4Triality
public import CFSG.ClassicalInvolution.ModelFacts.Orth15TwinSpin

public section

namespace CFSG.ClassicalInvolution.G2D4Models.Twin

open scoped MatrixGroups
open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.CurtisTits
  CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.ModelFacts.D4Rigid
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.LieType.HighestRoot QuadraticMap
  CFSG.ClassicalInvolution.Models.Transfer

section Action

variable {F : Type} [Field F]

theorem diagSL2_neg_one_eq : diagSL2 (-1 : Fˣ) = (-1 : SL(2, F)) := by
  apply Subtype.ext
  rw [coe_diagSL2, Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem longSL2_neg_one_eq_longTorus {i j : Fin 4} (hij : i ≠ j) (s t : Bool) :
    (fr F).longSL2 hij s t (-1) = (fr F).longTorus hij s t (-1) := by
  rw [HypFrame.longTorus_apply, diagSL2_neg_one_eq]

@[expose] def d0 (F : Type) [Field F] (μ : Idx) : F := if (Sum.elim id id μ).val < 2 then -1 else 1

@[expose] def d2 (F : Type) [Field F] (μ : Idx) : F := if 2 ≤ (Sum.elim id id μ).val then -1 else 1

theorem spinAction_z0_apply (v : Idx → F) (μ : Idx) :
    spinAction (quadPlus 4 F) (z0 F) v μ = d0 F μ * v μ := by
  rw [z0, longSL2_neg_one_eq_longTorus, spinAction_longTorus_apply]
  congr 1
  rcases μ with i | i <;> fin_cases i <;> simp [lamT, idx, d0]

theorem spinAction_z2_apply (v : Idx → F) (μ : Idx) :
    spinAction (quadPlus 4 F) (z2 F) v μ = d2 F μ * v μ := by
  rw [z2, longSL2_neg_one_eq_longTorus, spinAction_longTorus_apply]
  congr 1
  rcases μ with i | i <;> fin_cases i <;> simp [lamT, idx, d2]

theorem spinAction_z3_apply (v : Idx → F) (μ : Idx) :
    spinAction (quadPlus 4 F) (z3 F) v μ = d2 F μ * v μ := by
  rw [z3, longSL2_neg_one_eq_longTorus, spinAction_longTorus_apply]
  congr 1
  rcases μ with i | i <;> fin_cases i <;> simp [lamT, idx, d2]

end Action

section Products

variable {F : Type} [Field F]

theorem d2_mul_self (μ : Idx) : d2 F μ * d2 F μ = 1 := by
  rcases μ with i | i <;> fin_cases i <;> simp [d2]

theorem d0_mul_d2 (μ : Idx) : d0 F μ * d2 F μ = -1 := by
  rcases μ with i | i <;> fin_cases i <;> simp [d0, d2]

theorem spinAction_mul_apply (g h : spinGroup (quadPlus 4 F)) (v : Idx → F) :
    spinAction (quadPlus 4 F) (g * h) v =
      spinAction (quadPlus 4 F) g (spinAction (quadPlus 4 F) h v) := by
  rw [map_mul]
  rfl

theorem spinAction_z2_mul_z3 : spinAction (quadPlus 4 F) (z2 F * z3 F) = 1 := by
  refine LinearEquiv.ext fun v => funext fun μ => ?_
  rw [spinAction_mul_apply, spinAction_z2_apply]
  have h3 : spinAction (quadPlus 4 F) (z3 F) v = fun ν => d2 F ν * v ν :=
    funext fun ν => spinAction_z3_apply v ν
  rw [h3]
  show d2 F μ * (d2 F μ * v μ) = v μ
  rw [← mul_assoc, d2_mul_self, one_mul]

theorem spinAction_z3_mul_z0 :
    spinAction (quadPlus 4 F) (z3 F * z0 F) = LinearEquiv.neg F := by
  refine LinearEquiv.ext fun v => funext fun μ => ?_
  rw [spinAction_mul_apply, spinAction_z3_apply]
  have h3 : spinAction (quadPlus 4 F) (z0 F) v = fun ν => d0 F ν * v ν :=
    funext fun ν => spinAction_z0_apply v ν
  rw [h3]
  show d2 F μ * (d0 F μ * v μ) = -v μ
  rw [← mul_assoc, mul_comm (d2 F μ), d0_mul_d2]
  simp

theorem spinAction_z0_mul_z2 :
    spinAction (quadPlus 4 F) (z0 F * z2 F) = LinearEquiv.neg F := by
  refine LinearEquiv.ext fun v => funext fun μ => ?_
  rw [spinAction_mul_apply, spinAction_z0_apply]
  have h3 : spinAction (quadPlus 4 F) (z2 F) v = fun ν => d2 F ν * v ν :=
    funext fun ν => spinAction_z2_apply v ν
  rw [h3]
  show d0 F μ * (d2 F μ * v μ) = -v μ
  rw [← mul_assoc, d0_mul_d2]
  simp

theorem coe_z3 :
    (z3 F : CliffordAlgebra (quadPlus 4 F)) = -(z2 F : CliffordAlgebra (quadPlus 4 F)) :=
  coe_longSL2_not_neg_one (fr F) ne23 true false

theorem coe_z2_mul_z3 :
    ((z2 F * z3 F : spinGroup (quadPlus 4 F)) : CliffordAlgebra (quadPlus 4 F)) = -1 := by
  have h2 : (z2 F : CliffordAlgebra (quadPlus 4 F)) * (z2 F : CliffordAlgebra (quadPlus 4 F)) =
      1 := by
    have := congrArg (fun g : spinGroup (quadPlus 4 F) => (g : CliffordAlgebra (quadPlus 4 F)))
      (z2_mul_self (F := F))
    simpa using this
  rw [Submonoid.coe_mul, coe_z3, mul_neg, h2]

end Products

section Ordinary

variable {p f : ℕ} [Fact p.Prime]

theorem exists_aut_ordinary (hp2 : p ≠ 2) (hadm : StatedLieAdmissible .POmegaPlus 4 p f)
    (ρ : spinGroup (quadPlus 4 (GaloisField p f)) ≃* spinGroup (quadPlus 4 (GaloisField p f)))
    (hρ : ∀ k : Fin 4, (rankOne (plusDatum 4 (GaloisField p f) (by norm_num)).rootGroup k).map
      ρ.toMonoidHom = rankOne (plusDatum 4 (GaloisField p f) (by norm_num)).rootGroup (triPerm k))
    {c : spinGroup (quadPlus 4 (GaloisField p f))} (hc : c ∈ Subgroup.center _) (hc2 : c * c = 1) :
    ∃ σ : spinGroup (quadPlus 4 (GaloisField p f)) ≃* spinGroup (quadPlus 4 (GaloisField p f)),
      PreservesFund p f σ ∧ spinAction (quadPlus 4 (GaloisField p f)) (σ c) = 1 := by
  have hn3 : 3 ≤ 4 := by norm_num
  set F := GaloisField p f with hFdef
  set θ := spinAction (quadPlus 4 F) with hθ
  have h2 : (2 : F) ≠ 0 := CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f hp2
  obtain ⟨μ, hμ⟩ := CFSG.ClassicalInvolution.ModelFacts.Orth15.exists_smul_of_central
    (range_spinAction_quadPlus (K := F) hn3) (centerScalar_quadPlus (K := F) hn3) hc
  have hμ2 : μ * μ = 1 := by
    have h1 := hμ (Pi.single (Sum.inl 0) 1)
    have h3 : θ (c * c) (Pi.single (Sum.inl 0) 1) = Pi.single (Sum.inl 0) 1 := by
      rw [hc2, map_one]
      rfl
    rw [map_mul, LinearEquiv.mul_apply, h1, map_smul, hμ, smul_smul] at h3
    have h4 := congrFun h3 (Sum.inl 0)
    simpa using h4
  rcases mul_self_eq_one_iff.mp hμ2 with hμ1 | hμ1
  ·
    refine ⟨MulEquiv.refl _, PreservesFund.refl, ?_⟩
    refine LinearEquiv.ext fun v => ?_
    show θ c v = v
    rw [hμ, hμ1, one_smul]
  ·
    have hθc : θ c = LinearEquiv.neg F := LinearEquiv.ext fun v => by
      rw [hμ, hμ1, neg_one_smul]
      rfl
    set b : spinGroup (quadPlus 4 F) := z2 F * z3 F with hb
    set b₁ : spinGroup (quadPlus 4 F) := z3 F * z0 F with hb₁
    set b₂ : spinGroup (quadPlus 4 F) := z0 F * z2 F with hb₂
    have hθb : θ b = 1 := spinAction_z2_mul_z3
    have hθb₁ : θ b₁ = LinearEquiv.neg F := spinAction_z3_mul_z0
    have hθb₂ : θ b₂ = LinearEquiv.neg F := spinAction_z0_mul_z2
    have hker : ∀ g : spinGroup (quadPlus 4 F), θ g = 1 → g = 1 ∨ g = b := by
      intro g hg
      rcases eq_one_or_eq_neg_one_of_spinAction_eq_one (n := 4) (K := F) g hg with h | h
      · left
        exact Subtype.ext (by rw [h]; rfl)
      · right
        exact Subtype.ext (by rw [h, hb, coe_z2_mul_z3])
    have hz0 := triality_z0 h2 ρ hρ
    have hz2 := triality_z2 h2 ρ hρ
    have hz3 := triality_z3 h2 ρ hρ
    have s0 : ρ.symm (z2 F) = z0 F := by rw [← hz0]; simp
    have s2 : ρ.symm (z3 F) = z2 F := by rw [← hz2]; simp
    have s3 : ρ.symm (z0 F) = z3 F := by rw [← hz3]; simp
    have hσ1 : PreservesFund p f ρ.symm :=
      preservesFund_of_nodes hadm ρ.symm triEquiv.symm (symm_nodes ρ triEquiv hρ)
    have hg : θ (c * b₁⁻¹) = 1 := by
      rw [map_mul, map_inv, hθc, hθb₁]
      exact mul_inv_cancel _
    rcases hker _ hg with h | h
    ·
      have hcb : c = b₁ := mul_inv_eq_one.mp h
      refine ⟨ρ.symm, hσ1, ?_⟩
      rw [hcb, hb₁, map_mul, s2, s3]
      exact hθb
    ·
      have hcb : c = b * b₁ := by
        have := congrArg (· * b₁) h
        simpa using this
      refine ⟨ρ.symm.trans ρ.symm, hσ1.comp hσ1, ?_⟩
      have e1 : ρ.symm b = b₂ := by rw [hb, map_mul, s0, s2]
      have e2 : ρ.symm b₁ = b := by rw [hb₁, map_mul, s2, s3]
      have e3 : ρ.symm b₂ = b₁ := by rw [hb₂, map_mul, s3, s0]
      have hfin : ρ.symm (ρ.symm c) = b₁ * b₂ := by
        rw [hcb, map_mul, e1, e2, map_mul, e3, e1]
      show θ (ρ.symm (ρ.symm c)) = 1
      rw [hfin, map_mul, hθb₁, hθb₂]
      refine LinearEquiv.ext fun v => ?_
      exact neg_neg v

end Ordinary

end CFSG.ClassicalInvolution.G2D4Models.Twin
