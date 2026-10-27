module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.K32TableL3Field
public import CFSG.RankThree.PartTwo.KFacts.AutPSLOrderThree
public import CFSG.RankThree.SteinbergR3ELinearRegularUnipotent
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherFieldInvolution
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.K32TableL3Group

public section

namespace CFSG.QuasithinUnique.DoubleA3

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

section Bound

variable {F : Type} [Field F] [CharP F 2] [Finite F]

omit [CharP F 2] [Finite F] in
theorem k32_center_projectiveSL_three : Subgroup.center (LinearFlag.projectiveSL 3 F) = ⊥ :=
  CFSG.RankThree.RegularUnipotent.center_projectiveSL_eq_bot (n := 3) (k := F) le_rfl

omit [CharP F 2] [Finite F] in
theorem k32_l3_lift_order_three {g : LinearFlag.projectiveSL 3 F} (hg3 : g ^ 3 = 1) (hg1 : g ≠ 1) :
    ∃ ĝ : Matrix.SpecialLinearGroup (Fin 3) F, LinearFlag.proj 3 F ĝ = g ∧
      ∃ c : Fˣ, Matrix.SpecialLinearGroup.toGL ĝ ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 3) c ∧
        ¬ ∃ x : Fˣ, Matrix.GeneralLinearGroup.scalar (Fin 3) x = Matrix.SpecialLinearGroup.toGL ĝ := by
  obtain ⟨ĝ, rfl⟩ := LinearFlag.proj_surjective 3 F g
  refine ⟨ĝ, rfl, ?_⟩
  have h1 : LinearFlag.proj 3 F (ĝ ^ 3) = 1 := by rw [map_pow, hg3]
  obtain ⟨c, -, hc⟩ := LinearFlag.mem_scalars.mp (LinearFlag.proj_eq_one_iff.mp h1)
  refine ⟨c, ?_, ?_⟩
  · refine Units.ext ?_
    rw [Units.val_pow_eq_pow_val, Matrix.GeneralLinearGroup.coe_scalar]
    have h3 : ((ĝ ^ 3 : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        Matrix.scalar (Fin 3) (c : F) := hc
    rw [Matrix.SpecialLinearGroup.coe_pow] at h3
    exact h3
  · rintro ⟨x, hx⟩
    apply hg1
    have hmat : (ĝ : Matrix (Fin 3) (Fin 3) F) = Matrix.scalar (Fin 3) (x : F) := by
      have := congrArg (fun h : GL (Fin 3) F => (h : Matrix (Fin 3) (Fin 3) F)) hx
      simpa [Matrix.GeneralLinearGroup.coe_scalar] using this.symm
    have hx3 : x ^ 3 = 1 := by
      have h2 : (ĝ : Matrix (Fin 3) (Fin 3) F).det = 1 := ĝ.2
      rw [hmat, Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin] at h2
      exact Units.ext (by simpa using h2)
    rw [LinearFlag.proj_eq_one_iff]
    exact ⟨x, hx3, hmat⟩

theorem k32InnerBound_l3 : K32InnerBound (LinearFlag.projectiveSL 3 F) (Nat.card F) := by
  intro g hg3 hg1 W hW hC
  obtain ⟨ĝ, rfl, c, hA3, hns⟩ := k32_l3_lift_order_three hg3 hg1
  refine k32_l3_bound hA3 hns hW fun w hw => ?_
  rw [← CFSG.RankThree.PartTwo.KFacts.conj_proj_eq_conjAut 3 F ĝ, MulAut.conj_apply,
    ← hC w hw, mul_inv_cancel_right]

theorem k32InnerBound_l3_four (hF : Nat.card F = 4) :
    K32InnerBound (LinearFlag.projectiveSL 3 F) 1 := by
  have hK : ∀ x : F, x ^ 4 = x := by
    intro x
    have := Fintype.ofFinite F
    rw [Nat.card_eq_fintype_card] at hF
    rw [← hF]
    exact FiniteField.pow_card x
  intro g hg3 hg1 W hW hC
  obtain ⟨ĝ, rfl, c, hA3, hns⟩ := k32_l3_lift_order_three hg3 hg1
  refine (k32_l3_bound_four hK ĝ.2 hA3 hns hW fun w hw => ?_).le
  rw [← CFSG.RankThree.PartTwo.KFacts.conj_proj_eq_conjAut 3 F ĝ, MulAut.conj_apply,
    ← hC w hw, mul_inv_cancel_right]

theorem k32OuterBound_l3 : K32OuterBound (LinearFlag.projectiveSL 3 F) (Nat.card F) := by
  intro α hα3 hαout W hW hfix
  by_cases hlin : α ∈ LinearFlag.linearAutGroup 3 F
  · obtain ⟨A, rfl⟩ := LinearFlag.mem_linearAutGroup_iff.mp hlin
    have hA3' : LinearFlag.conjAut 3 F (A ^ 3) = 1 := by rw [map_pow, hα3]
    obtain ⟨-, c, hc⟩ := LinearFlag.eq_one_of_conjAut_mul_fieldAut_eq_one (n := 3) (K := F) le_rfl (A ^ 3) 1
      (by rw [map_one, mul_one]; exact hA3')
    have hns : ¬ ∃ x : Fˣ, Matrix.GeneralLinearGroup.scalar (Fin 3) x = A := by
      rintro ⟨x, rfl⟩
      apply hαout
      rw [LinearFlag.conjAut_scalar]
      exact one_mem _
    exact k32_l3_bound hc.symm hns hW hfix
  · obtain ⟨σ, hσ, H, hαH⟩ := CFSG.RankThree.PartTwo.KFacts.linear_order_three_field_descent
      (K := F) (n := 3) le_rfl α hα3 hlin
    set c : MulAut (LinearFlag.projectiveSL 3 F) := LinearFlag.conjAut 3 F H with hc
    have hfs : LinearFlag.fieldAut 3 F σ = c⁻¹ * α * c := by
      rw [hαH]
      group
    set ψ : LinearFlag.projectiveSL 3 F →* LinearFlag.projectiveSL 3 F :=
      (c⁻¹ : MulAut _).toMonoidHom with hψ
    have hψinj : Function.Injective ψ := (c⁻¹ : MulAut _).injective
    have hfix₀ : ∀ x ∈ W.map ψ, LinearFlag.fieldAut 3 F σ x = x := by
      rintro _ ⟨w, hw, rfl⟩
      have hcw : c (c⁻¹ w) = w := by
        rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
      change LinearFlag.fieldAut 3 F σ (c⁻¹ w) = c⁻¹ w
      rw [hfs, MulAut.mul_apply, MulAut.mul_apply, hcw, hfix w hw]
    have hW₀ : IsPGroup 2 ↥(W.map ψ) := hW.of_equiv (Subgroup.equivMapOfInjective W ψ hψinj)
    have hcard : Nat.card ↥(W.map ψ) = Nat.card ↥W := Subgroup.card_map_of_injective hψinj
    rw [← hcard]
    exact k32_l3_field_bound hσ hW₀ hfix₀

theorem k32ZBound2_l3 :
    K32ZBound2 (LinearFlag.projectiveSL 3 F) (Nat.card F) (Nat.card F) :=
  k32ZBound2_of_inner_outer k32_center_projectiveSL_three k32InnerBound_l3 k32OuterBound_l3

theorem k32ZBound2_l3_four (hF : Nat.card F = 4) :
    K32ZBound2 (LinearFlag.projectiveSL 3 F) 1 4 :=
  k32ZBound2_of_inner_outer k32_center_projectiveSL_three (k32InnerBound_l3_four hF)
    (hF ▸ k32OuterBound_l3)


end Bound

end CFSG.QuasithinUnique.DoubleA3
