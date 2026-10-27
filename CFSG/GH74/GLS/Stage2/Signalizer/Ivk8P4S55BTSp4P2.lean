module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTSp4P
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherParabolicData
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

namespace BS4

open Matrix Subgroup CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticHigher SymplecticFlag
open scoped commutatorElement

variable {F : Type} [Field F]

@[expose] def fixE0 : Subgroup (StatedSp 2 F) where
  carrier := {x | (((x : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ e0 = e0}
  one_mem' := by
    simp only [Set.mem_ofPred_eq, Subgroup.coe_one, Units.val_one, one_mulVec]
  mul_mem' := by
    intro x y hx hy
    simp only [Set.mem_ofPred_eq, Subgroup.coe_mul, Units.val_mul] at hx hy ⊢
    rw [← mulVec_mulVec, hy, hx]
  inv_mem' := by
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    have h1 : ((((x⁻¹ : StatedSp 2 F)) : GL (Fin 2 ⊕ Fin 2) F) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) * (((x : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = 1 := by
      rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, Units.val_one]
    conv_lhs => rw [← hx, mulVec_mulVec, h1, one_mulVec]

theorem inv_mulVec_e0 {x : StatedSp 2 F} {c : F}
    (hx : (((x : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ e0 = c • e0) :
    c ≠ 0 ∧ ((((x⁻¹ : StatedSp 2 F)) : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ e0 = c⁻¹ • e0 := by
  have h1 : ((((x⁻¹ : StatedSp 2 F)) : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) * (((x : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = 1 := by
    rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, Units.val_one]
  have he : (e0 : Fin 2 ⊕ Fin 2 → F) = c • (((((x⁻¹ : StatedSp 2 F)) : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ e0) := by
    conv_lhs => rw [← one_mulVec e0, ← h1, ← mulVec_mulVec, hx]
    rw [mulVec_smul]
  have hc : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at he
    simpa using congrFun he (Sum.inl 0)
  refine ⟨hc, ?_⟩
  conv_rhs => rw [he, smul_smul, inv_mul_cancel₀ hc, one_smul]

theorem commutator_le_fixE0 {I : Subgroup (StatedSp 2 F)}
    (hI : ∀ x ∈ I, ∃ c : F, (((x : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ e0 = c • e0) : ⁅I, I⁆ ≤ fixE0 := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  obtain ⟨c, hc⟩ := hI a ha
  obtain ⟨d, hd⟩ := hI b hb
  obtain ⟨hc0, hci⟩ := inv_mulVec_e0 hc
  obtain ⟨hd0, hdi⟩ := inv_mulVec_e0 hd
  show _ *ᵥ e0 = e0
  rw [commutatorElement_def]
  simp only [Subgroup.coe_mul, Units.val_mul, ← mulVec_mulVec, hdi, mulVec_smul, hci, hd, hc,
    smul_smul]
  rw [show d⁻¹ * (c⁻¹ * (d * c)) = 1 by field_simp, one_smul]

theorem eq_one_of_fixE0_scalar {x : StatedSp 2 F} (hx : x ∈ fixE0) (hs : x ∈ spScalars 2 F) :
    x = 1 := by
  obtain ⟨c, hc⟩ := (Subgroup.mem_subgroupOf.mp hs :)
  have hx' : (((x : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ e0 = e0 := hx
  rw [← hc, Matrix.GeneralLinearGroup.coe_scalar] at hx'
  have h1 : (c : F) = 1 := by simpa [Matrix.scalar_apply] using congrFun hx' (Sum.inl 0)
  apply Subtype.ext
  rw [← hc, Subgroup.coe_one]
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.coe_scalar, Units.val_one, h1]
  simp

theorem false_of_point (h2 : (2 : F) ≠ 0) {I : Subgroup (StatedSp 2 F)}
    (hI : ∀ x ∈ I, ∃ c : F, (((x : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ e0 = c • e0)
    {x₁ x₂ : StatedSp 2 F} (hx₁ : x₁ ∈ ⁅I, I⁆) (hx₂ : x₂ ∈ ⁅I, I⁆)
    (hsq₁ : x₁ * x₁ ∈ spScalars 2 F) (hsq₂ : x₂ * x₂ ∈ spScalars 2 F)
    (hsq₁₂ : x₁ * x₂ * (x₁ * x₂) ∈ spScalars 2 F) (hns₁ : x₁ ∉ spScalars 2 F)
    (hns₂ : x₂ ∉ spScalars 2 F) (hns₁₂ : x₁ * x₂ ∉ spScalars 2 F) : False := by
  have hD := commutator_le_fixE0 hI
  have hsp : ∀ x : StatedSp 2 F, (((x : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)ᵀ * jJ * (((x : StatedSp 2 F) :
        GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = jJ :=
    fun x => SymplecticTorusWeyl.mem_statedSp_iff.mp x.2
  have hmul : ∀ x y : StatedSp 2 F, x ∈ fixE0 → y ∈ fixE0 →
      midB (((x * y : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
      midB (((x : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
      midB (((y : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) := by
    intro x y hx hy
    obtain ⟨-, c1, -, c3⟩ := col_e0 hx
    obtain ⟨r1, r2, -⟩ := row_e0 hy (hsp y)
    rw [Subgroup.coe_mul, Units.val_mul]
    exact midB_mul ⟨c1, c3⟩ ⟨r1, r2⟩
  have key : ∀ x ∈ ⁅I, I⁆, x * x ∈ spScalars 2 F → x ∉ spScalars 2 F →
      midB (((x : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = -1 := by
    intro x hx hsq hns
    have hfix := hD hx
    have hxx : x * x = 1 := eq_one_of_fixE0_scalar (mul_mem hfix hfix) hsq
    have hM : (((x : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) * (((x : StatedSp 2 F) :
          GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = 1 := by
      rw [← Units.val_mul, ← Subgroup.coe_mul, hxx, Subgroup.coe_one, Units.val_one]
    have hmid2 := hmul x x hfix hfix
    rw [hxx, Subgroup.coe_one, Units.val_one] at hmid2
    have h1 : midB (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply]
    rw [h1] at hmid2
    rcases eq_one_or_neg_one_of_sq h2 hmid2.symm (det_midB hfix (hsp x)) with h | h
    · refine absurd ?_ hns
      have : x = 1 := Subtype.ext (Units.ext (by
        rw [Subgroup.coe_one, Units.val_one]
        exact eq_one_of_midB_eq_one h2 hfix (hsp x) hM h))
      rw [this]
      exact one_mem _
    · exact h
  have e12 := key (x₁ * x₂) (mul_mem hx₁ hx₂) hsq₁₂ hns₁₂
  rw [hmul x₁ x₂ (hD hx₁) (hD hx₂), key x₁ hx₁ hsq₁ hns₁, key x₂ hx₂ hsq₂ hns₂, neg_one_mul,
    neg_neg] at e12
  have h00 := congrFun (congrFun e12 0) 0
  rw [Matrix.one_apply_eq, Matrix.neg_apply, Matrix.one_apply_eq] at h00
  exact h2 (by linear_combination h00)

end BS4

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
