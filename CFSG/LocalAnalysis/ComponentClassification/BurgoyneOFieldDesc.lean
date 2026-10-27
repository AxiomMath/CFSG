module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSLOrthNormal
public import CFSG.LocalAnalysis.ComponentInitial.FieldUnitaryNorm
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherConjDescentFixed

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.O

open Matrix CFSG
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.Burgoyne.PSL (OrthNF exists_orth_normal_form)

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {d : ℕ}

abbrev barV (v : Fin d → K) : Fin d → K := fun i => h.bar (v i)

theorem bar_dot (R : Matrix (Fin d) (Fin d) K) (v w : Fin d → K) :
    h.bar (v ⬝ᵥ R *ᵥ w) = barV h v ⬝ᵥ R.map h.bar *ᵥ barV h w := by
  rw [RingHom.map_dotProduct]
  congr 1
  funext i
  exact RingHom.map_mulVec h.bar R w i

theorem dot_mulVec_mulVec (A R : Matrix (Fin d) (Fin d) K) (x y : Fin d → K) :
    (A *ᵥ x) ⬝ᵥ R *ᵥ (A *ᵥ y) = x ⬝ᵥ (Aᵀ * R * A) *ᵥ y := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec x Aᵀ, vecMul_transpose]

theorem dot_semilinear {R A : Matrix (Fin d) (Fin d) K} {μ : K}
    (hμ : Aᵀ * R * A = μ • R.map h.bar) (v w : Fin d → K) :
    (A *ᵥ barV h v) ⬝ᵥ R *ᵥ (A *ᵥ barV h w) = μ * h.bar (v ⬝ᵥ R *ᵥ w) := by
  rw [dot_mulVec_mulVec, hμ, smul_mulVec, dotProduct_smul, smul_eq_mul, bar_dot]

theorem mulVec_barV_mulVec (A : Matrix (Fin d) (Fin d) K) (v : Fin d → K) :
    A *ᵥ barV h (A *ᵥ barV h v) = (A * A.map h.bar) *ᵥ v := by
  have e : barV h (A *ᵥ barV h v) = A.map h.bar *ᵥ v := by
    funext i
    change h.bar ((A *ᵥ barV h v) i) = _
    rw [RingHom.map_mulVec]
    congr 1
    funext j
    exact h.bar_bar (v j)
  rw [e, mulVec_mulVec]

theorem exists_field_descent (hd : 1 ≤ d) {R : GL (Fin d) K} {A : Matrix (Fin d) (Fin d) K}
    (hAdet : A.det ≠ 0) {μ : K}
    (hμ : Aᵀ * (R : Matrix (Fin d) (Fin d) K) * A = μ • (R : Matrix (Fin d) (Fin d) K).map h.bar)
    {c : K} (hc0 : c ≠ 0) (hc : A * A.map h.bar = c • 1) :
    ∃ l r : K, l ≠ 0 ∧ r ≠ 0 ∧ (l⁻¹ • A) * (l⁻¹ • A).map h.bar = 1 ∧
      ∀ v w, (l⁻¹ • A) *ᵥ barV h v = v → (l⁻¹ • A) *ᵥ barV h w = w →
        r⁻¹ * (v ⬝ᵥ (R : Matrix (Fin d) (Fin d) K) *ᵥ w) ∈ h.fixedField := by
  set Rm := (R : Matrix (Fin d) (Fin d) K) with hRm
  have hbb : ∀ M : Matrix (Fin d) (Fin d) K, (M.map h.bar).map h.bar = M := fun M => by
    ext i j
    exact h.bar_bar _
  have hmapsmul : ∀ (a : K) (M : Matrix (Fin d) (Fin d) K), (a • M).map h.bar =
      h.bar a • M.map h.bar := fun a M => by
    ext i j
    simp [map_mul]
  have hA0 : A ≠ 0 := by
    intro h0
    have : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
    rw [h0, det_zero] at hAdet
    exact hAdet rfl
  have hcF : h.bar c = c := by
    have e1 : A.map h.bar * A = h.bar c • 1 := by
      have := congrArg (fun M => M.map h.bar) hc
      simp only [Matrix.map_mul, hbb, hmapsmul, Matrix.map_one _ (map_zero _) (map_one _)] at this
      exact this
    have e2 : c • A = h.bar c • A := by
      calc c • A = (A * A.map h.bar) * A := by rw [hc, Matrix.smul_mul, Matrix.one_mul]
        _ = A * (A.map h.bar * A) := Matrix.mul_assoc _ _ _
        _ = h.bar c • A := by rw [e1, Matrix.mul_smul, Matrix.mul_one]
    have e3 : (c - h.bar c) • A = 0 := by rw [sub_smul, e2, sub_self]
    exact (sub_eq_zero.1 ((smul_eq_zero.1 e3).resolve_right hA0)).symm
  obtain ⟨l, hl⟩ := h.normHom_surjective ⟨c, hcF⟩
  have hlc : l * h.bar l = c := by
    have := congrArg Subtype.val hl
    rwa [UnitaryFieldData.coe_normHom] at this
  have hl0 : l ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hlc
    exact hc0 hlc.symm
  have hbl0 : h.bar l ≠ 0 := (h.bar_eq_zero_iff).not.mpr hl0
  have hA'2 : (l⁻¹ • A) * (l⁻¹ • A).map h.bar = 1 := by
    rw [hmapsmul, Matrix.smul_mul, Matrix.mul_smul, hc, smul_smul, smul_smul, map_inv₀, ← hlc]
    rw [show l⁻¹ * (h.bar l)⁻¹ * (l * h.bar l) = 1 by field_simp, one_smul]
  set μ' := l⁻¹ * l⁻¹ * μ with hμ'
  have hμA' : (l⁻¹ • A)ᵀ * Rm * (l⁻¹ • A) = μ' • Rm.map h.bar := by
    rw [transpose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, hμ, smul_smul,
      smul_smul, hμ']
  have hN : μ' * h.bar μ' = 1 := by
    have : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
    set i₀ : Fin d := ⟨0, by omega⟩
    set v : Fin d → K := Pi.single i₀ 1
    set w : Fin d → K := ((R⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ Pi.single i₀ 1
    have hvw : v ⬝ᵥ Rm *ᵥ w = 1 := by
      rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
      simp [v]
    have e := dot_semilinear h hμA' ((l⁻¹ • A) *ᵥ barV h v) ((l⁻¹ • A) *ᵥ barV h w)
    rw [mulVec_barV_mulVec, mulVec_barV_mulVec, hA'2, one_mulVec, one_mulVec,
      dot_semilinear h hμA', map_mul, h.bar_bar, hvw, mul_one] at e
    exact e.symm
  obtain ⟨r, hr0, hr⟩ := h.exists_div_bar_eq (u := μ') hN
  have hbr0 : h.bar r ≠ 0 := (h.bar_eq_zero_iff).not.mpr hr0
  refine ⟨l, r, hl0, hr0, hA'2, fun v w hv hw => ?_⟩
  rw [h.mem_fixedField]
  have e := dot_semilinear h hμA' v w
  rw [hv, hw, ← hr] at e
  rw [map_mul, map_inv₀]
  have e' : h.bar (v ⬝ᵥ Rm *ᵥ w) = h.bar r / r * (v ⬝ᵥ Rm *ᵥ w) := by
    conv_rhs => rw [e]
    rw [show h.bar r / r * (r / h.bar r * h.bar (v ⬝ᵥ Rm *ᵥ w)) = h.bar (v ⬝ᵥ Rm *ᵥ w) by
      field_simp]
  rw [e']
  field_simp

end CFSG.ComponentClassification.Burgoyne.O
