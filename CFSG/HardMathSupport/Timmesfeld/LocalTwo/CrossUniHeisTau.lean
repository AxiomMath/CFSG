module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.UnitaryBalBlock

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.KCUnitaryFrame
  CFSG.HardMathSupport.Timmesfeld.CrossChar

variable {ℓ f n : ℕ} {K : Type} [Field K] {h : UnitaryFieldData ℓ f K}

theorem trace_projMat {b : Fin n → K} (hb : idForm h n b b = 1) : trace (projMat h b) = 1 := by
  rw [projMat, trace_vecMulVec, ← hb, idForm_eq_dotProduct, dotProduct_comm]

theorem trace_torusMat {u v : Fin n → K} (hb : IsONPair h u v) (c : K) :
    trace (torusMat h u v c) = (n : K) - 2 + c + c⁻¹ := by
  unfold torusMat
  rw [trace_add, trace_add, trace_smul, trace_smul, trace_projMat hb.self₁,
    trace_projMat hb.self₂, trace_one]
  simp only [Fintype.card_fin, smul_eq_mul, mul_one]
  ring

theorem tau_mem_of_torusComm {M : Matrix (Fin n) (Fin n) K} (hM : IsUnit M) {τ : K ≃+* K}
    {u v : Fin n → K} (hb : IsONPair h u v) (hT : TorusComm h M τ u v) {ζ : K} (hζ : ζ ≠ 0)
    (hζn : h.norm ζ = 1) : τ ζ = ζ ∨ τ ζ = ζ⁻¹ := by
  have h1 := hT (Units.mk0 ζ hζ) hζn
  simp only [Units.val_mk0] at h1
  obtain ⟨M', hM'⟩ := hM
  set T := torusMat h u v ζ with hTdef
  set X := T.map τ with hX
  have e1 : X = ((M'⁻¹ : (Matrix (Fin n) (Fin n) K)ˣ) : Matrix (Fin n) (Fin n) K) * (T * M) := by
    rw [← h1, ← Matrix.mul_assoc, ← hM', Units.inv_mul, Matrix.one_mul]
  have h2 : trace X = trace T := by
    rw [e1, trace_mul_comm, Matrix.mul_assoc T M, ← hM', Units.mul_inv, Matrix.mul_one]
  have h3 : trace X = τ (trace T) := by
    simp [hX, Matrix.trace, Matrix.diag, map_sum]
  rw [h3, trace_torusMat hb] at h2
  simp only [map_add, map_sub, map_inv₀, map_natCast, map_ofNat] at h2
  have hτ0 : τ ζ ≠ 0 := by simpa using hζ
  have h4 : (τ ζ - ζ) * (τ ζ * ζ - 1) = 0 := by
    field_simp at h2
    linear_combination h2
  rcases mul_eq_zero.mp h4 with h5 | h5
  · left; exact sub_eq_zero.mp h5
  · right
    field_simp
    linear_combination h5

theorem tau_eq_one_of_pair {M : Matrix (Fin n) (Fin n) K} (hM : IsUnit M) {τ : K ≃+* K}
    {u v : Fin n → K} (hb : IsONPair h u v) (hT : TorusComm h M τ u v) {c : K} (hc0 : c ≠ 0)
    (hcn : h.norm c = 1) (hc2 : c ^ 2 ≠ 1) (hτc : τ c = c) : τ = RingEquiv.refl K := by
  refine CFSG.RankThree.PartOne.KCUnitaryCoord.eq_one_of_fixes_norm_one h τ fun x hx => ?_
  have hx0 : (x : K) ≠ 0 := x.ne_zero
  rcases tau_mem_of_torusComm hM hb hT hx0 hx with h1 | h1
  · exact h1
  · have hxc : h.norm ((x : K) * c) = 1 := by
      rw [h.norm_eq_pow] at hx hcn ⊢
      rw [mul_pow, hx, hcn, one_mul]
    rcases tau_mem_of_torusComm hM hb hT (mul_ne_zero hx0 hc0) hxc with h2 | h2
    · rw [map_mul, hτc, h1] at h2
      have : (x : K)⁻¹ * c = x * c := h2
      have h3 : (x : K)⁻¹ = x := mul_right_cancel₀ hc0 this
      rw [h1, h3]
    · exfalso
      rw [map_mul, hτc, h1, mul_inv] at h2
      have h3 : c = c⁻¹ := mul_left_cancel₀ (inv_ne_zero hx0) h2
      apply hc2
      field_simp at h3
      linear_combination h3

end CFSG.HardMathSupport.Timmesfeld.LocalTwo
