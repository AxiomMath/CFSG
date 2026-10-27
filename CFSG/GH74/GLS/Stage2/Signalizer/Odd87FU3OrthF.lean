module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Orth3Mod

public section

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial
open scoped MatrixGroups

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

section OrthF

variable {k F : Type} [Field k] [Field F]

theorem adMat_map (τ : k →+* F) (S : SL(2, k)) :
    (adMat S).map τ = adMat (Matrix.SpecialLinearGroup.map τ S) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [adMat, Matrix.map_apply, SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, map_ofNat]

@[expose] def baseConj (τ : k →+* F) (Q : GL (Fin 3) F) (M : Matrix (Fin 3) (Fin 3) k) :
    Matrix (Fin 3) (Fin 3) F :=
  (Q : Matrix (Fin 3) (Fin 3) F) * M.map τ * ((Q⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)

omit [Field k] in
theorem irreducible_of_conj_uv (h2 : (2 : F) ≠ 0) {R R' : Matrix (Fin 3) (Fin 3) F}
    (hRR' : R * R' = 1) (hR'R : R' * R = 1) (W : Submodule F (Fin 3 → F))
    (hu : ∀ v ∈ W, (R' * adMat (uElt : SL(2, F)) * R) *ᵥ v ∈ W)
    (hv : ∀ v ∈ W, (R' * adMat (vElt : SL(2, F)) * R) *ᵥ v ∈ W) : W = ⊥ ∨ W = ⊤ := by
  let W' : Submodule F (Fin 3 → F) := W.comap (Matrix.mulVecLin R')
  have hW' : ∀ S : SL(2, F), (∀ v ∈ W, (R' * adMat S * R) *ᵥ v ∈ W) →
      ∀ x ∈ W', adMat S *ᵥ x ∈ W' := by
    intro S hS x hx
    show R' *ᵥ (adMat S *ᵥ x) ∈ W
    have hmatid : R' * adMat S = (R' * adMat S * R) * R' := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, hRR', Matrix.mul_one]
    have : R' *ᵥ (adMat S *ᵥ x) = (R' * adMat S * R) *ᵥ (R' *ᵥ x) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← hmatid]
    rw [this]
    exact hS _ hx
  rcases irreducible_uv h2 W' (fun w hw => hW' uElt hu w hw) (fun w hw => hW' vElt hv w hw) with h | h
  · left
    rw [eq_bot_iff]
    intro w hw
    have h1 : R *ᵥ w ∈ W' := by
      show R' *ᵥ (R *ᵥ w) ∈ W
      rw [Matrix.mulVec_mulVec, hR'R, Matrix.one_mulVec]
      exact hw
    rw [h] at h1
    have h3 : R *ᵥ w = 0 := (Submodule.mem_bot F).mp h1
    have h4 : w = R' *ᵥ (R *ᵥ w) := by
      rw [Matrix.mulVec_mulVec, hR'R, Matrix.one_mulVec]
    rw [Submodule.mem_bot, h4, h3, Matrix.mulVec_zero]
  · right
    rw [eq_top_iff]
    intro w _
    have h1 : R *ᵥ w ∈ W' := by rw [h]; exact Submodule.mem_top
    have h2' : R' *ᵥ (R *ᵥ w) ∈ W := h1
    rwa [Matrix.mulVec_mulVec, hR'R, Matrix.one_mulVec] at h2'

omit [Field k] in
theorem commutant_of_conj_uv (h2 : (2 : F) ≠ 0) {R R' : Matrix (Fin 3) (Fin 3) F}
    (hRR' : R * R' = 1) (hR'R : R' * R = 1) (T : Matrix (Fin 3) (Fin 3) F)
    (hu : T * (R' * adMat (uElt : SL(2, F)) * R) = (R' * adMat (uElt : SL(2, F)) * R) * T)
    (hv : T * (R' * adMat (vElt : SL(2, F)) * R) = (R' * adMat (vElt : SL(2, F)) * R) * T) :
    ∃ c : F, T = c • (1 : Matrix (Fin 3) (Fin 3) F) := by
  have hcomm : ∀ S : SL(2, F), T * (R' * adMat S * R) = (R' * adMat S * R) * T →
      (R * T * R') * adMat S = adMat S * (R * T * R') := by
    intro S h
    have hadj : adMat S = R * (R' * adMat S * R) * R' := by
      calc adMat S = (R * R') * adMat S * (R * R') := by rw [hRR', Matrix.one_mul, Matrix.mul_one]
        _ = R * (R' * adMat S * R) * R' := by simp only [Matrix.mul_assoc]
    rw [hadj]
    calc R * T * R' * (R * (R' * adMat S * R) * R')
        = R * T * (R' * R) * (R' * adMat S * R) * R' := by simp only [Matrix.mul_assoc]
      _ = R * (T * (R' * adMat S * R)) * R' := by
          rw [hR'R, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = R * ((R' * adMat S * R) * T) * R' := by rw [h]
      _ = R * (R' * adMat S * R) * R' * (R * T * R') := by
          calc R * ((R' * adMat S * R) * T) * R'
              = R * (R' * adMat S * R) * (R' * R) * T * R' := by
                rw [hR'R, Matrix.mul_one]; simp only [Matrix.mul_assoc]
            _ = _ := by simp only [Matrix.mul_assoc]
  obtain ⟨c, hc⟩ := commutant_uv h2 (R * T * R') (hcomm uElt hu) (hcomm vElt hv)
  refine ⟨c, ?_⟩
  calc T = R' * (R * T * R') * R := by
        calc T = (R' * R) * T * (R' * R) := by rw [hR'R, Matrix.one_mul, Matrix.mul_one]
          _ = R' * (R * T * R') * R := by simp only [Matrix.mul_assoc]
    _ = c • 1 := by
        rw [hc]
        simp [hR'R]

section Param

theorem map_uElt (τ : k →+* F) : (Matrix.SpecialLinearGroup.map τ (uElt : SL(2, k)) : SL(2, F)) = uElt := by
  ext i j
  rw [SpecialLinearGroup.map_apply_coe]
  fin_cases i <;> fin_cases j <;> simp [uElt, RingHom.mapMatrix_apply, Matrix.map_apply]

theorem map_vElt (τ : k →+* F) : (Matrix.SpecialLinearGroup.map τ (vElt : SL(2, k)) : SL(2, F)) = vElt := by
  ext i j
  rw [SpecialLinearGroup.map_apply_coe]
  fin_cases i <;> fin_cases j <;> simp [vElt, RingHom.mapMatrix_apply, Matrix.map_apply]

variable {ι : SL(2, k) →* SL(3, k)} {P P' : Matrix (Fin 3) (Fin 3) k}

theorem baseConj_eq (τ : k →+* F) (hι : ∀ S : SL(2, k), (ι S : Matrix (Fin 3) (Fin 3) k) = P' * adMat S * P)
    (Q : GL (Fin 3) F) (S : SL(2, k)) :
    baseConj τ Q (ι S : Matrix (Fin 3) (Fin 3) k) =
      ((Q : Matrix (Fin 3) (Fin 3) F) * P'.map τ) * adMat (Matrix.SpecialLinearGroup.map τ S) *
        (P.map τ * ((Q⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) := by
  rw [baseConj, hι S, Matrix.map_mul, Matrix.map_mul, adMat_map]
  simp only [Matrix.mul_assoc]

theorem map_inverse_pair (τ : k →+* F) (hPP' : P * P' = 1) (hP'P : P' * P = 1) (Q : GL (Fin 3) F) :
    (P.map τ * ((Q⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) *
        ((Q : Matrix (Fin 3) (Fin 3) F) * P'.map τ) = 1 ∧
      ((Q : Matrix (Fin 3) (Fin 3) F) * P'.map τ) *
        (P.map τ * ((Q⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) = 1 := by
  have hQ : ((Q⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * (Q : Matrix (Fin 3) (Fin 3) F) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hQ' : (Q : Matrix (Fin 3) (Fin 3) F) * ((Q⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h1 : P.map τ * P'.map τ = 1 := by rw [← Matrix.map_mul, hPP', Matrix.map_one _ (map_zero τ) (map_one τ)]
  have h2 : P'.map τ * P.map τ = 1 := by rw [← Matrix.map_mul, hP'P, Matrix.map_one _ (map_zero τ) (map_one τ)]
  constructor
  · calc (P.map τ * ((Q⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) *
          ((Q : Matrix (Fin 3) (Fin 3) F) * P'.map τ)
        = P.map τ * (((Q⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * (Q : Matrix (Fin 3) (Fin 3) F)) *
            P'.map τ := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hQ, Matrix.mul_one, h1]
  · calc ((Q : Matrix (Fin 3) (Fin 3) F) * P'.map τ) *
          (P.map τ * ((Q⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))
        = (Q : Matrix (Fin 3) (Fin 3) F) * (P'.map τ * P.map τ) *
            ((Q⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h2, Matrix.mul_one, hQ']

theorem irreducible_of_param_F (τ : k →+* F) (h2 : (2 : F) ≠ 0)
    {ι : SL(2, k) →* SL(3, k)} {P P' : Matrix (Fin 3) (Fin 3) k} (hPP' : P * P' = 1) (hP'P : P' * P = 1)
    (hι : ∀ S : SL(2, k), (ι S : Matrix (Fin 3) (Fin 3) k) = P' * adMat S * P)
    (Q : GL (Fin 3) F) (W : Submodule F (Fin 3 → F))
    (hW : ∀ S : SL(2, k), ∀ v ∈ W, baseConj τ Q (ι S : Matrix (Fin 3) (Fin 3) k) *ᵥ v ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  obtain ⟨h1, h1'⟩ := map_inverse_pair τ hPP' hP'P Q
  have hu := map_uElt (k := k) (F := F) τ
  have hv := map_vElt (k := k) (F := F) τ
  refine irreducible_of_conj_uv h2 h1 h1' W (fun v hv' => ?_) (fun v hv' => ?_)
  · have := hW uElt v hv'
    rwa [baseConj_eq τ hι Q uElt, hu] at this
  · have := hW vElt v hv'
    rwa [baseConj_eq τ hι Q vElt, hv] at this

theorem commutant_of_param_F (τ : k →+* F) (h2 : (2 : F) ≠ 0)
    {ι : SL(2, k) →* SL(3, k)} {P P' : Matrix (Fin 3) (Fin 3) k} (hPP' : P * P' = 1) (hP'P : P' * P = 1)
    (hι : ∀ S : SL(2, k), (ι S : Matrix (Fin 3) (Fin 3) k) = P' * adMat S * P)
    (Q : GL (Fin 3) F) (T : Matrix (Fin 3) (Fin 3) F)
    (hT : ∀ S : SL(2, k),
      T * baseConj τ Q (ι S : Matrix (Fin 3) (Fin 3) k) = baseConj τ Q (ι S : Matrix (Fin 3) (Fin 3) k) * T) :
    ∃ c : F, T = c • (1 : Matrix (Fin 3) (Fin 3) F) := by
  obtain ⟨h1, h1'⟩ := map_inverse_pair τ hPP' hP'P Q
  have hu := map_uElt (k := k) (F := F) τ
  have hv := map_vElt (k := k) (F := F) τ
  refine commutant_of_conj_uv h2 h1 h1' T ?_ ?_
  · have := hT uElt
    rwa [baseConj_eq τ hι Q uElt, hu] at this
  · have := hT vElt
    rwa [baseConj_eq τ hι Q vElt, hv] at this

end Param

theorem trace_baseConj (τ : k →+* F) (Q : GL (Fin 3) F) (M : Matrix (Fin 3) (Fin 3) k) :
    Matrix.trace (baseConj τ Q M) = τ (Matrix.trace M) := by
  rw [baseConj, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, ← Units.val_mul,
    inv_mul_cancel, Units.val_one, Matrix.mul_one]
  exact (AddMonoidHom.map_trace τ.toAddMonoidHom M).symm

theorem fixes_of_traces (τ : k →+* F) (h2 : (2 : k) ≠ 0)
    {ι : SL(2, k) →* SL(3, k)} {P P' : Matrix (Fin 3) (Fin 3) k} (hPP' : P * P' = 1) (_hP'P : P' * P = 1)
    (hι : ∀ S : SL(2, k), (ι S : Matrix (Fin 3) (Fin 3) k) = P' * adMat S * P)
    (Q : GL (Fin 3) F) (σ : F ≃+* F)
    (hσ : ∀ S : SL(2, k), σ (Matrix.trace (baseConj τ Q (ι S : Matrix (Fin 3) (Fin 3) k))) =
      Matrix.trace (baseConj τ Q (ι S : Matrix (Fin 3) (Fin 3) k))) (t : k) :
    σ (τ t) = τ t := by
  have hsq : ∀ s : k, σ (τ s ^ 2) = τ s ^ 2 := by
    intro s
    let S : SL(2, k) := ⟨!![s, -1; 1, 0], by simp [Matrix.det_fin_two]⟩
    have h := hσ S
    rw [trace_baseConj, hι S, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, hPP',
      Matrix.mul_one, trace_adMat S] at h
    have hS : ((S : Matrix (Fin 2) (Fin 2) k) 0 0 + (S : Matrix (Fin 2) (Fin 2) k) 1 1) = s := by
      simp [S]
    rw [hS, map_sub, map_pow, map_one, map_sub, map_pow, map_one] at h
    rw [map_pow]
    linear_combination h
  have e : ((t + 1) / 2) ^ 2 - ((t - 1) / 2) ^ 2 = t := by
    field_simp
    ring
  have hτ : τ t = τ ((t + 1) / 2) ^ 2 - τ ((t - 1) / 2) ^ 2 := by
    rw [← map_pow, ← map_pow, ← map_sub, e]
  rw [hτ, map_sub, hsq, hsq]

omit [Field k] in
theorem eq_one_or_bar_of_fixes {p f : ℕ} {F : Type} [Field F] (h : UnitaryFieldData p f F) (σ : F ≃+* F)
    (hσ : ∀ c : F, h.bar c = c → σ c = c) : σ = 1 ∨ ∀ c, σ c = h.bar c := by
  have hdich : ∀ c, σ c = c ∨ σ c = h.bar c := by
    intro c
    have h1 : σ (c + h.bar c) = c + h.bar c := hσ _ (by rw [map_add, h.bar_bar, add_comm])
    have h2' : σ (c * h.bar c) = c * h.bar c := hσ _ (by rw [map_mul, h.bar_bar, mul_comm])
    have h3 : (σ c - c) * (σ c - h.bar c) = 0 := by
      have h4 : σ (c ^ 2 - (c + h.bar c) * c + c * h.bar c) = 0 := by
        have : c ^ 2 - (c + h.bar c) * c + c * h.bar c = 0 := by ring
        rw [this, map_zero]
      rw [map_add, map_sub, map_mul, map_pow, h1, h2'] at h4
      linear_combination h4
    rcases mul_eq_zero.1 h3 with h5 | h5
    · exact Or.inl (sub_eq_zero.1 h5)
    · exact Or.inr (sub_eq_zero.1 h5)
  by_contra hcon
  push Not at hcon
  obtain ⟨hne1, hne2⟩ := hcon
  obtain ⟨a, ha⟩ : ∃ a, σ a ≠ a := by
    by_contra hall
    push Not at hall
    exact hne1 (RingEquiv.ext hall)
  obtain ⟨b, hb⟩ : ∃ b, σ b ≠ h.bar b := hne2
  have ha' : σ a = h.bar a := (hdich a).resolve_left ha
  have hb' : σ b = b := (hdich b).resolve_right hb
  rcases hdich (a + b) with h4 | h4
  · rw [map_add, ha', hb'] at h4
    exact ha (by rw [ha']; exact add_right_cancel h4)
  · rw [map_add, ha', hb', map_add] at h4
    exact hb (by rw [hb']; exact add_left_cancel h4)

end OrthF

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
