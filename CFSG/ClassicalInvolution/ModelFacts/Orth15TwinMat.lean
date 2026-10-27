module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15Frame

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Orth15

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal
  QuadraticMap Matrix
open scoped MatrixGroups

section Mat

variable {F : Type} [Field F]

theorem eq_one_or_neg_one_of_sq (h2 : (2 : F) ≠ 0) {A : Matrix (Fin 2) (Fin 2) F}
    (hd : A.det = 1) (hA : A * A = 1) : A = 1 ∨ A = -1 := by
  have hA' := Matrix.eta_fin_two A
  set a := A 0 0
  set b := A 0 1
  set c := A 1 0
  set d := A 1 1
  rw [hA'] at hA
  simp only [Matrix.mul_fin_two] at hA
  have e00 := congrFun (congrFun hA 0) 0
  have e01 := congrFun (congrFun hA 0) 1
  have e10 := congrFun (congrFun hA 1) 0
  have e11 := congrFun (congrFun hA 1) 1
  simp at e00 e01 e10 e11
  rw [Matrix.det_fin_two] at hd
  have hd' : a * d - b * c = 1 := hd
  by_cases hs : a + d = 0
  · exfalso
    apply h2
    have hd0 : d = -a := by linear_combination hs
    rw [hd0] at hd'
    linear_combination (-1 : F) * hd' - e00
  · have hb : b = 0 := by
      have : b * (a + d) = 0 := by linear_combination e01
      exact (mul_eq_zero.mp this).resolve_right hs
    have hc : c = 0 := by
      have : c * (a + d) = 0 := by linear_combination e10
      exact (mul_eq_zero.mp this).resolve_right hs
    rw [hb, hc] at e00 hd'
    have haa : a * a = 1 := by simpa using e00
    have had : a * d = 1 := by simpa using hd'
    have hda : d = a := by
      have h1 : a * (d - a) = 0 := by linear_combination had - haa
      have ha0 : a ≠ 0 := by
        intro h0
        rw [h0] at had
        simp at had
      have := (mul_eq_zero.mp h1).resolve_left ha0
      linear_combination this
    rcases mul_self_eq_one_iff.mp haa with ha | ha
    · left
      rw [hA', hb, hc, hda, ha]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    · right
      rw [hA', hb, hc, hda, ha]
      ext i j
      fin_cases i <;> fin_cases j <;> simp

theorem exists_smul_one_of_commute {P : Matrix (Fin 2) (Fin 2) F}
    (h : ∀ X : Matrix (Fin 2) (Fin 2) F, P * X = X * P) : ∃ a : F, P = a • 1 := by
  have hP := Matrix.eta_fin_two P
  have h1 := h !![1, 0; 0, 0]
  have h2 := h !![0, 1; 0, 0]
  rw [hP] at h1 h2
  simp only [Matrix.mul_fin_two] at h1 h2
  have e01 := congrFun (congrFun h1 0) 1
  have e10 := congrFun (congrFun h1 1) 0
  have g01 := congrFun (congrFun h2 0) 1
  simp at e01 e10 g01
  have hb : P 0 1 = 0 := e01.symm
  have hc : P 1 0 = 0 := e10
  have hd : P 1 1 = P 0 0 := g01.symm
  refine ⟨P 0 0, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hb, hc, hd]

end Mat

section Sigma

variable {F : Type} [Field F]

theorem sigmaLin_one : sigmaLin (1 : Matrix (Fin 2) (Fin 2) F) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sigmaLin_apply]

end Sigma

section Square

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

theorem sq_eq_of_twinInv_sq_scalar (fr : Frame Q) (hperp : fr.perp ≠ ⊥) {A A' : SL(2, F)} {μ : F}
    (h : ∀ v, twinInv fr A A' (twinInv fr A A' v) = μ • v) :
    ∃ ε : F, (ε = 1 ∨ ε = -1) ∧ (A : Matrix (Fin 2) (Fin 2) F) * A = ε • 1 ∧
      (A' : Matrix (Fin 2) (Fin 2) F) * A' = ε • 1 := by
  obtain ⟨p, hp, hp0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hperp
  have hμ : μ = 1 := by
    have h1 := h p
    rw [twinInv_perp fr A A' hp, twinInv_perp fr A A' hp] at h1
    have : (1 - μ) • p = 0 := by rw [sub_smul, one_smul, ← h1, sub_self]
    exact (sub_eq_zero.mp ((smul_eq_zero.mp this).resolve_right hp0)).symm
  have hX : ∀ X : Matrix (Fin 2) (Fin 2) F,
      (A : Matrix (Fin 2) (Fin 2) F) * (A : Matrix (Fin 2) (Fin 2) F) * X *
        (sigmaLin (A' : Matrix (Fin 2) (Fin 2) F) * sigmaLin (A' : Matrix (Fin 2) (Fin 2) F)) =
          X := by
    intro X
    have h1 := h (fr.incl X)
    rw [twinInv_incl, twinInv_incl, hμ, one_smul] at h1
    have h2 := (Frame.incl_injective fr) h1
    calc (A : Matrix (Fin 2) (Fin 2) F) * (A : Matrix (Fin 2) (Fin 2) F) * X *
          (sigmaLin (A' : Matrix (Fin 2) (Fin 2) F) * sigmaLin (A' : Matrix (Fin 2) (Fin 2) F))
        = (A : Matrix (Fin 2) (Fin 2) F) * ((A : Matrix (Fin 2) (Fin 2) F) * X *
            sigmaLin (A' : Matrix (Fin 2) (Fin 2) F)) *
          sigmaLin (A' : Matrix (Fin 2) (Fin 2) F) := by
          simp only [Matrix.mul_assoc]
      _ = X := h2
  set P : Matrix (Fin 2) (Fin 2) F :=
    (A : Matrix (Fin 2) (Fin 2) F) * (A : Matrix (Fin 2) (Fin 2) F) with hPdef
  set S : Matrix (Fin 2) (Fin 2) F :=
    sigmaLin (A' : Matrix (Fin 2) (Fin 2) F) * sigmaLin (A' : Matrix (Fin 2) (Fin 2) F) with hSdef
  have hX' : ∀ X : Matrix (Fin 2) (Fin 2) F, P * X * S = X := hX
  have hPS : P * S = 1 := by simpa using hX' 1
  have hSP : S * P = 1 := mul_eq_one_comm.mp hPS
  have hcomm : ∀ X : Matrix (Fin 2) (Fin 2) F, P * X = X * P := by
    intro X
    calc P * X = P * X * (S * P) := by rw [hSP, mul_one]
      _ = (P * X * S) * P := by simp only [Matrix.mul_assoc]
      _ = X * P := by rw [hX' X]
  obtain ⟨a, ha⟩ := exists_smul_one_of_commute hcomm
  have hdetP : P.det = 1 := by
    rw [hPdef, Matrix.det_mul, A.2, one_mul]
  have ha2 : a * a = 1 := by
    rw [ha, Matrix.det_smul, Matrix.det_one] at hdetP
    simpa [pow_two] using hdetP
  have hS : S = a • 1 := by
    rw [ha, Matrix.smul_mul, one_mul] at hPS
    calc S = (a * a) • S := by rw [ha2, one_smul]
      _ = a • (a • S) := (smul_smul a a S).symm
      _ = a • 1 := by rw [hPS]
  have hA'sq : (A' : Matrix (Fin 2) (Fin 2) F) * (A' : Matrix (Fin 2) (Fin 2) F) = a • 1 := by
    have h1 : sigmaLin ((A' : Matrix (Fin 2) (Fin 2) F) * (A' : Matrix (Fin 2) (Fin 2) F)) =
        a • 1 := by
      rw [sigmaLin_mul]
      exact hS
    calc (A' : Matrix (Fin 2) (Fin 2) F) * (A' : Matrix (Fin 2) (Fin 2) F)
        = sigmaLin (sigmaLin ((A' : Matrix (Fin 2) (Fin 2) F) *
            (A' : Matrix (Fin 2) (Fin 2) F))) := (sigmaLin_sigmaLin _).symm
      _ = sigmaLin (a • (1 : Matrix (Fin 2) (Fin 2) F)) := by rw [h1]
      _ = a • sigmaLin (1 : Matrix (Fin 2) (Fin 2) F) := map_smul _ _ _
      _ = a • 1 := by rw [sigmaLin_one]
  exact ⟨a, mul_self_eq_one_iff.mp ha2, ha, hA'sq⟩

end Square

end CFSG.ClassicalInvolution.ModelFacts.Orth15
