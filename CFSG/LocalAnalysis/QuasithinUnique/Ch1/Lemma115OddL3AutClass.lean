module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedGraphTools

public section

namespace CFSG.QuasithinUnique.Ch1

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix
open scoped MatrixGroups

section Classification

variable {F : Type} [Field F] [Finite F]

theorem subsingleton_ringEquiv_of_card_prime {p : ℕ} [Fact p.Prime] (hF : Nat.card F = p) :
    Subsingleton (F ≃+* F) := by
  have := Fintype.ofFinite F
  have hKF : Fintype.card F = p := by rw [← Nat.card_eq_fintype_card, hF]
  have : CharP F p := charP_of_card_eq_prime hKF
  let e : ZMod p ≃+* F := ZMod.ringEquiv F hKF
  refine ⟨fun σ τ => RingEquiv.ext fun x => ?_⟩
  obtain ⟨a, rfl⟩ := e.surjective x
  have h1 : (σ : F →+* F).comp (e : ZMod p →+* F) = (τ : F →+* F).comp e :=
    RingHom.ext_zmod _ _
  exact DFunLike.congr_fun h1 a

theorem exists_inner_of_sq_conjAut (A : GL (Fin 3) F)
    (h : conjAut 3 F A * conjAut 3 F A = 1) :
    ∃ g : projectiveSL 3 F, ∀ x, conjAut 3 F A x = g⁻¹ * x * g := by
  obtain ⟨-, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one (K := F) (n := 3) le_rfl (A * A) 1
    (by rw [map_one, mul_one, map_mul]; exact h)
  have hdet : (Matrix.GeneralLinearGroup.det A : Fˣ) ^ 2 = c ^ 3 := by
    apply Units.ext
    have h1 := congrArg (fun B : GL (Fin 3) F => ((B : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det)
      hc
    simp only [Units.val_mul, Matrix.det_mul, Matrix.GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin] at h1
    simpa [Matrix.GeneralLinearGroup.det, sq] using h1.symm
  set m : Fˣ := Matrix.GeneralLinearGroup.det A * c⁻¹ with hm
  have hm3 : m ^ 3 = Matrix.GeneralLinearGroup.det A := by
    have hc3 : c ^ 3 = (Matrix.GeneralLinearGroup.det A) ^ 2 := hdet.symm
    calc m ^ 3 = (Matrix.GeneralLinearGroup.det A) ^ 3 * (c ^ 3)⁻¹ := by
          rw [hm, mul_pow, inv_pow]
      _ = Matrix.GeneralLinearGroup.det A := by rw [hc3]; group
  set A' : GL (Fin 3) F := GeneralLinearGroup.scalar (Fin 3) m⁻¹ * A with hA'
  have hdetA' : ((A' : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = 1 := by
    have h1 : ((A' : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        ((m⁻¹ : Fˣ) : F) • ((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
      rw [hA', Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        ← Matrix.smul_eq_diagonal_mul]
    rw [h1, Matrix.det_smul, Fintype.card_fin]
    have hm3' : ((m : Fˣ) : F) ^ 3 = ((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det := by
      have := congrArg Units.val hm3
      simpa [Matrix.GeneralLinearGroup.det] using this
    have hdA : ((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det ≠ 0 :=
      (Matrix.isUnits_det_units A).ne_zero
    rw [Units.val_inv_eq_inv_val, inv_pow, hm3', inv_mul_cancel₀ hdA]
  let g : SL(3, F) := ⟨(A' : Matrix (Fin 3) (Fin 3) F), hdetA'⟩
  have hgA' : Matrix.SpecialLinearGroup.toGL g = A' := Units.ext rfl
  have hAA' : A = GeneralLinearGroup.scalar (Fin 3) m * A' := by
    rw [hA', ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  have hconjA : conjAut 3 F A = MulAut.conj (proj 3 F g) := by
    rw [← conjAut_toGL, hgA']
    conv_lhs => rw [hAA']
    rw [map_mul, conjAut_scalar, one_mul]
  refine ⟨(proj 3 F g)⁻¹, fun x => ?_⟩
  rw [hconjA, MulAut.conj_apply, inv_inv]

theorem symmetric_of_sq_conjAut_dualAut (h2 : (2 : F) ≠ 0) (A : GL (Fin 3) F)
    (h : (conjAut 3 F A * dualAut 3 F) ^ 2 = 1) :
    (A : Matrix (Fin 3) (Fin 3) F)ᵀ = A := by
  rcases transpose_eq_or_eq_neg_of_sq_conjAut_dualAut le_rfl A h with hs | hneg
  · exact hs
  · exfalso
    have hdet := congrArg Matrix.det hneg
    rw [Matrix.det_transpose, Matrix.det_neg, Fintype.card_fin] at hdet
    have hdA : ((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det ≠ 0 :=
      (Matrix.isUnits_det_units A).ne_zero
    apply hdA
    have h3 : (2 : F) * ((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = 0 := by
      linear_combination hdet
    exact (mul_eq_zero.mp h3).resolve_left h2

theorem classify_involution {p : ℕ} [Fact p.Prime] (hF : Nat.card F = p) (h2 : (2 : F) ≠ 0)
    (β : MulAut (projectiveSL 3 F)) (hβ : β * β = 1) :
    (∃ g : projectiveSL 3 F, ∀ x, β x = g⁻¹ * x * g) ∨
      ∃ A : GL (Fin 3) F, (A : Matrix (Fin 3) (Fin 3) F)ᵀ = A ∧
        β = conjAut 3 F A * dualAut 3 F := by
  have := subsingleton_ringEquiv_of_card_prime hF
  obtain ⟨A, σ, ε, hε, hβA⟩ := (automorphism_generation (n := 3) (K := F) le_rfl).2 β
  have hσ : σ = 1 := Subsingleton.elim _ _
  subst hσ
  interval_cases ε
  · left
    have hβ0 : β = conjAut 3 F A := by simpa using hβA
    rw [hβ0] at hβ
    obtain ⟨g, hg⟩ := exists_inner_of_sq_conjAut A hβ
    exact ⟨g, fun x => by rw [hβ0]; exact hg x⟩
  · right
    have hβ1 : β = conjAut 3 F A * dualAut 3 F := by simpa using hβA
    refine ⟨A, symmetric_of_sq_conjAut_dualAut h2 A ?_, hβ1⟩
    rw [← hβ1, sq]
    exact hβ

end Classification

end CFSG.QuasithinUnique.Ch1
