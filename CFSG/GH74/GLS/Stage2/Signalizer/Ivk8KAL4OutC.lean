module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAL4Out
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FSp4Out
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismTransport
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAL4Def
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL4
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL4Cases
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL4Kill
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedGraphSymm

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup Matrix CFSG CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open scoped commutatorElement

theorem ka_outc_ringEquiv_of_sq {F : Type} [Field F] (σ : F ≃+* F) {γ a d : F}
    (ha : a * a = γ ^ 4) (hγ : σ γ = d * d * γ) : σ a = d ^ 4 * a := by
  have h1 : a * a = γ ^ 2 * γ ^ 2 := by rw [ha]; ring
  rcases mul_self_eq_mul_self_iff.1 h1 with h | h
  · rw [h, map_pow, hγ]
    ring
  · rw [h, map_neg, map_pow, hγ]
    ring

theorem ka_outc_units_map {F : Type} [Field F] (σ : F ≃+* F) {c e d : Fˣ} (he : e * e = c ^ 4)
    (hd : Units.map (σ : F →* F) c * c⁻¹ = d * d) :
    Units.map ((σ : F →+* F) : F →* F) e = d ^ 4 * e := by
  have hd' : Units.map (σ : F →* F) c = d * d * c := mul_inv_eq_iff_eq_mul.1 hd
  have h1 : (e : F) * (e : F) = (c : F) ^ 4 := by
    rw [← Units.val_mul, he, Units.val_pow_eq_pow_val]
  have h2 : σ (c : F) = (d : F) * (d : F) * (c : F) := by
    have := congrArg (fun u : Fˣ => (u : F)) hd'
    simpa using this
  have h3 := ka_outc_ringEquiv_of_sq σ h1 h2
  apply Units.ext
  simpa using h3

theorem ka_outc_det_sq {F : Type} [Field F] {A : GL (Fin 4) F} {c : Fˣ}
    (hA : A * A = GeneralLinearGroup.scalar (Fin 4) c) :
    Matrix.GeneralLinearGroup.det A * Matrix.GeneralLinearGroup.det A = c ^ 4 := by
  rw [← map_mul, hA, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin]

theorem ka_outc_det_inverseTranspose {F : Type} [Field F] (A : GL (Fin 4) F) :
    Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.inverseTranspose A) =
      (Matrix.GeneralLinearGroup.det A)⁻¹ := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.coe_inverseTranspose,
    Matrix.det_transpose, ← Matrix.GeneralLinearGroup.val_det_apply, map_inv]

theorem ka_outc_conjAut_inner_of_det {F : Type} [Field F] [Finite F] (M : GL (Fin 4) F) (μ : Fˣ)
    (h : Matrix.GeneralLinearGroup.det M = μ ^ 4) :
    conjAut 4 F M ∈ innSub (projectiveSL 4 F) :=
  ka_conjAut_inner_of_det_pow4 M μ (by
    rw [← Matrix.GeneralLinearGroup.val_det_apply, h, Units.val_pow_eq_pow_val])

theorem ka_outCentral_pl4 {F : Type} [Field F] [Finite F] (hodd : ringChar F ≠ 2)
    (A : GL (Fin 4) F) (c : Fˣ) (hA : A * A = GeneralLinearGroup.scalar (Fin 4) c) :
    ∀ x : MulAut (projectiveSL 4 F), ⁅x, conjAut 4 F A⁆ ∈ innSub (projectiveSL 4 F) := by
  intro x
  obtain ⟨X, σ, ε, hε, rfl⟩ := (automorphism_generation (K := F) (n := 4) (by norm_num)).2 x
  obtain ⟨d, hd⟩ := isSquare_ratio hodd σ c
  have hdA := ka_outc_det_sq hA
  have hσ : Units.map ((σ : F →+* F) : F →* F) (Matrix.GeneralLinearGroup.det A) =
      d ^ 4 * Matrix.GeneralLinearGroup.det A := ka_outc_units_map σ hdA hd
  obtain ⟨-, -, h3, hdd, h5, -⟩ := standard_automorphism_transport (n := 4) (K := F)
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hε with rfl | rfl
  · rw [pow_zero, mul_one]
    have e : ⁅conjAut 4 F X * fieldAut 4 F σ, conjAut 4 F A⁆ =
        conjAut 4 F (X * GeneralLinearGroup.map (σ : F →+* F) A * X⁻¹ * A⁻¹) := by
      rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv, ← h3 σ A]
      group
    rw [e]
    refine ka_outc_conjAut_inner_of_det _ d ?_
    simp only [map_mul, map_inv, Matrix.GeneralLinearGroup.map_det]
    rw [mul_inv_cancel_comm, hσ, mul_inv_cancel_right]
  · rw [pow_one]
    have hδ : (dualAut 4 F)⁻¹ = dualAut 4 F := inv_eq_of_mul_eq_one_right hdd
    have hδc : dualAut 4 F * conjAut 4 F A * (dualAut 4 F)⁻¹ =
        conjAut 4 F (Matrix.GeneralLinearGroup.inverseTranspose A) := by
      rw [hδ]
      exact h5 A
    have e : ⁅conjAut 4 F X * fieldAut 4 F σ * dualAut 4 F, conjAut 4 F A⁆ =
        conjAut 4 F (X * GeneralLinearGroup.map (σ : F →+* F)
          (Matrix.GeneralLinearGroup.inverseTranspose A) * X⁻¹ * A⁻¹) := by
      rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv,
        ← h3 σ (Matrix.GeneralLinearGroup.inverseTranspose A), ← hδc]
      group
    rw [e]
    refine ka_outc_conjAut_inner_of_det _ (d * c)⁻¹ ?_
    simp only [map_mul, map_inv, Matrix.GeneralLinearGroup.map_det,
      ka_outc_det_inverseTranspose]
    rw [mul_inv_cancel_comm, hσ, ← mul_inv, mul_assoc, hdA, ← mul_pow, inv_pow]

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
