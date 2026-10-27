module

public import CFSG.LocalAnalysis.ComponentInitial.FieldFiniteAutomorphism
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.RootCenterAutomorphismBasic
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.RootCenterAutomorphismUnitaryAut

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.UnitaryOuter

open Matrix CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.ShultStronglyClosedTI CFSG.ShultStronglyClosedTI.UnitaryRootAutomorphism
open CFSG.ShultStronglyClosedTI.UnitaryAutomorphism CFSG.ProperTwoGeneratedCore.RootCenter
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)

variable {K : Type} [Field K]

theorem zpow_apply_eq_self_of_apply_eq_self {τ : K ≃+* K} {b : K} (h : τ b = b) (m : ℤ) :
    (τ ^ m) b = b := by
  let Stab : Subgroup (K ≃+* K) :=
    { carrier := {ρ | ρ b = b}
      mul_mem' := fun {ρ₁ ρ₂} h₁ h₂ => by
        change ρ₁ (ρ₂ b) = b
        rw [show ρ₂ b = b from h₂, show ρ₁ b = b from h₁]
      one_mem' := rfl
      inv_mem' := fun {ρ} hρ => by
        change ρ.symm b = b
        conv_lhs => rw [← show ρ b = b from hρ]
        exact ρ.symm_apply_apply b }
  exact (Subgroup.zpowers_le.mpr (show τ ∈ Stab from h)) (Subgroup.zpow_mem_zpowers τ m)

theorem ringEquiv_apply_eq_self_of_mul_self [Finite K] (J : HermitianForm 3 K) {f : ℕ}
    (hf : 1 ≤ f) (hcard : Nat.card K = (2 ^ f) ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f) {σ : K ≃+* K} (hσ : σ * σ = 1)
    {b : K} (hb : J.conj b = b) : σ b = b := by
  have hF : Nat.card K = 2 ^ (2 * f) := by rw [hcard, ← pow_mul, mul_comm]
  obtain ⟨φ, hφ, hord, hzp, -, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two (by omega) hF
  have hiter : ∀ (k : ℕ) (a : K), (φ ^ k) a = a ^ (2 ^ k) := by
    intro k
    induction k with
    | zero => intro a; simp
    | succ k ih =>
      intro a
      rw [pow_succ, show (φ ^ k * φ) a = (φ ^ k) (φ a) from rfl, hφ, ih, ← pow_mul, pow_succ',
        mul_comm]
  have hφf : (φ ^ f) b = b := by
    rw [hiter, ← huppert_II_10_4_conj_eq_frobenius J (2 ^ f) hcard hfixed, hb]
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hzp ▸ Subgroup.mem_top σ)
  have h2 : φ ^ (2 * j) = 1 := by rw [mul_comm, _root_.zpow_mul, hj, zpow_two, hσ]
  have hdvd : ((2 * f : ℕ) : ℤ) ∣ 2 * j := by
    rw [← hord]
    exact orderOf_dvd_iff_zpow_eq_one.mpr h2
  obtain ⟨m, hm⟩ : (f : ℤ) ∣ j := by
    obtain ⟨m, hm⟩ := hdvd
    exact ⟨m, by push_cast at hm; linarith⟩
  rw [← hj, hm, _root_.zpow_mul, zpow_natCast]
  exact zpow_apply_eq_self_of_apply_eq_self hφf m

theorem conj_comm_of_frobenius [Finite K] (J : HermitianForm 3 K) {q : ℕ}
    (hcard : Nat.card K = q ^ 2) (hfixed : Nat.card {x : K // J.conj x = x} = q) (σ : K ≃+* K)
    (x : K) : σ (J.conj x) = J.conj (σ x) := by
  rw [huppert_II_10_4_conj_eq_frobenius J q hcard hfixed,
    huppert_II_10_4_conj_eq_frobenius J q hcard hfixed, map_pow]

theorem eq_of_mk_eq_of_trace_eq {X Y : GL (Fin 3) K}
    (h : ProjGenLinGroup.mk X = ProjGenLinGroup.mk Y)
    (htr : (X : Matrix (Fin 3) (Fin 3) K).trace = (Y : Matrix (Fin 3) (Fin 3) K).trace)
    (h0 : (X : Matrix (Fin 3) (Fin 3) K).trace ≠ 0) : X = Y := by
  obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp h
  have h1 : (Y : Matrix (Fin 3) (Fin 3) K).trace = (X : Matrix (Fin 3) (Fin 3) K).trace * u := by
    rw [← hu, Units.val_mul, GeneralLinearGroup.coe_scalar]
    simp [Matrix.trace, Matrix.mul_apply, Matrix.scalar_apply, Matrix.diagonal_apply,
      Finset.sum_mul]
  have hu1 : (u : K) = 1 := by
    have h2 : (X : Matrix (Fin 3) (Fin 3) K).trace * ((u : K) - 1) = 0 := by
      rw [mul_sub, ← h1, ← htr, mul_one, sub_self]
    exact sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_left h0)
  rw [← hu, show u = 1 from Units.ext hu1, map_one, mul_one]

theorem trace_hermitianUnipotentMatrix [CharP K 2] (J : HermitianForm 3 K)
    (z : hermitianUnipotentCoord J) : (hermitianUnipotentMatrix J z).trace = 1 := by
  rw [hermitianUnipotentMatrix_eq, Matrix.trace_fin_three]
  simp only [of_apply, cons_val', cons_val_zero, cons_val_one, cons_val_two, empty_val',
    cons_val_fin_one, head_cons, tail_cons, head_fin_const]
  have : (2 : K) = 0 := CharTwo.two_eq_zero
  linear_combination this

@[expose] def sigmaCoord (J : HermitianForm 3 K) (σ : K ≃+* K)
    (hσ : ∀ x, σ (J.conj x) = J.conj (σ x)) (z : hermitianUnipotentCoord J) :
    hermitianUnipotentCoord J :=
  ⟨(σ z.1.1, σ z.1.2), by
    have h := congrArg σ z.2
    rw [map_add, map_add, map_mul, hσ, hσ, map_zero] at h
    exact h⟩

theorem glAut_hermitianUnipotentGL (J : HermitianForm 3 K) (σ : K ≃+* K)
    (hσ : ∀ x, σ (J.conj x) = J.conj (σ x)) (z : hermitianUnipotentCoord J) :
    glAut σ (hermitianUnipotentGL J z) = hermitianUnipotentGL J (sigmaCoord J σ hσ z) := by
  apply Units.ext
  rw [coe_glAut, hermitianUnipotentGL_val, hermitianUnipotentGL_val, hermitianUnipotentMatrix_eq,
    hermitianUnipotentMatrix_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sigmaCoord, hσ]

theorem hermitianUnipotentPSU_eq_psuMk (J : HermitianForm 3 K)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) (z : hermitianUnipotentCoord J) :
    hermitianUnipotentPSU J hJ z =
      psuMk J ⟨hermitianUnipotentGL J z, hermitianUnipotentGL_mem J hJ z⟩ :=
  Subtype.ext rfl

theorem trace_conj_GL (A X : GL (Fin 3) K) :
    ((A * X * A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).trace =
      (X : Matrix (Fin 3) (Fin 3) K).trace := by
  rw [Units.val_mul, Units.val_mul, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Units.val_mul,
    inv_mul_cancel, Units.val_one, Matrix.one_mul]

theorem conj_eq_of_psuMk_eq [CharP K 2] (J : HermitianForm 3 K)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) {A X : GL (Fin 3) K}
    (hX : (X : Matrix (Fin 3) (Fin 3) K).trace = 1) (hmem : A * X * A⁻¹ ∈ J.specialSubgroup)
    (w : hermitianUnipotentCoord J)
    (h : psuMk J ⟨A * X * A⁻¹, hmem⟩ = hermitianUnipotentPSU J hJ w) :
    A * X * A⁻¹ = hermitianUnipotentGL J w := by
  rw [hermitianUnipotentPSU_eq_psuMk J hJ] at h
  refine eq_of_mk_eq_of_trace_eq (congrArg Subtype.val h) ?_ ?_
  · rw [trace_conj_GL, hX, hermitianUnipotentGL_val, trace_hermitianUnipotentMatrix]
  · rw [trace_conj_GL, hX]
    exact one_ne_zero

abbrev rootE : Matrix (Fin 3) (Fin 3) K := !![0, 0, 1; 0, 0, 0; 0, 0, 0]

theorem hermitianUnipotentMatrix_of_fst_eq_zero (J : HermitianForm 3 K)
    {z : hermitianUnipotentCoord J} (hz : z.1.1 = 0) :
    hermitianUnipotentMatrix J z = 1 + z.1.2 • rootE := by
  rw [hermitianUnipotentMatrix_eq, hz]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem conj_one_add_smul (A : GL (Fin 3) K) (c : K) (N : Matrix (Fin 3) (Fin 3) K) :
    (A : Matrix (Fin 3) (Fin 3) K) * (1 + c • N) *
        ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      1 + c • ((A : Matrix (Fin 3) (Fin 3) K) * N *
        ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) := by
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, ← Units.val_mul, mul_inv_cancel,
    Units.val_one, Matrix.mul_smul, Matrix.smul_mul]

theorem entries_of_comm_one_add_rootE {B : Matrix (Fin 3) (Fin 3) K}
    (h : B * (1 + rootE) = (1 + rootE) * B) :
    B 2 0 = 0 ∧ B 2 1 = 0 ∧ B 1 0 = 0 ∧ B 0 0 = B 2 2 := by
  have h00 := congrFun (congrFun h 0) 0
  have h01 := congrFun (congrFun h 0) 1
  have h02 := congrFun (congrFun h 0) 2
  have h12 := congrFun (congrFun h 1) 2
  simp only [Matrix.mul_apply, Fin.sum_univ_three] at h00 h01 h02 h12
  simp [Matrix.add_apply] at h00 h01 h02 h12
  refine ⟨h00, h01, ?_, ?_⟩
  · linear_combination h12
  · linear_combination h02

theorem entry_one_two_of_comm (J : HermitianForm 3 K) {B : Matrix (Fin 3) (Fin 3) K}
    (hB : B 1 0 = 0) {z w : hermitianUnipotentCoord J}
    (h : B * hermitianUnipotentMatrix J w = hermitianUnipotentMatrix J z * B) :
    B 1 1 * J.conj w.1.1 = J.conj z.1.1 * B 2 2 := by
  have h12 := congrFun (congrFun h 1) 2
  simp [Matrix.mul_apply, Fin.sum_univ_three, hB] at h12
  linear_combination -h12

@[expose] def coordZeroOne [CharP K 2] (J : HermitianForm 3 K) : hermitianUnipotentCoord J :=
  ⟨(0, 1), by rw [map_one, map_zero, mul_zero, add_zero, CharTwo.add_self_eq_zero]⟩

end CFSG.ProperTwoGeneratedCore.Lemma37.UnitaryOuter
