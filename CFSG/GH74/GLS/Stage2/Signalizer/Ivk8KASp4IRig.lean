module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KASp4Out

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.ComponentClassification CFSG.ComponentClassification.CatFactsSp4

section Sigma

variable {F : Type} [Field F]

theorem ka_trace_one_four :
    Matrix.trace (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = 4 := by
  rw [Matrix.trace_one, Fintype.card_sum, Fintype.card_fin]
  norm_num

theorem ka_trace_map_ringEquiv (σ : F ≃+* F) (N : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) :
    Matrix.trace (N.map σ) = σ (Matrix.trace N) := by
  simp [Matrix.trace]

theorem ka_sigma_eq_one_of_fix (h2 : (2 : F) ≠ 0)
    (N Am Ai : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)
    (hN : N ≠ 0) (hNtr : Matrix.trace N = 0) (hAmAi : Am * Ai = 1) (hAiAm : Ai * Am = 1)
    (σ : F ≃+* F)
    (hfix : ∀ c : F, (1 + c • N) = Am * (1 + c • N).map σ * Ai ∨
        (1 + c • N) = -(Am * (1 + c • N).map σ * Ai)) : σ = 1 := by
  set Nt : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F := Am * N.map σ * Ai with hNt
  have hexp : ∀ c : F, Am * (1 + c • N).map σ * Ai = 1 + σ c • Nt := by
    intro c
    have h1 : (1 + c • N).map σ = 1 + σ c • N.map σ := by
      ext i j
      by_cases hij : i = j <;> simp [Matrix.map_apply, hij]
    rw [h1, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hAmAi, Matrix.mul_smul,
      Matrix.smul_mul]
  have htrNt : Matrix.trace Nt = 0 := by
    rw [hNt, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hAiAm, Matrix.one_mul,
      ka_trace_map_ringEquiv, hNtr, map_zero]
  have hc : ∀ c : F, c • N = σ c • Nt := by
    intro c
    rcases hfix c with h | h
    · rw [hexp] at h
      exact add_left_cancel h
    · exfalso
      rw [hexp] at h
      have h3 := congrArg Matrix.trace h
      simp only [Matrix.trace_add, Matrix.trace_neg, Matrix.trace_smul, hNtr, htrNt,
        ka_trace_one_four, smul_zero, add_zero] at h3
      have h8 : (8 : F) = 0 := by linear_combination h3
      have : (8 : F) = 2 * 2 * 2 := by norm_num
      rw [this] at h8
      exact mul_ne_zero (mul_ne_zero h2 h2) h2 h8
  have h1 : N = Nt := by simpa using hc 1
  obtain ⟨i, j, hij⟩ : ∃ i j, N i j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hN (by ext i j; exact hcon i j)
  ext c
  have h3 := congrFun (congrFun (hc c) i) j
  rw [← h1] at h3
  simp only [Matrix.smul_apply, smul_eq_mul] at h3
  exact (mul_right_cancel₀ hij h3).symm

theorem ka_fix_matrix (A : gsp 2 F) (σ : F ≃+* F) (g : StatedSp 2 F)
    (h : (conjAut 2 F A * fieldAut 2 F σ) (proj 2 F g) = proj 2 F g) :
    ((g : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
        ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
          ((g : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).map σ *
          (((A : GL (Fin 2 ⊕ Fin 2) F)⁻¹ : GL (Fin 2 ⊕ Fin 2) F) :
            Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) ∨
      ((g : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
        -(((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
          ((g : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).map σ *
          (((A : GL (Fin 2 ⊕ Fin 2) F)⁻¹ : GL (Fin 2 ⊕ Fin 2) F) :
            Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)) := by
  have h1 : proj 2 F (conjSp 2 F A (fieldSp 2 F σ g)) = proj 2 F g := by
    rw [← conjAut_proj, ← fieldAut_proj]
    exact h
  have h2 := eq_or_eq_neg_of_proj_eq h1
  rw [coe_conjSp, Units.val_mul, Units.val_mul, coe_fieldSp] at h2
  exact h2

end Sigma

section Root

variable {F : Type} [Field F]

@[expose] def kaRigE12 : Matrix (Fin 2) (Fin 2) F := !![0, 1; 0, 0]

@[expose] def kaRigN (a : F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
  bA a * kron kaRigE12 1 * bAinv a

@[expose] def kaRigU (c : F) : Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨!![1, c; 0, 1], by simp [Matrix.det_fin_two]⟩

theorem ka_kron_rigU (c : F) :
    kron (kaRigU c : Matrix (Fin 2) (Fin 2) F) 1 = 1 + c • kron kaRigE12 1 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [kron, kaRigU, kaRigE12]

theorem ka_coe_gI_rigU {a : F} (ha : a ≠ 0) (c : F) :
    (((gI ha (kaRigU c) : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = 1 + c • kaRigN a := by
  rw [coe_gI, ka_kron_rigU, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, bA_mul_bAinv ha,
    Matrix.mul_smul, Matrix.smul_mul]
  rfl

theorem ka_rigN_ne_zero {a : F} (ha : a ≠ 0) : kaRigN a ≠ 0 := by
  intro h
  have h1 : kron (kaRigE12 : Matrix (Fin 2) (Fin 2) F) 1 = bAinv a * kaRigN a * bA a := by
    rw [kaRigN]
    calc kron (kaRigE12 : Matrix (Fin 2) (Fin 2) F) 1 =
        (bAinv a * bA a) * kron kaRigE12 1 * (bAinv a * bA a) := by
          rw [bAinv_mul_bA ha, Matrix.one_mul, Matrix.mul_one]
      _ = bAinv a * (bA a * kron kaRigE12 1 * bAinv a) * bA a := by
          simp only [Matrix.mul_assoc]
  rw [h, Matrix.mul_zero, Matrix.zero_mul] at h1
  have h2 := congrFun (congrFun h1 (Sum.inl 0)) (Sum.inr 0)
  simp [kron, kaRigE12] at h2

theorem ka_trace_rigN {a : F} (ha : a ≠ 0) : Matrix.trace (kaRigN a) = 0 := by
  rw [kaRigN, Matrix.trace_mul_comm, ← Matrix.mul_assoc, bAinv_mul_bA ha, Matrix.one_mul]
  simp [Matrix.trace, kron, kaRigE12]

end Root

theorem kaSp4I_rigid {F : Type} [Field F] [Finite F] (hodd : ringChar F ≠ 2) {a : F}
    (ha : a ≠ 0) : KARigid (JI ha) := by
  intro p hp hp2 e hpe hfix
  obtain ⟨A, σ, rfl⟩ :=
    (CatalogueBSymplecticRepresentation.odd_symplectic_automorphism_semilinear_representation
      hodd le_rfl).1 e
  have hσ : σ = 1 := by
    refine ka_sigma_eq_one_of_fix (Ring.two_ne_zero hodd) (kaRigN a)
      ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)
      (((A : GL (Fin 2 ⊕ Fin 2) F)⁻¹ : GL (Fin 2 ⊕ Fin 2) F) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)
      (ka_rigN_ne_zero ha) (ka_trace_rigN ha) (Units.mul_inv _) (Units.inv_mul _) σ fun c => ?_
    have h := ka_fix_matrix A σ (gI ha (kaRigU c))
      (hfix _ ⟨gI ha (kaRigU c), ⟨kaRigU c, rfl⟩, rfl⟩)
    rw [ka_coe_gI_rigU ha c] at h
    exact h
  subst hσ
  have ho : Odd (orderOf (conjAut 2 F A * fieldAut 2 F 1)) :=
    ka_odd_of_mem_pGroup hp hp2 hpe (Subgroup.mem_zpowers _)
  rw [map_one, mul_one] at ho ⊢
  exact ka_conjAut_inner_of_odd hodd A ho

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
