module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL3CharRad
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL3CharVec
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherFieldInvolution

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.L46E.AutC

open Matrix Subgroup CFSG.GH74.GLS.Stage2.Signalizer.Odd87
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ComponentClassification
open scoped MatrixGroups

section PElements

variable {F : Type} [Field F]

theorem elP_pow (a b : F) (k : ℕ) : (elP a b : SL(3, F)) ^ k = elP (k • a) (k • b) := by
  induction k with
  | zero => simp [elP_zero]
  | succ k ih => rw [pow_succ, ih, elP_mul]; simp [add_smul]

theorem elP_pow_char {p : ℕ} [CharP F p] (a b : F) : (elP a b : SL(3, F)) ^ p = 1 := by
  rw [elP_pow]
  have h : (p • a : F) = 0 := by rw [nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]
  have h' : (p • b : F) = 0 := by rw [nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]
  rw [h, h', elP_zero]

theorem elM_pow (a b : F) (k : ℕ) : (elM a b : SL(3, F)) ^ k = elM (k • a) (k • b) := by
  induction k with
  | zero => simp [elM_zero]
  | succ k ih => rw [pow_succ, ih, elM_mul]; simp [add_smul]

theorem elM_pow_char {p : ℕ} [CharP F p] (a b : F) : (elM a b : SL(3, F)) ^ p = 1 := by
  rw [elM_pow]
  have h : (p • a : F) = 0 := by rw [nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]
  have h' : (p • b : F) = 0 := by rw [nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]
  rw [h, h', elM_zero]

theorem eq_of_proj_eq_of_pow_eq_one [Finite F] {p : ℕ} [Fact p.Prime] [CharP F p]
    {M N : SL(3, F)} (hM : M ^ p = 1) (hN : N ^ p = 1)
    (h : proj 3 F M = proj 3 F N) : M = N := by
  have hs : M⁻¹ * N ∈ scalars 3 F := proj_eq_proj_iff.mp h
  set s : SL(3, F) := M⁻¹ * N with hsdef
  have hcen : s ∈ Subgroup.center SL(3, F) := scalars_le_center 3 F hs
  have hN' : N = M * s := by rw [hsdef]; group
  have hsp : s ^ p = 1 := by
    have hc : Commute M s := ((Subgroup.mem_center_iff.mp hcen) M)
    have : (M * s) ^ p = M ^ p * s ^ p := hc.mul_pow p
    rw [← hN', hN, hM, one_mul] at this
    exact this.symm
  have h1 : orderOf s ∣ p := orderOf_dvd_of_pow_eq_one hsp
  have h2 : orderOf s ∣ Nat.card (scalars 3 F) := Subgroup.orderOf_dvd_natCard (scalars 3 F) hs
  have h3 : Nat.Coprime (orderOf s) p := Nat.Coprime.coprime_dvd_left h2 (coprime_card_scalars p)
  have h4 : orderOf s = 1 := Nat.Coprime.eq_one_of_dvd h3 h1
  have : s = 1 := orderOf_eq_one_iff.mp h4
  rw [hN', this, mul_one]

end PElements

section LIII

variable {F : Type} [Field F]

theorem map_elP (σ : F ≃+* F) (a b : F) :
    SpecialLinearGroup.map σ.toRingHom (elP a b) = elP (σ a) (σ b) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [coe_elP, SpecialLinearGroup.map_apply_coe]

theorem map_elM (σ : F ≃+* F) (a b : F) :
    SpecialLinearGroup.map σ.toRingHom (elM a b) = elM (σ a) (σ b) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [coe_elM, SpecialLinearGroup.map_apply_coe]

theorem inv_elP (a b : F) : (elP a b : SL(3, F))⁻¹ = elP (-a) (-b) := by
  rw [inv_eq_iff_mul_eq_one, elP_mul]
  simp [elP_zero]

theorem transpose_elP (a b : F) : (elP a b : SL(3, F)).transpose = elM a b := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [coe_elP, coe_elM, SpecialLinearGroup.coe_transpose]

theorem dual_elP (a b : F) :
    dualAut 3 F (proj 3 F (elP a b)) = proj 3 F (elM (-a) (-b)) := by
  rw [dualAut_proj, inv_elP, transpose_elP]

end LIII

section Core

variable {F : Type} [Field F]

theorem mul_eq_of_slConj_eq (A : GL (Fin 3) F) {x N : SL(3, F)}
    (h : CatalogueBHigherLinearAction.slConjugation 3 F A x = N) :
    (A : Matrix (Fin 3) (Fin 3) F) * (x : Matrix (Fin 3) (Fin 3) F) =
      (N : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F) := by
  have h1 := congrArg (fun g : SL(3, F) => (g : Matrix (Fin 3) (Fin 3) F)) h
  simp only [CatalogueBHigherLinearAction.slConjugation_matrix] at h1
  rw [← h1]
  have hAinv : ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F) = 1 :=
    Units.inv_mul A
  calc (A : Matrix (Fin 3) (Fin 3) F) * (x : Matrix (Fin 3) (Fin 3) F)
      = (A : Matrix (Fin 3) (Fin 3) F) * (x : Matrix (Fin 3) (Fin 3) F) * 1 := (mul_one _).symm
    _ = (A : Matrix (Fin 3) (Fin 3) F) * (x : Matrix (Fin 3) (Fin 3) F) *
        (((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F)) := by
        rw [hAinv]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem apply_ε0 (A : GL (Fin 3) F) (σ : F ≃+* F) (a b : F) :
    (conjAut 3 F A * fieldAut 3 F σ) (proj 3 F (elP a b)) =
      proj 3 F (CatalogueBHigherLinearAction.slConjugation 3 F A (elP (σ a) (σ b))) := by
  rw [MulAut.mul_apply, fieldAut_proj, conjAut_proj, map_elP]

theorem apply_ε1 (A : GL (Fin 3) F) (σ : F ≃+* F) (a b : F) :
    (conjAut 3 F A * fieldAut 3 F σ * dualAut 3 F) (proj 3 F (elP a b)) =
      proj 3 F (CatalogueBHigherLinearAction.slConjugation 3 F A (elM (-σ a) (-σ b))) := by
  rw [MulAut.mul_apply, MulAut.mul_apply, dual_elP, fieldAut_proj, conjAut_proj, map_elM, map_neg,
    map_neg]

theorem key0 [Finite F] (p : ℕ) [Fact p.Prime] [CharP F p] (A : GL (Fin 3) F) (σ : F ≃+* F)
    (hfix : ∀ a b : F, (conjAut 3 F A * fieldAut 3 F σ) (proj 3 F (elP a b)) = proj 3 F (elP a b))
    (a b : F) :
    (A : Matrix (Fin 3) (Fin 3) F) * ((elP (σ a) (σ b) : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      ((elP a b : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F) := by
  have h := hfix a b
  rw [apply_ε0] at h
  refine mul_eq_of_slConj_eq A ?_
  refine eq_of_proj_eq_of_pow_eq_one (p := p) ?_ (elP_pow_char a b) h
  rw [← map_pow, elP_pow_char, map_one]

theorem key1 [Finite F] (p : ℕ) [Fact p.Prime] [CharP F p] (A : GL (Fin 3) F) (σ : F ≃+* F)
    (hfix : ∀ a b : F, (conjAut 3 F A * fieldAut 3 F σ * dualAut 3 F) (proj 3 F (elP a b)) =
      proj 3 F (elP a b))
    (a b : F) :
    (A : Matrix (Fin 3) (Fin 3) F) * ((elM (-σ a) (-σ b) : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      ((elP a b : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F) := by
  have h := hfix a b
  rw [apply_ε1] at h
  refine mul_eq_of_slConj_eq A ?_
  refine eq_of_proj_eq_of_pow_eq_one (p := p) ?_ (elP_pow_char a b) h
  rw [← map_pow, elM_pow_char, map_one]

theorem det_eq_zero_of_key1 (A : GL (Fin 3) F) (σ : F ≃+* F)
    (hk : ∀ a b : F, (A : Matrix (Fin 3) (Fin 3) F) *
      ((elM (-σ a) (-σ b) : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      ((elP a b : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F)) :
    Matrix.det (A : Matrix (Fin 3) (Fin 3) F) = 0 := by
  have h10 := hk 1 0
  have h01 := hk 0 1
  have e1 := congrFun (congrFun h10 2) 0
  have e2 := congrFun (congrFun h10 1) 2
  have e3 := congrFun (congrFun h01 2) 1
  have e4 := congrFun (congrFun h01 0) 2
  simp [Matrix.mul_apply, Fin.sum_univ_three, coe_elP, coe_elM] at e1 e2 e3 e4
  rw [Matrix.det_fin_three]
  simp [e1, e2, e3, e4]

theorem shape_of_key0 (A : GL (Fin 3) F) (σ : F ≃+* F)
    (hk : ∀ a b : F, (A : Matrix (Fin 3) (Fin 3) F) *
      ((elP (σ a) (σ b) : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      ((elP a b : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F)) :
    (A : Matrix (Fin 3) (Fin 3) F) 0 1 = 0 ∧ (A : Matrix (Fin 3) (Fin 3) F) 0 2 = 0 ∧
      (A : Matrix (Fin 3) (Fin 3) F) 1 0 = 0 ∧ (A : Matrix (Fin 3) (Fin 3) F) 1 2 = 0 ∧
      (A : Matrix (Fin 3) (Fin 3) F) 1 1 = (A : Matrix (Fin 3) (Fin 3) F) 0 0 ∧
      (A : Matrix (Fin 3) (Fin 3) F) 2 2 = (A : Matrix (Fin 3) (Fin 3) F) 0 0 := by
  have h10 := hk 1 0
  have h01 := hk 0 1
  have e1 := congrFun (congrFun h10 0) 0
  have e2 := congrFun (congrFun h10 1) 0
  have e3 := congrFun (congrFun h10 2) 0
  have e4 := congrFun (congrFun h10 2) 1
  have e5 := congrFun (congrFun h01 2) 1
  have e6 := congrFun (congrFun h01 2) 0
  simp [Matrix.mul_apply, Fin.sum_univ_three, coe_elP] at e1 e2 e3 e4 e5 e6
  have h3 : (A : Matrix (Fin 3) (Fin 3) F) 2 2 = (A : Matrix (Fin 3) (Fin 3) F) 0 0 := by
    linear_combination e3
  have h5 : (A : Matrix (Fin 3) (Fin 3) F) 2 2 = (A : Matrix (Fin 3) (Fin 3) F) 1 1 := by
    linear_combination e5
  exact ⟨e4, e1, e6, e2, h5.symm.trans h3, h3⟩

theorem exists_conj_of_key0 (A : GL (Fin 3) F) (σ : F ≃+* F)
    (hk : ∀ a b : F, (A : Matrix (Fin 3) (Fin 3) F) *
      ((elP (σ a) (σ b) : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      ((elP a b : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F)) :
    ∃ r s : F, conjAut 3 F A * fieldAut 3 F σ = MulAut.conj (proj 3 F (elP r s)) := by
  obtain ⟨h01, h02, h10, h12, h11, h22⟩ := shape_of_key0 A σ hk
  have hdet : Matrix.det (A : Matrix (Fin 3) (Fin 3) F) ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp A.isUnit).ne_zero
  set κ := (A : Matrix (Fin 3) (Fin 3) F) 0 0 with hκ
  have hκ0 : κ ≠ 0 := by
    intro h
    apply hdet
    rw [Matrix.det_fin_three]
    simp [h01, h02, h10, h12, h11, h22, h]
  have hσ : σ = 1 := by
    apply RingEquiv.ext
    intro t
    have := congrFun (congrFun (hk t 0) 2) 0
    simp [Matrix.mul_apply, Fin.sum_univ_three, coe_elP] at this
    have h' : κ * σ t = κ * t := by linear_combination this - σ t * h22 - t * hκ
    exact mul_left_cancel₀ hκ0 h'
  have hA00 : (A : Matrix (Fin 3) (Fin 3) F) 0 0 ≠ 0 := hκ0
  obtain ⟨r, hr⟩ : ∃ r : F, r = (A : Matrix (Fin 3) (Fin 3) F) 2 0 / κ := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s : F, s = (A : Matrix (Fin 3) (Fin 3) F) 2 1 / κ := ⟨_, rfl⟩
  refine ⟨r, s, ?_⟩
  have hGL : A = Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.mk0 κ hκ0) *
      SpecialLinearGroup.toGL (elP r s) := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [coe_elP, Matrix.mul_apply, Fin.sum_univ_three, Matrix.GeneralLinearGroup.coe_scalar,
        h01, h02, h10, h12, h11, h22, hr, hs] <;> first | exact hκ.symm | field_simp
  rw [hσ, map_one, mul_one]
  conv_lhs => rw [hGL]
  rw [map_mul, conjAut_scalar, one_mul, conjAut_toGL]

end Core

section Main

variable {F : Type} [Field F]

theorem aut_eq_one_of_fix_radP [Finite F] (p : ℕ) [Fact p.Prime] [CharP F p]
    (α : MulAut (projectiveSL 3 F))
    (hfix : ∀ a b : F, α (proj 3 F (elP a b)) = proj 3 F (elP a b))
    (hord : Nat.Coprime (orderOf α) p) : α = 1 := by
  obtain ⟨A, σ, ε, hε, hα⟩ := (automorphism_generation (n := 3) (K := F) le_rfl).2 α
  interval_cases ε
  · rw [pow_zero, mul_one] at hα
    have hfix' : ∀ a b : F, (conjAut 3 F A * fieldAut 3 F σ) (proj 3 F (elP a b)) =
        proj 3 F (elP a b) := by
      intro a b
      rw [← hα]
      exact hfix a b
    obtain ⟨r, s, hconj⟩ := exists_conj_of_key0 A σ (key0 p A σ hfix')
    have hα' : α = MulAut.conj (proj 3 F (elP r s)) := by rw [hα, hconj]
    have hp1 : α ^ p = 1 := by
      rw [hα', ← map_pow, ← map_pow, elP_pow_char, map_one, map_one]
    have h1 : orderOf α = 1 := Nat.Coprime.eq_one_of_dvd hord (orderOf_dvd_of_pow_eq_one hp1)
    exact orderOf_eq_one_iff.mp h1
  · rw [pow_one] at hα
    exfalso
    have hfix' : ∀ a b : F, (conjAut 3 F A * fieldAut 3 F σ * dualAut 3 F) (proj 3 F (elP a b)) =
        proj 3 F (elP a b) := by
      intro a b
      rw [← hα]
      exact hfix a b
    have hdet := det_eq_zero_of_key1 A σ (key1 p A σ hfix')
    exact ((Matrix.isUnit_iff_isUnit_det _).mp A.isUnit).ne_zero hdet

theorem inv_elM (a b : F) : (elM a b : SL(3, F))⁻¹ = elM (-a) (-b) := by
  rw [inv_eq_iff_mul_eq_one, elM_mul]
  simp [elM_zero]

theorem transpose_elM (a b : F) : (elM a b : SL(3, F)).transpose = elP a b := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [coe_elP, coe_elM, SpecialLinearGroup.coe_transpose]

theorem dual_elM (a b : F) :
    dualAut 3 F (proj 3 F (elM a b)) = proj 3 F (elP (-a) (-b)) := by
  rw [dualAut_proj, inv_elM, transpose_elM]

theorem aut_eq_one_of_fix_radM [Finite F] (p : ℕ) [Fact p.Prime] [CharP F p]
    (α : MulAut (projectiveSL 3 F))
    (hfix : ∀ a b : F, α (proj 3 F (elM a b)) = proj 3 F (elM a b))
    (hord : Nat.Coprime (orderOf α) p) : α = 1 := by
  have hδ : dualAut 3 F * dualAut 3 F = 1 :=
    (standard_automorphism_transport (K := F) (n := 3)).2.2.2.1
  have hδinv : (dualAut 3 F)⁻¹ = dualAut 3 F := inv_eq_of_mul_eq_one_right hδ
  have h : dualAut 3 F * α * dualAut 3 F = 1 := by
    refine aut_eq_one_of_fix_radP p _ (fun a b => ?_) ?_
    · rw [MulAut.mul_apply, MulAut.mul_apply, dual_elP, hfix, dual_elM, neg_neg, neg_neg]
    · have hc : (dualAut 3 F * α * dualAut 3 F) ^ orderOf α = 1 := by
        have this : (dualAut 3 F * α * (dualAut 3 F)⁻¹) ^ orderOf α =
            dualAut 3 F * α ^ orderOf α * (dualAut 3 F)⁻¹ := conj_pow
        rw [hδinv] at this
        rw [this, pow_orderOf_eq_one, mul_one, hδ]
      exact Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hc) hord
  calc α = (dualAut 3 F * dualAut 3 F) * α * (dualAut 3 F * dualAut 3 F) := by rw [hδ]; group
    _ = dualAut 3 F * (dualAut 3 F * α * dualAut 3 F) * dualAut 3 F := by group
    _ = 1 := by rw [h]; exact hδ

end Main

end CFSG.GH74.GLS.Stage2.Signalizer.L46E.AutC
