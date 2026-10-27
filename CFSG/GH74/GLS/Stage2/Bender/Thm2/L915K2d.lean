module

public import CFSG.LinearAlgebra.LinearGroups.Generation
public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.L915

open Subgroup
open scoped commutatorElement

@[expose] def D2 (F : Type) [Field F] : Subgroup (GL (Fin 2) F) :=
  (Subgroup.zpowers (-1 : Fˣ)).comap (Matrix.GeneralLinearGroup.det : GL (Fin 2) F →* Fˣ)

theorem negOne_mem_D2 (F : Type) [Field F] : (-1 : GL (Fin 2) F) ∈ D2 F := by
  rw [D2, Subgroup.mem_comap]
  have h : Matrix.GeneralLinearGroup.det (-1 : GL (Fin 2) F) = 1 := by
    ext
    simp [Matrix.det_neg]
  rw [h]
  exact one_mem _

namespace D2

variable {F : Type} [Field F]

@[expose] def sigmaGL (F : Type) [Field F] : GL (Fin 2) F :=
  ⟨!![1, 0; 0, -1], !![1, 0; 0, -1], by simp [Matrix.one_fin_two], by simp [Matrix.one_fin_two]⟩

theorem det_sigmaGL : Matrix.GeneralLinearGroup.det (sigmaGL F) = -1 := by
  ext
  simp [sigmaGL, Matrix.det_fin_two_of]

theorem sigmaGL_mem : sigmaGL F ∈ D2 F := by
  rw [D2, Subgroup.mem_comap, det_sigmaGL]
  exact Subgroup.mem_zpowers _

@[expose] def sigma (F : Type) [Field F] : ↥(D2 F) :=
  ⟨sigmaGL F, sigmaGL_mem⟩

theorem sigma_mul_self : sigma F * sigma F = 1 := by
  apply Subtype.ext
  apply Units.ext
  simp [sigma, sigmaGL, Matrix.one_fin_two]

theorem toGL_mem (A : Matrix.SpecialLinearGroup (Fin 2) F) :
    Matrix.SpecialLinearGroup.toGL A ∈ D2 F := by
  rw [D2, Subgroup.mem_comap, Matrix.SpecialLinearGroup.coeToGL_det]
  exact one_mem _

@[expose] def ofSL : Matrix.SpecialLinearGroup (Fin 2) F →* ↥(D2 F) :=
  Matrix.SpecialLinearGroup.toGL.codRestrict (D2 F) toGL_mem

theorem exists_ofSL (g : ↥(D2 F)) (hg : Matrix.GeneralLinearGroup.det (g : GL (Fin 2) F) = 1) :
    ∃ A : Matrix.SpecialLinearGroup (Fin 2) F, ofSL A = g := by
  refine ⟨⟨((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F), ?_⟩, ?_⟩
  · simpa using congrArg Units.val hg
  · apply Subtype.ext
    apply Units.ext
    rfl

theorem one_add_single_zero_one (b : F) :
    (1 + Matrix.single (0 : Fin 2) (1 : Fin 2) b : Matrix (Fin 2) (Fin 2) F) = !![1, b; 0, 1] := by
  ext a c
  fin_cases a <;> fin_cases c <;> simp

theorem one_add_single_one_zero (b : F) :
    (1 + Matrix.single (1 : Fin 2) (0 : Fin 2) b : Matrix (Fin 2) (Fin 2) F) = !![1, 0; b, 1] := by
  ext a c
  fin_cases a <;> fin_cases c <;> simp

theorem sigma_conj_aux {i j : Fin 2} (hij : i ≠ j) (b : F) :
    (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) F) * (1 + Matrix.single i j b) * !![1, 0; 0, -1] *
      (1 + Matrix.single i j (-b)) = 1 + Matrix.single i j (-2 * b) := by
  have h : (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) := by
    fin_cases i <;> fin_cases j <;> simp_all
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp only [one_add_single_zero_one, Matrix.mul_fin_two]
    simp
    ring
  · simp only [one_add_single_one_zero, Matrix.mul_fin_two]
    simp
    ring

theorem comm_sigma_transvection {i j : Fin 2} (hij : i ≠ j) (b : F) :
    ⁅sigma F, ofSL (Matrix.SpecialLinearGroup.transvection hij b)⁆ =
      ofSL (Matrix.SpecialLinearGroup.transvection hij (-2 * b)) := by
  have hinv : (sigma F)⁻¹ = sigma F := inv_eq_of_mul_eq_one_right sigma_mul_self
  rw [commutatorElement_def, hinv, ← map_inv, Matrix.SpecialLinearGroup.transvection_inv]
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul]
  exact sigma_conj_aux hij b

theorem ofSL_transvection_mem (h2 : (2 : F) ≠ 0) {i j : Fin 2} (hij : i ≠ j) (c : F) :
    ofSL (Matrix.SpecialLinearGroup.transvection hij c) ∈
      ⁅(⊤ : Subgroup ↥(D2 F)), (⊤ : Subgroup ↥(D2 F))⁆ := by
  have h := comm_sigma_transvection (F := F) hij (-c / 2)
  have hc : -2 * (-c / 2) = c := by field_simp
  rw [hc] at h
  rw [← h]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

theorem ofSL_mem_commutator (h2 : (2 : F) ≠ 0) (A : Matrix.SpecialLinearGroup (Fin 2) F) :
    ofSL A ∈ ⁅(⊤ : Subgroup ↥(D2 F)), (⊤ : Subgroup ↥(D2 F))⁆ := by
  have hA : A ∈ Subgroup.closure (CFSG.LinearGroups.elementarySet 2 F) := by
    rw [CFSG.LinearGroups.special_linear_elementary_generation]
    exact Subgroup.mem_top _
  have hle : Subgroup.closure (CFSG.LinearGroups.elementarySet 2 F) ≤
      (⁅(⊤ : Subgroup ↥(D2 F)), (⊤ : Subgroup ↥(D2 F))⁆).comap ofSL := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, j, hij, c, rfl⟩
    exact ofSL_transvection_mem h2 hij c
  exact hle hA

theorem two_ne_zero_of_odd_natCard [Finite F] (hodd : Odd (Nat.card F)) : (2 : F) ≠ 0 := by
  intro h2
  have : CharP F 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
  have := Fintype.ofFinite F
  have h := FiniteField.even_card_of_char_two (ringChar.eq F 2)
  rw [Nat.card_eq_fintype_card] at hodd
  obtain ⟨m, hm⟩ := hodd
  omega

theorem exists_sq_add_sq_eq_neg_one [Finite F] : ∃ a b : F, a ^ 2 + b ^ 2 = -1 := by
  have : NeZero (ringChar F) := ⟨CharP.char_ne_zero_of_finite F (ringChar F)⟩
  obtain ⟨a, b, hab⟩ := CharP.sq_add_sq F (ringChar F) (-1)
  exact ⟨a, b, by exact_mod_cast hab⟩

end D2

theorem exists_sigma_D2 (F : Type) [Field F] (h2 : (2 : F) ≠ 0) :
    ∃ σ : ↥(D2 F), σ * σ = 1 ∧
      (⊤ : Subgroup ↥(D2 F)) = ⁅(⊤ : Subgroup ↥(D2 F)), (⊤ : Subgroup ↥(D2 F))⁆ ⊔ zpowers σ := by
  refine ⟨D2.sigma F, D2.sigma_mul_self, (top_unique fun g _ => ?_).symm⟩
  have hg : Matrix.GeneralLinearGroup.det (g : GL (Fin 2) F) ∈ zpowers (-1 : Fˣ) := g.2
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hg
  rcases Int.even_or_odd k with he | ho
  · rw [he.neg_one_zpow] at hk
    obtain ⟨A, hA⟩ := D2.exists_ofSL g hk.symm
    exact Subgroup.mem_sup_left (hA ▸ D2.ofSL_mem_commutator h2 A)
  · rw [ho.neg_one_zpow] at hk
    have hdet : Matrix.GeneralLinearGroup.det
        ((D2.sigma F * g : ↥(D2 F)) : GL (Fin 2) F) = 1 := by
      rw [Subgroup.coe_mul, map_mul]
      change Matrix.GeneralLinearGroup.det (D2.sigmaGL F) * _ = 1
      rw [D2.det_sigmaGL, ← hk]
      simp
    obtain ⟨A, hA⟩ := D2.exists_ofSL _ hdet
    have hmem : D2.sigma F * g ∈ ⁅(⊤ : Subgroup ↥(D2 F)), (⊤ : Subgroup ↥(D2 F))⁆ :=
      hA ▸ D2.ofSL_mem_commutator h2 A
    have hg' : g = (D2.sigma F)⁻¹ * (D2.sigma F * g) := by group
    rw [hg']
    exact mul_mem (Subgroup.mem_sup_right (inv_mem (mem_zpowers _))) (Subgroup.mem_sup_left hmem)

theorem negOne_mem_derived_D2 (F : Type) [Field F] [Finite F] (hodd : Odd (Nat.card F)) :
    (⟨-1, negOne_mem_D2 F⟩ : ↥(D2 F)) ∈
      ⁅⁅(⊤ : Subgroup ↥(D2 F)), (⊤ : Subgroup ↥(D2 F))⁆,
        ⁅(⊤ : Subgroup ↥(D2 F)), (⊤ : Subgroup ↥(D2 F))⁆⁆ := by
  have h2 : (2 : F) ≠ 0 := D2.two_ne_zero_of_odd_natCard hodd
  obtain ⟨a, b, hab⟩ := D2.exists_sq_add_sq_eq_neg_one (F := F)
  let xS : Matrix.SpecialLinearGroup (Fin 2) F :=
    ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two_of]⟩
  let yS : Matrix.SpecialLinearGroup (Fin 2) F :=
    ⟨!![a, b; b, -a], by simp [Matrix.det_fin_two_of]; linear_combination -hab⟩
  have hxy : D2.ofSL xS * D2.ofSL yS = ⟨-1, negOne_mem_D2 F⟩ * (D2.ofSL yS * D2.ofSL xS) := by
    apply Subtype.ext
    apply Units.ext
    simp only [Subgroup.coe_mul, Units.val_mul]
    change (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) F) * !![a, b; b, -a] =
      (-1) * (!![a, b; b, -a] * !![0, 1; -1, 0])
    simp
  have hcomm : ⁅D2.ofSL xS, D2.ofSL yS⁆ = ⟨-1, negOne_mem_D2 F⟩ := by
    rw [commutatorElement_def, hxy]
    group
  rw [← hcomm]
  exact Subgroup.commutator_mem_commutator (D2.ofSL_mem_commutator h2 xS)
    (D2.ofSL_mem_commutator h2 yS)

end CFSG.GH74.GLS.Stage2.Bender.Thm2.L915
