module

public import CFSG.GH74.Generic.S1.LinKron

public section

namespace CFSG.GH74.Generic.S1

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Assembly.LowTwoRank Matrix
open scoped MatrixGroups

variable {F : Type} [Field F]

section Basis

variable (A : Matrix (Fin 4) (Fin 4) F) {c : F} (hA : A * A = c • (1 : Matrix (Fin 4) (Fin 4) F))
  (hc : ∀ μ : F, μ * μ ≠ c)
include hA

theorem mulVec_mulVec_eq (w : Fin 4 → F) : A *ᵥ (A *ᵥ w) = c • w := by
  rw [Matrix.mulVec_mulVec, hA, Matrix.smul_mulVec, Matrix.one_mulVec]

include hc

theorem eq_zero_of_comb {w : Fin 4 → F} (hw : w ≠ 0) {a b : F} (h : a • w + b • (A *ᵥ w) = 0) :
    a = 0 ∧ b = 0 := by
  have hb : b = 0 := by
    by_contra hb
    have h1 : A *ᵥ w = -(a / b) • w := by
      have h2 : b • (A *ᵥ w) = -(a • w) := eq_neg_of_add_eq_zero_right h
      calc A *ᵥ w = b⁻¹ • (b • (A *ᵥ w)) := by rw [smul_smul, inv_mul_cancel₀ hb, one_smul]
        _ = -(a / b) • w := by rw [h2, smul_neg, smul_smul, neg_smul, div_eq_inv_mul]
    have h3 : A *ᵥ (A *ᵥ w) = (a / b) ^ 2 • w := by
      rw [h1, Matrix.mulVec_smul, h1, smul_smul, neg_mul_neg, sq]
    rw [mulVec_mulVec_eq A hA] at h3
    have h4 : (c - (a / b) ^ 2) • w = 0 := by rw [sub_smul, h3, sub_self]
    rcases smul_eq_zero.1 h4 with h5 | h5
    · exact hc (a / b) (by rw [← sq]; exact (sub_eq_zero.1 h5).symm)
    · exact hw h5
  subst hb
  rw [zero_smul, add_zero] at h
  exact ⟨(smul_eq_zero.1 h).resolve_right hw, rfl⟩

end Basis

section Basis2

variable (A : Matrix (Fin 4) (Fin 4) F) {c : F} (hA : A * A = c • (1 : Matrix (Fin 4) (Fin 4) F))
  (hc : ∀ μ : F, μ * μ ≠ c)
include hA hc

theorem eq_zero_of_comb4 {u₁ u₂ : Fin 4 → F} (hu₁ : u₁ ≠ 0)
    (hu₂ : ¬ ∃ x y : F, x • u₁ + y • (A *ᵥ u₁) = u₂) {x₀ x₁ x₂ x₃ : F}
    (h : x₀ • u₁ + x₁ • (A *ᵥ u₁) + x₂ • u₂ + x₃ • (A *ᵥ u₂) = 0) :
    x₀ = 0 ∧ x₁ = 0 ∧ x₂ = 0 ∧ x₃ = 0 := by
  by_cases h23 : x₂ = 0 ∧ x₃ = 0
  · obtain ⟨rfl, rfl⟩ := h23
    simp only [zero_smul, add_zero] at h
    obtain ⟨h0, h1⟩ := eq_zero_of_comb A hA hc hu₁ h
    exact ⟨h0, h1, rfl, rfl⟩
  · exfalso
    have hN : x₂ ^ 2 - c * x₃ ^ 2 ≠ 0 := by
      intro hN
      apply h23
      by_cases hx3 : x₃ = 0
      · subst hx3
        have : x₂ ^ 2 = 0 := by simpa using hN
        exact ⟨pow_eq_zero_iff (by norm_num) |>.1 this, rfl⟩
      · exfalso
        exact hc (x₂ / x₃) (by field_simp; linear_combination hN)
    obtain ⟨w, hw⟩ : ∃ w : Fin 4 → F, w = x₀ • u₁ + x₁ • (A *ᵥ u₁) := ⟨_, rfl⟩
    obtain ⟨z, hz⟩ : ∃ z : Fin 4 → F, z = x₂ • u₂ + x₃ • (A *ᵥ u₂) := ⟨_, rfl⟩
    have hwz : w + z = 0 := by
      rw [hw, hz, ← add_assoc]
      exact h
    have hz' : z = -w := eq_neg_of_add_eq_zero_right hwz
    have key : (x₂ ^ 2 - c * x₃ ^ 2) • u₂ = x₂ • z - x₃ • (A *ᵥ z) := by
      rw [hz, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, mulVec_mulVec_eq A hA]
      module
    have key2 : x₂ • z - x₃ • (A *ᵥ z) =
        (-(x₂ * x₀ - x₃ * x₁ * c)) • u₁ + (-(x₂ * x₁ - x₃ * x₀)) • (A *ᵥ u₁) := by
      rw [hz', Matrix.mulVec_neg, hw, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
        mulVec_mulVec_eq A hA]
      module
    have hu : u₂ = (x₂ ^ 2 - c * x₃ ^ 2)⁻¹ • ((x₂ ^ 2 - c * x₃ ^ 2) • u₂) := by
      rw [smul_smul, inv_mul_cancel₀ hN, one_smul]
    rw [key, key2, smul_add, smul_smul, smul_smul] at hu
    exact hu₂ ⟨_, _, hu.symm⟩

end Basis2

theorem exists_not_mem_span_pair (u v : Fin 4 → F) : ∃ w : Fin 4 → F, ¬ ∃ x y : F, x • u + y • v = w := by
  classical
  by_contra hcon
  push Not at hcon
  have htop : Submodule.span F ({u, v} : Set (Fin 4 → F)) = ⊤ := by
    refine eq_top_iff.2 fun w _ => ?_
    obtain ⟨x, y, hxy⟩ := hcon w
    exact Submodule.mem_span_pair.2 ⟨x, y, hxy⟩
  have h1 := finrank_span_finset_le_card (R := F) ({u, v} : Finset (Fin 4 → F))
  rw [Finset.coe_insert, Finset.coe_singleton, Set.finrank, htop, finrank_top, Module.finrank_fin_fun] at h1
  have h2 : ({u, v} : Finset (Fin 4 → F)).card ≤ 2 := Finset.card_le_two
  omega


theorem exists_conj_compK (A : Matrix (Fin 4) (Fin 4) F) {c : F}
    (hA : A * A = c • (1 : Matrix (Fin 4) (Fin 4) F)) (hc : ∀ μ : F, μ * μ ≠ c) :
    ∃ P : GL (Fin 4) F, A * (P : Matrix (Fin 4) (Fin 4) F) =
      (P : Matrix (Fin 4) (Fin 4) F) * compK c := by
  classical
  set u₁ : Fin 4 → F := Pi.single 0 1 with hu₁def
  have hu₁ : u₁ ≠ 0 := fun h => by simpa [hu₁def] using congrFun h 0
  obtain ⟨u₂, hu₂⟩ := exists_not_mem_span_pair u₁ (A *ᵥ u₁)
  let Pm : Matrix (Fin 4) (Fin 4) F :=
    Matrix.of fun r j => ![u₁, A *ᵥ u₁, u₂, A *ᵥ u₂] j r
  have hPmul : ∀ x : Fin 4 → F,
      Pm *ᵥ x = x 0 • u₁ + x 1 • (A *ᵥ u₁) + x 2 • u₂ + x 3 • (A *ᵥ u₂) := by
    intro x
    ext r
    simp [Pm, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
    ring
  have hdet : Pm.det ≠ 0 := by
    intro h0
    obtain ⟨x, hx, hx0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    rw [hPmul] at hx0
    obtain ⟨h0, h1, h2, h3⟩ := eq_zero_of_comb4 A hA hc hu₁ hu₂ hx0
    apply hx
    ext i
    fin_cases i <;> simp [h0, h1, h2, h3]
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero Pm hdet, ?_⟩
  change A * Pm = Pm * compK c
  have hcol : ∀ (j r : Fin 4), (A * Pm) r j = (A *ᵥ (![u₁, A *ᵥ u₁, u₂, A *ᵥ u₂] j)) r :=
    fun j r => rfl
  ext r j
  rw [hcol]
  fin_cases j
  · simp [Pm, compK, Matrix.mul_apply, Fin.sum_univ_four]
  · simp [Pm, compK, Matrix.mul_apply, Fin.sum_univ_four, mulVec_mulVec_eq A hA]
    ring
  · simp [Pm, compK, Matrix.mul_apply, Fin.sum_univ_four]
  · simp [Pm, compK, Matrix.mul_apply, Fin.sum_univ_four, mulVec_mulVec_eq A hA]
    ring


theorem classify_inner [Finite F] (hF : Nat.card F % 4 = 3) (α : MulAut ↥(StatedSL 4 F))
    (A : GL (Fin 4) F) (c : Fˣ) (hA : A * A = GeneralLinearGroup.scalar (Fin 4) c)
    (hα : ∀ k : ↥(StatedSL 4 F),
      ((α k : ↥(StatedSL 4 F)) : GL (Fin 4) F) = A * (k : GL (Fin 4) F) * A⁻¹)
    (hout : ∀ k : ↥(StatedSL 4 F), α ≠ MulAut.conj k) :
    GoodFixedCentral (Nat.card F = 3) α ∨ IsReflection (StatedSL 4 F) α := by
  classical
  by_cases hsq : ∃ d : F, d * d = (c : F)
  ·
    right
    obtain ⟨d, hd⟩ := hsq
    have hd0 : d ≠ 0 := by
      rintro rfl
      exact c.ne_zero (by simpa using hd.symm)
    set s : Fˣ := (Units.mk0 d hd0)⁻¹ with hsdef
    set ρ : GL (Fin 4) F := GeneralLinearGroup.scalar (Fin 4) s * A with hρ
    have hs : s * s * c = 1 := by
      apply Units.ext
      simp only [hsdef, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, Units.val_one]
      rw [← hd]
      field_simp
    have hρρ : ρ * ρ = 1 := by
      calc ρ * ρ = GeneralLinearGroup.scalar (Fin 4) s * GeneralLinearGroup.scalar (Fin 4) s *
            (A * A) := by
            rw [hρ, mul_assoc, ← mul_assoc A, ← GeneralLinearGroup.scalar_commute]
            group
        _ = 1 := by rw [hA, ← map_mul, ← map_mul, hs, map_one]
    have hconjρ : ∀ g : GL (Fin 4) F, ρ * g * ρ⁻¹ = A * g * A⁻¹ := by
      intro g
      rw [hρ, _root_.mul_inv_rev]
      calc GeneralLinearGroup.scalar (Fin 4) s * A * g * (A⁻¹ * (GeneralLinearGroup.scalar (Fin 4) s)⁻¹)
          = GeneralLinearGroup.scalar (Fin 4) s * (A * g * A⁻¹) *
              (GeneralLinearGroup.scalar (Fin 4) s)⁻¹ := by simp only [mul_assoc]
        _ = A * g * A⁻¹ * GeneralLinearGroup.scalar (Fin 4) s *
              (GeneralLinearGroup.scalar (Fin 4) s)⁻¹ := by rw [GeneralLinearGroup.scalar_commute]
        _ = A * g * A⁻¹ := by rw [mul_assoc _ (GeneralLinearGroup.scalar (Fin 4) s), mul_inv_cancel,
              mul_one]
    have hdet2 : (ρ : Matrix (Fin 4) (Fin 4) F).det * (ρ : Matrix (Fin 4) (Fin 4) F).det = 1 := by
      have := congrArg (fun g : GL (Fin 4) F => (g : Matrix (Fin 4) (Fin 4) F).det) hρρ
      simpa [Matrix.det_mul] using this
    rcases mul_self_eq_one_iff.1 hdet2 with h1 | h1
    · exfalso
      have hρK : ρ ∈ StatedSL 4 F := by
        rw [statedSL_eq_detOne, mem_detOne]
        exact h1
      apply hout ⟨ρ, hρK⟩
      refine MulEquiv.ext fun k => Subtype.ext ?_
      rw [hα, MulAut.conj_apply]
      exact (hconjρ k).symm
    · exact ⟨ρ, hρρ, h1, fun k => by rw [hα, hconjρ]⟩
  ·
    left
    have hc : ∀ μ : F, μ * μ ≠ (c : F) := fun μ h => hsq ⟨μ, h⟩
    have hAA : (A : Matrix (Fin 4) (Fin 4) F) * A = (c : F) • (1 : Matrix (Fin 4) (Fin 4) F) := by
      have := congrArg Units.val hA
      rw [Units.val_mul] at this
      rw [this, smul_one_eq_diagonal]
      rfl
    obtain ⟨P, hP⟩ := exists_conj_compK (A : Matrix (Fin 4) (Fin 4) F) hAA hc
    refine goodFixedCentral_of_phiP hF α P fun X => ?_
    set Pm : Matrix (Fin 4) (Fin 4) F := (P : Matrix (Fin 4) (Fin 4) F) with hPm
    set Pim : Matrix (Fin 4) (Fin 4) F := ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) with hPim
    have hPPi : Pm * Pim = 1 := by rw [hPm, hPim, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hPiP : Pim * Pm = 1 := by rw [hPm, hPim, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hPiA : Pim * (A : Matrix (Fin 4) (Fin 4) F) = compK (c : F) * Pim := by
      calc Pim * (A : Matrix (Fin 4) (Fin 4) F) =
            Pim * ((A : Matrix (Fin 4) (Fin 4) F) * Pm) * Pim := by
            rw [Matrix.mul_assoc Pim, Matrix.mul_assoc, hPPi, Matrix.mul_one]
        _ = compK (c : F) * Pim := by
            rw [hP, ← Matrix.mul_assoc Pim, hPiP, Matrix.one_mul]
    have hcomm : A * (P * kronGL X * P⁻¹) = (P * kronGL X * P⁻¹) * A := by
      apply Units.ext
      simp only [Units.val_mul]
      change (A : Matrix (Fin 4) (Fin 4) F) * (Pm * kron1 (X : Matrix (Fin 2) (Fin 2) F) * Pim) =
        Pm * kron1 (X : Matrix (Fin 2) (Fin 2) F) * Pim * (A : Matrix (Fin 4) (Fin 4) F)
      calc (A : Matrix (Fin 4) (Fin 4) F) * (Pm * kron1 (X : Matrix (Fin 2) (Fin 2) F) * Pim)
          = ((A : Matrix (Fin 4) (Fin 4) F) * Pm) * kron1 (X : Matrix (Fin 2) (Fin 2) F) * Pim := by
            simp only [Matrix.mul_assoc]
        _ = Pm * (compK (c : F) * kron1 (X : Matrix (Fin 2) (Fin 2) F)) * Pim := by
            rw [hP]
            simp only [Matrix.mul_assoc]
        _ = Pm * (kron1 (X : Matrix (Fin 2) (Fin 2) F) * compK (c : F)) * Pim := by
            rw [kron1_compK]
        _ = Pm * kron1 (X : Matrix (Fin 2) (Fin 2) F) * (compK (c : F) * Pim) := by
            simp only [Matrix.mul_assoc]
        _ = Pm * kron1 (X : Matrix (Fin 2) (Fin 2) F) * (Pim * (A : Matrix (Fin 4) (Fin 4) F)) := by
            rw [hPiA]
        _ = Pm * kron1 (X : Matrix (Fin 2) (Fin 2) F) * Pim * (A : Matrix (Fin 4) (Fin 4) F) := by
            simp only [Matrix.mul_assoc]
    rw [hα (phiP P X), coe_phiP]
    exact mul_inv_eq_iff_eq_mul.2 hcomm

end CFSG.GH74.Generic.S1
