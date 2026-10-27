module

public import CFSG.GH74.Generic.S1.UniClassA

public section

namespace CFSG.GH74.Generic.S1.Uni

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Assembly.LowTwoRank Matrix
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag
open scoped MatrixGroups

variable {p f : ℕ} {F : Type} [Field F]

theorem glAut_refl_apply (k : GL (Fin 4) F) : glAut (RingEquiv.refl F) k = k :=
  Units.ext rfl

theorem norm_eq_one_of_sq (h : UnitaryFieldData p f F) {A : Matrix (Fin 4) (Fin 4) F}
    (hAu : cT h A * A = 1) {c : F} (hAA : A * A = c • 1) : h.norm c = 1 := by
  have h1 : cT h (A * A) * (A * A) = 1 := by
    rw [cT_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (cT h A) A A, hAu, Matrix.one_mul, hAu]
  rw [hAA, cT_smul, cT_one, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_one] at h1
  have h2 := congrFun (congrFun h1 0) 0
  simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h2
  rw [UnitaryFieldData.norm, mul_comm]
  exact h2

theorem cT_mul_smul (h : UnitaryFieldData p f F) {A : Matrix (Fin 4) (Fin 4) F}
    (hAu : cT h A * A = 1) {l : F} (hl : l ≠ 0) :
    cT h (l⁻¹ • A) * (l⁻¹ • A) = (h.norm l)⁻¹ • (1 : Matrix (Fin 4) (Fin 4) F) := by
  rw [cT_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hAu]
  congr 1
  simp only [map_inv₀, UnitaryFieldData.norm]
  field_simp

theorem classify_diag (h : UnitaryFieldData p f F) (hp2 : p ≠ 2) (hq4 : p ^ f % 4 = 1)
    (α : MulAut ↥(StatedSU 4 (p ^ f) F))
    (hout : ∀ k : ↥(StatedSU 4 (p ^ f) F), α ≠ MulAut.conj k)
    {A : GL (Fin 4) F} (hAu : cT h (A : Matrix (Fin 4) (Fin 4) F) * (A : Matrix (Fin 4) (Fin 4) F) = 1)
    (hαA : ∀ k : ↥(StatedSU 4 (p ^ f) F),
      ((α k : ↥(StatedSU 4 (p ^ f) F)) : GL (Fin 4) F) = A * (k : GL (Fin 4) F) * A⁻¹)
    {c : F} (hc0 : c ≠ 0)
    (hAA : (A : Matrix (Fin 4) (Fin 4) F) * (A : Matrix (Fin 4) (Fin 4) F) = c • 1) :
    GoodFixedCentral False α ∨ IsReflection (StatedSU 4 (p ^ f) F) α := by
  classical
  have hfin : Finite F := h.finite
  have : Fact p.Prime := ⟨h.prime⟩
  have hF : Nat.card F = (p ^ f) ^ 2 := h.card_eq_sq
  set Ar : Matrix (Fin 4) (Fin 4) F := (A : Matrix (Fin 4) (Fin 4) F) with hAr
  have hcN : h.norm c = 1 := norm_eq_one_of_sq h hAu hAA
  obtain ⟨l, hl0, hlc⟩ := exists_sq_eq_of_norm_eq_one h hp2 hcN
  have hlN : h.norm l = 1 ∨ h.norm l = -1 := by
    have h1 : h.norm l * h.norm l = 1 := by
      rw [← norm_mul_eq', ← pow_two, hlc, hcN]
    exact mul_self_eq_one_iff.mp h1
  set Bm : Matrix (Fin 4) (Fin 4) F := l⁻¹ • Ar with hBm
  have hBB : Bm * Bm = 1 := by
    rw [hBm, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hAA, smul_smul]
    have : l⁻¹ * l⁻¹ * c = 1 := by
      rw [← hlc]
      field_simp
    rw [this, one_smul]
  have hBu := cT_mul_smul h hAu hl0
  have hAinv : ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = c⁻¹ • Ar := by
    have h1 : (c⁻¹ • Ar) * Ar = 1 := by
      rw [Matrix.smul_mul, hAA, smul_smul, inv_mul_cancel₀ hc0, one_smul]
    exact Units.inv_eq_of_mul_eq_one_left h1
  have hαB : ∀ k : ↥(StatedSU 4 (p ^ f) F),
      (((α k : ↥(StatedSU 4 (p ^ f) F)) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
        Bm * ((k : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * Bm := by
    intro k
    rw [hαA k, Units.val_mul, Units.val_mul, hAinv, hBm, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← hAr]
    congr 1
    rw [← hlc]
    field_simp
  rcases hlN with hl1 | hl1
  ·
    right
    have hBu1 : cT h Bm * Bm = 1 := by rw [hBu, hl1, inv_one, one_smul]
    set Bg : GL (Fin 4) F := ⟨Bm, Bm, hBB, hBB⟩ with hBg
    have hBgi : Bg⁻¹ = Bg := inv_eq_of_mul_eq_one_right (Units.ext hBB)
    have hdet : Bm.det = 1 ∨ Bm.det = -1 := by
      have h1 : Bm.det * Bm.det = 1 := by rw [← Matrix.det_mul, hBB, Matrix.det_one]
      exact mul_self_eq_one_iff.mp h1
    have hαg : ∀ k : ↥(StatedSU 4 (p ^ f) F),
        ((α k : ↥(StatedSU 4 (p ^ f) F)) : GL (Fin 4) F) = Bg * (k : GL (Fin 4) F) * Bg⁻¹ := by
      intro k
      rw [hBgi]
      exact Units.ext (hαB k)
    rcases hdet with hd | hd
    · exfalso
      have hmem : Bg ∈ StatedSU 4 (p ^ f) F := by
        rw [show StatedSU 4 (p ^ f) F = unitarySU p f F 4 from rfl, mem_unitarySU_iff h]
        exact ⟨hd, hBu1⟩
      apply hout ⟨Bg, hmem⟩
      refine MulEquiv.ext fun k => ?_
      apply Subtype.ext
      rw [hαg k]
      change _ = (⟨Bg, hmem⟩ * k * ⟨Bg, hmem⟩⁻¹ : ↥(StatedSU 4 (p ^ f) F)).1
      simp [hBgi]
    · exact ⟨Bg, Units.ext hBB, hd, fun k => hαg k⟩
  ·
    left
    have hBu1 : cT h Bm * Bm = -1 := by
      rw [hBu, hl1, inv_neg, inv_one, neg_one_smul]
    exact goodFixedCentral_of_paired h hp2 hq4 α hBB hBu1 hαB

end CFSG.GH74.Generic.S1.Uni
