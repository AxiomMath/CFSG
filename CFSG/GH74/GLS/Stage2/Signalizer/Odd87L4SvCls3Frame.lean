module

public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorGraph
import CFSG.RankThree.PartOne.LIT.CongruenceFive
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorBasic
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup Matrix CFSG CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ComponentClassification.OddSelector
open scoped MatrixGroups commutatorElement

section Frame

theorem l4_exists_diagonal_congr {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K) (hM : Mᵀ = M) :
    ∃ (g : GL (Fin n) K) (d : Fin n → K),
      (g : Matrix (Fin n) (Fin n) K)ᵀ * M * (g : Matrix (Fin n) (Fin n) K) = Matrix.diagonal d :=
  CFSG.RankThree.PartOne.LIT.exists_diagonal_congr h2 M hM

end Frame


section FrameMain

variable {F : Type} [Field F] [Finite F]

theorem l4_two_ne_zero_of_odd (hodd : Odd (Nat.card F)) : (2 : F) ≠ 0 := by
  intro h2
  have := Fintype.ofFinite F
  obtain ⟨n, hch, hcard⟩ := FiniteField.card F (ringChar F)
  have hdvd : ringChar F ∣ 2 := ringChar.dvd (by exact_mod_cast h2)
  have h2eq : ringChar F = 2 := (Nat.prime_dvd_prime_iff_eq hch Nat.prime_two).mp hdvd
  have h2dvd : 2 ∣ Nat.card F := by
    rw [← Nat.card_eq_fintype_card] at hcard
    rw [hcard, h2eq]
    exact dvd_pow_self 2 n.pos.ne'
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2dvd)

omit [Finite F] in
theorem l4_frame_of_congr {A : GL (Fin 4) F} (g : GL (Fin 4) F) (d : Fin 4 → F)
    (hg : (g : Matrix (Fin 4) (Fin 4) F)ᵀ * ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
      (g : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal d) :
    (∀ i, d i ≠ 0) ∧ ∃ P D : GL (Fin 4) F,
      conjAut 4 F P * (conjAut 4 F A * dualAut 4 F) * (conjAut 4 F P)⁻¹ =
        conjAut 4 F D * dualAut 4 F ∧
      ((D⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal d := by
  refine ⟨?_, g⁻¹, g⁻¹ * A * GeneralLinearGroup.inverseTranspose (g⁻¹)⁻¹, ?_, ?_⟩
  · have hg0 : (g : Matrix (Fin 4) (Fin 4) F).det ≠ 0 :=
      ((Matrix.isUnit_iff_isUnit_det _).mp g.isUnit).ne_zero
    have hR0 : ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).det ≠ 0 :=
      ((Matrix.isUnit_iff_isUnit_det _).mp (A⁻¹).isUnit).ne_zero
    have hdet : (Matrix.diagonal d).det ≠ 0 := by
      rw [← hg, det_mul, det_mul, det_transpose]
      exact mul_ne_zero (mul_ne_zero hg0 hR0) hg0
    rw [det_diagonal] at hdet
    exact fun i => Finset.prod_ne_zero_iff.mp hdet i (Finset.mem_univ i)
  · have h1 : (conjAut 4 F (g⁻¹))⁻¹ = conjAut 4 F ((g⁻¹)⁻¹) := (map_inv _ _).symm
    rw [h1]
    calc conjAut 4 F g⁻¹ * (conjAut 4 F A * dualAut 4 F) * conjAut 4 F (g⁻¹)⁻¹
        = conjAut 4 F g⁻¹ * conjAut 4 F A * (dualAut 4 F * conjAut 4 F (g⁻¹)⁻¹) := by
          simp only [mul_assoc]
      _ = conjAut 4 F g⁻¹ * conjAut 4 F A *
          (conjAut 4 F (GeneralLinearGroup.inverseTranspose (g⁻¹)⁻¹) * dualAut 4 F) := by
          rw [dualAut_mul_conjAut]
      _ = conjAut 4 F (g⁻¹ * A * GeneralLinearGroup.inverseTranspose (g⁻¹)⁻¹) * dualAut 4 F := by
          simp only [map_mul, mul_assoc]
  · rw [_root_.mul_inv_rev, _root_.mul_inv_rev, Units.val_mul, Units.val_mul,
      coe_inverseTranspose_inv, inv_inv]
    rw [← hg, Matrix.mul_assoc]


omit [Finite F] in
theorem l4_inv_symm {A : GL (Fin 4) F} (hA : (A : Matrix (Fin 4) (Fin 4) F)ᵀ = A) :
    (((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F))ᵀ =
      ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
  rw [Matrix.coe_units_inv, Matrix.transpose_nonsing_inv, hA]

theorem l4_cls3_frame (hodd : Odd (Nat.card F)) {A : GL (Fin 4) F}
    (hA : (A : Matrix (Fin 4) (Fin 4) F)ᵀ = A) :
    ∃ (P D : GL (Fin 4) F) (d : Fin 4 → F), (∀ i, d i ≠ 0) ∧
      conjAut 4 F P * (conjAut 4 F A * dualAut 4 F) * (conjAut 4 F P)⁻¹ =
        conjAut 4 F D * dualAut 4 F ∧
      ((D⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal d := by
  obtain ⟨g, d, hg⟩ := l4_exists_diagonal_congr (l4_two_ne_zero_of_odd hodd) _ (l4_inv_symm hA)
  obtain ⟨hd, P, D, h1, h2⟩ := l4_frame_of_congr g d hg
  exact ⟨P, D, d, hd, h1, h2⟩

omit [Finite F] in
theorem l4_submatrix_congr_perm (g R : Matrix (Fin 4) (Fin 4) F) (σ : Equiv.Perm (Fin 4)) :
    (g.submatrix id σ)ᵀ * R * g.submatrix id σ = (gᵀ * R * g).submatrix σ σ := by
  rw [Matrix.transpose_submatrix]
  have h1 := Matrix.submatrix_mul_equiv gᵀ R σ (Equiv.refl (Fin 4)) id
  have h2 := Matrix.submatrix_mul_equiv (gᵀ * R) g σ (Equiv.refl (Fin 4)) σ
  simp only [Equiv.coe_refl, Matrix.submatrix_id_id] at h1 h2
  rw [h1, h2]

theorem l4_cls3_frame_three (hF : Nat.card F = 3) {A : GL (Fin 4) F}
    (hA : (A : Matrix (Fin 4) (Fin 4) F)ᵀ = A) :
    ∃ (P D : GL (Fin 4) F) (d : Fin 4 → F), (∀ i, d i ≠ 0) ∧ d 0 = d 1 ∧
      conjAut 4 F P * (conjAut 4 F A * dualAut 4 F) * (conjAut 4 F P)⁻¹ =
        conjAut 4 F D * dualAut 4 F ∧
      ((D⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal d := by
  classical
  have hodd : Odd (Nat.card F) := by rw [hF]; decide
  obtain ⟨g, d, hg⟩ := l4_exists_diagonal_congr (l4_two_ne_zero_of_odd hodd) _ (l4_inv_symm hA)
  obtain ⟨hd, -⟩ := l4_frame_of_congr g d hg
  have hpm : ∀ i, d i = 1 ∨ d i = -1 := by
    intro i
    have := Fintype.ofFinite F
    have hq : Fintype.card F = 3 := by rw [← Nat.card_eq_fintype_card, hF]
    have h1 := FiniteField.pow_card_sub_one_eq_one (d i) (hd i)
    rw [hq] at h1
    exact mul_self_eq_one_iff.mp (by simpa [sq] using h1)
  obtain ⟨i, j, hij, hdij⟩ : ∃ i j : Fin 4, i ≠ j ∧ d i = d j := by
    obtain ⟨i, j, hij, h⟩ := Fintype.exists_ne_map_eq_of_card_lt (fun i : Fin 4 => decide (d i = 1))
      (by simp)
    refine ⟨i, j, hij, ?_⟩
    simp only [decide_eq_decide] at h
    rcases hpm i with hi | hi
    · rw [hi]; exact ((h.mp hi).symm)
    · rcases hpm j with hj | hj
      · exfalso
        have := h.mpr hj
        rw [hi] at this
        have h2 : (2 : F) ≠ 0 := l4_two_ne_zero_of_odd hodd
        apply h2
        linear_combination -this
      · rw [hi, hj]
  have hperm : ∀ i j : Fin 4, i ≠ j → ∃ σ : Equiv.Perm (Fin 4), σ 0 = i ∧ σ 1 = j := by decide
  obtain ⟨σ, hσ0, hσ1⟩ := hperm i j hij
  have hdet : ((g : Matrix (Fin 4) (Fin 4) F).submatrix id σ).det ≠ 0 := by
    rw [Matrix.det_permute']
    have hg0 : (g : Matrix (Fin 4) (Fin 4) F).det ≠ 0 :=
      ((Matrix.isUnit_iff_isUnit_det _).mp g.isUnit).ne_zero
    refine mul_ne_zero ?_ hg0
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  let g' : GL (Fin 4) F := GeneralLinearGroup.mkOfDetNeZero _ hdet
  have hg' : (g' : Matrix (Fin 4) (Fin 4) F)ᵀ * ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
      (g' : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal (d ∘ σ) := by
    rw [show (g' : Matrix (Fin 4) (Fin 4) F) = (g : Matrix (Fin 4) (Fin 4) F).submatrix id σ from
      GeneralLinearGroup.val_mkOfDetNeZero _ _, l4_submatrix_congr_perm, hg,
      Matrix.submatrix_diagonal_equiv]
  obtain ⟨hd', P, D, h1, h2⟩ := l4_frame_of_congr g' (d ∘ σ) hg'
  refine ⟨P, D, d ∘ σ, hd', ?_, h1, h2⟩
  simp [hσ0, hσ1, hdij]

end FrameMain

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
