module

public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.RouteWSym2
public import CFSG.RankThree.Classical2.SLnRootPermutingFixedGroups
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Inner

open Matrix
open CFSG.RankThree.Classical2 (conjSLn coe_conjSLn fixSubgroup)
open scoped MatrixGroups

section Inj

variable {K : Type} [Field K] {n : ℕ}

theorem conjSLn_injective (M : GL (Fin n) K) : Function.Injective (conjSLn M) := by
  intro A B h
  have := congrArg (conjSLn M⁻¹) h
  refine Subtype.ext ?_
  have e := congrArg (fun X : SL(n, K) => (X : Matrix (Fin n) (Fin n) K)) this
  simp only [coe_conjSLn] at e
  have h1 : (↑M⁻¹ : Matrix (Fin n) (Fin n) K) * (M : Matrix (Fin n) (Fin n) K) = 1 := M.inv_mul
  have key : ∀ X : Matrix (Fin n) (Fin n) K,
      (↑M⁻¹ : Matrix (Fin n) (Fin n) K) * ((M : Matrix (Fin n) (Fin n) K) * X *
        (↑M⁻¹ : Matrix (Fin n) (Fin n) K)) * (↑(M⁻¹)⁻¹ : Matrix (Fin n) (Fin n) K) = X := by
    intro X
    have : ((M⁻¹)⁻¹ : GL (Fin n) K) = M := inv_inv M
    rw [this]
    calc (↑M⁻¹ : Matrix (Fin n) (Fin n) K) * ((M : Matrix (Fin n) (Fin n) K) * X *
          (↑M⁻¹ : Matrix (Fin n) (Fin n) K)) * (M : Matrix (Fin n) (Fin n) K)
        = ((↑M⁻¹ : Matrix (Fin n) (Fin n) K) * M) * X * ((↑M⁻¹ : Matrix (Fin n) (Fin n) K) * M) := by
          simp only [Matrix.mul_assoc]
      _ = X := by rw [h1, Matrix.one_mul, Matrix.mul_one]
  rw [key, key] at e
  exact e

end Inj

section Card

theorem card_SL2_field (F : Type) [Field F] [Finite F] :
    Nat.card SL(2, F) = Nat.card F * (Nat.card F ^ 2 - 1) := by
  classical
  have := Fintype.ofFinite F
  rw [Matrix.card_SL_field, ← Nat.card_eq_fintype_card, Fin.prod_univ_two]
  have hq : 2 ≤ Nat.card F := by
    have := Nat.card_pos (α := F)
    have h2 : 2 ≤ Nat.card F := by
      have : Nontrivial F := inferInstance
      exact Nat.succ_le_of_lt (Finite.one_lt_card)
    exact h2
  obtain ⟨m, hm⟩ : ∃ m, Nat.card F = m + 1 := ⟨Nat.card F - 1, by omega⟩
  rw [hm]
  have hsq : (m + 1) ^ 2 = m * (m + 2) + 1 := by ring
  have h1 : (m + 1) ^ 2 - 1 = m * (m + 2) := by omega
  have h2 : (m + 1) ^ 2 - (m + 1) = m * (m + 1) := by
    have : (m + 1) ^ 2 = m * (m + 1) + (m + 1) := by ring
    omega
  have hm0 : 0 < m := by omega
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, Nat.add_sub_cancel]
  rw [h1, h2, show m * (m + 2) * (m * (m + 1)) = (m * (m + 2) * (m + 1)) * m by ring,
    Nat.mul_div_cancel _ hm0]
  ring

end Card

section Simple

theorem sym2Hom_ker_eq_center {F : Type} [Field F] (_h2 : (2 : F) ≠ 0) :
    (sym2Hom F).ker = Subgroup.center SL(2, F) := by
  ext g
  rw [MonoidHom.mem_ker, sym2Hom_eq_one_iff, Matrix.SpecialLinearGroup.mem_center_iff]
  constructor
  · rintro (rfl | rfl)
    · exact ⟨1, by simp, by simp⟩
    · refine ⟨-1, by simp, ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;> simp
  · rintro ⟨r, hr, hg⟩
    have hr' : r ^ 2 = 1 := by simpa using hr
    have hrr : r * r = 1 := by rw [← sq]; exact hr'
    rcases mul_self_eq_one_iff.1 hrr with h | h
    · left
      refine Subtype.ext ?_
      rw [← hg, h]
      simp
    · right
      refine Subtype.ext ?_
      rw [← hg, h]
      ext i j
      fin_cases i <;> fin_cases j <;> simp

theorem sym2_range_simple {F : Type} [Field F] [Finite F] (h2 : (2 : F) ≠ 0)
    (h4 : 4 ≤ Nat.card F) : IsSimpleGroup (sym2Hom F).range := by
  have e : (sym2Hom F).range ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F :=
    (QuotientGroup.quotientKerEquivRange (sym2Hom F)).symm.trans
      (QuotientGroup.quotientMulEquivOfEq (sym2Hom_ker_eq_center h2))
  have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
  exact e.isSimpleGroup_congr.mpr inferInstance

end Simple

section Main

variable {ℓ f : ℕ} [Fact ℓ.Prime] {L k : Type} [Field L] [Field k] [Algebra k L] [IsAlgClosure k L]

theorem mapSL_algebraMap_injective :
    Function.Injective (Matrix.SpecialLinearGroup.map (n := Fin 3) (algebraMap k L)) := by
  intro A B h
  refine Subtype.ext (Matrix.ext fun i j => ?_)
  have := congrArg (fun X : SL(3, L) => (X : Matrix (Fin 3) (Fin 3) L) i j) h
  simpa using this

theorem conj_sym2_form (P : GL (Fin 3) k) (c : k) (Z : SL(2, k)) :
    ((conjSLn P (sym2Hom k Z) : SL(3, k)) : Matrix (Fin 3) (Fin 3) k) *
        (c • ((P : Matrix (Fin 3) (Fin 3) k) * sym2Form k * (P : Matrix (Fin 3) (Fin 3) k)ᵀ)) *
      ((conjSLn P (sym2Hom k Z) : SL(3, k)) : Matrix (Fin 3) (Fin 3) k)ᵀ =
    c • ((P : Matrix (Fin 3) (Fin 3) k) * sym2Form k * (P : Matrix (Fin 3) (Fin 3) k)ᵀ) := by
  have hM := sym2Mat_form (F := k) (Z : Matrix (Fin 2) (Fin 2) k) Z.det_coe
  have h1 : (↑P⁻¹ : Matrix (Fin 3) (Fin 3) k) * (P : Matrix (Fin 3) (Fin 3) k) = 1 := P.inv_mul
  have h1t : (P : Matrix (Fin 3) (Fin 3) k)ᵀ * (↑P⁻¹ : Matrix (Fin 3) (Fin 3) k)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, h1, Matrix.transpose_one]
  rw [coe_conjSLn, coe_sym2Hom, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.mul_smul,
    Matrix.smul_mul]
  congr 1
  calc (P : Matrix (Fin 3) (Fin 3) k) * sym2Mat (Z : Matrix (Fin 2) (Fin 2) k) *
          (↑P⁻¹ : Matrix (Fin 3) (Fin 3) k) *
        ((P : Matrix (Fin 3) (Fin 3) k) * sym2Form k * (P : Matrix (Fin 3) (Fin 3) k)ᵀ) *
        ((↑P⁻¹ : Matrix (Fin 3) (Fin 3) k)ᵀ * ((sym2Mat (Z : Matrix (Fin 2) (Fin 2) k))ᵀ *
          (P : Matrix (Fin 3) (Fin 3) k)ᵀ))
      = (P : Matrix (Fin 3) (Fin 3) k) * sym2Mat (Z : Matrix (Fin 2) (Fin 2) k) *
          ((↑P⁻¹ : Matrix (Fin 3) (Fin 3) k) * (P : Matrix (Fin 3) (Fin 3) k)) * sym2Form k *
          ((P : Matrix (Fin 3) (Fin 3) k)ᵀ * (↑P⁻¹ : Matrix (Fin 3) (Fin 3) k)ᵀ) *
          (sym2Mat (Z : Matrix (Fin 2) (Fin 2) k))ᵀ * (P : Matrix (Fin 3) (Fin 3) k)ᵀ := by
        simp only [Matrix.mul_assoc]
    _ = (P : Matrix (Fin 3) (Fin 3) k) * (sym2Mat (Z : Matrix (Fin 2) (Fin 2) k) * sym2Form k *
          (sym2Mat (Z : Matrix (Fin 2) (Fin 2) k))ᵀ) * (P : Matrix (Fin 3) (Fin 3) k)ᵀ := by
        rw [h1, h1t, Matrix.mul_one, Matrix.mul_one]
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [hM]

end Main

end CFSG.HardMathSupport.Seitz.TrialityOdd.Inner
