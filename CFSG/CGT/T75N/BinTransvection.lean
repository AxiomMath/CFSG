module

public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagData
public import Mathlib.LinearAlgebra.Matrix.SchurComplement

public section

namespace CFSG.CGT.T75N

open Matrix MatrixGroups CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped commutatorElement

variable {F : Type} [Field F] {n : ℕ}

@[expose] def tv (v ψ : Fin n → F) (h : ψ ⬝ᵥ v = 0) : SpecialLinearGroup (Fin n) F :=
  ⟨1 + vecMulVec v ψ, by
    rw [vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow, h, add_zero]⟩

theorem tv_coe (v ψ : Fin n → F) (h : ψ ⬝ᵥ v = 0) :
    ((tv v ψ h : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      1 + vecMulVec v ψ :=
  rfl

theorem tv_congr {v v' ψ ψ' : Fin n → F} (hv : v = v') (hψ : ψ = ψ') (h : ψ ⬝ᵥ v = 0)
    (h' : ψ' ⬝ᵥ v' = 0) : tv v ψ h = tv v' ψ' h' := by
  subst hv
  subst hψ
  rfl

theorem tv_mulVec (v ψ x : Fin n → F) (h : ψ ⬝ᵥ v = 0) :
    (tv v ψ h : Matrix (Fin n) (Fin n) F) *ᵥ x = x + (ψ ⬝ᵥ x) • v := by
  rw [tv_coe, add_mulVec, one_mulVec, vecMulVec_mulVec, op_smul_eq_smul]

theorem coe_mul_coe_inv (g : SpecialLinearGroup (Fin n) F) :
    (g : Matrix (Fin n) (Fin n) F) *
      ((g⁻¹ : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 := by
  rw [← SpecialLinearGroup.coe_mul, mul_inv_cancel, SpecialLinearGroup.coe_one]

theorem tv_conj (g : SpecialLinearGroup (Fin n) F) (v ψ : Fin n → F) (h : ψ ⬝ᵥ v = 0) :
    g * tv v ψ h * g⁻¹ = tv ((g : Matrix (Fin n) (Fin n) F) *ᵥ v)
      (ψ ᵥ* ((g⁻¹ : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F))
      (by
        rw [← dotProduct_mulVec, mulVec_mulVec, coe_inv_mul_coe, one_mulVec]
        exact h) := by
  apply Subtype.ext
  simp only [SpecialLinearGroup.coe_mul, tv_coe, Matrix.mul_add, Matrix.mul_one, add_mul,
    coe_mul_coe_inv, mul_vecMulVec, vecMulVec_mul]

theorem tv_mem_unitriangular {v ψ : Fin n → F} (h : ψ ⬝ᵥ v = 0)
    (hvψ : ∀ a b : Fin n, b ≤ a → v a * ψ b = 0) : tv v ψ h ∈ unitriangular n F := by
  refine ⟨fun a b hba => ?_, fun a => ?_⟩
  · rw [tv_coe, Matrix.add_apply, vecMulVec_apply, hvψ a b hba.le,
      Matrix.one_apply_ne (ne_of_gt hba), add_zero]
  · rw [tv_coe, Matrix.add_apply, vecMulVec_apply, hvψ a a le_rfl, Matrix.one_apply_eq, add_zero]

theorem transvection_eq_tv {i j : Fin n} (hij : i ≠ j) :
    SpecialLinearGroup.transvection hij (1 : F) =
      tv (Pi.single i 1) (Pi.single j 1) (by simp [dotProduct_single, hij]) := by
  apply Subtype.ext
  rw [SpecialLinearGroup.transvection_coe, tv_coe, single_eq_single_vecMulVec_single]

theorem transvection_mem_unitriangular {i j : Fin n} (hij : i < j) :
    SpecialLinearGroup.transvection (ne_of_lt hij) (1 : F) ∈ unitriangular n F := by
  rw [transvection_eq_tv (ne_of_lt hij)]
  refine tv_mem_unitriangular _ fun a b hba => ?_
  rw [Pi.single_apply, Pi.single_apply]
  by_cases ha : a = i
  · by_cases hb : b = j
    · subst ha
      subst hb
      exact absurd (lt_of_lt_of_le hij hba) (lt_irrefl _)
    · simp [hb]
  · simp [ha]

theorem comm_aux {R : Type*} [Ring R] (p q r : R) (hpp : p * p = 0) (hqq : q * q = 0)
    (hqp : q * p = 0) (hpq : p * q = r) (hrp : r * p = 0) (hrq : r * q = 0) :
    (1 + p) * (1 + q) * (1 + -p) * (1 + -q) = 1 + r := by
  simp only [mul_add, add_mul, mul_neg, neg_mul, mul_one, one_mul, hpp, hqq, hqp, hpq, hrp, hrq,
    add_zero]
  abel

theorem commutator_transvection {i a j : Fin n} (hia : i ≠ a) (haj : a ≠ j) (hij : i ≠ j) :
    ⁅SpecialLinearGroup.transvection hia (1 : F), SpecialLinearGroup.transvection haj (1 : F)⁆ =
      SpecialLinearGroup.transvection hij (1 : F) := by
  rw [commutatorElement_def, SpecialLinearGroup.transvection_inv,
    SpecialLinearGroup.transvection_inv]
  apply Subtype.ext
  simp only [SpecialLinearGroup.coe_mul, SpecialLinearGroup.transvection_coe]
  rw [← single_neg, ← single_neg]
  exact comm_aux (single i a (1 : F)) (single a j (1 : F)) (single i j (1 : F))
    (single_mul_single_of_ne _ _ _ _ hia.symm _) (single_mul_single_of_ne _ _ _ _ haj.symm _)
    (single_mul_single_of_ne _ _ _ _ hij.symm _) (by rw [single_mul_single_same, one_mul])
    (single_mul_single_of_ne _ _ _ _ hij.symm _) (single_mul_single_of_ne _ _ _ _ haj.symm _)

theorem eq_zero_or_one_of_card_two (hF : Nat.card F = 2) (a : F) : a = 0 ∨ a = 1 := by
  by_cases ha : a = 0
  · exact Or.inl ha
  · right
    obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (0 : F)).1 hF
    exact (hy a ha).trans (hy 1 one_ne_zero).symm

theorem eq_top_of_transvections (hF : Nat.card F = 2) (hn : 2 ≤ n)
    (S : Subgroup (SpecialLinearGroup (Fin n) F))
    (h : ∀ (i j : Fin n) (hij : i ≠ j), SpecialLinearGroup.transvection hij (1 : F) ∈ S) :
    S = ⊤ := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 hn
  rw [eq_top_iff]
  intro M _
  refine SpecialLinearGroup.diagonal_transvection_induction' (fun g => g ∈ S) M ?_ ?_ ?_
  · intro i j hij c hc
    obtain rfl : c = 1 := (eq_zero_or_one_of_card_two hF c).resolve_left hc
    have : SpecialLinearGroup.diag2n hij (1 : F) hc = 1 :=
      Subtype.ext (by simp [SpecialLinearGroup.diag2n_coe])
    rw [this]
    exact S.one_mem
  · intro i j hij a
    rcases eq_zero_or_one_of_card_two hF a with rfl | rfl
    · rw [SpecialLinearGroup.transvection_coeff_zero]
      exact S.one_mem
    · exact h i j hij
  · intro A B hA hB
    exact S.mul_mem hA hB

end CFSG.CGT.T75N
