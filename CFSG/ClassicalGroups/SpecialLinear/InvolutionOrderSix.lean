module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.Algebra.CharP.Two
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.GroupTheory.Perm.Sign
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotPositionBNormalForm
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotFusionNotTransvectionCore
import CFSG.Quasithin.Vol2.Ch8Sec2L829NKLin
import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherSubspaceIndex
import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
import CFSG.Open.QuasithinDefs
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
import CFSG.Walter.JRFacts

public section

namespace CFSG.ClassicalGroups.SpecialLinear

open Matrix
open scoped BigOperators

section FourPoint

variable {K : Type*} [Field K] [CharP K 2]

local notation "Z4" => (Matrix.single (0 : Fin 4) 1 (1 : K) +
  Matrix.single 2 3 (1 : K) + Matrix.single 3 0 (1 : K) +
  Matrix.single 1 2 (1 : K) + Matrix.single 0 2 (1 : K) +
  Matrix.single 2 0 (1 : K) : Matrix (Fin 4) (Fin 4) K)

private lemma fourPoint_sq :
    (1 + Z4) ^ 2 = 1 + Matrix.single 0 0 (1 : K) + Matrix.single 2 2 (1 : K) +
      Matrix.single 0 2 (1 : K) + Matrix.single 2 0 (1 : K) +
      Matrix.single 2 1 (1 : K) + Matrix.single 1 3 (1 : K) +
      Matrix.single 3 1 (1 : K) + Matrix.single 0 3 (1 : K) +
      Matrix.single 1 0 (1 : K) + Matrix.single 3 2 (1 : K) := by
  rw [pow_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
      Matrix.mul_apply, Fin.sum_univ_four, Matrix.add_apply, Matrix.one_apply,
      Matrix.single_apply, CharTwo.add_self_eq_zero]

private lemma fourPoint_cube :
    (1 + Z4) ^ 3 = Matrix.single 0 2 (1 : K) + Matrix.single 1 3 (1 : K) +
      Matrix.single 2 0 (1 : K) + Matrix.single 3 1 (1 : K) := by
  change (1 + Z4) ^ (2 + 1) = _
  rw [pow_succ, fourPoint_sq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
      Matrix.mul_apply, Fin.sum_univ_four, Matrix.add_apply,
      Matrix.one_apply, Matrix.single_apply, CharTwo.add_self_eq_zero]

private lemma fourPoint_pow_six : (1 + Z4 : Matrix (Fin 4) (Fin 4) K) ^ 6 = 1 := by
  change (1 + Z4) ^ (3 * 2) = 1
  rw [pow_mul, fourPoint_cube, pow_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
      Matrix.mul_apply, Fin.sum_univ_four, Matrix.add_apply, Matrix.one_apply,
      Matrix.single_apply, CharTwo.add_self_eq_zero]

private lemma fourPoint_sq_ne_one : (1 + Z4 : Matrix (Fin 4) (Fin 4) K) ^ 2 ≠ 1 := by
  intro h
  have h00 := congrFun (congrFun h 0) 0
  simp [fourPoint_sq, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply] at h00

private lemma fourPoint_cube_ne_one : (1 + Z4 : Matrix (Fin 4) (Fin 4) K) ^ 3 ≠ 1 := by
  intro h
  have h00 := congrFun (congrFun h 0) 0
  simp [fourPoint_cube, Matrix.one_apply, Matrix.single_apply] at h00

private lemma fourPoint_sq_not_scalar (r : K) :
    Matrix.scalar (Fin 4) r ≠ (1 + Z4 : Matrix (Fin 4) (Fin 4) K) ^ 2 := by
  intro h
  have h00 := congrFun (congrFun h 0) 0
  have h02 := congrFun (congrFun h 0) 2
  simp [fourPoint_sq, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.add_apply,
    Matrix.one_apply, Matrix.single_apply] at h00 h02

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {β : Type*} [Fintype β] [DecidableEq β]

private lemma submatrix_pow_equiv (B : Matrix α α K) (e : α ≃ β) (n : ℕ) :
    (B.submatrix e.symm e.symm : Matrix β β K) ^ n =
      (B ^ n).submatrix e.symm e.symm := by
  induction n with
  | zero => simp [Matrix.submatrix_one_equiv]
  | succ n ih =>
      rw [pow_succ, ih, pow_succ, Matrix.submatrix_mul_equiv]

private lemma one_add_submatrix_eq (e : Fin 4 ≃ α) :
    (1 + (Z4).submatrix e.symm e.symm : Matrix α α K) =
      ((1 + Z4 : Matrix (Fin 4) (Fin 4) K).submatrix e.symm e.symm) := by
  ext i j
  simp [Matrix.submatrix_apply, Matrix.add_apply, Matrix.one_apply]

private lemma submatrix_scalar_equiv (e : Fin 4 ≃ α) (r : K) :
    (Matrix.scalar α r).submatrix e e = Matrix.scalar (Fin 4) r := by
  ext i j
  by_cases h : i = j <;> simp [Matrix.scalar_apply, Matrix.diagonal_apply, h]

private lemma submatrix_eq_one_iff (B : Matrix (Fin 4) (Fin 4) K) (e : Fin 4 ≃ α) :
    (B.submatrix e.symm e.symm : Matrix α α K) = 1 ↔ B = 1 := by
  constructor
  · intro h
    have := congrArg (fun M : Matrix α α K => M.submatrix e e) h
    simpa [Matrix.submatrix_submatrix, Matrix.submatrix_one_equiv] using this
  · intro h
    rw [h, Matrix.submatrix_one_equiv]

private lemma fourPoint_submatrix_pow_six (e : Fin 4 ≃ α) :
    (1 + (Z4).submatrix e.symm e.symm : Matrix α α K) ^ 6 = 1 := by
  rw [one_add_submatrix_eq, submatrix_pow_equiv, fourPoint_pow_six,
    Matrix.submatrix_one_equiv]

private lemma fourPoint_submatrix_sq_ne_one (e : Fin 4 ≃ α) :
    (1 + (Z4).submatrix e.symm e.symm : Matrix α α K) ^ 2 ≠ 1 := by
  intro h
  have h' : (((1 + Z4 : Matrix (Fin 4) (Fin 4) K) ^ 2).submatrix e.symm e.symm) = 1 := by
    rw [← submatrix_pow_equiv, ← one_add_submatrix_eq]
    exact h
  exact fourPoint_sq_ne_one
    ((submatrix_eq_one_iff (B := (1 + Z4 : Matrix (Fin 4) (Fin 4) K) ^ 2) e).mp h')

private lemma fourPoint_submatrix_cube_ne_one (e : Fin 4 ≃ α) :
    (1 + (Z4).submatrix e.symm e.symm : Matrix α α K) ^ 3 ≠ 1 := by
  intro h
  have h' : (((1 + Z4 : Matrix (Fin 4) (Fin 4) K) ^ 3).submatrix e.symm e.symm) = 1 := by
    rw [← submatrix_pow_equiv, ← one_add_submatrix_eq]
    exact h
  exact fourPoint_cube_ne_one
    ((submatrix_eq_one_iff (B := (1 + Z4 : Matrix (Fin 4) (Fin 4) K) ^ 3) e).mp h')

private lemma fourPoint_submatrix_sq_not_scalar (e : Fin 4 ≃ α) (r : K) :
    Matrix.scalar α r ≠ (1 + (Z4).submatrix e.symm e.symm : Matrix α α K) ^ 2 := by
  intro h
  apply fourPoint_sq_not_scalar r
  have h' : (((1 + Z4 : Matrix (Fin 4) (Fin 4) K) ^ 2).submatrix e.symm e.symm) =
      Matrix.scalar α r := by
    rw [← submatrix_pow_equiv, ← one_add_submatrix_eq]
    exact h.symm
  have := congrArg (fun M : Matrix α α K => M.submatrix e e) h'
  have hdiag : ((fun _ : α => r) ∘ e) = (fun _ : Fin 4 => r) := rfl
  simpa [submatrix_scalar_equiv, Matrix.submatrix_submatrix, hdiag] using this.symm

end FourPoint

section Block

variable {K : Type*} [Field K] [CharP K 2]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (a b c d : ι)

local notation "Z4" => (Matrix.single (0 : Fin 4) 1 (1 : K) +
  Matrix.single 2 3 (1 : K) + Matrix.single 3 0 (1 : K) +
  Matrix.single 1 2 (1 : K) + Matrix.single 0 2 (1 : K) +
  Matrix.single 2 0 (1 : K) : Matrix (Fin 4) (Fin 4) K)

local notation "P4" => (1 + Matrix.single a b (1 : K) + Matrix.single c d (1 : K) +
  Matrix.single d a (1 : K) + Matrix.single b c (1 : K) +
  Matrix.single a c (1 : K) + Matrix.single c a (1 : K) : Matrix ι ι K)

private lemma exists_fourEquiv {α : Type*} [Fintype α] [DecidableEq α]
    (a b c d : α) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) (hcover : ∀ x, x = a ∨ x = b ∨ x = c ∨ x = d) :
    ∃ e : Fin 4 ≃ α, e 0 = a ∧ e 1 = b ∧ e 2 = c ∧ e 3 = d := by
  let e : Fin 4 ≃ α :=
    { toFun := fun i => if i = 0 then a else if i = 1 then b else if i = 2 then c else d
      invFun := fun x => if x = a then 0 else if x = b then 1 else if x = c then 2 else 3
      left_inv := by
        intro i
        fin_cases i <;> simp [hab, hac, had, hbc, hbd, hcd, hab.symm, hac.symm, had.symm,
          hbc.symm, hbd.symm, hcd.symm]
      right_inv := by
        intro x
        rcases hcover x with rfl | rfl | rfl | rfl <;> simp [hab, hac, had, hbc, hbd, hcd,
          hab.symm, hac.symm, had.symm, hbc.symm, hbd.symm, hcd.symm] }
  refine ⟨e, ?_, ?_, ?_, ?_⟩ <;> simp [e]

private lemma fourPoint_symm_four {a b c d : ι}
    (e : Fin 4 ≃ ↥({a, b, c, d} : Set ι)) (he0 : (e 0 : ι) = a) (he1 : (e 1 : ι) = b)
    (he2 : (e 2 : ι) = c) (he3 : (e 3 : ι) = d) :
    e.symm ⟨a, by simp⟩ = 0 ∧ e.symm ⟨b, by simp⟩ = 1 ∧
      e.symm ⟨c, by simp⟩ = 2 ∧ e.symm ⟨d, by simp⟩ = 3 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply e.injective
    rw [Equiv.apply_symm_apply]
    exact Subtype.ext he0.symm
  · apply e.injective
    rw [Equiv.apply_symm_apply]
    exact Subtype.ext he1.symm
  · apply e.injective
    rw [Equiv.apply_symm_apply]
    exact Subtype.ext he2.symm
  · apply e.injective
    rw [Equiv.apply_symm_apply]
    exact Subtype.ext he3.symm

private lemma fourPoint_eq_blocks (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (e : Fin 4 ≃ ↥({a, b, c, d} : Set ι)) (he0 : (e 0 : ι) = a) (he1 : (e 1 : ι) = b)
    (he2 : (e 2 : ι) = c) (he3 : (e 3 : ι) = d) :
    let S : Set ι := {a, b, c, d}
    let E : S ⊕ ↥(Sᶜ : Set ι) ≃ ι := Equiv.sumCompl (· ∈ S)
    P4 = (fromBlocks (1 + (Z4).submatrix e.symm e.symm : Matrix S S K) 0 0
      (1 : Matrix ↥(Sᶜ : Set ι) ↥(Sᶜ : Set ι) K)).reindex E E := by
  intro S E
  ext x y
  by_cases hx : x ∈ S <;> by_cases hy : y ∈ S
  · simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
    rw [Equiv.sumCompl_symm_apply_of_pos hx, Equiv.sumCompl_symm_apply_of_pos hy]
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.add_apply, Matrix.submatrix_apply,
      Matrix.one_apply]
    obtain ⟨hsymm0, hsymm1, hsymm2, hsymm3⟩ := fourPoint_symm_four e he0 he1 he2 he3
    simp only [S, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
      simp [hsymm0, hsymm1, hsymm2, hsymm3, Matrix.single_apply, Matrix.one_apply,
        hab, hac, had, hbc, hbd, hcd, hab.symm, hac.symm, had.symm, hbc.symm, hbd.symm,
        hcd.symm]
  · simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
    rw [Equiv.sumCompl_symm_apply_of_pos hx, Equiv.sumCompl_symm_apply_of_neg hy]
    simp only [Matrix.fromBlocks_apply₁₂, Matrix.zero_apply]
    simp only [S, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hx hy
    have hya : a ≠ y := fun h => hy.1 h.symm
    have hyb : b ≠ y := fun h => hy.2.1 h.symm
    have hyc : c ≠ y := fun h => hy.2.2.1 h.symm
    have hyd : d ≠ y := fun h => hy.2.2.2 h.symm
    rcases hx with rfl | rfl | rfl | rfl <;>
      simp [Matrix.single_apply, Matrix.one_apply, hya, hyb, hyc, hyd,
        hya.symm, hyb.symm, hyc.symm, hyd.symm, eq_comm,
        hab, hac, had, hbc, hbd, hcd]
  · simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
    rw [Equiv.sumCompl_symm_apply_of_neg hx, Equiv.sumCompl_symm_apply_of_pos hy]
    simp only [Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
    simp only [S, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hx hy
    have hxa : a ≠ x := fun h => hx.1 h.symm
    have hxb : b ≠ x := fun h => hx.2.1 h.symm
    have hxc : c ≠ x := fun h => hx.2.2.1 h.symm
    have hxd : d ≠ x := fun h => hx.2.2.2 h.symm
    rcases hy with rfl | rfl | rfl | rfl <;>
      simp [Matrix.single_apply, Matrix.one_apply, hxa, hxb, hxc, hxd,
        hxa.symm, hxb.symm, hxc.symm, hxd.symm, eq_comm,
        hab, hac, had, hbc, hbd, hcd]
  · simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
    rw [Equiv.sumCompl_symm_apply_of_neg hx, Equiv.sumCompl_symm_apply_of_neg hy]
    simp only [Matrix.fromBlocks_apply₂₂, Matrix.one_apply]
    simp only [S, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hx hy
    have hxa : a ≠ x := fun h => hx.1 h.symm
    have hxb : b ≠ x := fun h => hx.2.1 h.symm
    have hxc : c ≠ x := fun h => hx.2.2.1 h.symm
    have hxd : d ≠ x := fun h => hx.2.2.2 h.symm
    have hya : a ≠ y := fun h => hy.1 h.symm
    have hyb : b ≠ y := fun h => hy.2.1 h.symm
    have hyc : c ≠ y := fun h => hy.2.2.1 h.symm
    have hyd : d ≠ y := fun h => hy.2.2.2 h.symm
    simp [Matrix.single_apply, Matrix.one_apply, hxa, hxb, hxc, hxd, hya, hyb, hyc, hyd,
      hxa.symm, hxb.symm, hxc.symm, hxd.symm, hya.symm, hyb.symm, hyc.symm, hyd.symm,
      eq_comm, hab, hac, had, hbc, hbd, hcd]
private lemma reindex_eq_one_iff {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    [DecidableEq β] (E : α ≃ β) (B : Matrix α α K) :
    (B.reindex E E : Matrix β β K) = 1 ↔ B = 1 := by
  constructor
  · intro h
    have := congrArg (fun M : Matrix β β K => M.submatrix E E) h
    simpa [Matrix.reindex_apply, Matrix.submatrix_submatrix, Matrix.submatrix_one_equiv] using this
  · intro h
    rw [h, Matrix.reindex_apply, Matrix.submatrix_one_equiv]

private lemma scalar_reindex_blocks (r : K) :
    let S : Set ι := {a, b, c, d}
    let E : S ⊕ ↥(Sᶜ : Set ι) ≃ ι := Equiv.sumCompl (· ∈ S)
    (Matrix.scalar ι r).reindex E.symm E.symm =
      fromBlocks (Matrix.scalar S r) 0 0 (Matrix.scalar ↥(Sᶜ : Set ι) r) := by
  intro S E
  rw [Matrix.reindex_apply, Matrix.scalar_apply, Matrix.submatrix_diagonal_equiv]
  change diagonal (fun _ : S ⊕ ↥(Sᶜ : Set ι) => r) =
    fromBlocks (diagonal (fun _ : S => r)) 0 0 (diagonal (fun _ : ↥(Sᶜ : Set ι) => r))
  rw [Matrix.fromBlocks_diagonal]
  ext x
  cases x <;> rfl

private lemma fourPointMatrix_pow_six (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) : (P4) ^ 6 = 1 := by
  obtain ⟨e, he0, he1, he2, he3⟩ := exists_fourEquiv
    (a := (⟨a, by simp⟩ : ↥({a, b, c, d} : Set ι)))
    (b := (⟨b, by simp⟩ : ↥({a, b, c, d} : Set ι)))
    (c := (⟨c, by simp⟩ : ↥({a, b, c, d} : Set ι)))
    (d := (⟨d, by simp⟩ : ↥({a, b, c, d} : Set ι)))
    (by simpa using hab) (by simpa using hac) (by simpa using had)
    (by simpa using hbc) (by simpa using hbd) (by simpa using hcd)
    (by
      rintro ⟨x, hx⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> simp)
  let S : Set ι := {a, b, c, d}
  let E : S ⊕ ↥(Sᶜ : Set ι) ≃ ι := Equiv.sumCompl (· ∈ S)
  let M_S : Matrix S S K := 1 + (Z4).submatrix e.symm e.symm
  have hblock : P4 = (fromBlocks M_S 0 0
      (1 : Matrix ↥(Sᶜ : Set ι) ↥(Sᶜ : Set ι) K)).reindex E E := by
    simpa only [S, E, M_S] using
      fourPoint_eq_blocks (K := K) a b c d hab hac had hbc hbd hcd e
        (congrArg Subtype.val he0) (congrArg Subtype.val he1)
        (congrArg Subtype.val he2) (congrArg Subtype.val he3)
  rw [hblock]
  change (Matrix.reindexRingEquiv K E (fromBlocks M_S 0 0
    (1 : Matrix ↥(Sᶜ : Set ι) ↥(Sᶜ : Set ι) K))) ^ 6 = 1
  rw [← map_pow]
  change Matrix.reindexRingEquiv K E ((fromBlocks M_S 0 0
    (1 : Matrix ↥(Sᶜ : Set ι) ↥(Sᶜ : Set ι) K)) ^ 6) = 1
  rw [Matrix.fromBlocks_diagonal_pow]
  simp only [one_pow]
  dsimp only [M_S]
  rw [fourPoint_submatrix_pow_six e, Matrix.fromBlocks_one]
  exact map_one _

private lemma fourPointMatrix_sq_ne_one (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) : (P4) ^ 2 ≠ 1 := by
  obtain ⟨e, he0, he1, he2, he3⟩ := exists_fourEquiv
    (a := (⟨a, by simp⟩ : ↥({a, b, c, d} : Set ι)))
    (b := (⟨b, by simp⟩ : ↥({a, b, c, d} : Set ι)))
    (c := (⟨c, by simp⟩ : ↥({a, b, c, d} : Set ι)))
    (d := (⟨d, by simp⟩ : ↥({a, b, c, d} : Set ι)))
    (by simpa using hab) (by simpa using hac) (by simpa using had)
    (by simpa using hbc) (by simpa using hbd) (by simpa using hcd)
    (by
      rintro ⟨x, hx⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> simp)
  let S : Set ι := {a, b, c, d}
  let E : S ⊕ ↥(Sᶜ : Set ι) ≃ ι := Equiv.sumCompl (· ∈ S)
  let M_S : Matrix S S K := 1 + (Z4).submatrix e.symm e.symm
  have hblock : P4 = (fromBlocks M_S 0 0
      (1 : Matrix ↥(Sᶜ : Set ι) ↥(Sᶜ : Set ι) K)).reindex E E := by
    simpa only [S, E, M_S] using
      fourPoint_eq_blocks (K := K) a b c d hab hac had hbc hbd hcd e
        (congrArg Subtype.val he0) (congrArg Subtype.val he1)
        (congrArg Subtype.val he2) (congrArg Subtype.val he3)
  intro h
  rw [hblock] at h
  change (Matrix.reindexRingEquiv K E (fromBlocks M_S 0 0
    (1 : Matrix ↥(Sᶜ : Set ι) ↥(Sᶜ : Set ι) K))) ^ 2 = 1 at h
  rw [← map_pow] at h
  change Matrix.reindexRingEquiv K E ((fromBlocks M_S 0 0
    (1 : Matrix ↥(Sᶜ : Set ι) ↥(Sᶜ : Set ι) K)) ^ 2) = 1 at h
  have hB : (fromBlocks M_S 0 0
      (1 : Matrix ↥(Sᶜ : Set ι) ↥(Sᶜ : Set ι) K)) ^ 2 = 1 :=
    (reindex_eq_one_iff E _).mp (by simpa [Matrix.reindex_apply] using h)
  rw [Matrix.fromBlocks_diagonal_pow] at hB
  simp only [one_pow] at hB
  have h' : Matrix.fromBlocks (M_S ^ 2) 0 0
      (1 : Matrix ↥(Sᶜ : Set ι) ↥(Sᶜ : Set ι) K) =
      Matrix.fromBlocks (1 : Matrix S S K) 0 0
        (1 : Matrix ↥(Sᶜ : Set ι) ↥(Sᶜ : Set ι) K) := by
    simpa using hB
  exact fourPoint_submatrix_sq_ne_one e (Matrix.fromBlocks_inj.mp h').1

private lemma fourPointMatrix_cube_ne_one (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) : (P4) ^ 3 ≠ 1 := by
  obtain ⟨e, he0, he1, he2, he3⟩ := exists_fourEquiv
    (a := (⟨a, by simp⟩ : ↥({a, b, c, d} : Set ι)))
    (b := (⟨b, by simp⟩ : ↥({a, b, c, d} : Set ι)))
    (c := (⟨c, by simp⟩ : ↥({a, b, c, d} : Set ι)))
    (d := (⟨d, by simp⟩ : ↥({a, b, c, d} : Set ι)))
    (by simpa using hab) (by simpa using hac) (by simpa using had)
    (by simpa using hbc) (by simpa using hbd) (by simpa using hcd)
    (by
      rintro ⟨x, hx⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> simp)
  let S : Set ι := {a, b, c, d}
  let E : S ⊕ ↥(Sᶜ : Set ι) ≃ ι := Equiv.sumCompl (· ∈ S)
  let M_S : Matrix S S K := 1 + (Z4).submatrix e.symm e.symm
  have hblock : P4 = (fromBlocks M_S 0 0
      (1 : Matrix ↥(Sᶜ : Set ι) ↥(Sᶜ : Set ι) K)).reindex E E := by
    simpa only [S, E, M_S] using
      fourPoint_eq_blocks (K := K) a b c d hab hac had hbc hbd hcd e
        (congrArg Subtype.val he0) (congrArg Subtype.val he1)
        (congrArg Subtype.val he2) (congrArg Subtype.val he3)
  intro h
  rw [hblock] at h
  change (Matrix.reindexRingEquiv K E (fromBlocks M_S 0 0
    (1 : Matrix ↥(Sᶜ : Set ι) ↥(Sᶜ : Set ι) K))) ^ 3 = 1 at h
  rw [← map_pow] at h
  change Matrix.reindexRingEquiv K E ((fromBlocks M_S 0 0
    (1 : Matrix ↥(Sᶜ : Set ι) ↥(Sᶜ : Set ι) K)) ^ 3) = 1 at h
  have hB : (fromBlocks M_S 0 0
      (1 : Matrix ↥(Sᶜ : Set ι) ↥(Sᶜ : Set ι) K)) ^ 3 = 1 :=
    (reindex_eq_one_iff E _).mp (by simpa [Matrix.reindex_apply] using h)
  rw [Matrix.fromBlocks_diagonal_pow] at hB
  simp only [one_pow] at hB
  have h' : Matrix.fromBlocks (M_S ^ 3) 0 0
      (1 : Matrix ↥(Sᶜ : Set ι) ↥(Sᶜ : Set ι) K) =
      Matrix.fromBlocks (1 : Matrix S S K) 0 0
        (1 : Matrix ↥(Sᶜ : Set ι) ↥(Sᶜ : Set ι) K) := by
    simpa using hB
  exact fourPoint_submatrix_cube_ne_one e (Matrix.fromBlocks_inj.mp h').1

private lemma fourPointMatrix_sq_not_scalar (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) (r : K) :
    Matrix.scalar ι r ≠ (P4) ^ 2 := by
  obtain ⟨e, he0, he1, he2, he3⟩ := exists_fourEquiv
    (a := (⟨a, by simp⟩ : ↥({a, b, c, d} : Set ι)))
    (b := (⟨b, by simp⟩ : ↥({a, b, c, d} : Set ι)))
    (c := (⟨c, by simp⟩ : ↥({a, b, c, d} : Set ι)))
    (d := (⟨d, by simp⟩ : ↥({a, b, c, d} : Set ι)))
    (by simpa using hab) (by simpa using hac) (by simpa using had)
    (by simpa using hbc) (by simpa using hbd) (by simpa using hcd)
    (by
      rintro ⟨x, hx⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> simp)
  let S : Set ι := {a, b, c, d}
  let E : S ⊕ ↥(Sᶜ : Set ι) ≃ ι := Equiv.sumCompl (· ∈ S)
  let M_S : Matrix S S K := 1 + (Z4).submatrix e.symm e.symm
  have hblock : P4 = (fromBlocks M_S 0 0
      (1 : Matrix ↥(Sᶜ : Set ι) ↥(Sᶜ : Set ι) K)).reindex E E := by
    simpa only [S, E, M_S] using
      fourPoint_eq_blocks (K := K) a b c d hab hac had hbc hbd hcd e
        (congrArg Subtype.val he0) (congrArg Subtype.val he1)
        (congrArg Subtype.val he2) (congrArg Subtype.val he3)
  intro h
  have h' : (Matrix.scalar ι r).reindex E.symm E.symm =
      (((fromBlocks M_S 0 0 (1 : Matrix ↥(Sᶜ : Set ι) ↥(Sᶜ : Set ι) K)).reindex
        E E) ^ 2).reindex E.symm E.symm := by
    rw [← hblock]
    exact congrArg (fun M : Matrix ι ι K => M.reindex E.symm E.symm) h
  have hL : (Matrix.scalar ι r).reindex E.symm E.symm =
      fromBlocks (Matrix.scalar S r) 0 0 (Matrix.scalar ↥(Sᶜ : Set ι) r) := by
    simpa only [S, E] using scalar_reindex_blocks (K := K) (ι := ι) a b c d r
  have hR : (((fromBlocks M_S 0 0
      (1 : Matrix ↥(Sᶜ : Set ι) ↥(Sᶜ : Set ι) K)).reindex E E) ^ 2).reindex
        E.symm E.symm =
      fromBlocks (M_S ^ 2) 0 0 (1 : Matrix ↥(Sᶜ : Set ι) ↥(Sᶜ : Set ι) K) := by
    change ((((fromBlocks M_S 0 0
      (1 : Matrix ↥(Sᶜ : Set ι) ↥(Sᶜ : Set ι) K)).submatrix E.symm E.symm) ^ 2).submatrix
        E E) =
      fromBlocks (M_S ^ 2) 0 0 (1 : Matrix ↥(Sᶜ : Set ι) ↥(Sᶜ : Set ι) K)
    rw [submatrix_pow_equiv (fromBlocks M_S 0 0
      (1 : Matrix ↥(Sᶜ : Set ι) ↥(Sᶜ : Set ι) K)) E 2]
    rw [Matrix.fromBlocks_diagonal_pow]
    simp only [one_pow, Matrix.submatrix_submatrix, Equiv.symm_comp_self,
      Matrix.submatrix_id_id]
  rw [hL, hR] at h'
  exact fourPoint_submatrix_sq_not_scalar e r (Matrix.fromBlocks_inj.mp h').1

end Block

section Product

variable {K : Type*} [Field K] [CharP K 2]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {k : ℕ} {u w : Fin k → ι}
variable (a0 a1 : Fin k)

open CFSG.SeitzReduction.LinearPilot

local notation "P4" => (1 + Matrix.single (u a0) (w a0) (1 : K) +
  Matrix.single (u a1) (w a1) (1 : K) + Matrix.single (w a1) (u a0) (1 : K) +
  Matrix.single (w a0) (u a1) (1 : K) + Matrix.single (u a0) (u a1) (1 : K) +
  Matrix.single (u a1) (u a0) (1 : K) : Matrix ι ι K)

private lemma nilOf_eq_sum_single (hu : Function.Injective u) :
    nilOf K u w = Finset.sum Finset.univ (fun a : Fin k => Matrix.single (u a) (w a) (1 : K)) := by
  classical
  ext i j
  rw [nilOf_apply, Matrix.sum_apply]
  by_cases h : ∃ a : Fin k, u a = i ∧ w a = j
  · obtain ⟨a, rfl, rfl⟩ := h
    rw [if_pos ⟨a, rfl, rfl⟩]
    rw [Finset.sum_eq_single a]
    · rw [Matrix.single_apply_same]
    · intro b _ hba
      rw [Matrix.single_apply_of_ne]
      rintro ⟨hub, -⟩
      exact hba (hu hub)
    · intro ha
      exact absurd (Finset.mem_univ a) ha
  · rw [if_neg h]
    symm
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [Matrix.single_apply_of_ne]
    rintro ⟨rfl, rfl⟩
    exact h ⟨a, rfl, rfl⟩

private lemma nilOf_eq_head_add_tail (ha01 : a0 ≠ a1)
    (hu : Function.Injective u) :
    nilOf K u w = Matrix.single (u a0) (w a0) (1 : K) +
      Matrix.single (u a1) (w a1) (1 : K) +
      Finset.sum ((Finset.univ.erase a0).erase a1)
        (fun a => Matrix.single (u a) (w a) (1 : K)) := by
  classical
  rw [nilOf_eq_sum_single hu]
  rw [← Finset.add_sum_erase (Finset.univ) (fun a => Matrix.single (u a) (w a) (1 : K))
    (Finset.mem_univ a0)]
  rw [← Finset.add_sum_erase (Finset.univ.erase a0)
    (fun a => Matrix.single (u a) (w a) (1 : K))
    (Finset.mem_erase.2 ⟨ha01.symm, Finset.mem_univ a1⟩)]
  abel

private lemma sum_single_mul_single_eq_zero (T : Finset (Fin k)) (b : ι) (c : ι)
    (h : ∀ a ∈ T, w a ≠ b) :
    (Finset.sum T (fun a => Matrix.single (u a) (w a) (1 : K))) *
      Matrix.single b c (1 : K) = 0 := by
  rw [Finset.sum_mul]
  refine Finset.sum_eq_zero fun a ha => ?_
  rw [Matrix.single_mul_single_of_ne (1 : K) (u a) (w a) b (h a ha) (1 : K)]

private lemma single_mul_sum_single_eq_zero (T : Finset (Fin k)) (b : ι) (c : ι)
    (h : ∀ a ∈ T, u a ≠ c) :
    Matrix.single b c (1 : K) *
      Finset.sum T (fun a => Matrix.single (u a) (w a) (1 : K)) = 0 := by
  rw [Finset.mul_sum]
  refine Finset.sum_eq_zero fun a ha => ?_
  rw [Matrix.single_mul_single_of_ne (1 : K) b c (u a) (h a ha).symm (1 : K)]

private lemma sum_single_mul_sum_single_eq_zero (T : Finset (Fin k))
    (h : ∀ a ∈ T, ∀ b ∈ T, w a ≠ u b) :
    (Finset.sum T (fun a => Matrix.single (u a) (w a) (1 : K))) *
      (Finset.sum T (fun b => Matrix.single (u b) (w b) (1 : K))) = 0 := by
  rw [Finset.sum_mul]
  refine Finset.sum_eq_zero fun a ha => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_eq_zero fun b hb => ?_
  rw [Matrix.single_mul_single_of_ne (1 : K) (u a) (w a) (u b) (h a ha b hb) (1 : K)]

private lemma head_mul_cross {a b c d : ι} (hbd : b ≠ d) :
    (Matrix.single a b (1 : K) + Matrix.single c d (1 : K)) *
      (Matrix.single d a (1 : K) + Matrix.single b c (1 : K)) =
      Matrix.single a c (1 : K) + Matrix.single c a (1 : K) := by
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
  rw [Matrix.single_mul_single_of_ne (1 : K) a b d hbd (1 : K),
    Matrix.single_mul_single_of_ne (1 : K) c d b hbd.symm (1 : K)]
  simp only [Matrix.single_zero, zero_add, add_zero]
  rw [Matrix.single_mul_single_same (1 : K) a b c (1 : K),
    Matrix.single_mul_single_same (1 : K) c d a (1 : K)]
  simp

private lemma fourCycle_apply {a b c d : ι} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    let σ : Equiv.Perm ι := Equiv.swap a d * Equiv.swap a c * Equiv.swap a b
    σ a = b ∧ σ b = c ∧ σ c = d ∧ σ d = a := by
  intro σ
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [σ, Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne, hab, hac, had, hbc, hbd,
      hcd, hab.symm, hac.symm, had.symm, hbc.symm, hbd.symm, hcd.symm]

private lemma fourCycle_fixes_of_ne {a b c d x : ι} (hxa : x ≠ a) (hxb : x ≠ b)
    (hxc : x ≠ c) (hxd : x ≠ d) :
    (Equiv.swap a d * Equiv.swap a c * Equiv.swap a b) x = x := by
  simp [Equiv.swap_apply_of_ne_of_ne, hxa, hxb, hxc, hxd, hxa.symm, hxb.symm, hxc.symm,
    hxd.symm]

private lemma fourCycle_symm_fixes_of_ne {a b c d x : ι} (hxa : x ≠ a) (hxb : x ≠ b)
    (hxc : x ≠ c) (hxd : x ≠ d) :
    (Equiv.swap a d * Equiv.swap a c * Equiv.swap a b).symm x = x := by
  have h := fourCycle_fixes_of_ne hxa hxb hxc hxd
  simpa [h] using
    (Equiv.symm_apply_apply (Equiv.swap a d * Equiv.swap a c * Equiv.swap a b) x)

end Product

section ProductMain

variable {K : Type*} [Field K] [CharP K 2]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {k : ℕ} {u w : Fin k → ι}
variable (a0 a1 : Fin k)

open CFSG.SeitzReduction.LinearPilot

local notation "P4" => (1 + Matrix.single (u a0) (w a0) (1 : K) +
  Matrix.single (u a1) (w a1) (1 : K) + Matrix.single (w a1) (u a0) (1 : K) +
  Matrix.single (w a0) (u a1) (1 : K) + Matrix.single (u a0) (u a1) (1 : K) +
  Matrix.single (u a1) (u a0) (1 : K) : Matrix ι ι K)

private lemma permMatrix_conj_nilOf (σ : Equiv.Perm ι) :
    (σ.permMatrix K) * nilOf K u w * (σ.permMatrix K)⁻¹ =
      nilOf K (σ.symm ∘ u) (σ.symm ∘ w) := by
  have hPinv : (σ.permMatrix K)⁻¹ = Equiv.Perm.permMatrix K σ.symm := by
    refine Matrix.inv_eq_right_inv ?_
    change (Equiv.toPEquiv σ).toMatrix * (Equiv.toPEquiv σ.symm).toMatrix = 1
    rw [← PEquiv.toMatrix_trans, Equiv.toPEquiv_symm]
    have htrans : (Equiv.toPEquiv σ).trans (Equiv.toPEquiv σ).symm = PEquiv.refl ι := by
      rw [PEquiv.trans_symm_eq_iff_forall_isSome]
      intro x
      rw [Equiv.toPEquiv_apply]
      rfl
    rw [htrans, PEquiv.toMatrix_refl]
  rw [hPinv]
  change (Equiv.toPEquiv σ).toMatrix * nilOf K u w *
      (Equiv.toPEquiv σ.symm).toMatrix = nilOf K (σ.symm ∘ u) (σ.symm ∘ w)
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  rw [Matrix.submatrix_submatrix]
  ext i j
  simp only [Matrix.submatrix_apply, nilOf_apply, Function.comp_apply, Equiv.symm_apply_eq,
    id_eq, Equiv.symm_symm]

private lemma det_permMatrix_charTwo (σ : Equiv.Perm ι) : (σ.permMatrix K).det = 1 := by
  rw [Matrix.det_permutation]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> rw [h] <;>
    simp [CharTwo.neg_eq]

private lemma fourCycle_maps {a b c d : ι} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    let σ : Equiv.Perm ι := Equiv.swap a d * Equiv.swap a c * Equiv.swap a b
    σ a = b ∧ σ b = c ∧ σ c = d ∧ σ d = a ∧
      σ.symm a = d ∧ σ.symm b = a ∧ σ.symm c = b ∧ σ.symm d = c := by
  intro σ
  have h := fourCycle_apply (a := a) (b := b) (c := c) (d := d) hab hac had hbc hbd hcd
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, ?_, ?_, ?_, ?_⟩ <;>
    rw [Equiv.symm_apply_eq] <;>
    simp [σ, h.1, h.2.1, h.2.2.1, h.2.2.2]

private lemma nilOf_conj_head_tail (ha01 : a0 ≠ a1)
    (hu : Function.Injective u) (hw : Function.Injective w)
    (huw : ∀ a b, u a ≠ w b) :
    let σ : Equiv.Perm ι := Equiv.swap (u a0) (w a1) * Equiv.swap (u a0) (u a1) *
      Equiv.swap (u a0) (w a0)
    nilOf K u w = Matrix.single (u a0) (w a0) (1 : K) +
        Matrix.single (u a1) (w a1) (1 : K) +
        Finset.sum ((Finset.univ.erase a0).erase a1)
          (fun a => Matrix.single (u a) (w a) (1 : K)) ∧
      nilOf K (σ.symm ∘ u) (σ.symm ∘ w) = Matrix.single (w a1) (u a0) (1 : K) +
        Matrix.single (w a0) (u a1) (1 : K) +
        Finset.sum ((Finset.univ.erase a0).erase a1)
          (fun a => Matrix.single (u a) (w a) (1 : K)) := by
  intro σ
  classical
  let T : Finset (Fin k) := (Finset.univ.erase a0).erase a1
  let X : Matrix ι ι K := Matrix.single (u a0) (w a0) (1 : K)
  let Y : Matrix ι ι K := Matrix.single (u a1) (w a1) (1 : K)
  let B1 : Matrix ι ι K := Matrix.single (w a1) (u a0) (1 : K)
  let B2 : Matrix ι ι K := Matrix.single (w a0) (u a1) (1 : K)
  let R : Matrix ι ι K := Finset.sum T (fun a => Matrix.single (u a) (w a) (1 : K))
  have hab : u a0 ≠ w a0 := huw a0 a0
  have hac : u a0 ≠ u a1 := hu.ne ha01
  have had : u a0 ≠ w a1 := huw a0 a1
  have hbc : w a0 ≠ u a1 := (huw a1 a0).symm
  have hbd : w a0 ≠ w a1 := hw.ne ha01
  have hcd : u a1 ≠ w a1 := huw a1 a1
  obtain ⟨hσa0, hσb0, hσa1, hσb1, hσa0', hσb0', hσa1', hσb1'⟩ :=
    fourCycle_maps (a := u a0) (b := w a0) (c := u a1) (d := w a1)
      hab hac had hbc hbd hcd
  have htail : ∀ a ∈ T, σ.symm (u a) = u a ∧ σ.symm (w a) = w a := by
    intro a ha
    have ha1 : a ≠ a1 := (Finset.mem_erase.mp ha).1
    have ha0 : a ≠ a0 := (Finset.mem_erase.mp (Finset.mem_erase.mp ha).2).1
    have hua0 : u a ≠ u a0 := hu.ne ha0
    have hua1 : u a ≠ u a1 := hu.ne ha1
    have huw0 : u a ≠ w a0 := huw a a0
    have huw1 : u a ≠ w a1 := huw a a1
    have hwa0 : w a ≠ w a0 := hw.ne ha0
    have hwa1 : w a ≠ w a1 := hw.ne ha1
    have hwu0 : w a ≠ u a0 := (huw a0 a).symm
    have hwu1 : w a ≠ u a1 := (huw a1 a).symm
    exact ⟨fourCycle_symm_fixes_of_ne hua0 huw0 hua1 huw1,
      fourCycle_symm_fixes_of_ne hwu0 hwa0 hwu1 hwa1⟩
  have hN : nilOf K u w = X + Y + R := by
    simpa only [X, Y, R, T] using nilOf_eq_head_add_tail (K := K) a0 a1 ha01 hu
  have hN' : nilOf K (σ.symm ∘ u) (σ.symm ∘ w) = B1 + B2 + R := by
    have hu' : Function.Injective (σ.symm ∘ u) := fun a b h => hu (σ.symm.injective h)
    have hsplit := nilOf_eq_head_add_tail (K := K) (u := σ.symm ∘ u) (w := σ.symm ∘ w)
      a0 a1 ha01 hu'
    have hB1 : (σ.symm ∘ u) a0 = w a1 := by simp only [Function.comp_apply, σ, hσa0']
    have hB2 : (σ.symm ∘ w) a0 = u a0 := by simp only [Function.comp_apply, σ, hσb0']
    have hB3 : (σ.symm ∘ u) a1 = w a0 := by simp only [Function.comp_apply, σ, hσa1']
    have hB4 : (σ.symm ∘ w) a1 = u a1 := by simp only [Function.comp_apply, σ, hσb1']
    have htail' : Finset.sum T (fun a => Matrix.single ((σ.symm ∘ u) a) ((σ.symm ∘ w) a)
        (1 : K)) = R := by
      refine Finset.sum_congr rfl ?_
      intro a ha
      obtain ⟨h1, h2⟩ := htail a ha
      simp only [Function.comp_apply, h1, h2]
    simpa only [X, Y, B1, B2, R, T, hB1, hB2, hB3, hB4, htail'] using hsplit
  refine ⟨?_, ?_⟩
  · simpa only [X, Y] using hN
  · simpa only [B1, B2] using hN'

private lemma mul_conj_eq_fourPoint (ha01 : a0 ≠ a1)
    (hu : Function.Injective u) (hw : Function.Injective w)
    (huw : ∀ a b, u a ≠ w b) :
    let σ : Equiv.Perm ι := Equiv.swap (u a0) (w a1) * Equiv.swap (u a0) (u a1) *
      Equiv.swap (u a0) (w a0)
    (1 + nilOf K u w) * (1 + nilOf K (σ.symm ∘ u) (σ.symm ∘ w)) = P4 := by
  intro σ
  classical
  let T : Finset (Fin k) := (Finset.univ.erase a0).erase a1
  let X : Matrix ι ι K := Matrix.single (u a0) (w a0) (1 : K)
  let Y : Matrix ι ι K := Matrix.single (u a1) (w a1) (1 : K)
  let B1 : Matrix ι ι K := Matrix.single (w a1) (u a0) (1 : K)
  let B2 : Matrix ι ι K := Matrix.single (w a0) (u a1) (1 : K)
  let R : Matrix ι ι K := Finset.sum T (fun a => Matrix.single (u a) (w a) (1 : K))
  have hsplit := nilOf_conj_head_tail (K := K) (u := u) (w := w) a0 a1 ha01 hu hw huw
  have hN : nilOf K u w = X + Y + R := by
    simpa only [X, Y, R, T] using hsplit.1
  have hN' : nilOf K (σ.symm ∘ u) (σ.symm ∘ w) = B1 + B2 + R := by
    simpa only [B1, B2, R, T] using hsplit.2
  have hXR : X * R = 0 := by
    simpa only [X] using single_mul_sum_single_eq_zero (K := K) (u := u) (w := w) T (u a0)
      (w a0) (fun a ha => huw a a0)
  have hYR : Y * R = 0 := by
    simpa only [Y] using single_mul_sum_single_eq_zero (K := K) (u := u) (w := w) T (u a1)
      (w a1) (fun a ha => huw a a1)
  have hRB1 : R * B1 = 0 := by
    simpa only [B1] using sum_single_mul_single_eq_zero (K := K) (u := u) (w := w) T (w a1)
      (u a0) (fun a ha => hw.ne (Finset.mem_erase.mp ha).1)
  have hRB2 : R * B2 = 0 := by
    simpa only [B2] using sum_single_mul_single_eq_zero (K := K) (u := u) (w := w) T (w a0)
      (u a1) (fun a ha => hw.ne (Finset.mem_erase.mp (Finset.mem_erase.mp ha).2).1)
  have hRR : R * R = 0 := by
    simpa only [R] using sum_single_mul_sum_single_eq_zero (K := K) (u := u) (w := w) T
      (fun a ha b hb => (huw b a).symm)
  have hbd : w a0 ≠ w a1 := hw.ne ha01
  have hhead : (X + Y) * (B1 + B2) = Matrix.single (u a0) (u a1) (1 : K) +
      Matrix.single (u a1) (u a0) (1 : K) := by
    simpa only [X, Y, B1, B2] using head_mul_cross (K := K) hbd
  have hRRzero : R + R = 0 := by
    ext i j
    simp only [Matrix.add_apply, Matrix.zero_apply]
    exact CharTwo.add_self_eq_zero _
  calc
    (1 + nilOf K u w) * (1 + nilOf K (σ.symm ∘ u) (σ.symm ∘ w)) =
        1 + nilOf K u w + nilOf K (σ.symm ∘ u) (σ.symm ∘ w) +
          nilOf K u w * nilOf K (σ.symm ∘ u) (σ.symm ∘ w) := by noncomm_ring
    _ = 1 + (X + Y + R) + (B1 + B2 + R) + (X + Y + R) * (B1 + B2 + R) := by rw [hN, hN']
    _ = 1 + (X + Y + B1 + B2) + ((X + Y) * (B1 + B2)) := by
      simp only [Matrix.add_mul, Matrix.mul_add]
      rw [hXR, hYR, hRB1, hRB2, hRR]
      simp only [add_zero]
      calc
        1 + (X + Y + R) + (B1 + B2 + R) +
            (X * B1 + Y * B1 + (X * B2 + Y * B2)) =
            1 + (X + Y + B1 + B2) + (R + R) +
              (X * B1 + Y * B1 + (X * B2 + Y * B2)) := by abel
        _ = 1 + (X + Y + B1 + B2) +
              (X * B1 + Y * B1 + (X * B2 + Y * B2)) := by
              rw [hRRzero]
              simp only [add_zero]
    _ = P4 := by
      rw [hhead]
      dsimp only [X, Y, B1, B2]
      abel

end ProductMain

section Main

variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K] [Finite K] [CharP K 2]

local notation "P4[" a ", " b ", " c ", " d "]" => (1 + Matrix.single a b (1 : K) +
  Matrix.single c d (1 : K) + Matrix.single d a (1 : K) + Matrix.single b c (1 : K) +
  Matrix.single a c (1 : K) + Matrix.single c a (1 : K) : Matrix ι ι K)

open CFSG.SeitzReduction.LinearPilot

private lemma mem_center_conj_iff {G : Type*} [Group G] (g z : G) :
    g * z * g⁻¹ ∈ Subgroup.center G ↔ z ∈ Subgroup.center G := by
  rw [Subgroup.mem_center_iff, Subgroup.mem_center_iff]
  constructor
  · intro h y
    have hh := h (g * y * g⁻¹)
    calc y * z = g⁻¹ * ((g * y * g⁻¹) * (g * z * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * z * g⁻¹) * (g * y * g⁻¹)) * g := by rw [hh]
      _ = z * y := by group
  · intro h y
    calc y * (g * z * g⁻¹) = g * ((g⁻¹ * y * g) * z) * g⁻¹ := by group
      _ = g * (z * (g⁻¹ * y * g)) * g⁻¹ := by rw [h (g⁻¹ * y * g)]
      _ = (g * z * g⁻¹) * y := by group

private lemma orderOf_eq_six_of_pow_six {G : Type*} [Group G] {x : G} (h6 : x ^ 6 = 1)
    (h2 : x ^ 2 ≠ 1) (h3 : x ^ 3 ≠ 1) : orderOf x = 6 := by
  refine orderOf_eq_of_pow_and_pow_div_prime (n := 6) (by norm_num) h6 ?_
  intro p hp hp6
  have hp23 : p = 2 ∨ p = 3 := by
    have h : p ∣ 2 * 3 := by simpa using hp6
    rcases (Nat.Prime.dvd_mul hp).mp h with h2 | h3
    · left
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2
    · right
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3
  rcases hp23 with rfl | rfl
  · simpa using h3
  · simpa using h2

private lemma rank_two_normal_form {A : Matrix.SpecialLinearGroup ι K} (hA : A * A = 1)
    (hrank : 2 ≤ ((A : Matrix ι ι K) - 1).rank) :
    ∃ (k : ℕ) (u w : Fin k → ι) (g0 : Matrix.SpecialLinearGroup ι K),
      2 ≤ k ∧ Function.Injective u ∧ Function.Injective w ∧
        (∀ a b, u a ≠ w b) ∧
        ((g0 * A * g0⁻¹ : Matrix.SpecialLinearGroup ι K) : Matrix ι ι K) =
          1 + CFSG.SeitzReduction.LinearPilot.nilOf K u w := by
  obtain ⟨k, u, w, hu, hw, huw, g0, hg0⟩ :=
    CFSG.SeitzReduction.LinearPilot.exists_conj_eq_one_add_nilOf (K := K) hA
  have hk : 2 ≤ k := by
    have hA' : (A : Matrix ι ι K) * (A : Matrix ι ι K) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, hA, Matrix.SpecialLinearGroup.coe_one]
    have hunit : ∀ g : Matrix.SpecialLinearGroup ι K,
        IsUnit ((g : Matrix ι ι K).det) := fun g => by
      rw [g.2]
      exact isUnit_one
    have hgg : (g0 : Matrix ι ι K) * (((g0⁻¹ : Matrix.SpecialLinearGroup ι K)) :
        Matrix ι ι K) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.SpecialLinearGroup.coe_one]
    have hconj : ((g0 * A * g0⁻¹ : Matrix.SpecialLinearGroup ι K) : Matrix ι ι K) - 1 =
        (g0 : Matrix ι ι K) * ((A : Matrix ι ι K) - 1) *
          (((g0⁻¹ : Matrix.SpecialLinearGroup ι K)) : Matrix ι ι K) := by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, mul_sub,
        sub_mul, Matrix.mul_one, hgg]
    have hconjrank : ((g0 : Matrix ι ι K) * ((A : Matrix ι ι K) - 1) *
        (((g0⁻¹ : Matrix.SpecialLinearGroup ι K)) : Matrix ι ι K)).rank =
        ((A : Matrix ι ι K) - 1).rank := by
      rw [Matrix.rank_mul_eq_left_of_isUnit_det (((g0⁻¹ : Matrix.SpecialLinearGroup ι K)) :
          Matrix ι ι K) ((g0 : Matrix ι ι K) * ((A : Matrix ι ι K) - 1))
          (hunit (g0⁻¹)),
        Matrix.rank_mul_eq_right_of_isUnit_det (g0 : Matrix ι ι K)
          ((A : Matrix ι ι K) - 1) (hunit g0)]
    have hnil : ((g0 * A * g0⁻¹ : Matrix.SpecialLinearGroup ι K) : Matrix ι ι K) - 1 =
        CFSG.SeitzReduction.LinearPilot.nilOf K u w := by
      rw [hg0]
      abel
    have hk' : (CFSG.SeitzReduction.LinearPilot.nilOf K u w).rank = k :=
      CFSG.SeitzReduction.LinearPilot.rank_nilOf hu hw
    have hrank_eq : ((A : Matrix ι ι K) - 1).rank = k := by
      calc
        ((A : Matrix ι ι K) - 1).rank =
            ((g0 : Matrix ι ι K) * ((A : Matrix ι ι K) - 1) *
              (((g0⁻¹ : Matrix.SpecialLinearGroup ι K)) : Matrix ι ι K)).rank :=
              hconjrank.symm
        _ = (((g0 * A * g0⁻¹ : Matrix.SpecialLinearGroup ι K) : Matrix ι ι K) - 1).rank := by
              rw [hconj]
        _ = (CFSG.SeitzReduction.LinearPilot.nilOf K u w).rank := by rw [hnil]
        _ = k := hk'
    simpa [hrank_eq] using hrank
  exact ⟨k, u, w, g0, hk, hu, hw, huw, hg0⟩


private lemma exists_conj_eq_fourPoint {A : Matrix.SpecialLinearGroup ι K}
    {k : ℕ} {u w : Fin k → ι} {g0 : Matrix.SpecialLinearGroup ι K}
    (a0 a1 : Fin k) (ha01 : a0 ≠ a1) (hu : Function.Injective u)
    (hw : Function.Injective w) (huw : ∀ a b, u a ≠ w b)
    (hg0 : ((g0 * A * g0⁻¹ : Matrix.SpecialLinearGroup ι K) : Matrix ι ι K) =
      1 + CFSG.SeitzReduction.LinearPilot.nilOf K u w) :
    ∃ (g M : Matrix.SpecialLinearGroup ι K),
      M = g0 * (A * (g * A * g⁻¹)) * g0⁻¹ ∧
        (M : Matrix ι ι K) = P4[u a0, w a0, u a1, w a1] := by
  let a : ι := u a0
  let b : ι := w a0
  let c : ι := u a1
  let d : ι := w a1
  let σ : Equiv.Perm ι := Equiv.swap a d * Equiv.swap a c * Equiv.swap a b
  have hdet : (σ.permMatrix K).det = 1 := det_permMatrix_charTwo σ
  let P : Matrix.SpecialLinearGroup ι K := ⟨σ.permMatrix K, hdet⟩
  let s : Matrix.SpecialLinearGroup ι K := g0 * A * g0⁻¹
  let t : Matrix.SpecialLinearGroup ι K := P * s * P⁻¹
  let g : Matrix.SpecialLinearGroup ι K := g0⁻¹ * P * g0
  let x : Matrix.SpecialLinearGroup ι K := A * (g * A * g⁻¹)
  let M : Matrix.SpecialLinearGroup ι K := g0 * x * g0⁻¹
  have hs : (s : Matrix ι ι K) = 1 + CFSG.SeitzReduction.LinearPilot.nilOf K u w := by
    simpa only [s] using hg0
  have hP : (P : Matrix ι ι K) = σ.permMatrix K := rfl
  have hadj : (σ.permMatrix K).adjugate = (σ.permMatrix K)⁻¹ := by
    rw [Matrix.inv_def, hdet]
    simp
  have ht : (t : Matrix ι ι K) =
      (σ.permMatrix K) * (1 + CFSG.SeitzReduction.LinearPilot.nilOf K u w) *
        (σ.permMatrix K)⁻¹ := by
    dsimp only [t]
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hs, hP]
    rw [Matrix.SpecialLinearGroup.coe_inv, hP, hadj]
  have hconjNil := permMatrix_conj_nilOf (K := K) (u := u) (w := w) σ
  have hPP : (σ.permMatrix K) * (σ.permMatrix K)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ (by rw [hdet]; exact isUnit_one)
  have ht' : (t : Matrix ι ι K) = 1 +
      CFSG.SeitzReduction.LinearPilot.nilOf K (σ.symm ∘ u) (σ.symm ∘ w) := by
    rw [ht]
    calc
      (σ.permMatrix K) * (1 + CFSG.SeitzReduction.LinearPilot.nilOf K u w) *
          (σ.permMatrix K)⁻¹ =
          (σ.permMatrix K) * (σ.permMatrix K)⁻¹ +
            (σ.permMatrix K) * CFSG.SeitzReduction.LinearPilot.nilOf K u w *
              (σ.permMatrix K)⁻¹ := by noncomm_ring
      _ = 1 + (σ.permMatrix K) * CFSG.SeitzReduction.LinearPilot.nilOf K u w *
              (σ.permMatrix K)⁻¹ := by rw [hPP]
      _ = 1 + CFSG.SeitzReduction.LinearPilot.nilOf K (σ.symm ∘ u) (σ.symm ∘ w) := by
            rw [hconjNil]
  have hA' : A = g0⁻¹ * s * g0 := by
    dsimp only [s]
    group
  have hgA : g * A * g⁻¹ = g0⁻¹ * t * g0 := by
    rw [hA']
    dsimp only [g, t, s]
    group
  have hx : x = g0⁻¹ * (s * t) * g0 := by
    calc x = A * (g * A * g⁻¹) := rfl
      _ = (g0⁻¹ * s * g0) * (g0⁻¹ * t * g0) := by rw [hgA, hA']
      _ = g0⁻¹ * (s * t) * g0 := by group
  have hM : M = s * t := by
    calc M = g0 * x * g0⁻¹ := rfl
      _ = g0 * (g0⁻¹ * (s * t) * g0) * g0⁻¹ := by rw [hx]
      _ = s * t := by group
  have hMmat : (M : Matrix ι ι K) =
      1 + Matrix.single a b (1 : K) + Matrix.single c d (1 : K) +
        Matrix.single d a (1 : K) + Matrix.single b c (1 : K) +
        Matrix.single a c (1 : K) + Matrix.single c a (1 : K) := by
    rw [hM, Matrix.SpecialLinearGroup.coe_mul, hs, ht']
    simpa only [a, b, c, d] using
      (mul_conj_eq_fourPoint (K := K) (u := u) (w := w) a0 a1 ha01 hu hw huw)
  exact ⟨g, M, by dsimp only [M, x], hMmat⟩

private lemma order_center_of_fourPoint {g0 x M : Matrix.SpecialLinearGroup ι K}
    {a b c d : ι} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d)
    (hMdef : M = g0 * x * g0⁻¹) (hxM : SemiconjBy g0 x M)
    (hMmat : (M : Matrix ι ι K) = P4[a, b, c, d]) :
    orderOf x = 6 ∧ x ^ 2 ∉ Subgroup.center (Matrix.SpecialLinearGroup ι K) := by
  have hMsix : M ^ 6 = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, hMmat, Matrix.SpecialLinearGroup.coe_one]
    exact fourPointMatrix_pow_six (K := K) a b c d hab hac had hbc hbd hcd
  have hMsq : M ^ 2 ≠ 1 := by
    intro h
    apply fourPointMatrix_sq_ne_one (K := K) a b c d hab hac had hbc hbd hcd
    rw [← hMmat, ← Matrix.SpecialLinearGroup.coe_pow, h, Matrix.SpecialLinearGroup.coe_one]
  have hMcube : M ^ 3 ≠ 1 := by
    intro h
    apply fourPointMatrix_cube_ne_one (K := K) a b c d hab hac had hbc hbd hcd
    rw [← hMmat, ← Matrix.SpecialLinearGroup.coe_pow, h, Matrix.SpecialLinearGroup.coe_one]
  have hMorder : orderOf M = 6 := orderOf_eq_six_of_pow_six hMsix hMsq hMcube
  have hxorder : orderOf x = 6 := (SemiconjBy.orderOf_eq g0 hxM).trans hMorder
  have hMsq_not_center : M ^ 2 ∉ Subgroup.center (Matrix.SpecialLinearGroup ι K) := by
    intro hc
    obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hc
    apply fourPointMatrix_sq_not_scalar (K := K) a b c d hab hac had hbc hbd hcd r
    rw [← hMmat]
    calc
      Matrix.scalar ι r = ((M ^ 2 : Matrix.SpecialLinearGroup ι K) : Matrix ι ι K) := hr
      _ = (M : Matrix ι ι K) ^ 2 := by rw [Matrix.SpecialLinearGroup.coe_pow]
  have hxsq_not_center : x ^ 2 ∉ Subgroup.center (Matrix.SpecialLinearGroup ι K) := by
    intro hc
    apply hMsq_not_center
    have hM2 : M ^ 2 = g0 * x ^ 2 * g0⁻¹ := by
      rw [hMdef, pow_two, pow_two]
      group
    rw [hM2]
    exact (mem_center_conj_iff g0 (x ^ 2)).mpr hc
  exact ⟨hxorder, hxsq_not_center⟩


theorem exists_conj_orderOf_mul_eq_six {A : Matrix.SpecialLinearGroup ι K} (hA : A * A = 1)
    (hrank : 2 ≤ ((A : Matrix ι ι K) - 1).rank) :
    ∃ g : Matrix.SpecialLinearGroup ι K, orderOf (A * (g * A * g⁻¹)) = 6 ∧
      (A * (g * A * g⁻¹)) ^ 2 ∉ Subgroup.center (Matrix.SpecialLinearGroup ι K) := by
  classical
  obtain ⟨k, u, w, g0, hk, hu, hw, huw, hg0⟩ := rank_two_normal_form hA hrank
  let a0 : Fin k := ⟨0, by omega⟩
  let a1 : Fin k := ⟨1, by omega⟩
  have ha01 : a0 ≠ a1 := by
    intro h
    have := congrArg Fin.val h
    simp [a0, a1] at this
  obtain ⟨g, M, hMdef, hMmat⟩ :=
    exists_conj_eq_fourPoint (A := A) a0 a1 ha01 hu hw huw hg0
  let a : ι := u a0
  let b : ι := w a0
  let c : ι := u a1
  let d : ι := w a1
  have hab : a ≠ b := huw a0 a0
  have hac : a ≠ c := hu.ne ha01
  have had : a ≠ d := huw a0 a1
  have hbc : b ≠ c := (huw a1 a0).symm
  have hbd : b ≠ d := hw.ne ha01
  have hcd : c ≠ d := huw a1 a1
  let x : Matrix.SpecialLinearGroup ι K := A * (g * A * g⁻¹)
  have hxM : SemiconjBy g0 x M := by
    rw [hMdef]
    change g0 * x = (g0 * x * g0⁻¹) * g0
    group
  have hMmat' : (M : Matrix ι ι K) = P4[a, b, c, d] := by
    dsimp only [a, b, c, d]
    exact hMmat
  obtain ⟨hord, hsq⟩ :=
    order_center_of_fourPoint (g0 := g0) (x := x) (M := M) hab hac had hbc hbd hcd hMdef hxM hMmat'
  exact ⟨g, hord, hsq⟩


end Main

section Transvection

variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharP K 2]

open CFSG.SeitzReduction.LinearPilot

theorem exists_vecMulVec_of_mul_self_eq_one_of_rank_le_one {A : Matrix.SpecialLinearGroup ι K}
    (hA : A * A = 1) (hrank : ((A : Matrix ι ι K) - 1).rank ≤ 1) :
    ∃ v w : ι → K, (A : Matrix ι ι K) = 1 + Matrix.vecMulVec v w ∧ w ⬝ᵥ v = 0 := by
  classical
  obtain ⟨v, w, hNvec⟩ :=
    CFSG.Quasithin.H13.L829NK.exists_vecMulVec_of_rank_le_one
      ((A : Matrix ι ι K) - 1) hrank
  have hA' : (A : Matrix ι ι K) * (A : Matrix ι ι K) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, hA, Matrix.SpecialLinearGroup.coe_one]
  have hN2 : ((A : Matrix ι ι K) - 1) * ((A : Matrix ι ι K) - 1) = 0 :=
    CFSG.SeitzReduction.LinearPilot.sub_one_mul_sub_one_eq_zero_of_mul_self hA'
  have hdot : (w ⬝ᵥ v) • Matrix.vecMulVec v w = 0 := by
    rw [← Matrix.vecMulVec_smul, ← Matrix.vecMulVec_mul_vecMulVec, ← hNvec, hN2]
  have hAdecomp : (A : Matrix ι ι K) = 1 + ((A : Matrix ι ι K) - 1) := by
    rw [add_comm, sub_add_cancel]
  by_cases hzero : Matrix.vecMulVec v w = 0
  · refine ⟨0, 0, ?_, by simp⟩
    rw [hAdecomp, hNvec, hzero]
    simp
  · have hwv : w ⬝ᵥ v = 0 := (smul_eq_zero.mp hdot).resolve_right hzero
    refine ⟨v, w, ?_, hwv⟩
    rw [hAdecomp, hNvec]

end Transvection

section Quotient

variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K] [Finite K] [CharP K 2]

local notation "P4[" a ", " b ", " c ", " d "]" => (1 + Matrix.single a b (1 : K) +
  Matrix.single c d (1 : K) + Matrix.single d a (1 : K) + Matrix.single b c (1 : K) +
  Matrix.single a c (1 : K) + Matrix.single c a (1 : K) : Matrix ι ι K)

open CFSG.SeitzReduction.LinearPilot

private lemma eq_one_of_mem_center_of_sq_eq_one [Nonempty ι]
    {z : Matrix.SpecialLinearGroup ι K}
    (hz : z ∈ Subgroup.center (Matrix.SpecialLinearGroup ι K)) (hz2 : z ^ 2 = 1) : z = 1 := by
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hz
  have hsq : (Matrix.scalar ι r) ^ 2 = 1 := by
    rw [hr, ← Matrix.SpecialLinearGroup.coe_pow, hz2, Matrix.SpecialLinearGroup.coe_one]
  have hr2 : r ^ 2 = 1 := by
    have h : Matrix.scalar ι (r ^ 2) = Matrix.scalar ι (1 : K) := by
      rw [map_pow, hsq, map_one]
    exact (Matrix.scalar_inj).mp h
  have hr1 : r = 1 := by
    rcases sq_eq_one_iff.mp hr2 with h | h
    · exact h
    · rwa [CharTwo.neg_eq] at h
  apply Subtype.ext
  rw [← hr, hr1, map_one, Matrix.SpecialLinearGroup.coe_one]

theorem vecMulVec_or_exists_conj_orderOf_mk_mul_eq_six {A : Matrix.SpecialLinearGroup ι K}
    (hA : A * A = 1) :
    (∃ v w : ι → K, (A : Matrix ι ι K) = 1 + Matrix.vecMulVec v w ∧ w ⬝ᵥ v = 0) ∨
      ∃ g : Matrix.SpecialLinearGroup ι K, ∀ (C : Subgroup (Matrix.SpecialLinearGroup ι K))
        [C.Normal], C ≤ Subgroup.center (Matrix.SpecialLinearGroup ι K) →
          orderOf (QuotientGroup.mk (A * (g * A * g⁻¹)) :
            Matrix.SpecialLinearGroup ι K ⧸ C) = 6 := by
  by_cases hrank : ((A : Matrix ι ι K) - 1).rank ≤ 1
  · left
    exact exists_vecMulVec_of_mul_self_eq_one_of_rank_le_one hA hrank
  · right
    have hrank2 : 2 ≤ ((A : Matrix ι ι K) - 1).rank := by omega
    obtain ⟨g, hord, hsq⟩ := exists_conj_orderOf_mul_eq_six hA hrank2
    refine ⟨g, ?_⟩
    intro C hCnorm hCle
    let x : Matrix.SpecialLinearGroup ι K := A * (g * A * g⁻¹)
    have hx6 : x ^ 6 = 1 := by
      rw [← hord, pow_orderOf_eq_one]
    have hx2 : x ^ 2 ∉ C := fun h => hsq (hCle h)
    have hx3 : x ^ 3 ∉ C := by
      intro h
      haveI : Nonempty ι := by
        apply Fintype.card_pos_iff.mp
        have hle := Matrix.rank_le_card_height ((A : Matrix ι ι K) - 1)
        omega
      have hz_center : x ^ 3 ∈ Subgroup.center (Matrix.SpecialLinearGroup ι K) := hCle h
      have h3dvd : 3 ∣ orderOf x := by rw [hord]; norm_num
      have hz_order : orderOf (x ^ 3) = 2 := by
        rw [orderOf_pow_of_dvd (by norm_num : 3 ≠ 0) h3dvd, hord]
      have hz2 : (x ^ 3) ^ 2 = 1 := by
        rw [← hz_order, pow_orderOf_eq_one]
      have hz1 : x ^ 3 = 1 := eq_one_of_mem_center_of_sq_eq_one hz_center hz2
      rw [hz1, orderOf_one] at hz_order
      omega
    let q : Matrix.SpecialLinearGroup ι K ⧸ C := QuotientGroup.mk x
    have hq6 : q ^ 6 = 1 := by
      change ((QuotientGroup.mk' C) x) ^ 6 = 1
      rw [← map_pow, hx6, map_one]
    have hq2 : q ^ 2 ≠ 1 := by
      intro h
      apply hx2
      have hmem : ((QuotientGroup.mk' C) (x ^ 2)) = 1 := by
        rw [map_pow]
        simpa only [q, QuotientGroup.coe_mk'] using h
      exact (QuotientGroup.eq_one_iff (x ^ 2)).mp hmem
    have hq3 : q ^ 3 ≠ 1 := by
      intro h
      apply hx3
      have hmem : ((QuotientGroup.mk' C) (x ^ 3)) = 1 := by
        rw [map_pow]
        simpa only [q, QuotientGroup.coe_mk'] using h
      exact (QuotientGroup.eq_one_iff (x ^ 3)).mp hmem
    have hqorder : orderOf q = 6 := orderOf_eq_six_of_pow_six hq6 hq2 hq3
    simpa only [q, x] using hqorder

end Quotient

