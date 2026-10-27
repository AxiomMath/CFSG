module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Cardinality
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.PSL2Table

open Matrix
open scoped MatrixGroups

section Matrices

variable {F : Type} [Field F]

@[expose] def unip (t : F) : SL(2, F) :=
  ⟨!![1, t; 0, 1], by simp [Matrix.det_fin_two_of]⟩

@[expose] def diag (a : Fˣ) : SL(2, F) :=
  ⟨!![(a : F), 0; 0, (a : F)⁻¹], by simp [Matrix.det_fin_two_of]⟩

@[expose] def weyl : SL(2, F) :=
  ⟨!![0, -1; 1, 0], by simp [Matrix.det_fin_two_of]⟩

@[expose] def nsElem (ν x y : F) (h : x ^ 2 - ν * y ^ 2 = 1) : SL(2, F) :=
  ⟨!![x, ν * y; y, x], by rw [Matrix.det_fin_two_of, ← h]; ring⟩

@[simp] theorem coe_unip (t : F) : (unip t : Matrix (Fin 2) (Fin 2) F) = !![1, t; 0, 1] := rfl

@[simp] theorem coe_diag (a : Fˣ) :
    (diag a : Matrix (Fin 2) (Fin 2) F) = !![(a : F), 0; 0, (a : F)⁻¹] := rfl

@[simp] theorem coe_weyl : ((weyl : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![0, -1; 1, 0] :=
  rfl

@[simp] theorem coe_nsElem (ν x y : F) (h : x ^ 2 - ν * y ^ 2 = 1) :
    (nsElem ν x y h : Matrix (Fin 2) (Fin 2) F) = !![x, ν * y; y, x] := rfl

theorem coe_inv_SL (A : SL(2, F)) :
    ((A⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
      !![(A : Matrix (Fin 2) (Fin 2) F) 1 1, -(A : Matrix (Fin 2) (Fin 2) F) 0 1;
        -(A : Matrix (Fin 2) (Fin 2) F) 1 0, (A : Matrix (Fin 2) (Fin 2) F) 0 0] := by
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  rfl

theorem det_entries (A : SL(2, F)) :
    (A : Matrix (Fin 2) (Fin 2) F) 0 0 * (A : Matrix (Fin 2) (Fin 2) F) 1 1 -
      (A : Matrix (Fin 2) (Fin 2) F) 0 1 * (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 1 := by
  have h := A.2
  rw [Matrix.det_fin_two] at h
  exact h

theorem mul_apply_SL (A B : SL(2, F)) (i j : Fin 2) :
    ((A * B : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) i j =
      (A : Matrix (Fin 2) (Fin 2) F) i 0 * (B : Matrix (Fin 2) (Fin 2) F) 0 j +
        (A : Matrix (Fin 2) (Fin 2) F) i 1 * (B : Matrix (Fin 2) (Fin 2) F) 1 j := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

theorem neg_apply_SL (A : SL(2, F)) (i j : Fin 2) :
    ((-A : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) i j = -(A : Matrix (Fin 2) (Fin 2) F) i j := by
  rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply]

theorem SL_ext {A B : SL(2, F)}
    (h00 : (A : Matrix (Fin 2) (Fin 2) F) 0 0 = (B : Matrix (Fin 2) (Fin 2) F) 0 0)
    (h01 : (A : Matrix (Fin 2) (Fin 2) F) 0 1 = (B : Matrix (Fin 2) (Fin 2) F) 0 1)
    (h10 : (A : Matrix (Fin 2) (Fin 2) F) 1 0 = (B : Matrix (Fin 2) (Fin 2) F) 1 0)
    (h11 : (A : Matrix (Fin 2) (Fin 2) F) 1 1 = (B : Matrix (Fin 2) (Fin 2) F) 1 1) : A = B := by
  ext i j
  fin_cases i <;> fin_cases j <;> assumption

theorem unip_add (s t : F) : unip (s + t) = unip s * unip t := by
  apply SL_ext <;> simp [mul_apply_SL] ; ring

theorem unip_zero : unip (0 : F) = 1 := by
  apply SL_ext <;> simp

theorem unip_neg (t : F) : (unip t)⁻¹ = unip (-t) := by
  apply SL_ext <;> simp [Matrix.adjugate_fin_two]

theorem diag_mul (a b : Fˣ) : diag (a * b) = diag a * diag b := by
  apply SL_ext <;> simp [mul_apply_SL, mul_comm]

theorem diag_one : diag (1 : Fˣ) = 1 := by
  apply SL_ext <;> simp

theorem diag_inv (a : Fˣ) : (diag a)⁻¹ = diag a⁻¹ := by
  apply SL_ext <;> simp [Matrix.adjugate_fin_two]

theorem diag_neg_one : diag (-1 : Fˣ) = -1 := by
  apply SL_ext <;> simp [neg_apply_SL]

theorem diag_conj_unip (a : Fˣ) (t : F) :
    diag a * unip t * (diag a)⁻¹ = unip ((a : F) ^ 2 * t) := by
  apply SL_ext <;> simp [mul_apply_SL, Matrix.adjugate_fin_two] ; ring

theorem weyl_conj_diag (a : Fˣ) : weyl * diag a * weyl⁻¹ = diag a⁻¹ := by
  apply SL_ext <;> simp [mul_apply_SL, Matrix.adjugate_fin_two]

theorem weyl_sq : weyl * weyl = (-1 : SL(2, F)) := by
  apply SL_ext <;> simp [mul_apply_SL, neg_apply_SL]

end Matrices

section Center

variable {F : Type} [Field F]

theorem mem_center_SL_iff (A : SL(2, F)) :
    A ∈ Subgroup.center SL(2, F) ↔ A = 1 ∨ A = -1 := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  constructor
  · rintro ⟨r, hr, hA⟩
    rw [Fintype.card_fin, sq] at hr
    rcases mul_self_eq_one_iff.mp hr with rfl | rfl
    · left
      ext i j
      rw [← hA]
      simp
    · right
      ext i j
      rw [← hA, Matrix.SpecialLinearGroup.coe_neg]
      fin_cases i <;> fin_cases j <;> simp
  · rintro (rfl | rfl)
    · exact ⟨1, by simp, by simp⟩
    · refine ⟨-1, by simp, ?_⟩
      rw [Matrix.SpecialLinearGroup.coe_neg]
      ext i j
      fin_cases i <;> fin_cases j <;> simp

theorem neg_one_mem_center : (-1 : SL(2, F)) ∈ Subgroup.center SL(2, F) :=
  (mem_center_SL_iff _).mpr (Or.inr rfl)

@[expose] def mk : SL(2, F) →* PSL(2, F) :=
  QuotientGroup.mk' (Subgroup.center SL(2, F))

theorem mk_surjective : Function.Surjective (mk : SL(2, F) →* PSL(2, F)) :=
  QuotientGroup.mk'_surjective _

theorem mk_eq_mk_iff (A B : SL(2, F)) : mk A = mk B ↔ B = A ∨ B = -A := by
  rw [mk, QuotientGroup.mk'_eq_mk']
  constructor
  · rintro ⟨z, hz, rfl⟩
    rcases (mem_center_SL_iff z).mp hz with rfl | rfl
    · left
      rw [mul_one]
    · right
      rw [mul_neg, mul_one]
  · rintro (rfl | rfl)
    · exact ⟨1, Subgroup.one_mem _, mul_one _⟩
    · exact ⟨-1, neg_one_mem_center, by rw [mul_neg, mul_one]⟩

theorem mk_neg (A : SL(2, F)) : mk (-A) = mk A :=
  ((mk_eq_mk_iff A (-A)).mpr (Or.inr rfl)).symm

theorem mk_eq_one_iff (A : SL(2, F)) : mk A = 1 ↔ A = 1 ∨ A = -1 := by
  rw [← (mk : SL(2, F) →* PSL(2, F)).map_one, mk_eq_mk_iff]
  constructor
  · rintro (h | h)
    · exact Or.inl h.symm
    · right
      rw [h, neg_neg]
  · rintro (h | h)
    · exact Or.inl h.symm
    · right
      rw [h, neg_neg]

theorem mk_mem_map_iff (H : Subgroup SL(2, F)) (A : SL(2, F)) :
    mk A ∈ H.map mk ↔ A ∈ H ∨ -A ∈ H := by
  constructor
  · rintro ⟨B, hB, hBA⟩
    rcases (mk_eq_mk_iff B A).mp hBA with rfl | rfl
    · exact Or.inl hB
    · right
      rwa [neg_neg]
  · rintro (h | h)
    · exact ⟨A, h, rfl⟩
    · exact ⟨-A, h, mk_neg A⟩

theorem mk_mem_map_iff_of_neg (H : Subgroup SL(2, F)) (hH : ∀ A ∈ H, -A ∈ H) (A : SL(2, F)) :
    mk A ∈ H.map mk ↔ A ∈ H := by
  rw [mk_mem_map_iff]
  constructor
  · rintro (h | h)
    · exact h
    · simpa using hH _ h
  · exact Or.inl

end Center

section Subgroups

variable {F : Type} [Field F]

@[expose] def splitSL (F : Type) [Field F] : Subgroup SL(2, F) where
  carrier := {A | (A : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 ∧ (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0}
  mul_mem' := by
    rintro A B ⟨hA1, hA2⟩ ⟨hB1, hB2⟩
    exact ⟨by simp [mul_apply_SL, hA1, hB1], by simp [mul_apply_SL, hA2, hB2]⟩
  one_mem' := ⟨by simp, by simp⟩
  inv_mem' := by
    rintro A ⟨h1, h2⟩
    exact ⟨by simp [Matrix.adjugate_fin_two, h1], by simp [Matrix.adjugate_fin_two, h2]⟩

@[expose] def nonsplitSL (ν : F) : Subgroup SL(2, F) where
  carrier := {A | (A : Matrix (Fin 2) (Fin 2) F) 1 1 = (A : Matrix (Fin 2) (Fin 2) F) 0 0 ∧
    (A : Matrix (Fin 2) (Fin 2) F) 0 1 = ν * (A : Matrix (Fin 2) (Fin 2) F) 1 0}
  mul_mem' := by
    rintro A B ⟨hA1, hA2⟩ ⟨hB1, hB2⟩
    refine ⟨?_, ?_⟩
    · simp only [mul_apply_SL, hA1, hA2, hB1, hB2]
      ring
    · simp only [mul_apply_SL, hA1, hA2, hB1, hB2]
      ring
  one_mem' := ⟨by simp, by simp⟩
  inv_mem' := by
    rintro A ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · simp [Matrix.adjugate_fin_two, h1]
    · simp [Matrix.adjugate_fin_two, h2]

@[expose] def unipSL (F : Type) [Field F] : Subgroup SL(2, F) where
  carrier := {A | (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 ∧ (A : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 ∧
    (A : Matrix (Fin 2) (Fin 2) F) 1 1 = 1}
  mul_mem' := by
    rintro A B ⟨hA1, hA2, hA3⟩ ⟨hB1, hB2, hB3⟩
    exact ⟨by simp [mul_apply_SL, hA1, hA3, hB1], by simp [mul_apply_SL, hA2, hB1, hB2],
      by simp [mul_apply_SL, hA1, hA3, hB3]⟩
  one_mem' := ⟨by simp, by simp, by simp⟩
  inv_mem' := by
    rintro A ⟨h1, h2, h3⟩
    exact ⟨by simp [Matrix.adjugate_fin_two, h1], by simp [Matrix.adjugate_fin_two, h3],
      by simp [Matrix.adjugate_fin_two, h2]⟩

@[expose] def borelSL (F : Type) [Field F] : Subgroup SL(2, F) where
  carrier := {A | (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0}
  mul_mem' := by
    intro A B hA hB
    change (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 at hA
    change (B : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 at hB
    change ((A * B : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
    simp [mul_apply_SL, hA, hB]
  one_mem' := by
    change ((1 : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
    simp
  inv_mem' := by
    intro A hA
    change (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 at hA
    change ((A⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
    simp [Matrix.adjugate_fin_two, hA]

theorem mem_splitSL_iff (A : SL(2, F)) :
    A ∈ splitSL F ↔
      (A : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 ∧ (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 :=
  Iff.rfl

theorem mem_nonsplitSL_iff (ν : F) (A : SL(2, F)) :
    A ∈ nonsplitSL ν ↔ (A : Matrix (Fin 2) (Fin 2) F) 1 1 = (A : Matrix (Fin 2) (Fin 2) F) 0 0 ∧
      (A : Matrix (Fin 2) (Fin 2) F) 0 1 = ν * (A : Matrix (Fin 2) (Fin 2) F) 1 0 :=
  Iff.rfl

theorem mem_unipSL_iff (A : SL(2, F)) :
    A ∈ unipSL F ↔ (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 ∧
      (A : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 ∧ (A : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 :=
  Iff.rfl

theorem mem_borelSL_iff (A : SL(2, F)) :
    A ∈ borelSL F ↔ (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 :=
  Iff.rfl

theorem neg_mem_splitSL {A : SL(2, F)} (h : A ∈ splitSL F) : -A ∈ splitSL F := by
  rw [mem_splitSL_iff] at h ⊢
  simp [neg_apply_SL, h.1, h.2]

theorem neg_mem_nonsplitSL (ν : F) {A : SL(2, F)} (h : A ∈ nonsplitSL ν) :
    -A ∈ nonsplitSL ν := by
  rw [mem_nonsplitSL_iff] at h ⊢
  simp [neg_apply_SL, h.1, h.2]

theorem neg_mem_borelSL {A : SL(2, F)} (h : A ∈ borelSL F) : -A ∈ borelSL F := by
  rw [mem_borelSL_iff] at h ⊢
  simp [neg_apply_SL, h]

theorem diag_mem_splitSL (a : Fˣ) : diag a ∈ splitSL F := ⟨by simp, by simp⟩

theorem unip_mem_unipSL (t : F) : unip t ∈ unipSL F := ⟨by simp, by simp, by simp⟩

theorem nsElem_mem_nonsplitSL (ν x y : F) (h : x ^ 2 - ν * y ^ 2 = 1) :
    nsElem ν x y h ∈ nonsplitSL ν := ⟨by simp, by simp⟩

@[expose] def splitTorus (F : Type) [Field F] : Subgroup PSL(2, F) := (splitSL F).map mk

@[expose] def nonsplitTorus (ν : F) : Subgroup PSL(2, F) := (nonsplitSL ν).map mk

@[expose] def unipotent (F : Type) [Field F] : Subgroup PSL(2, F) := (unipSL F).map mk

@[expose] def borel (F : Type) [Field F] : Subgroup PSL(2, F) := (borelSL F).map mk

noncomputable instance decidableMemSplitTorus : DecidablePred (· ∈ splitTorus F) :=
  Classical.decPred _

noncomputable instance decidableMemNonsplitTorus (ν : F) : DecidablePred (· ∈ nonsplitTorus ν) :=
  Classical.decPred _

noncomputable instance decidableMemUnipotent : DecidablePred (· ∈ unipotent F) :=
  Classical.decPred _

noncomputable instance decidableMemBorel : DecidablePred (· ∈ borel F) :=
  Classical.decPred _

theorem mk_mem_splitTorus_iff (A : SL(2, F)) : mk A ∈ splitTorus F ↔ A ∈ splitSL F :=
  mk_mem_map_iff_of_neg _ (fun _ h => neg_mem_splitSL h) A

theorem mk_mem_nonsplitTorus_iff (ν : F) (A : SL(2, F)) :
    mk A ∈ nonsplitTorus ν ↔ A ∈ nonsplitSL ν :=
  mk_mem_map_iff_of_neg _ (fun _ h => neg_mem_nonsplitSL ν h) A

theorem mk_mem_borel_iff (A : SL(2, F)) : mk A ∈ borel F ↔ A ∈ borelSL F :=
  mk_mem_map_iff_of_neg _ (fun _ h => neg_mem_borelSL h) A

theorem mk_mem_unipotent_iff (A : SL(2, F)) :
    mk A ∈ unipotent F ↔ (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 ∧
      (A : Matrix (Fin 2) (Fin 2) F) 0 0 = (A : Matrix (Fin 2) (Fin 2) F) 1 1 := by
  rw [unipotent, mk_mem_map_iff, mem_unipSL_iff, mem_unipSL_iff]
  simp only [neg_apply_SL]
  constructor
  · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
    · exact ⟨h1, h2.trans h3.symm⟩
    · refine ⟨neg_eq_zero.mp h1, ?_⟩
      rw [neg_eq_iff_eq_neg.mp h2, neg_eq_iff_eq_neg.mp h3]
  · rintro ⟨h1, h2⟩
    have hdet := det_entries A
    rw [h1, mul_zero, sub_zero, h2] at hdet
    rcases mul_self_eq_one_iff.mp hdet with h | h
    · exact Or.inl ⟨h1, h2.trans h, h⟩
    · exact Or.inr ⟨by rw [h1, neg_zero], by rw [h2, h, neg_neg], by rw [h, neg_neg]⟩

theorem mk_unip_mem_unipotent (t : F) : mk (unip t) ∈ unipotent F :=
  ⟨unip t, unip_mem_unipSL t, rfl⟩

theorem mk_diag_mem_splitTorus (a : Fˣ) : mk (diag a) ∈ splitTorus F :=
  ⟨diag a, diag_mem_splitSL a, rfl⟩

end Subgroups

section NormForm

open Polynomial

variable {F : Type} [Field F]

theorem normForm_mul (ν a b x y : F) :
    (a * x + ν * b * y) ^ 2 - ν * (a * y + b * x) ^ 2 =
      (a ^ 2 - ν * b ^ 2) * (x ^ 2 - ν * y ^ 2) := by ring

theorem ne_zero_of_not_isSquare {ν : F} (hν : ¬ IsSquare ν) : ν ≠ 0 :=
  fun h => hν ⟨0, by rw [h, mul_zero]⟩

theorem normForm_eq_zero {ν : F} (hν : ¬ IsSquare ν) {x y : F} (h : x ^ 2 - ν * y ^ 2 = 0) :
    x = 0 ∧ y = 0 := by
  by_cases hy : y = 0
  · subst hy
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, sub_zero,
      pow_eq_zero_iff] at h
    exact ⟨h, rfl⟩
  · exfalso
    apply hν
    refine ⟨x / y, ?_⟩
    field_simp
    linear_combination -h

variable [Fintype F]

theorem exists_normForm_eq (hF : ringChar F ≠ 2) {ν : F} (hν : ν ≠ 0) (c : F) :
    ∃ x y : F, x ^ 2 - ν * y ^ 2 = c := by
  have hf : (X ^ 2 - C c : F[X]).degree = 2 := by
    rw [degree_sub_C (by rw [degree_X_pow]; norm_num), degree_X_pow]; rfl
  have hg : (-(C ν) * X ^ 2 : F[X]).degree = 2 := by
    rw [neg_mul, degree_neg, degree_C_mul_X_pow 2 hν]; rfl
  obtain ⟨a, b, h⟩ := FiniteField.exists_root_sum_quadratic hf hg
    (FiniteField.odd_card_of_char_ne_two hF)
  refine ⟨a, b, ?_⟩
  simp only [eval_sub, eval_pow, eval_X, eval_C, eval_mul, eval_neg] at h
  linear_combination h

variable [DecidableEq F]

theorem card_normForm_fiber (hF : ringChar F ≠ 2) {ν : F} (hν0 : ν ≠ 0) {c : F} (hc : c ≠ 0) :
    (Finset.univ.filter (fun v : F × F => v.1 ^ 2 - ν * v.2 ^ 2 = c)).card =
      (Finset.univ.filter (fun v : F × F => v.1 ^ 2 - ν * v.2 ^ 2 = 1)).card := by
  obtain ⟨x, y, hxy⟩ := exists_normForm_eq hF hν0 c
  symm
  refine Finset.card_nbij' (fun v => (v.1 * x + ν * v.2 * y, v.1 * y + v.2 * x))
    (fun w => ((w.1 * x - ν * w.2 * y) / c, (w.2 * x - w.1 * y) / c)) ?_ ?_ ?_ ?_
  · intro v hv
    simp only [Finset.coe_filter, Finset.mem_univ, true_and] at hv ⊢
    change v.1 ^ 2 - ν * v.2 ^ 2 = 1 at hv
    change (v.1 * x + ν * v.2 * y) ^ 2 - ν * (v.1 * y + v.2 * x) ^ 2 = c
    rw [normForm_mul, hv, hxy, one_mul]
  · intro w hw
    simp only [Finset.coe_filter, Finset.mem_univ, true_and] at hw ⊢
    change w.1 ^ 2 - ν * w.2 ^ 2 = c at hw
    change ((w.1 * x - ν * w.2 * y) / c) ^ 2 - ν * ((w.2 * x - w.1 * y) / c) ^ 2 = 1
    calc ((w.1 * x - ν * w.2 * y) / c) ^ 2 - ν * ((w.2 * x - w.1 * y) / c) ^ 2
        = ((w.1 ^ 2 - ν * w.2 ^ 2) * (x ^ 2 - ν * y ^ 2)) / c ^ 2 := by
          field_simp
          ring
      _ = 1 := by
          rw [hw, hxy]
          field_simp
  · intro v hv
    simp only
    ext
    · change (((v.1 * x + ν * v.2 * y) * x - ν * (v.1 * y + v.2 * x) * y) / c) = v.1
      rw [show (v.1 * x + ν * v.2 * y) * x - ν * (v.1 * y + v.2 * x) * y =
        v.1 * (x ^ 2 - ν * y ^ 2) by ring, hxy]
      field_simp
    · change (((v.1 * y + v.2 * x) * x - (v.1 * x + ν * v.2 * y) * y) / c) = v.2
      rw [show (v.1 * y + v.2 * x) * x - (v.1 * x + ν * v.2 * y) * y =
        v.2 * (x ^ 2 - ν * y ^ 2) by ring, hxy]
      field_simp
  · intro w hw
    simp only
    ext
    · change (w.1 * x - ν * w.2 * y) / c * x + ν * ((w.2 * x - w.1 * y) / c) * y = w.1
      rw [show (w.1 * x - ν * w.2 * y) / c * x + ν * ((w.2 * x - w.1 * y) / c) * y =
        w.1 * (x ^ 2 - ν * y ^ 2) / c by ring, hxy]
      field_simp
    · change (w.1 * x - ν * w.2 * y) / c * y + (w.2 * x - w.1 * y) / c * x = w.2
      rw [show (w.1 * x - ν * w.2 * y) / c * y + (w.2 * x - w.1 * y) / c * x =
        w.2 * (x ^ 2 - ν * y ^ 2) / c by ring, hxy]
      field_simp

theorem card_normForm_one (hF : ringChar F ≠ 2) {ν : F} (hν : ¬ IsSquare ν) :
    (Finset.univ.filter (fun v : F × F => v.1 ^ 2 - ν * v.2 ^ 2 = 1)).card =
      Fintype.card F + 1 := by
  have hν0 : ν ≠ 0 := fun h => hν ⟨0, by rw [h, mul_zero]⟩
  set n := (Finset.univ.filter (fun v : F × F => v.1 ^ 2 - ν * v.2 ^ 2 = 1)).card with hn
  have hsum := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (F × F)))
    (t := (Finset.univ : Finset F)) (f := fun v : F × F => v.1 ^ 2 - ν * v.2 ^ 2)
    (fun _ _ => Finset.mem_univ _)
  have hzero : (Finset.univ.filter (fun v : F × F => v.1 ^ 2 - ν * v.2 ^ 2 = 0)).card = 1 := by
    rw [Finset.card_eq_one]
    refine ⟨(0, 0), ?_⟩
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h
      obtain ⟨h1, h2⟩ := normForm_eq_zero hν h
      exact Prod.ext h1 h2
    · rintro rfl
      simp
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : F)), hzero,
    Finset.sum_congr rfl (fun c hc => card_normForm_fiber hF hν0 (Finset.ne_of_mem_erase hc)),
    Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    Finset.card_univ, Fintype.card_prod, smul_eq_mul] at hsum
  rw [← hn] at hsum
  have hq : 2 ≤ Fintype.card F := Fintype.one_lt_card
  have key : (Fintype.card F - 1) * (Fintype.card F + 1) = (Fintype.card F - 1) * n := by
    have h1 : Fintype.card F * Fintype.card F =
        (Fintype.card F - 1) * (Fintype.card F + 1) + 1 := by
      obtain ⟨k, hk⟩ : ∃ k, Fintype.card F = k + 1 := ⟨Fintype.card F - 1, by omega⟩
      rw [hk]; simp; ring
    omega
  exact (Nat.eq_of_mul_eq_mul_left (by omega) key).symm


end NormForm

section Card

variable {F : Type} [Field F]

theorem neg_one_ne_one_SL (h2 : (2 : F) ≠ 0) : (-1 : SL(2, F)) ≠ 1 := by
  intro h
  have h00 := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 0) h
  simp only [neg_apply_SL, Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply_eq] at h00
  apply h2
  linear_combination -h00

theorem card_map_mk (h2 : (2 : F) ≠ 0) (H : Subgroup SL(2, F)) (hH : (-1 : SL(2, F)) ∈ H) :
    Nat.card (H.map mk) * 2 = Nat.card H := by
  let f : H →* PSL(2, F) := mk.comp H.subtype
  have hrange : f.range = H.map mk := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hker : Nat.card f.ker = 2 := by
    have hmem : ⟨-1, hH⟩ ∈ f.ker := by
      change mk (-1 : SL(2, F)) = 1
      rw [mk_neg, map_one]
    rw [Nat.card_eq_two_iff]
    refine ⟨1, ⟨⟨-1, hH⟩, hmem⟩, ?_, ?_⟩
    · intro heq
      apply neg_one_ne_one_SL h2
      exact (congrArg (fun x : f.ker => ((x : H) : SL(2, F))) heq).symm
    · ext ⟨⟨A, hA⟩, hAker⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
      have hA1 : mk A = 1 := hAker
      rcases (mk_eq_one_iff A).mp hA1 with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
  have h := Subgroup.card_mul_index f.ker
  rw [Subgroup.index_ker, hrange, hker] at h
  rw [← h, mul_comm]

theorem card_map_mk_of_injOn (H : Subgroup SL(2, F))
    (hH : ∀ A ∈ H, -A ∈ H → False) : Nat.card (H.map mk) = Nat.card H := by
  let f : H →* PSL(2, F) := mk.comp H.subtype
  have hrange : f.range = H.map mk := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hker : f.ker = ⊥ := by
    rw [eq_bot_iff]
    rintro ⟨A, hA⟩ hAker
    have hA1 : mk A = 1 := hAker
    rcases (mk_eq_one_iff A).mp hA1 with rfl | rfl
    · rfl
    · exact (hH 1 H.one_mem (by simpa using hA)).elim
  rw [← hrange, ← Subgroup.index_ker, hker, Subgroup.index_bot]

variable [Fintype F]

theorem card_SL : Nat.card SL(2, F) = Fintype.card F * (Fintype.card F ^ 2 - 1) := by
  rw [CFSG.GorensteinWalter.sl2_card_formula, Nat.card_eq_fintype_card]

theorem card_PSL (h2 : (2 : F) ≠ 0) :
    Nat.card PSL(2, F) * 2 = Fintype.card F * (Fintype.card F ^ 2 - 1) := by
  have h := card_map_mk h2 ⊤ (Subgroup.mem_top _)
  rw [Subgroup.map_top_of_surjective _ mk_surjective, Subgroup.card_top, Subgroup.card_top] at h
  rw [h, card_SL]

theorem card_splitSL : Nat.card (splitSL F) = Fintype.card F - 1 := by
  classical
  have hbij : Function.Bijective (fun a : Fˣ => (⟨diag a, diag_mem_splitSL a⟩ : splitSL F)) := by
    constructor
    · intro a b hab
      have h := congrArg (fun A : splitSL F => ((A : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 0) hab
      simp only [coe_diag, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.empty_val', Matrix.cons_val_fin_one] at h
      exact Units.ext h
    · rintro ⟨A, h01, h10⟩
      have hdet := det_entries A
      rw [h01, zero_mul, sub_zero] at hdet
      have h0 : (A : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hdet
      refine ⟨Units.mk0 _ h0, ?_⟩
      apply Subtype.ext
      apply SL_ext
      · simp
      · simp [h01]
      · simp [h10]
      · simp only [coe_diag, Units.val_mk0]
        simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.empty_val',
          Matrix.cons_val_fin_one]
        exact (eq_inv_of_mul_eq_one_right hdet).symm
  rw [← Nat.card_eq_of_bijective _ hbij, Nat.card_eq_fintype_card, Fintype.card_units]

theorem card_splitTorus (h2 : (2 : F) ≠ 0) :
    Nat.card (splitTorus F) * 2 = Fintype.card F - 1 := by
  rw [splitTorus, card_map_mk h2 _ (by rw [← diag_neg_one]; exact diag_mem_splitSL _),
    card_splitSL]

theorem card_unipSL : Nat.card (unipSL F) = Fintype.card F := by
  have hbij : Function.Bijective (fun t : F => (⟨unip t, unip_mem_unipSL t⟩ : unipSL F)) := by
    constructor
    · intro s t hst
      have h := congrArg (fun A : unipSL F => ((A : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 1) hst
      simpa using h
    · rintro ⟨A, h10, h00, h11⟩
      refine ⟨(A : Matrix (Fin 2) (Fin 2) F) 0 1, ?_⟩
      apply Subtype.ext
      apply SL_ext <;> simp [h10, h00, h11]
  rw [← Nat.card_eq_of_bijective _ hbij, Nat.card_eq_fintype_card]

theorem card_unipotent (h2 : (2 : F) ≠ 0) : Nat.card (unipotent F) = Fintype.card F := by
  rw [unipotent, card_map_mk_of_injOn, card_unipSL]
  rintro A ⟨-, h00, -⟩ ⟨-, h00', -⟩
  rw [neg_apply_SL, h00] at h00'
  apply h2
  linear_combination -h00'

@[expose] def borelElem (a : Fˣ) (b : F) : SL(2, F) :=
  ⟨!![(a : F), b; 0, (a : F)⁻¹], by simp [Matrix.det_fin_two_of]⟩

omit [Fintype F] in
@[simp] theorem coe_borelElem (a : Fˣ) (b : F) :
    (borelElem a b : Matrix (Fin 2) (Fin 2) F) = !![(a : F), b; 0, (a : F)⁻¹] := rfl

theorem card_borelSL : Nat.card (borelSL F) = (Fintype.card F - 1) * Fintype.card F := by
  classical
  have hbij : Function.Bijective
      (fun p : Fˣ × F => (⟨borelElem p.1 p.2, by simp [mem_borelSL_iff]⟩ : borelSL F)) := by
    constructor
    · rintro ⟨a, b⟩ ⟨a', b'⟩ h
      have h0 := congrArg (fun A : borelSL F => ((A : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 0) h
      have h1 := congrArg (fun A : borelSL F => ((A : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 1) h
      simp only [coe_borelElem, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val_one] at h0 h1
      exact Prod.ext (Units.ext h0) h1
    · rintro ⟨A, h10⟩
      have hdet := det_entries A
      rw [mem_borelSL_iff] at h10
      rw [h10, mul_zero, sub_zero] at hdet
      have h0 : (A : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hdet
      refine ⟨(Units.mk0 _ h0, (A : Matrix (Fin 2) (Fin 2) F) 0 1), ?_⟩
      apply Subtype.ext
      apply SL_ext
      · simp
      · simp
      · simp [h10]
      · simp only [coe_borelElem, Units.val_mk0]
        simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.empty_val',
          Matrix.cons_val_fin_one]
        exact (eq_inv_of_mul_eq_one_right hdet).symm
  rw [← Nat.card_eq_of_bijective _ hbij, Nat.card_prod, Nat.card_eq_fintype_card,
    Nat.card_eq_fintype_card, Fintype.card_units]

theorem card_borel (h2 : (2 : F) ≠ 0) :
    Nat.card (borel F) * 2 = (Fintype.card F - 1) * Fintype.card F := by
  rw [borel, card_map_mk h2 _ (by rw [mem_borelSL_iff, neg_apply_SL]; simp), card_borelSL]

theorem card_nonsplitSL (hF : ringChar F ≠ 2) {ν : F} (hν : ¬ IsSquare ν) :
    Nat.card (nonsplitSL ν) = Fintype.card F + 1 := by
  classical
  let e : nonsplitSL ν ≃ {v : F × F // v.1 ^ 2 - ν * v.2 ^ 2 = 1} :=
    { toFun := fun A => ⟨(((A : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 0,
        ((A : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 0), by
          have hdet := det_entries (A : SL(2, F))
          obtain ⟨h1, h2⟩ := A.2
          rw [h1, h2] at hdet
          linear_combination hdet⟩
      invFun := fun v => ⟨nsElem ν v.1.1 v.1.2 v.2, nsElem_mem_nonsplitSL ν _ _ _⟩
      left_inv := by
        rintro ⟨A, h1, h2⟩
        apply Subtype.ext
        apply SL_ext <;> simp [h1, h2]
      right_inv := by
        rintro ⟨⟨x, y⟩, h⟩
        rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype,
    card_normForm_one hF hν]

theorem card_nonsplitTorus (hF : ringChar F ≠ 2) {ν : F} (hν : ¬ IsSquare ν) :
    Nat.card (nonsplitTorus ν) * 2 = Fintype.card F + 1 := by
  rw [nonsplitTorus, card_map_mk (Ring.two_ne_zero hF) _
    (neg_mem_nonsplitSL ν (nonsplitSL ν).one_mem), card_nonsplitSL hF hν]

end Card

end CFSG.PSL2Table
