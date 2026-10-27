module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87U4SvConj

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup Matrix Module CFSG CFSG.Blueprint CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open scoped MatrixGroups commutatorElement

section Frame

variable {p f : ℕ} {K : Type} [Field K]

@[expose] def dSign : HypIndex 2 0 → K :=
  Sum.elim (fun _ => 1) (Sum.elim (fun _ => 1) (fun _ => -1))

@[expose] def a0Mat (l : K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K :=
  Matrix.diagonal (fun a => l * dSign a)

theorem det_a0Mat {l : K} (hl0 : l ≠ 0) : (a0Mat l).det ≠ 0 := by
  rw [a0Mat, det_diagonal]
  refine Finset.prod_ne_zero_iff.2 fun a _ => mul_ne_zero hl0 ?_
  rcases a with i | k | i
  · simp [dSign]
  · exact k.elim0
  · simp [dSign]

theorem a0Mat_isometry (h : UnitaryFieldData p f K) {l : K} (hN : h.norm l = -1) :
    ((a0Mat l).map h.bar)ᵀ * hypGram 2 0 K * a0Mat l = hypGram 2 0 K := by
  have hN' : l * h.bar l = -1 := hN
  rw [a0Mat, diagonal_map (map_zero h.bar), diagonal_transpose]
  ext a b
  rw [mul_diagonal, diagonal_mul, hypGram_apply]
  by_cases hb : b = hypPartner a
  · subst hb
    rcases a with i | k | i
    · simp [dSign]
      linear_combination -hN'
    · exact k.elim0
    · simp [dSign]
      linear_combination -hN'
  · simp [hb]

@[expose] noncomputable def a0GL {l : K} (hl0 : l ≠ 0) : GL (HypIndex 2 0) K :=
  GeneralLinearGroup.mkOfDetNeZero (a0Mat l) (det_a0Mat hl0)

theorem coe_a0GL {l : K} (hl0 : l ≠ 0) :
    ((a0GL hl0 : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) = a0Mat l := rfl

@[expose] noncomputable def a0U (h : UnitaryFieldData p f K) {l : K} (hl0 : l ≠ 0)
    (hN : h.norm l = -1) : ↥(hypUnitary h 2 0) :=
  ⟨a0GL hl0, a0Mat_isometry h hN⟩

theorem hypProj_mem_fixSub_of_comm (h : UnitaryFieldData p f K) {l : K} (hl0 : l ≠ 0)
    (hN : h.norm l = -1) (g : ↥(hypSU h 2 0))
    (hg : a0Mat l * ((g : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) =
      ((g : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) * a0Mat l) :
    hypProj h 2 0 g ∈ fixSub (hypPhi h (a0U h hl0 hN)) := by
  rw [mem_fixSub, ← hypProj_hypConj]
  congr 1
  refine Subtype.ext ?_
  rw [coe_hypConj]
  change a0GL hl0 * (g : GL (HypIndex 2 0) K) * (a0GL hl0)⁻¹ = g
  rw [mul_inv_eq_iff_eq_mul]
  exact Units.ext hg

theorem negOne_mem (h : UnitaryFieldData p f K) :
    ∃ z : ↥(hypSU h 2 0), z ∈ hypScalars h 2 0 ∧
      ((z : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) = -1 := by
  have hcm : ((GeneralLinearGroup.scalar (HypIndex 2 0) (-1 : Kˣ) : GL (HypIndex 2 0) K) :
      Matrix (HypIndex 2 0) (HypIndex 2 0) K) = -1 := by
    rw [GeneralLinearGroup.coe_scalar, Units.val_neg, Units.val_one, map_neg, map_one]
  have hz : GeneralLinearGroup.scalar (HypIndex 2 0) (-1 : Kˣ) ∈ hypSU h 2 0 := by
    rw [mem_hypSU, GeneralLinearGroup.coe_scalar]
    refine ⟨?_, ?_⟩
    · rw [scalar_gram h]
      simp [UnitaryFieldData.norm]
    · have hc4 : Fintype.card (HypIndex 2 0) = 4 := by simp [Fintype.card_sum]
      rw [Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, hc4]
      norm_num
  refine ⟨⟨_, hz⟩, ?_, hcm⟩
  rw [mem_normOneScalars]
  refine ⟨-1, ?_, ?_, rfl⟩
  · simp [UnitaryFieldData.norm]
  · exact Even.neg_one_pow ⟨2, rfl⟩

theorem hypProj_mem_fixSub_of_anticomm (h : UnitaryFieldData p f K) {l : K} (hl0 : l ≠ 0)
    (hN : h.norm l = -1) (g : ↥(hypSU h 2 0))
    (hg : a0Mat l * ((g : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) =
      -(((g : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) * a0Mat l)) :
    hypProj h 2 0 g ∈ fixSub (hypPhi h (a0U h hl0 hN)) := by
  obtain ⟨z, hz, hzm⟩ := negOne_mem h
  rw [mem_fixSub, ← hypProj_hypConj]
  have hconj : hypConj h (a0U h hl0 hN) g = g * z := by
    refine Subtype.ext ?_
    rw [coe_hypConj, Subgroup.coe_mul]
    change a0GL hl0 * (g : GL (HypIndex 2 0) K) * (a0GL hl0)⁻¹ = (g : GL (HypIndex 2 0) K) * z
    rw [mul_inv_eq_iff_eq_mul]
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, Units.val_mul, coe_a0GL, hzm, Matrix.mul_neg, Matrix.mul_one,
      neg_mul]
    exact hg
  have h1 : hypProj h 2 0 z = 1 := (QuotientGroup.eq_one_iff z).2 hz
  rw [hconj, map_mul, h1, mul_one]

theorem a0Mat_comm_levi (h : UnitaryFieldData p f K) (l : K) (A : SL(2, K)) :
    a0Mat l * (((leviSU h 0 A : ↥(hypSU h 2 0)) : GL (HypIndex 2 0) K) :
      Matrix (HypIndex 2 0) (HypIndex 2 0) K) =
    (((leviSU h 0 A : ↥(hypSU h 2 0)) : GL (HypIndex 2 0) K) :
      Matrix (HypIndex 2 0) (HypIndex 2 0) K) * a0Mat l := by
  rw [coe_leviSU, coe_leviGL, a0Mat]
  ext a b
  rw [diagonal_mul, mul_diagonal]
  rcases a with i | k | i <;> rcases b with j | k' | j
  · simp [dSign, mul_comm]
  · exact k'.elim0
  · simp [dSign]
  · exact k.elim0
  · exact k.elim0
  · exact k.elim0
  · simp [dSign]
  · exact k'.elim0
  · simp [dSign, mul_comm]

theorem sumComm_mem_hypWeyl : (Equiv.sumComm (Fin 2) (Fin 2)) ∈ hypWeyl 2 := by
  rw [mem_hypWeyl]
  intro x
  rcases x with i | i <;> rfl

theorem exists_swap (h : UnitaryFieldData p f K) :
    ∃ (w : ↥(hypSU h 2 0)) (c d : K), c ≠ 0 ∧ d ≠ 0 ∧
      (∀ i : Fin 2, ((w : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ
        Pi.single (Sum.inl i) 1 = c • Pi.single (Sum.inr (Sum.inr i)) 1) ∧
      (∀ i : Fin 2, ((w : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ
        Pi.single (Sum.inr (Sum.inr i)) 1 = d • Pi.single (Sum.inl i) 1) := by
  obtain ⟨c, hc, hc0⟩ := h.exists_mem_traceZero_ne_zero
  refine ⟨weylElt h hc hc0 sumComm_mem_hypWeyl, c, (h.bar c)⁻¹, hc0,
    inv_ne_zero ((map_ne_zero h.bar).mpr hc0), fun i => ?_, fun i => ?_⟩
  · exact (weylMat_mulVec_of_inr (ε := 0) h c sumComm_mem_hypWeyl (i := i) (j := i) rfl).1
  · exact (weylMat_mulVec_of_inr (ε := 0) h c sumComm_mem_hypWeyl (i := i) (j := i) rfl).2

theorem a0Mat_anticomm_of_swap (l : K) {M : Matrix (HypIndex 2 0) (HypIndex 2 0) K} {c d : K}
    (hM1 : ∀ i : Fin 2, M *ᵥ Pi.single (Sum.inl i) 1 = c • Pi.single (Sum.inr (Sum.inr i)) 1)
    (hM2 : ∀ i : Fin 2, M *ᵥ Pi.single (Sum.inr (Sum.inr i)) 1 = d • Pi.single (Sum.inl i) 1) :
    a0Mat l * M = -(M * a0Mat l) := by
  rw [a0Mat]
  ext a b
  rw [diagonal_mul, Matrix.neg_apply, mul_diagonal]
  rcases b with j | k | j
  · have h1 := congrFun (hM1 j) a
    rw [Matrix.mulVec_single_one, Matrix.col_apply] at h1
    rw [h1]
    by_cases ha : a = Sum.inr (Sum.inr j)
    · subst ha
      simp [dSign, mul_comm]
    · simp [ha]
  · exact k.elim0
  · have h1 := congrFun (hM2 j) a
    rw [Matrix.mulVec_single_one, Matrix.col_apply] at h1
    rw [h1]
    by_cases ha : a = Sum.inl j
    · subst ha
      simp [dSign, mul_comm]
    · simp [ha]

end Frame

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
