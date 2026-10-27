module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerA4Diag
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open Matrix

variable {K : Type} [Field K]

@[expose] def embM (A : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 4) (Fin 4) K :=
  !![A 0 0, A 0 1, 0, 0; A 1 0, A 1 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

theorem det_embM (A : Matrix (Fin 2) (Fin 2) K) : (embM A).det = A.det := by
  rw [Matrix.det_succ_row_zero]
  simp [embM, Fin.sum_univ_succ, Fin.succAbove, Matrix.det_succ_row_zero, Matrix.det_fin_two]

@[expose] def IsBlock (g : Matrix (Fin 4) (Fin 4) K) : Prop :=
  ∀ i j : Fin 4, ¬ (i.val < 2 ∧ j.val < 2) → g i j = if i = j then 1 else 0

@[expose] def OffBlock (g : Matrix (Fin 4) (Fin 4) K) : Prop :=
  ∀ i j : Fin 4, ¬ (i.val < 2 ∧ j.val < 2) → i ≠ j → g i j = 0

theorem isBlock_embM (A : Matrix (Fin 2) (Fin 2) K) : IsBlock (embM A) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [embM]

@[expose] def emb : Matrix.SpecialLinearGroup (Fin 2) K →* Matrix.SpecialLinearGroup (Fin 4) K where
  toFun A := ⟨embM (A : Matrix (Fin 2) (Fin 2) K), by rw [det_embM]; exact A.2⟩
  map_one' := Subtype.ext (by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [embM])
  map_mul' A B := Subtype.ext (by
    show embM ((A : Matrix (Fin 2) (Fin 2) K) * (B : Matrix (Fin 2) (Fin 2) K)) =
      embM (A : Matrix (Fin 2) (Fin 2) K) * embM (B : Matrix (Fin 2) (Fin 2) K)
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [embM, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_two])

theorem emb_apply_coe (A : Matrix.SpecialLinearGroup (Fin 2) K) :
    ((emb A : Matrix.SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      embM (A : Matrix (Fin 2) (Fin 2) K) := rfl

theorem emb_injective : Function.Injective (emb (K := K)) := by
  rw [injective_iff_map_eq_one]
  intro A hA
  have h : embM (A : Matrix (Fin 2) (Fin 2) K) = 1 := by
    have := congrArg (fun x : Matrix.SpecialLinearGroup (Fin 4) K =>
      (x : Matrix (Fin 4) (Fin 4) K)) hA
    simpa [emb_apply_coe] using this
  apply Subtype.ext
  ext i j
  have h' := congrFun (congrFun h (Fin.castLE (by norm_num) i)) (Fin.castLE (by norm_num) j)
  fin_cases i <;> fin_cases j <;> simp_all [embM]

theorem offBlock_of_comm_diag (x : Matrix (Fin 4) (Fin 4) K) (v : Fin 4 → K)
    (hcomm : x * Matrix.diagonal v = Matrix.diagonal v * x)
    (hdist : ∀ i j : Fin 4, ¬ (i.val < 2 ∧ j.val < 2) → i ≠ j → v i ≠ v j) :
    OffBlock x := by
  intro i j hij hne
  have h := congrFun (congrFun hcomm i) j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at h
  have hv : v i ≠ v j := hdist i j hij hne
  have h2 : x i j * (v j - v i) = 0 := by
    rw [mul_sub]
    linear_combination h
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact h3
  · exact absurd (sub_eq_zero.mp h3).symm hv

theorem isBlock_conj {x y g : Matrix (Fin 4) (Fin 4) K} (hxy : x * y = 1) (hyx : y * x = 1)
    (hx : OffBlock x) (hy : OffBlock y) (hg : IsBlock g) : IsBlock (x * g * y) := by
  intro i j hij
  by_cases hi : i.val < 2
  · have hj : ¬ j.val < 2 := fun h => hij ⟨hi, h⟩
    have hne : i ≠ j := by
      intro h
      apply hj
      rw [← h]
      exact hi
    have hxg0 : ∀ k : Fin 4, ¬ k.val < 2 → (x * g) i k = 0 := by
      intro k hk
      rw [Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro l _
      by_cases hl : l = k
      · rw [hl, hx i k (fun h => hk h.2) (fun h => hk (by rw [← h]; exact hi)), zero_mul]
      · rw [hg l k (fun h => hk h.2), if_neg hl, mul_zero]
    rw [Matrix.mul_apply, if_neg hne]
    apply Finset.sum_eq_zero
    intro l _
    by_cases hl : l = j
    · rw [hl, hxg0 j hj, zero_mul]
    · rw [hy l j (fun h => hj h.2) hl, mul_zero]
  · have hyii : ∀ k, k ≠ i → y i k = 0 := fun k hk =>
      hy i k (fun h => hi h.1) hk.symm
    have hxgi : ∀ l : Fin 4, (x * g) i l = x i i * g i l := by
      intro l
      rw [Matrix.mul_apply, Finset.sum_eq_single i]
      · intro k _ hk
        rw [hx i k (fun h => hi h.1) (Ne.symm hk), zero_mul]
      · intro h
        exact absurd (Finset.mem_univ i) h
    have hgil : ∀ l : Fin 4, g i l = if i = l then 1 else 0 := fun l =>
      hg i l (fun h => hi h.1)
    have hxy_ii : x i i * y i i = 1 := by
      have h : (y * x) i i = 1 := by
        have h0 := congrFun (congrFun hyx i) i
        rw [Matrix.one_apply_eq] at h0
        exact h0
      rw [Matrix.mul_apply, Finset.sum_eq_single i] at h
      · rw [mul_comm]
        exact h
      · intro k _ hk
        rw [hyii k hk, zero_mul]
      · intro h'
        exact absurd (Finset.mem_univ i) h'
    rw [Matrix.mul_apply]
    simp only [hxgi, hgil]
    have hsum : ∀ l : Fin 4, x i i * (if i = l then (1 : K) else 0) * y l j =
        if i = l then x i i * y l j else 0 := by
      intro l
      split_ifs <;> simp
    simp only [hsum]
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_univ, if_true]
    by_cases hij' : i = j
    · subst hij'
      rw [if_pos rfl]
      exact hxy_ii
    · rw [if_neg hij', hy i j (fun h => hi h.1) hij', mul_zero]

theorem tElt_matrix {ζ : K} (hζ : IsPrimitiveRoot ζ 3) :
    ((tElt K hζ : Matrix.SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      Matrix.diagonal ![1, 1, ζ, ζ ^ 2] := by
  ext i j
  by_cases h : i = j
  · subst h
    rw [tElt_apply, Matrix.diagonal_apply_eq]
  · rw [Matrix.diagonal_apply_ne _ h]
    unfold tElt
    rw [diagHom_apply_coe]
    simp [diagM, Matrix.diagonal_apply_ne _ h]

theorem exists_emb_eq_of_isBlock (g : Matrix.SpecialLinearGroup (Fin 4) K)
    (hg : IsBlock (g : Matrix (Fin 4) (Fin 4) K)) :
    ∃ B : Matrix.SpecialLinearGroup (Fin 2) K, emb B = g := by
  set A : Matrix (Fin 2) (Fin 2) K :=
    !![(g : Matrix (Fin 4) (Fin 4) K) 0 0, (g : Matrix (Fin 4) (Fin 4) K) 0 1;
      (g : Matrix (Fin 4) (Fin 4) K) 1 0, (g : Matrix (Fin 4) (Fin 4) K) 1 1] with hAdef
  have hEq : embM A = (g : Matrix (Fin 4) (Fin 4) K) := by
    ext i j
    by_cases h : i.val < 2 ∧ j.val < 2
    · fin_cases i <;> fin_cases j <;> simp_all [embM, hAdef]
    · rw [hg i j h]
      fin_cases i <;> fin_cases j <;> simp_all [embM]
  have hdet : A.det = 1 := by
    have h1 := det_embM A
    rw [hEq, g.2] at h1
    exact h1.symm
  exact ⟨⟨A, hdet⟩, Subtype.ext hEq⟩

theorem embM_mul_diagonal (A : Matrix (Fin 2) (Fin 2) K) (v : Fin 4 → K) (hv : v 0 = v 1) :
    embM A * Matrix.diagonal v = Matrix.diagonal v * embM A := by
  ext i j
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
  fin_cases i <;> fin_cases j <;> simp [embM, hv, mul_comm]

theorem emb_conj_mem {ζ : K} (hζ : IsPrimitiveRoot ζ 3) (x : Matrix.SpecialLinearGroup (Fin 4) K)
    (hx : x * tElt K hζ = tElt K hζ * x) (A : Matrix.SpecialLinearGroup (Fin 2) K) :
    ∃ B : Matrix.SpecialLinearGroup (Fin 2) K, emb B = x * emb A * x⁻¹ := by
  have hζ1 : ζ ≠ 1 := by
    simpa using hζ.pow_ne_one_of_pos_of_lt (l := 1) one_ne_zero (by norm_num)
  have hζ2 : ζ ^ 2 ≠ 1 := hζ.pow_ne_one_of_pos_of_lt (l := 2) two_ne_zero (by norm_num)
  have hζζ : ζ ≠ ζ ^ 2 := by
    intro h
    apply hζ1
    have hz : ζ ≠ 0 := hζ.ne_zero (by norm_num)
    have : ζ * ζ = ζ * 1 := by
      rw [mul_one, ← pow_two, ← h]
    exact mul_left_cancel₀ hz this
  have hvdist : ∀ i j : Fin 4, ¬ (i.val < 2 ∧ j.val < 2) → i ≠ j →
      (![1, 1, ζ, ζ ^ 2] : Fin 4 → K) i ≠ (![1, 1, ζ, ζ ^ 2] : Fin 4 → K) j := by
    intro i j hij hne
    fin_cases i <;> fin_cases j <;> simp_all [Ne.symm hζ1, Ne.symm hζ2, Ne.symm hζζ]
  have hcomm : (x : Matrix (Fin 4) (Fin 4) K) * Matrix.diagonal ![1, 1, ζ, ζ ^ 2] =
      Matrix.diagonal ![1, 1, ζ, ζ ^ 2] * (x : Matrix (Fin 4) (Fin 4) K) := by
    rw [← tElt_matrix hζ]
    have h := congrArg Subtype.val hx
    simpa [Matrix.SpecialLinearGroup.coe_mul] using h
  have hOx : OffBlock (x : Matrix (Fin 4) (Fin 4) K) :=
    offBlock_of_comm_diag _ _ hcomm hvdist
  have hx' : x⁻¹ * tElt K hζ = tElt K hζ * x⁻¹ :=
    (Commute.inv_left (show Commute x (tElt K hζ) from hx))
  have hcomm' : ((x⁻¹ : Matrix.SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
      Matrix.diagonal ![1, 1, ζ, ζ ^ 2] =
      Matrix.diagonal ![1, 1, ζ, ζ ^ 2] *
        ((x⁻¹ : Matrix.SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
    rw [← tElt_matrix hζ]
    have h := congrArg Subtype.val hx'
    simpa [Matrix.SpecialLinearGroup.coe_mul] using h
  have hOy : OffBlock ((x⁻¹ : Matrix.SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) :=
    offBlock_of_comm_diag _ _ hcomm' hvdist
  have hxy : (x : Matrix (Fin 4) (Fin 4) K) *
      ((x⁻¹ : Matrix.SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = 1 := by
    have h := congrArg Subtype.val (mul_inv_cancel x)
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] at h
    exact h
  have hyx : ((x⁻¹ : Matrix.SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
      (x : Matrix (Fin 4) (Fin 4) K) = 1 := by
    have h := congrArg Subtype.val (inv_mul_cancel x)
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] at h
    exact h
  have hblock := isBlock_conj hxy hyx hOx hOy (isBlock_embM (A : Matrix (Fin 2) (Fin 2) K))
  apply exists_emb_eq_of_isBlock
  simpa [Matrix.SpecialLinearGroup.coe_mul, emb_apply_coe] using hblock

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
