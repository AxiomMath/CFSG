module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanU62O10CentU62Block

public section

namespace CFSG.AGLEmbedding.U62O10Cent

open Matrix Finset CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIVU62 CFSG.AGLEmbedding.U62ThreeCent

theorem sum_zmod_three {M : Type*} [AddCommMonoid M] (f : ZMod 3 → M) :
    ∑ t : ZMod 3, f t = f 0 + f 1 + f 2 :=
  Fin.sum_univ_three f

abbrev Ncnt (κ : Fin 6 → ZMod 3) (t : ZMod 3) : ℕ := Fintype.card (Fib κ t)

theorem Ncnt_eq_card_filter (κ : Fin 6 → ZMod 3) (t : ZMod 3) :
    Ncnt κ t = (Finset.univ.filter fun i => κ i = t).card :=
  Fintype.card_subtype _

theorem sum_Ncnt (κ : Fin 6 → ZMod 3) : Ncnt κ 0 + Ncnt κ 1 + Ncnt κ 2 = 6 := by
  have h := Finset.card_eq_sum_card_fiberwise (f := κ) (s := (Finset.univ : Finset (Fin 6)))
    (t := (Finset.univ : Finset (ZMod 3))) (fun _ _ => Finset.mem_univ _)
  simp only [Finset.card_univ, Fintype.card_fin, sum_zmod_three] at h
  simp only [Ncnt_eq_card_filter]
  exact h.symm

theorem prod_rootUnit (κ : Fin 6 → ZMod 3) : ∏ i, rootUnit (κ i) = rootUnit (∑ i, κ i) := by
  simp only [rootUnit, ← map_prod, ← ofAdd_sum]

theorem sum_eq_Ncnt (κ : Fin 6 → ZMod 3) :
    ∑ i, κ i = (Ncnt κ 0 : ZMod 3) * 0 + (Ncnt κ 1 : ZMod 3) * 1 + (Ncnt κ 2 : ZMod 3) * 2 := by
  have h := Finset.sum_fiberwise (Finset.univ : Finset (Fin 6)) κ (fun i => κ i)
  rw [← h, sum_zmod_three]
  have h' : ∀ t : ZMod 3, ∑ i ∈ Finset.univ.filter (fun i => κ i = t), κ i =
      (Ncnt κ t : ZMod 3) * t := fun t => by
    rw [Finset.sum_congr rfl (fun i hi => (Finset.mem_filter.1 hi).2), Finset.sum_const,
      nsmul_eq_mul, Ncnt_eq_card_filter]
  simp only [h']

theorem three_dvd_Ncnt (κ : Fin 6 → ZMod 3) (hdet : ∏ i, rootUnit (κ i) = 1) :
    3 ∣ Ncnt κ 1 + 2 * Ncnt κ 2 := by
  rw [prod_rootUnit, ← rootUnit_zero] at hdet
  have h0 : ∑ i, κ i = 0 := rootUnit_injective hdet
  rw [sum_eq_Ncnt] at h0
  have h1 : ((Ncnt κ 1 + 2 * Ncnt κ 2 : ℕ) : ZMod 3) = 0 := by
    push_cast
    linear_combination h0
  exact (ZMod.natCast_eq_zero_iff _ 3).1 h1

theorem type_cases (κ : Fin 6 → ZMod 3) (hdet : ∏ i, rootUnit (κ i) = 1) :
    (Ncnt κ 0 = 6 ∨ Ncnt κ 1 = 6 ∨ Ncnt κ 2 = 6) ∨
    (Ncnt κ 0 = 4 ∨ Ncnt κ 1 = 4 ∨ Ncnt κ 2 = 4) ∨
    ((Ncnt κ 0 = 3 ∧ Ncnt κ 1 = 3 ∧ Ncnt κ 2 = 0) ∨ (Ncnt κ 0 = 3 ∧ Ncnt κ 1 = 0 ∧ Ncnt κ 2 = 3) ∨
      (Ncnt κ 0 = 0 ∧ Ncnt κ 1 = 3 ∧ Ncnt κ 2 = 3)) ∨
    (Ncnt κ 0 = 2 ∧ Ncnt κ 1 = 2 ∧ Ncnt κ 2 = 2) := by
  have h1 := sum_Ncnt κ
  have h2 := three_dvd_Ncnt κ hdet
  generalize Ncnt κ 0 = a at *
  generalize Ncnt κ 1 = b at *
  generalize Ncnt κ 2 = c at *
  have hb : b ≤ 6 := by omega
  have hc : c ≤ 6 := by omega
  interval_cases b <;> interval_cases c <;> omega

open Classical in
theorem card_ne_shift {A : GL (Fin 6) F4} {d : Fin 6 → F4} {c : F4}
    (h : (A : Matrix (Fin 6) (Fin 6) F4) * Matrix.diagonal d *
      ((A⁻¹ : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) = Matrix.diagonal fun i => c * d i)
    (μ : F4) :
    Fintype.card {i // c * d i - μ ≠ 0} = Fintype.card {i // d i - μ ≠ 0} := by
  have hAA : (A : Matrix (Fin 6) (Fin 6) F4) * ((A⁻¹ : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4)
      = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hdiag : ∀ e : Fin 6 → F4, Matrix.diagonal (fun i => e i - μ) =
      Matrix.diagonal e - μ • (1 : Matrix (Fin 6) (Fin 6) F4) := fun e => by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij]
  have hconj : (A : Matrix (Fin 6) (Fin 6) F4) * Matrix.diagonal (fun i => d i - μ) *
      ((A⁻¹ : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) =
        Matrix.diagonal fun i => c * d i - μ := by
    rw [hdiag d, hdiag (fun i => c * d i), ← h, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_one, hAA]
  have hr : (Matrix.diagonal fun i => c * d i - μ).rank =
      (Matrix.diagonal fun i => d i - μ).rank := by
    have hd1 : IsUnit ((A : Matrix (Fin 6) (Fin 6) F4)).det :=
      (Matrix.isUnit_iff_isUnit_det _).1 A.isUnit
    have hd2 : IsUnit (((A⁻¹ : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4)).det :=
      (Matrix.isUnit_iff_isUnit_det _).1 (A⁻¹).isUnit
    rw [← hconj, Matrix.rank_mul_eq_left_of_isUnit_det _ _ hd2,
      Matrix.rank_mul_eq_right_of_isUnit_det _ _ hd1]
  rw [Matrix.rank_diagonal, Matrix.rank_diagonal] at hr
  exact hr

end CFSG.AGLEmbedding.U62O10Cent
