module

public import CFSG.ClassicalInvolution.Phan.PhanS5D3Indep
public import Mathlib.FieldTheory.ChevalleyWarning

public section

namespace CFSG.ClassicalInvolution.PhanB3.S.Std.D

open CFSG.ClassicalInvolution.PhanB3.S.Std

variable {K : Type} [Field K] (M : Model K)

theorem bf_sum_right {ι : Type} [Fintype ι] (g : ι → K) (u : ι → Vec K) (z : Vec K) :
    bf M z (∑ i, g i • u i) = ∑ i, g i * bf M z (u i) := by
  rw [bf_comm, bf_sum_left]
  simp [bf_comm]

theorem bf_sum_sum (x : Fin 3 → K) (z : Fin 3 → Vec K) :
    bf M (∑ i, x i • z i) (∑ i, x i • z i) = ∑ i, ∑ j, bf M (z i) (z j) * (x i * x j) := by
  rw [bf_sum_left]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [bf_sum_right, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

@[expose] noncomputable def quadPoly (z : Fin 3 → Vec K) : MvPolynomial (Fin 3) K :=
  ∑ i, ∑ j, MvPolynomial.C (bf M (z i) (z j)) * (MvPolynomial.X i * MvPolynomial.X j)

theorem eval_quadPoly (z : Fin 3 → Vec K) (x : Fin 3 → K) :
    MvPolynomial.eval x (quadPoly M z) = bf M (∑ i, x i • z i) (∑ i, x i • z i) := by
  rw [bf_sum_sum]
  simp only [quadPoly, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]

theorem totalDegree_quadPoly_lt (z : Fin 3 → Vec K) :
    (quadPoly M z).totalDegree < Fintype.card (Fin 3) := by
  have h : (quadPoly M z).totalDegree ≤ 2 := by
    unfold quadPoly
    refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun i _ => ?_)
    refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun j _ => ?_)
    have h1 : (MvPolynomial.X i * MvPolynomial.X j : MvPolynomial (Fin 3) K).totalDegree ≤ 2 := by
      refine (MvPolynomial.totalDegree_mul _ _).trans ?_
      rw [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_X]
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.totalDegree_C, zero_add]
    exact h1
  simp only [Fintype.card_fin]
  omega

variable [Finite K]

theorem exists_singular_comb (z : Fin 3 → Vec K) :
    ∃ x : Fin 3 → K, x ≠ 0 ∧ bf M (∑ i, x i • z i) (∑ i, x i • z i) = 0 := by
  classical
  have := Fintype.ofFinite K
  have hdvd := char_dvd_card_solutions (ringChar K) (totalDegree_quadPoly_lt M z)
  by_contra hcon
  have hcon' : ∀ x : Fin 3 → K, bf M (∑ i, x i • z i) (∑ i, x i • z i) = 0 → x = 0 := fun x hx => by
    by_contra hne
    exact hcon ⟨x, hne, hx⟩
  have h0 : MvPolynomial.eval (0 : Fin 3 → K) (quadPoly M z) = 0 := by
    rw [eval_quadPoly]
    simp [bf_zero_left]
  have hpos : 0 < Fintype.card {x : Fin 3 → K // MvPolynomial.eval x (quadPoly M z) = 0} :=
    Fintype.card_pos_iff.mpr ⟨⟨0, h0⟩⟩
  have hone : Fintype.card {x : Fin 3 → K // MvPolynomial.eval x (quadPoly M z) = 0} ≤ 1 := by
    rw [Fintype.card_le_one_iff]
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    rw [eval_quadPoly] at hx hy
    exact Subtype.ext ((hcon' x hx).trans (hcon' y hy).symm)
  have hle := Nat.le_of_dvd hpos hdvd
  have h1 := CharP.ringChar_ne_one (R := K)
  have h2 := CharP.ringChar_ne_zero_of_finite K
  omega

end CFSG.ClassicalInvolution.PhanB3.S.Std.D
