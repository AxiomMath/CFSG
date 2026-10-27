module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P54DB3Core
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P54DB3Six
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P54DBMinus

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P54.DB

open CFSG Subgroup Matrix Assembly.LowTwoRank CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal
open scoped MatrixGroups commutatorElement

variable {K : Type} [Field K] {b c : K}

theorem spinMatrix_minusX_mem_of_comm {n : ℕ} (hn : 2 ≤ n)
    (hAB : ∃ A B : SL(2, K), ⁅A, B⁆ = -1) :
    spinMatrix (quadMinus (n + 3) K b c) ((Twisted.minusFrame (n + 3) b c).toHypFrame.longSL2
      (i := ⟨2, by omega⟩) (j := ⟨3, by omega⟩) (by simp) true true (-1)) ∈
      rblock (eMinus n) (StatedQuadMinus (n + 1) K b c) := by
  set fr := (Twisted.minusFrame (n + 1) b c).toHypFrame.toFrame (i := ⟨0, by omega⟩)
    (j := ⟨1, by omega⟩) (by simp) true true with hfr
  set g₀ := (toLinEquiv (Fin (n + 1 - 1) ⊕ Fin (n + 1 - 1) ⊕ Fin 2) K).symm (fr.La (-1)) with hg₀
  have hg : ∀ w, (g₀ : Matrix _ _ K) *ᵥ w = fr.La (-1) w := by
    intro w
    rw [← toLinEquiv_apply, hg₀, MulEquiv.apply_symm_apply]
  refine ⟨blockL (Fin 2 ⊕ Fin 2) g₀,
    ⟨g₀, la_neg_one_mem_statedOmega (coe_quadMinus (n + 1) K b c) _ hAB, rfl⟩,
    (spinMatrix_eq_of_apply (eMinus n) (M := reGL (eMinus n) (blockL (Fin 2 ⊕ Fin 2) g₀))
      fun v y => ?_).symm⟩
  rw [T1.spinAction_longSL2, La_minus_apply]
  rcases y with a | b
  · rw [reGL_blockL_mulVec_inl, hg, hfr, La_minus_apply, pvalM_eMinus_inl]
    dsimp only
    by_cases ha : pvalM a = 0 ∨ pvalM a = 1
    · rw [ite_eq_left (by omega), ite_eq_left ha]
    · rw [ite_eq_right (by omega), ite_eq_right ha]
  · have := pval_lt_two b
    dsimp only
    rw [reGL_blockL_mulVec_inr, ite_eq_right (by rw [pvalM_eMinus_inr]; omega)]

variable [Finite K]

theorem false_of_minus_even (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (h2 : (2 : K) ≠ 0)
    {m : ℕ} (hm : 4 ≤ m) (hme : Even m) {t : spinGroup (quadMinus m K b c)}
    (htZ : t ∈ center (spinGroup (quadMinus m K b c))) (ht1 : t ≠ 1)
    (htn : (t : CliffordAlgebra (quadMinus m K b c)) ≠ -1) : False := by
  obtain ⟨-, hcomap, hZ⟩ := spinToStatedProj_quadMinus (K := K) (n := m) hm hirr
  set F := (Twisted.minusFrame m b c).toHypFrame
  have hv₀ : quadMinus m K b c (F.vec ⟨0, by omega⟩ true + F.vec ⟨0, by omega⟩ false) = 1 := by
    have h1 := F.polar_vec_not ⟨0, by omega⟩ true
    rw [QuadraticMap.polar, F.map_vec, F.map_vec, sub_zero, sub_zero] at h1
    exact h1
  have hπt := spinMatrix_eq_neg_one (mem_ker_spinMatrix_quadMinus_iff hirr)
    (hZ.symm.trans hcomap).le hv₀ htZ ht1 htn
  have hneg : (-1 : GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K) ∈
      StatedOmega (StatedQuadMinus m K b c) := by
    rw [← hπt, ← range_spinMatrix_quadMinus hm hirr]
    exact MonoidHom.mem_range.mpr ⟨t, rfl⟩
  rw [neg_one_mem_statedOmega_quadMinus_iff h2 hirr hm] at hneg
  refine not_isSquare_discr h2 hirr ?_
  have hodd : Odd (m - 1) := by
    obtain ⟨r, hr⟩ := hme
    exact ⟨r - 1, by omega⟩
  rwa [hodd.neg_one_pow, neg_one_mul, neg_sub] at hneg

theorem rawF3_minus_block (hK : Nat.card K = 3) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {n : ℕ} (hn : 2 ≤ n) {t : spinGroup (quadMinus (n + 3) K b c)}
    (htZ : t ∈ center (spinGroup (quadMinus (n + 3) K b c))) (ht1 : t ≠ 1)
    (htn : (t : CliffordAlgebra (quadMinus (n + 3) K b c)) ≠ -1) :
    F3.RawF3 (spinGroup (quadMinus (n + 3) K b c)) t := by
  have hodd : Odd (Nat.card K) := by
    rw [hK]
    decide
  have h2 : (2 : K) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card K hodd
  have : Finite (spinGroup (quadMinus (n + 3) K b c)) :=
    LieType.Steinberg.finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadMinus (n := n + 3) hirr)
  obtain ⟨-, hcomap, hZ⟩ := spinToStatedProj_quadMinus (K := K) (n := n + 3) (by omega) hirr
  have hBq : IsQuasisimple (StatedOmega (StatedQuadMinus (n + 1) K b c)) := by
    rcases Nat.lt_or_ge n 3 with h | h
    · obtain rfl : n = 2 := by omega
      exact isQuasisimple_statedOmega_six hodd (coe_quadMinus 3 K b c)
        (nondegenerate_polarBilin_quadMinus_of_finite 3 K hirr) (by simp)
    · exact isQuasisimple_statedOmega_quadMinus (by omega) hirr
  have hlie : ∃ (τ' : StatedLieTag) (n' : ℕ), Blueprint.LieModel
      (StatedOmega (StatedQuadMinus (n + 1) K b c) ⧸
        center (StatedOmega (StatedQuadMinus (n + 1) K b c))) τ' n' 3 1 := by
    rcases Nat.lt_or_ge n 3 with h | h
    · obtain rfl : n = 2 := by omega
      exact exists_lieModel_six' Nat.prime_three (by norm_num) le_rfl
        (by rw [pow_one]; exact hK) (coe_quadMinus 3 K b c)
        (nondegenerate_polarBilin_quadMinus_of_finite 3 K hirr) (by simp) hBq
    · exact ⟨.POmegaMinus, n + 1, Or.inl ⟨by decide, ⟨Nat.prime_three, le_rfl, by omega⟩, K,
        inferInstance, inferInstance, by rw [pow_one]; exact hK, b, c, hirr,
        ⟨QuotientGroup.quotientMulEquivOfEq (center_statedOmega_quadMinus (by omega) hirr)⟩⟩⟩
  refine rawF3_of_block (Twisted.minusFrame (n + 3) b c).toHypFrame hK
    (nondegenerate_quadMinus_of_finite (n + 3) K hirr).ne_zero
    (mem_ker_spinMatrix_quadMinus_iff hirr)
    (by rw [coe_quadMinus]; exact range_spinMatrix_quadMinus (by omega) hirr)
    (range_spinAction_quadMinus (by omega) hirr).le (hZ.symm.trans hcomap).le
    (i := ⟨0, by omega⟩) (j := ⟨1, by omega⟩) (k := ⟨2, by omega⟩) (i' := ⟨2, by omega⟩)
    (j' := ⟨3, by omega⟩) (by simp) (by simp) (by simp) (by simp) (eMinus n)
    (Q₂ := StatedQuadPlus 2 K) (by rw [coe_quadMinus]; exact pullQ_eMinus n)
    (spinMatrix_minusU hn)
    (spinMatrix_minusX_mem_of_comm hn
      (exists_commutator_eq_neg_one_sl2 (sq_add_sq_eq_neg_one_of_card_three hK)))
    hBq ?_ hlie htZ ht1 htn
  intro hneg
  rw [coe_quadMinus, neg_one_mem_statedOmega_quadMinus_iff h2 hirr (by omega)] at hneg
  rcases Nat.lt_or_ge n 3 with h | h
  · obtain rfl : n = 2 := by omega
    refine neg_one_mem_statedOmega_quadMinus_three' h2 hirr ?_
    have e : (-1 : K) ^ (2 + 3 - 1) = 1 := by
      rw [show (2 + 3 - 1 : ℕ) = 4 from rfl]
      norm_num
    rwa [e, one_mul] at hneg
  · rw [neg_one_mem_statedOmega_quadMinus_iff h2 hirr (by omega)]
    have e : (-1 : K) ^ (n + 3 - 1) = (-1) ^ (n + 1 - 1) := by
      rw [show n + 3 - 1 = n + 1 - 1 + 2 by omega, pow_add, neg_one_sq, mul_one]
    rwa [e] at hneg

theorem rawF3_minus (hK : Nat.card K = 3) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {m : ℕ}
    (hm : 4 ≤ m) {t : spinGroup (quadMinus m K b c)}
    (htZ : t ∈ center (spinGroup (quadMinus m K b c))) (ht1 : t ≠ 1)
    (htn : (t : CliffordAlgebra (quadMinus m K b c)) ≠ -1) :
    F3.RawF3 (spinGroup (quadMinus m K b c)) t := by
  have h2 : (2 : K) ≠ 0 :=
    CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card K (by rw [hK]; decide)
  rcases Nat.even_or_odd m with hme | hmo
  · exact (false_of_minus_even hirr h2 hm hme htZ ht1 htn).elim
  · obtain ⟨n, rfl⟩ : ∃ n, m = n + 3 := ⟨m - 3, by omega⟩
    have hn : 2 ≤ n := by
      obtain ⟨r, hr⟩ := hmo
      omega
    exact rawF3_minus_block hK hirr hn htZ ht1 htn

end CFSG.ComponentClassification.HarrisLit.T1.P54.DB
