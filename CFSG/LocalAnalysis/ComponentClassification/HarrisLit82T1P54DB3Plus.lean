module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P54DB3Core
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P54DBEight

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P54.DB

open CFSG Subgroup Matrix Assembly.LowTwoRank CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal
open scoped MatrixGroups commutatorElement

variable {K : Type} [Field K]

theorem spinMatrix_plusX_mem_of_comm {n : ℕ} (hn : 3 ≤ n) (hAB : ∃ A B : SL(2, K), ⁅A, B⁆ = -1) :
    spinMatrix (quadPlus (n + 2) K) ((plusFrame (n + 2) K (by omega)).longSL2
      (i := ⟨2, by omega⟩) (j := ⟨3, by omega⟩) (by simp) true true (-1)) ∈
      rblock (ePlus n) (StatedQuadPlus n K) := by
  set fr := (plusFrame n K hn).toFrame (i := ⟨0, by omega⟩) (j := ⟨1, by omega⟩)
    (by simp) true true with hfr
  set g₀ := (toLinEquiv (Fin n ⊕ Fin n) K).symm (fr.La (-1)) with hg₀
  have hg : ∀ w, (g₀ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ w = fr.La (-1) w := by
    intro w
    rw [← toLinEquiv_apply, hg₀, MulEquiv.apply_symm_apply]
  refine ⟨blockL (Fin 2 ⊕ Fin 2) g₀,
    ⟨g₀, la_neg_one_mem_statedOmega (coe_quadPlus n K) _ hAB, rfl⟩,
    (spinMatrix_eq_of_apply (ePlus n) (M := reGL (ePlus n) (blockL (Fin 2 ⊕ Fin 2) g₀))
      fun v y => ?_).symm⟩
  rw [T1.spinAction_longSL2, La_plus_apply]
  rcases y with a | b
  · rw [reGL_blockL_mulVec_inl, hg, hfr, La_plus_apply, pval_ePlus_inl]
    dsimp only
    by_cases ha : pval a = 0 ∨ pval a = 1
    · rw [ite_eq_left (by omega), ite_eq_left ha]
    · rw [ite_eq_right (by omega), ite_eq_right ha]
  · have := pval_lt_two b
    dsimp only
    rw [reGL_blockL_mulVec_inr, ite_eq_right (by rw [pval_ePlus_inr]; omega)]

variable [Finite K]

theorem not_isSquare_neg_one_of_card_three (hK : Nat.card K = 3) : ¬ IsSquare (-1 : K) := by
  rintro ⟨x, hx⟩
  have := Fintype.ofFinite K
  have h2 : (2 : K) ≠ 0 :=
    CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card K (by rw [hK]; decide)
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hx
    exact one_ne_zero (neg_eq_zero.mp hx)
  have h := FiniteField.pow_card_sub_one_eq_one x hx0
  rw [← Nat.card_eq_fintype_card, hK] at h
  exact h2 (by linear_combination -hx - h)

theorem false_of_plus_odd_three (hK : Nat.card K = 3) {m : ℕ} (hm : 3 ≤ m) (hmo : Odd m)
    {t : spinGroup (quadPlus m K)} (htZ : t ∈ center (spinGroup (quadPlus m K))) (ht1 : t ≠ 1)
    (htn : (t : CliffordAlgebra (quadPlus m K)) ≠ -1) : False := by
  have h2 : (2 : K) ≠ 0 :=
    CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card K (by rw [hK]; decide)
  have : NeZero m := ⟨by omega⟩
  obtain ⟨-, hcomap, hZ⟩ := spinToStatedProj_quadPlus (K := K) (n := m) hm
  set F := plusFrame m K hm
  have hv₀ : quadPlus m K (F.vec ⟨0, by omega⟩ true + F.vec ⟨0, by omega⟩ false) = 1 := by
    have h1 := F.polar_vec_not ⟨0, by omega⟩ true
    rw [QuadraticMap.polar, F.map_vec, F.map_vec, sub_zero, sub_zero] at h1
    exact h1
  have hπt := spinMatrix_eq_neg_one mem_ker_spinMatrix_quadPlus_iff (hZ.symm.trans hcomap).le
    hv₀ htZ ht1 htn
  have hneg : (-1 : GL (Fin m ⊕ Fin m) K) ∈ StatedOmega (StatedQuadPlus m K) := by
    rw [← hπt, ← range_spinMatrix_quadPlus hm]
    exact MonoidHom.mem_range.mpr ⟨t, rfl⟩
  rw [neg_one_mem_statedOmega_quadPlus_iff h2 hm, hmo.neg_one_pow] at hneg
  exact not_isSquare_neg_one_of_card_three hK hneg

theorem rawF3_plus_even (hK : Nat.card K = 3) {n : ℕ} (hn : 4 ≤ n)
    {t : spinGroup (quadPlus (n + 2) K)} (htZ : t ∈ center (spinGroup (quadPlus (n + 2) K)))
    (ht1 : t ≠ 1) (htn : (t : CliffordAlgebra (quadPlus (n + 2) K)) ≠ -1) :
    F3.RawF3 (spinGroup (quadPlus (n + 2) K)) t := by
  have h2 : (2 : K) ≠ 0 :=
    CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card K (by rw [hK]; decide)
  have : Finite (spinGroup (quadPlus (n + 2) K)) :=
    LieType.Steinberg.finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadPlus (n := n + 2))
  obtain ⟨-, hcomap, hZ⟩ := spinToStatedProj_quadPlus (K := K) (n := n + 2) (by omega)
  have hlie : ∃ (τ' : StatedLieTag) (n' : ℕ), Blueprint.LieModel
      (StatedOmega (StatedQuadPlus n K) ⧸ center (StatedOmega (StatedQuadPlus n K))) τ' n' 3 1 :=
    ⟨.POmegaPlus, n, Or.inl ⟨by decide, ⟨Nat.prime_three, le_rfl, hn⟩, K, inferInstance,
      inferInstance, by rw [pow_one]; exact hK,
      ⟨QuotientGroup.quotientMulEquivOfEq (center_statedOmega_quadPlus (by omega))⟩⟩⟩
  refine rawF3_of_block (plusFrame (n + 2) K (by omega)) hK
    (nondegenerate_quadPlus (n + 2) K).ne_zero mem_ker_spinMatrix_quadPlus_iff
    (by rw [coe_quadPlus]; exact range_spinMatrix_quadPlus (by omega))
    (range_spinAction_quadPlus (by omega)).le (hZ.symm.trans hcomap).le
    (i := ⟨0, by omega⟩) (j := ⟨1, by omega⟩) (k := ⟨2, by omega⟩) (i' := ⟨2, by omega⟩)
    (j' := ⟨3, by omega⟩) (by simp) (by simp) (by simp) (by simp) (ePlus n)
    (Q₂ := StatedQuadPlus 2 K) (by rw [coe_quadPlus]; exact pullQ_ePlus n)
    (spinMatrix_plusU (by omega))
    (spinMatrix_plusX_mem_of_comm (by omega)
      (exists_commutator_eq_neg_one_sl2 (sq_add_sq_eq_neg_one_of_card_three hK)))
    (isQuasisimple_statedOmega_quadPlus (by omega)) ?_ hlie htZ ht1 htn
  intro hneg
  rw [coe_quadPlus, neg_one_mem_statedOmega_quadPlus_iff h2 (by omega)] at hneg
  rw [neg_one_mem_statedOmega_quadPlus_iff h2 (by omega)]
  rwa [pow_add, neg_one_sq, mul_one] at hneg

theorem rawF3_eight (hK : Nat.card K = 3) {t : spinGroup (quadPlus 4 K)}
    (htZ : t ∈ center (spinGroup (quadPlus 4 K))) (ht1 : t ≠ 1)
    (htn : (t : CliffordAlgebra (quadPlus 4 K)) ≠ -1) : F3.RawF3 (spinGroup (quadPlus 4 K)) t := by
  have hodd : Odd (Nat.card K) := by
    rw [hK]
    decide
  have hQ := (nondegenerate_quadPlus 4 K).ne_zero
  obtain ⟨-, hcomap, hZc⟩ := spinToStatedProj_quadPlus (K := K) (n := 4) (by norm_num)
  have hcen := (hZc.symm.trans hcomap).le
  have hZ := DA.smul_of_le_comap hcen
  have hker := mem_ker_spinMatrix_quadPlus_iff (n := 4) (K := K)
  have hrangeE := (range_spinAction_quadPlus (K := K) (n := 4) (by norm_num)).le
  set F := plusFrame 4 K (by norm_num) with hF
  have h01 : (⟨0, by omega⟩ : Fin 4) ≠ ⟨1, by omega⟩ := by simp
  have h23 : (⟨2, by omega⟩ : Fin 4) ≠ ⟨3, by omega⟩ := by simp
  have hv₀ : quadPlus 4 K (F.vec ⟨0, by omega⟩ true + F.vec ⟨0, by omega⟩ false) = 1 := by
    have h1 := F.polar_vec_not ⟨0, by omega⟩ true
    rw [QuadraticMap.polar, F.map_vec, F.map_vec, sub_zero, sub_zero] at h1
    exact h1
  have hπt := spinMatrix_eq_neg_one hker hcen hv₀ htZ ht1 htn
  have hta : ∀ w, spinAction (quadPlus 4 K) t w = -w := by
    intro w
    rw [← spinMatrix_mulVec, hπt, Units.val_neg, Units.val_one, neg_mulVec, one_mulVec]
  have hz : t * F.longSL2 h01 true true (-1) * (F.longSL2 h23 true true (-1))⁻¹ ∈
      (spinMatrix (quadPlus 4 K)).ker := by
    rw [ker_spinMatrix, MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one]
    refine LinearEquiv.ext fun v => ?_
    rw [map_mul, LinearEquiv.mul_apply, hta, T1.spinAction_longSL2, T1.spinAction_longSL2]
    exact spinAction_neg_mul_eight v
  obtain ⟨s, hs⟩ := ker_mul_longSL2 F hQ hker h23 hz
  rw [inv_mul_cancel_right] at hs
  have hC : centralizer {F.longSL2 h23 true s (-1)} =
      centralizer {F.longSL2 h01 true true (-1)} := by
    rw [← hs]
    exact T1.centralizer_mul_of_mem_center htZ
  have huZ := DA.longSL2_neg_one_not_mem_center F hodd hZ h01 (k := ⟨2, by omega⟩) (by simp)
    (by simp) true true
  have hxZ := DA.longSL2_neg_one_not_mem_center F hodd hZ h23 (k := ⟨0, by omega⟩) (by simp)
    (by simp) true s
  have h₂C := T1.range_longSL2_le_centralizer F h23 true s
  have h₂s := F3.isSubnormal_range_longSL2_of_odd F h23 hodd hrangeE true s
  rw [hC] at h₂C h₂s
  obtain ⟨eK⟩ := F3.nonempty_sl2_equiv_zmod_three hK
  refine ⟨F.longSL2 h01 true true (-1), T1.orderOf_longSL2_neg_one F h01 hodd true true, huZ,
    (F.longSL2 h01 true true).range, (F.longSL2 h23 true s).range,
    T1.range_longSL2_le_centralizer F h01 true true,
    F3.isSubnormal_range_longSL2_of_odd F h01 hodd hrangeE true true,
    MonoidHom.mem_range.mpr ⟨-1, rfl⟩, F3.range_longSL2_inf_center F h01 true true huZ,
    ⟨(MonoidHom.ofInjective (T1.longSL2_injective F h01 true true)).symm.trans eK⟩,
    .inr ⟨h₂C, h₂s, F3.range_longSL2_inf_center F h23 true s hxZ,
      ⟨(MonoidHom.ofInjective (T1.longSL2_injective F h23 true s)).symm.trans eK⟩⟩, .inr ?_⟩
  rw [hs]
  exact MonoidHom.mem_range.mpr ⟨-1, rfl⟩

theorem rawF3_plus (hK : Nat.card K = 3) {m : ℕ} (hm : 4 ≤ m) {t : spinGroup (quadPlus m K)}
    (htZ : t ∈ center (spinGroup (quadPlus m K))) (ht1 : t ≠ 1)
    (htn : (t : CliffordAlgebra (quadPlus m K)) ≠ -1) : F3.RawF3 (spinGroup (quadPlus m K)) t := by
  rcases Nat.even_or_odd m with hme | hmo
  · rcases Nat.lt_or_ge m 6 with h | h
    · obtain rfl : m = 4 := by
        obtain ⟨r, hr⟩ := hme
        omega
      exact rawF3_eight hK htZ ht1 htn
    · obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
      exact rawF3_plus_even hK (by omega) htZ ht1 htn
  · exact (false_of_plus_odd_three hK (by omega) hmo htZ ht1 htn).elim

end CFSG.ComponentClassification.HarrisLit.T1.P54.DB
