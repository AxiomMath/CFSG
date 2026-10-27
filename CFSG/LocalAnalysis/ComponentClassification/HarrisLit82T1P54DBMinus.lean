module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P54DBPlus

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P54.DB

open CFSG Subgroup Matrix Assembly.LowTwoRank CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
open scoped MatrixGroups

variable {K : Type} [Field K] {b c : K}

@[expose] def pvalM {N : ℕ} : Fin N ⊕ Fin N ⊕ Fin 2 → ℕ :=
  Sum.elim (fun a => a) (Sum.elim (fun a => a) fun _ => N)

theorem La_minus_apply {m : ℕ} {i j : Fin (m - 1)} (hij : i ≠ j)
    (x : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K) (k : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) :
    ((Twisted.minusFrame m b c).toHypFrame.toFrame hij true true).La (-1) x k =
      if pvalM k = i ∨ pvalM k = j then -x k else x k := by
  rw [Frame.La_neg_one_apply, Frame.incl_apply, Frame.coords_apply]
  rcases k with a | a | a
  · simp [HypFrame.toFrame, Frame.e₁, Frame.f₁, Frame.e₂, Frame.f₂, polar_quadMinus_single_inl,
      polar_quadMinus_single_inr_inl, Pi.single_apply, Twisted.eVec, Twisted.fVec]
    simp only [pvalM, Sum.elim_inl, ← Fin.ext_iff]
    exact ite_two hij (fun b => x (.inl b)) a
  · simp [HypFrame.toFrame, Frame.e₁, Frame.f₁, Frame.e₂, Frame.f₂, polar_quadMinus_single_inl,
      polar_quadMinus_single_inr_inl, Pi.single_apply, Twisted.eVec, Twisted.fVec]
    simp only [pvalM, Sum.elim_inl, Sum.elim_inr, ← Fin.ext_iff]
    exact ite_two hij (fun b => x (.inr (.inl b))) a
  · have hi := i.isLt
    have hj := j.isLt
    have hc : ¬(pvalM (.inr (.inr a) : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) = (i : ℕ) ∨
        pvalM (.inr (.inr a) : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) = (j : ℕ)) := by
      simp only [pvalM, Sum.elim_inr]
      omega
    rw [ite_eq_right hc]
    simp [HypFrame.toFrame, Frame.e₁, Frame.f₁, Frame.e₂, Frame.f₂, polar_quadMinus_single_inl,
      polar_quadMinus_single_inr_inl, Twisted.eVec, Twisted.fVec]

section Split

variable (n : ℕ)

@[expose] def eMinus : (Fin (n + 1 - 1) ⊕ Fin (n + 1 - 1) ⊕ Fin 2) ⊕ (Fin 2 ⊕ Fin 2) ≃
    Fin (n + 3 - 1) ⊕ Fin (n + 3 - 1) ⊕ Fin 2 where
  toFun
    | .inl (.inl i) => .inl (splitEquiv n (.inl i))
    | .inl (.inr (.inl i)) => .inr (.inl (splitEquiv n (.inl i)))
    | .inl (.inr (.inr d)) => .inr (.inr d)
    | .inr (.inl j) => .inl (splitEquiv n (.inr j))
    | .inr (.inr j) => .inr (.inl (splitEquiv n (.inr j)))
  invFun
    | .inl a => Sum.elim (fun i => .inl (.inl i)) (fun j => .inr (.inl j)) ((splitEquiv n).symm a)
    | .inr (.inl a) =>
      Sum.elim (fun i => .inl (.inr (.inl i))) (fun j => .inr (.inr j)) ((splitEquiv n).symm a)
    | .inr (.inr d) => .inl (.inr (.inr d))
  left_inv := by
    rintro ((i | i | d) | (j | j)) <;> simp
  right_inv := by
    rintro (a | a | d)
    · obtain ⟨x, rfl⟩ := (splitEquiv n).surjective a
      rcases x with i | j <;> simp
    · obtain ⟨x, rfl⟩ := (splitEquiv n).surjective a
      rcases x with i | j <;> simp
    · rfl

theorem pvalM_eMinus_inl (a : Fin (n + 1 - 1) ⊕ Fin (n + 1 - 1) ⊕ Fin 2) :
    pvalM (eMinus n (.inl a)) = pvalM a + 2 := by
  rcases a with i | i | d
  · exact val_splitEquiv_inl n i
  · exact val_splitEquiv_inl n i
  · show n + 3 - 1 = n + 1 - 1 + 2
    omega

theorem pvalM_eMinus_inr (b : Fin 2 ⊕ Fin 2) : pvalM (eMinus n (.inr b)) = pval b := by
  rcases b with j | j <;> exact val_splitEquiv_inr n j

theorem pullQ_eMinus :
    pullQ (eMinus n) (StatedQuadMinus (n + 3) K b c) =
      sumQ (StatedQuadMinus (n + 1) K b c) (StatedQuadPlus 2 K) := by
  funext v
  have h1 : ∀ x, (eMinus n).symm (.inl (splitEquiv n x)) =
      Sum.elim (fun i => .inl (.inl i)) (fun j => .inr (.inl j)) x := by
    rintro (i | j) <;> rw [Equiv.symm_apply_eq] <;> rfl
  have h2 : ∀ x, (eMinus n).symm (.inr (.inl (splitEquiv n x))) =
      Sum.elim (fun i => .inl (.inr (.inl i))) (fun j => .inr (.inr j)) x := by
    rintro (i | j) <;> rw [Equiv.symm_apply_eq] <;> rfl
  have h3 : ∀ d, (eMinus n).symm (.inr (.inr d)) = .inl (.inr (.inr d)) := by
    intro d
    rw [Equiv.symm_apply_eq]
    rfl
  have hsum : ∀ g : Fin (n + 3 - 1) → K,
      ∑ k, g k = ∑ x : Fin (n + 1 - 1) ⊕ Fin 2, g (splitEquiv n x) :=
    fun g => (Fintype.sum_equiv (splitEquiv n) _ _ fun _ => rfl).symm
  simp only [pullQ, sumQ, StatedQuadMinus, StatedQuadPlus, Function.comp_apply]
  rw [hsum, Fintype.sum_sum_type]
  simp only [h1, h2, h3, Sum.elim_inl, Sum.elim_inr]
  ring

end Split

section Block

variable {n : ℕ} (hn : 2 ≤ n)

include hn in
theorem spinMatrix_minusU :
    spinMatrix (quadMinus (n + 3) K b c) ((Twisted.minusFrame (n + 3) b c).toHypFrame.longSL2
      (i := ⟨0, by omega⟩) (j := ⟨1, by omega⟩) (by simp) true true (-1)) = uMat (eMinus n) := by
  refine spinMatrix_eq_of_apply (eMinus n) fun v y => ?_
  rw [T1.spinAction_longSL2, La_minus_apply]
  dsimp only
  rcases y with a | b
  · rw [uMat_mulVec_inl, ite_eq_right (by rw [pvalM_eMinus_inl]; omega)]
  · have := pval_lt_two b
    rw [uMat_mulVec_inr, ite_eq_left (by rw [pvalM_eMinus_inr]; omega)]

theorem spinMatrix_minusX_mem [Finite K] (h4 : 4 ≤ Nat.card K) :
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
    ⟨g₀, la_mem_statedOmega h4 (coe_quadMinus (n + 1) K b c) _ (-1), rfl⟩,
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

end Block

section Minus

variable [Finite K] {n : ℕ}

theorem neg_one_mem_statedOmega_quadMinus_iff (h2 : (2 : K) ≠ 0)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {m : ℕ} (hm : 4 ≤ m) :
    (-1 : GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K) ∈ StatedOmega (StatedQuadMinus m K b c) ↔
      IsSquare ((-1 : K) ^ (m - 1) * (4 * c - b ^ 2)) := by
  have e : toLinEquiv (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K (-1) = LinearEquiv.neg K := by
    refine LinearEquiv.ext fun x => ?_
    rw [toLinEquiv_apply, Units.val_neg, Units.val_one, neg_mulVec, one_mulVec]
    rfl
  rw [statedOmega_eq_map_elementaryGroup (coe_quadMinus m K b c)
    (commutator_orthogonalGroup_quadMinus hm hirr), mem_map_equiv, MulEquiv.symm_symm, e,
    CFSG.ClassicalInvolution.neg_mem_elementaryGroup_quadMinus_iff h2 hirr hm]

omit [Finite K] in
theorem not_isSquare_discr (h2 : (2 : K) ≠ 0) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ¬ IsSquare (b ^ 2 - 4 * c) := by
  rintro ⟨d, hd⟩
  apply hirr ((d - b) / 2)
  field_simp
  linear_combination -hd

theorem conclZ_minus (hn : 2 ≤ n) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) (h5 : 5 ≤ p ^ f)
    {t : spinGroup (quadMinus (n + 3) K b c)}
    (htZ : t ∈ center (spinGroup (quadMinus (n + 3) K b c))) (ht1 : t ≠ 1)
    (htn : (t : CliffordAlgebra (quadMinus (n + 3) K b c)) ≠ -1) :
    ConclZ p f (spinGroup (quadMinus (n + 3) K b c)) t := by
  have hodd : Odd (Nat.card K) := hK ▸ (hp.odd_of_ne_two hp2).pow
  have h2 : (2 : K) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card K hodd
  have hf : 1 ≤ f := Nat.pos_of_ne_zero fun h => by simp [h] at h5
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
        center (StatedOmega (StatedQuadMinus (n + 1) K b c))) τ' n' p f := by
    rcases Nat.lt_or_ge n 3 with h | h
    · obtain rfl : n = 2 := by omega
      exact exists_lieModel_six hp hp2 hK h5 (coe_quadMinus 3 K b c)
        (nondegenerate_polarBilin_quadMinus_of_finite 3 K hirr) (by simp) hBq
    · exact ⟨.POmegaMinus, n + 1, Or.inl ⟨by decide, ⟨hp, hf, by omega⟩, K, inferInstance,
        inferInstance, hK, b, c, hirr,
        ⟨QuotientGroup.quotientMulEquivOfEq (center_statedOmega_quadMinus (by omega) hirr)⟩⟩⟩
  refine conclZ_of_block (Twisted.minusFrame (n + 3) b c).toHypFrame
    (nondegenerate_quadMinus_of_finite (n + 3) K hirr).ne_zero
    (mem_ker_spinMatrix_quadMinus_iff hirr)
    (by rw [coe_quadMinus]; exact range_spinMatrix_quadMinus (by omega) hirr)
    (range_spinAction_quadMinus (by omega) hirr).le (hZ.symm.trans hcomap).le hp hp2 hK h5
    (i := ⟨0, by omega⟩) (j := ⟨1, by omega⟩) (k := ⟨2, by omega⟩) (i' := ⟨2, by omega⟩)
    (j' := ⟨3, by omega⟩) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (eMinus n)
    (Q₂ := StatedQuadPlus 2 K) (by rw [coe_quadMinus]; exact pullQ_eMinus n)
    (spinMatrix_minusU hn) (spinMatrix_minusX_mem hn (by omega)) hBq ?_ hlie htZ ht1 htn
  intro hneg
  rw [coe_quadMinus, neg_one_mem_statedOmega_quadMinus_iff h2 hirr (by omega)] at hneg
  rcases Nat.lt_or_ge n 3 with h | h
  · obtain rfl : n = 2 := by omega
    refine neg_one_mem_statedOmega_quadMinus_three h2 (by omega) hirr ?_
    have e : (-1 : K) ^ (2 + 3 - 1) = 1 := by
      rw [show (2 + 3 - 1 : ℕ) = 4 from rfl]
      norm_num
    rwa [e, one_mul] at hneg
  · rw [neg_one_mem_statedOmega_quadMinus_iff h2 hirr (by omega)]
    have e : (-1 : K) ^ (n + 3 - 1) = (-1) ^ (n + 1 - 1) := by
      rw [show n + 3 - 1 = n + 1 - 1 + 2 by omega, pow_add, neg_one_sq, mul_one]
    rwa [e] at hneg

theorem false_of_minus_four (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (h2 : (2 : K) ≠ 0)
    {t : spinGroup (quadMinus 4 K b c)} (htZ : t ∈ center (spinGroup (quadMinus 4 K b c)))
    (ht1 : t ≠ 1) (htn : (t : CliffordAlgebra (quadMinus 4 K b c)) ≠ -1) : False := by
  obtain ⟨-, hcomap, hZ⟩ := spinToStatedProj_quadMinus (K := K) (n := 4) le_rfl hirr
  set F := (Twisted.minusFrame 4 b c).toHypFrame
  have hv₀ : quadMinus 4 K b c (F.vec ⟨0, by omega⟩ true + F.vec ⟨0, by omega⟩ false) = 1 := by
    have h1 := F.polar_vec_not ⟨0, by omega⟩ true
    rw [QuadraticMap.polar, F.map_vec, F.map_vec, sub_zero, sub_zero] at h1
    exact h1
  have hπt := spinMatrix_eq_neg_one (mem_ker_spinMatrix_quadMinus_iff hirr)
    (hZ.symm.trans hcomap).le hv₀ htZ ht1 htn
  have hneg : (-1 : GL (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) K) ∈
      StatedOmega (StatedQuadMinus 4 K b c) := by
    rw [← hπt, ← range_spinMatrix_quadMinus le_rfl hirr]
    exact MonoidHom.mem_range.mpr ⟨t, rfl⟩
  rw [neg_one_mem_statedOmega_quadMinus_iff h2 hirr le_rfl] at hneg
  refine not_isSquare_discr h2 hirr ?_
  have e : (-1 : K) ^ (4 - 1) * (4 * c - b ^ 2) = b ^ 2 - 4 * c := by
    rw [show (4 - 1 : ℕ) = 3 from rfl]
    ring
  rwa [e] at hneg

end Minus

end CFSG.ComponentClassification.HarrisLit.T1.P54.DB
