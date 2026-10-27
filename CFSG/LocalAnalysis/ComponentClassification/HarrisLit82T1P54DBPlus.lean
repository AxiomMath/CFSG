module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P54DBSix

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P54.DB

open CFSG Subgroup Matrix Assembly.LowTwoRank CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
open scoped MatrixGroups

variable {K : Type} [Field K]

@[expose] def pval {N : ℕ} : Fin N ⊕ Fin N → ℕ :=
  Sum.elim (fun a => a) fun a => a

theorem La_plus_apply {m : ℕ} (hm : 3 ≤ m) {i j : Fin m} (hij : i ≠ j) (x : Fin m ⊕ Fin m → K)
    (k : Fin m ⊕ Fin m) :
    ((plusFrame m K hm).toFrame hij true true).La (-1) x k =
      if pval k = i ∨ pval k = j then -x k else x k := by
  rw [Frame.La_neg_one_apply, Frame.incl_apply, Frame.coords_apply]
  rcases k with a | a
  · simp [HypFrame.toFrame, Frame.e₁, Frame.f₁, Frame.e₂, Frame.f₂, polar_quadPlus_single_inl,
      polar_quadPlus_single_inr, Pi.single_apply]
    simp only [pval, Sum.elim_inl, ← Fin.ext_iff]
    exact ite_two hij (fun b => x (.inl b)) a
  · simp [HypFrame.toFrame, Frame.e₁, Frame.f₁, Frame.e₂, Frame.f₂, polar_quadPlus_single_inl,
      polar_quadPlus_single_inr, Pi.single_apply]
    simp only [pval, Sum.elim_inr, ← Fin.ext_iff]
    exact ite_two hij (fun b => x (.inr b)) a

section Split

variable (n : ℕ)

@[expose] def splitEquiv : Fin n ⊕ Fin 2 ≃ Fin (n + 2) :=
  ((Equiv.sumComm (Fin n) (Fin 2)).trans finSumFinEquiv).trans (finCongr (Nat.add_comm 2 n))

theorem val_splitEquiv_inl (i : Fin n) : ((splitEquiv n (.inl i) : Fin (n + 2)) : ℕ) = i + 2 := by
  simp [splitEquiv]

theorem val_splitEquiv_inr (j : Fin 2) : ((splitEquiv n (.inr j) : Fin (n + 2)) : ℕ) = j := by
  simp [splitEquiv]

@[expose] def ePlus : (Fin n ⊕ Fin n) ⊕ (Fin 2 ⊕ Fin 2) ≃ Fin (n + 2) ⊕ Fin (n + 2) :=
  (Equiv.sumSumSumComm _ _ _ _).trans (Equiv.sumCongr (splitEquiv n) (splitEquiv n))

theorem pval_ePlus_inl (a : Fin n ⊕ Fin n) : pval (ePlus n (.inl a)) = pval a + 2 := by
  rcases a with i | i <;> exact val_splitEquiv_inl n i

theorem pval_ePlus_inr (b : Fin 2 ⊕ Fin 2) : pval (ePlus n (.inr b)) = pval b := by
  rcases b with j | j <;> exact val_splitEquiv_inr n j

theorem pval_lt_two (b : Fin 2 ⊕ Fin 2) : pval b < 2 := by
  rcases b with j | j <;> exact j.isLt

theorem pullQ_ePlus :
    pullQ (ePlus n) (StatedQuadPlus (n + 2) K) =
      sumQ (StatedQuadPlus n K) (StatedQuadPlus 2 K) := by
  funext v
  have h1 : ∀ x, (ePlus n).symm (.inl (splitEquiv n x)) =
      Sum.elim (fun i => .inl (.inl i)) (fun j => .inr (.inl j)) x := by
    rintro (i | j) <;> rw [Equiv.symm_apply_eq] <;> rfl
  have h2 : ∀ x, (ePlus n).symm (.inr (splitEquiv n x)) =
      Sum.elim (fun i => .inl (.inr i)) (fun j => .inr (.inr j)) x := by
    rintro (i | j) <;> rw [Equiv.symm_apply_eq] <;> rfl
  simp only [pullQ, sumQ, StatedQuadPlus, Function.comp_apply]
  rw [← (splitEquiv n).sum_comp, Fintype.sum_sum_type]
  simp only [h1, h2, Sum.elim_inl, Sum.elim_inr]

end Split

section Block

variable {n : ℕ} (hn : 3 ≤ n)

include hn in
theorem spinMatrix_plusU :
    spinMatrix (quadPlus (n + 2) K) ((plusFrame (n + 2) K (by omega)).longSL2
      (i := ⟨0, by omega⟩) (j := ⟨1, by omega⟩) (by simp) true true (-1)) =
      uMat (ePlus n) := by
  refine spinMatrix_eq_of_apply (ePlus n) fun v y => ?_
  rw [T1.spinAction_longSL2, La_plus_apply]
  dsimp only
  rcases y with a | b
  · rw [uMat_mulVec_inl, ite_eq_right (by rw [pval_ePlus_inl]; omega)]
  · have := pval_lt_two b
    rw [uMat_mulVec_inr, ite_eq_left (by rw [pval_ePlus_inr]; omega)]

theorem spinMatrix_plusX_mem [Finite K] (h4 : 4 ≤ Nat.card K) :
    spinMatrix (quadPlus (n + 2) K) ((plusFrame (n + 2) K (by omega)).longSL2
      (i := ⟨2, by omega⟩) (j := ⟨3, by omega⟩) (by simp) true true (-1)) ∈
      rblock (ePlus n) (StatedQuadPlus n K) := by
  set fr := (plusFrame n K hn).toFrame (i := ⟨0, by omega⟩) (j := ⟨1, by omega⟩)
    (by simp) true true with hfr
  set g₀ := (toLinEquiv (Fin n ⊕ Fin n) K).symm (fr.La (-1)) with hg₀
  have hg : ∀ w, (g₀ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ w = fr.La (-1) w := by
    intro w
    rw [← toLinEquiv_apply, hg₀, MulEquiv.apply_symm_apply]
  refine ⟨blockL (Fin 2 ⊕ Fin 2) g₀, ⟨g₀, la_mem_statedOmega h4 (coe_quadPlus n K) _ (-1), rfl⟩,
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

end Block

section Plus

variable [Finite K] {n : ℕ}

theorem neg_one_mem_statedOmega_quadPlus_iff (h2 : (2 : K) ≠ 0) {m : ℕ} (hm : 3 ≤ m) :
    (-1 : GL (Fin m ⊕ Fin m) K) ∈ StatedOmega (StatedQuadPlus m K) ↔
      IsSquare ((-1 : K) ^ m) := by
  have e : toLinEquiv (Fin m ⊕ Fin m) K (-1) = LinearEquiv.neg K := by
    refine LinearEquiv.ext fun x => ?_
    rw [toLinEquiv_apply, Units.val_neg, Units.val_one, neg_mulVec, one_mulVec]
    rfl
  rw [statedOmega_eq_map_elementaryGroup (coe_quadPlus m K)
    (commutator_orthogonalGroup_quadPlus hm), mem_map_equiv, MulEquiv.symm_symm, e,
    CFSG.ClassicalInvolution.neg_mem_elementaryGroup_quadPlus_iff h2 hm]

theorem conclZ_plus (hn : 3 ≤ n) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) (h5 : 5 ≤ p ^ f) {t : spinGroup (quadPlus (n + 2) K)}
    (htZ : t ∈ center (spinGroup (quadPlus (n + 2) K))) (ht1 : t ≠ 1)
    (htn : (t : CliffordAlgebra (quadPlus (n + 2) K)) ≠ -1) :
    ConclZ p f (spinGroup (quadPlus (n + 2) K)) t := by
  have hodd : Odd (Nat.card K) := hK ▸ (hp.odd_of_ne_two hp2).pow
  have h2 : (2 : K) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card K hodd
  have hf : 1 ≤ f := Nat.pos_of_ne_zero fun h => by simp [h] at h5
  have : Finite (spinGroup (quadPlus (n + 2) K)) :=
    LieType.Steinberg.finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadPlus (n := n + 2))
  obtain ⟨-, hcomap, hZ⟩ := spinToStatedProj_quadPlus (K := K) (n := n + 2) (by omega)
  have hlie : ∃ (τ' : StatedLieTag) (n' : ℕ), Blueprint.LieModel
      (StatedOmega (StatedQuadPlus n K) ⧸ center (StatedOmega (StatedQuadPlus n K))) τ' n' p f := by
    rcases Nat.lt_or_ge n 4 with h | h
    · obtain rfl : n = 3 := by omega
      exact exists_lieModel_six hp hp2 hK h5 (coe_quadPlus 3 K)
        (nondegenerate_polarBilin_quadPlus 3 K) (by simp)
        (isQuasisimple_statedOmega_quadPlus le_rfl)
    · exact ⟨.POmegaPlus, n, Or.inl ⟨by decide, ⟨hp, hf, h⟩, K, inferInstance, inferInstance, hK,
        ⟨QuotientGroup.quotientMulEquivOfEq (center_statedOmega_quadPlus hn)⟩⟩⟩
  refine conclZ_of_block (plusFrame (n + 2) K (by omega))
    (nondegenerate_quadPlus (n + 2) K).ne_zero (mem_ker_spinMatrix_quadPlus_iff)
    (by rw [coe_quadPlus]; exact range_spinMatrix_quadPlus (by omega))
    (range_spinAction_quadPlus (by omega)).le (hZ.symm.trans hcomap).le hp hp2 hK h5
    (i := ⟨0, by omega⟩) (j := ⟨1, by omega⟩) (k := ⟨2, by omega⟩) (i' := ⟨2, by omega⟩)
    (j' := ⟨3, by omega⟩) (by simp) (by simp) (by simp)
    (by simp) (by simp) (by simp) (ePlus n)
    (Q₂ := StatedQuadPlus 2 K) (by rw [coe_quadPlus]; exact pullQ_ePlus n) (spinMatrix_plusU hn)
    (spinMatrix_plusX_mem hn (by omega)) (isQuasisimple_statedOmega_quadPlus hn) ?_ hlie htZ ht1
    htn
  intro hneg
  rw [coe_quadPlus, neg_one_mem_statedOmega_quadPlus_iff h2 (by omega)] at hneg
  rw [neg_one_mem_statedOmega_quadPlus_iff h2 hn]
  rwa [pow_add, neg_one_sq, mul_one] at hneg

end Plus

end CFSG.ComponentClassification.HarrisLit.T1.P54.DB
