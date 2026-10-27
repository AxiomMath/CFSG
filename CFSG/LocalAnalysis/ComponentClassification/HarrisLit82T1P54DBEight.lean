module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P54DBPlus

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P54.DB

open CFSG Subgroup Matrix Assembly.LowTwoRank CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal
open scoped MatrixGroups

variable {K : Type} [Field K]

theorem pval_lt {N : ℕ} (k : Fin N ⊕ Fin N) : pval k < N := by
  rcases k with a | a <;> exact a.isLt

theorem spinAction_neg_mul_eight (x : Fin 4 ⊕ Fin 4 → K) :
    -((plusFrame 4 K (by norm_num)).toFrame (i := ⟨0, by omega⟩) (j := ⟨1, by omega⟩) (by simp)
      true true).La (-1) x =
      ((plusFrame 4 K (by norm_num)).toFrame (i := ⟨2, by omega⟩) (j := ⟨3, by omega⟩) (by simp)
        true true).La (-1) x := by
  funext k
  rw [Pi.neg_apply, La_plus_apply, La_plus_apply]
  have := pval_lt k
  dsimp only
  by_cases h : pval k = 0 ∨ pval k = 1
  · rw [ite_eq_left h, ite_eq_right (by omega), neg_neg]
  · rw [ite_eq_right h, ite_eq_left (by omega)]

variable [Finite K]

theorem conclZ_eight {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f)
    (h5 : 5 ≤ p ^ f) {t : spinGroup (quadPlus 4 K)} (htZ : t ∈ center (spinGroup (quadPlus 4 K)))
    (ht1 : t ≠ 1) (htn : (t : CliffordAlgebra (quadPlus 4 K)) ≠ -1) :
    ConclZ p f (spinGroup (quadPlus 4 K)) t := by
  have hodd : Odd (Nat.card K) := hK ▸ (hp.odd_of_ne_two hp2).pow
  have h2 : (2 : K) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card K hodd
  have hf : 1 ≤ f := Nat.pos_of_ne_zero fun h => by simp [h] at h5
  have hQ := (nondegenerate_quadPlus 4 K).ne_zero
  obtain ⟨-, hcomap, hZc⟩ := spinToStatedProj_quadPlus (K := K) (n := 4) (by norm_num)
  have hcen := (hZc.symm.trans hcomap).le
  have hZ := DA.smul_of_le_comap hcen
  have hker := mem_ker_spinMatrix_quadPlus_iff (n := 4) (K := K)
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
  have hneg1 : spinAction (quadPlus 4 K) (CliffordAlgebra.spinGroup.negOne _ hQ) = 1 := by
    have h1 := (hker _).mpr (Or.inr (CliffordAlgebra.spinGroup.coe_negOne _ hQ))
    rw [ker_spinMatrix] at h1
    exact h1
  have hz : t * F.longSL2 h01 true true (-1) * (F.longSL2 h23 true true (-1))⁻¹ ∈
      (spinMatrix (quadPlus 4 K)).ker := by
    rw [ker_spinMatrix, MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one]
    refine LinearEquiv.ext fun v => ?_
    rw [map_mul, LinearEquiv.mul_apply, hta, T1.spinAction_longSL2, T1.spinAction_longSL2]
    exact spinAction_neg_mul_eight v
  obtain ⟨s, hs⟩ := ker_mul_longSL2 F hQ hker h23 hz
  rw [inv_mul_cancel_right] at hs
  have := T1.finite_range_longSL2 F h23 true s
  have hs₂ := T1.isSLTwoOver_range_longSL2 F h23 hK true s
  have hC : centralizer {F.longSL2 h23 true s (-1)} =
      centralizer {F.longSL2 h01 true true (-1)} := by
    rw [← hs]
    exact T1.centralizer_mul_of_mem_center htZ
  have hJc : IsTwoComponentIn (F.longSL2 h23 true s).range
      (centralizer {F.longSL2 h01 true true (-1)}) := by
    rw [← hC]
    exact T1.isTwoComponentIn_range_longSL2 F h23 hp hp2 hK h5
      (range_spinAction_quadPlus (by norm_num)).le true s
  have hJu : ∀ s', F.longSL2 h01 true s' (-1) ∉ (F.longSL2 h23 true s).range := by
    intro s' ⟨A, hA⟩
    have hact : spinAction (quadPlus 4 K) (F.longSL2 h01 true s' (-1)) =
        spinAction (quadPlus 4 K) (F.longSL2 h01 true true (-1)) := by
      cases s'
      · have h := T1.longSL2_neg_one_not F h01 hQ true true
        rw [Bool.not_true] at h
        rw [h, map_mul, hneg1, one_mul]
      · rfl
    have h1 := congrArg (fun g => spinAction (quadPlus 4 K) g (F.vec ⟨0, by omega⟩ true)
      (.inl ⟨0, by omega⟩)) hA
    simp only at h1
    rw [hact, T1.spinAction_longSL2,
      (F.toFrame h23 true s).La_apply_of_coords_eq_zero A
        (DA.coords_vec_of_ne F h23 (k := ⟨0, by omega⟩) (by simp) (by simp) true s true),
      T1.spinAction_longSL2, La_plus_apply, ite_eq_left (by left; rfl)] at h1
    have hv : F.vec ⟨0, by omega⟩ true (.inl ⟨0, by omega⟩) = 1 := by simp [hF]
    rw [hv] at h1
    exact h2 (by linear_combination h1)
  refine conclZ_of_frame F h01 (k := ⟨2, by omega⟩) (by simp) (by simp) hp hp2 hK h5
    (range_spinAction_quadPlus (by norm_num)).le hZ hQ hJc hJu
    (isQuasisimple_of_isSLTwoOver hp hp2 h5 hs₂).1
    ⟨F.longSL2 h23 true s (-1), MonoidHom.mem_range.mpr ⟨-1, rfl⟩,
      T1.orderOf_longSL2_neg_one F h23 hodd true s,
      DA.longSL2_neg_one_not_mem_center F hodd hZ h23 (k := ⟨0, by omega⟩) (by simp) (by simp)
        true s⟩
    ⟨.PSL, 2, (Lemma47.sl2_facts hp hp2 hf h5 hs₂).2.2.1⟩ (s := true) ?_
  rw [hs]
  exact MonoidHom.mem_range.mpr ⟨-1, rfl⟩

end CFSG.ComponentClassification.HarrisLit.T1.P54.DB
