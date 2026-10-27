module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotQ2TenRModel
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotQ2EnnolaMinusChart

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap Module
open CFSG.ClassicalGroups.Orthogonal (HypPair)
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadMinus
  minusIndexEquiv)
open CFSG.Quasithin (perfectCore le_perfectCore_of_perfect)

section Gen

variable {K : Type} [Field K] [CharP K 2] [Finite K] {d : ℕ} {r : ℕ}
  {Q : QuadraticForm K (Fin d → K)} {a a' : Fin (r + 1) → Fin d → K} {F : Type} [Field F]

theorem IsEnnolaFrame.top_le_iSup_perfectCore_of_hypPair (hF : IsEnnolaFrame Q a a')
    (E : EnnolaParam K F) (hr : 2 ≤ r) (P : HypPair Q)
    (hPe : ∀ i : Fin (r + 1), i.val < 3 → polar Q (a i) P.e = 0 ∧ polar Q (a' i) P.e = 0)
    (hPf : ∀ i : Fin (r + 1), i.val < 3 → polar Q (a i) P.f = 0 ∧ polar Q (a' i) P.f = 0)
    (hperf : ⁅fixVecBar Q {a 0, a' 0}, fixVecBar Q {a 0, a' 0}⁆ = fixVecBar Q {a 0, a' 0}) :
    ⊤ ≤ ⨆ k, perfectCore (centralizer ((rootParam (K := F) k).map (hF.torus E) :
      Set (matrixProjectiveDerived Q))) := by
  let ix : Fin 3 → Fin (r + 1) := fun i => ⟨i, by omega⟩
  have hix : Function.Injective ix := fun i j h => Fin.ext (by simpa [ix] using congrArg Fin.val h)
  have hixlt : ∀ i : Fin 3, (ix i).val < 3 := fun i => i.isLt
  let v : Fin 3 → Bool → Fin d → K := fun i b => if b then a (ix i) else a' (ix i)
  have hv : OrthPairTriple Q v :=
    { one := fun i => (hF.unit (ix i)).polar_eq
      orth := fun i j hij s t => by
        have hij' : ix i ≠ ix j := hix.ne hij
        cases s <;> cases t
        · exact hF.orth_a'a' _ _ hij'
        · exact hF.orth_a'a hij'
        · exact hF.orth_aa' _ _ hij'
        · exact hF.orth_aa _ _ hij' }
  have hve : ∀ i s, polar Q (v i s) P.e = 0 := fun i s => by
    cases s
    · exact (hPe (ix i) (hixlt i)).2
    · exact (hPe (ix i) (hixlt i)).1
  have hvf : ∀ i s, polar Q (v i s) P.f = 0 := fun i s => by
    cases s
    · exact (hPf (ix i) (hixlt i)).2
    · exact (hPf (ix i) (hixlt i)).1
  have htop := hv.fixVecBar_sup_eq_top hF.regular hF.singular P hve hvf
  have hps : ∀ i : Fin 3, pairSet v i = {a (ix i), a' (ix i)} := fun i => by
    simp [pairSet, v]
  have hix0 : ix 0 = 0 := rfl
  set i1 : Fin (r + 1) := ix 1
  have h01 : (0 : Fin (r + 1)) ≠ i1 := fun h => by simpa [i1, ix] using congrArg Fin.val h
  set C : Fin (r + 1) → Subgroup (matrixProjectiveDerived Q) := fun k =>
    perfectCore (centralizer ((rootParam (K := F) k).map (hF.torus E) :
      Set (matrixProjectiveDerived Q))) with hC
  have hD0 : fixVecBar Q {a 0, a' 0} ≤ C 0 :=
    le_perfectCore_of_perfect (hF.fixVecBar_le_centralizer E 0) hperf
  set W : orthDerived Q := ⟨ennolaSwap Q a a' 0 i1, hF.ennolaSwap_mem_orthDerived 0 i1⟩
  have hD1eq : (fixVecBar Q {a 0, a' 0}).map (MulAut.conj (projHom Q W)).toMonoidHom =
      fixVecBar Q {a i1, a' i1} := by
    rw [map_conj_fixVecBar]
    congr 1
    change (ennolaSwap Q a a' 0 i1) '' {a 0, a' 0} = _
    rw [Set.image_insert_eq, Set.image_singleton, hF.planeSwap_left h01, hF.planeSwap_right h01,
      Equiv.swap_apply_left]
  have hD1 : fixVecBar Q {a i1, a' i1} ≤ C i1 := by
    refine le_perfectCore_of_perfect (hF.fixVecBar_le_centralizer E i1) ?_
    rw [← hD1eq, ← Subgroup.map_commutator, hperf]
  calc (⊤ : Subgroup (matrixProjectiveDerived Q))
      = fixVecBar Q (pairSet v 0 ∪ pairSet v 1) ⊔ fixVecBar Q (pairSet v 0 ∪ pairSet v 2) ⊔
          fixVecBar Q (pairSet v 1 ∪ pairSet v 2) := htop.symm
    _ ≤ C 0 ⊔ C i1 := by
        refine sup_le (sup_le ?_ ?_) ?_
        · refine le_sup_of_le_left ((fixVecBar_anti Set.subset_union_left).trans ?_)
          rw [hps, hix0]
          exact hD0
        · refine le_sup_of_le_left ((fixVecBar_anti Set.subset_union_left).trans ?_)
          rw [hps, hix0]
          exact hD0
        · refine le_sup_of_le_right ((fixVecBar_anti Set.subset_union_left).trans ?_)
          rw [hps]
          exact hD1
    _ ≤ ⨆ k, C k := sup_le (le_iSup C 0) (le_iSup C i1)

end Gen

section Minus

variable {K : Type} [Field K] [CharP K 2] [Finite K] {r : ℕ} {F : Type} [Field F]
  (E : EnnolaParam K F)

theorem top_le_iSup_minusTorus_of_three_le (hr : 3 ≤ r) (hirr : ∀ s : K, s ^ 2 + 1 * s + 1 ≠ 0) :
    ⊤ ≤ ⨆ k, perfectCore (centralizer ((rootParam (K := F) k).map
      ((isEnnolaFrame_minus (by omega : 2 ≤ r) hirr).torus E) :
        Set (matrixProjectiveDerived (coordinateQuadMinus (r + 2) K (by omega) 1 1)))) := by
  have hn : 1 ≤ r + 2 := by omega
  have hS := isHypSystem_minus (K := K) hn 1 1
  have hP := isHypCoord_coordinateQuadMinus (K := K) hn 1 1 (⟨3, by omega⟩ : Fin (r + 2 - 1))
  have he : hP.hypPair.e = minusHypE (K := K) hn 3 := by
    rw [hP.hypPair_e, minusHypE_of_lt hn (by omega)]
  have hf : hP.hypPair.f = minusHypF (K := K) hn 3 := by
    rw [hP.hypPair_f, minusHypF_of_lt hn (by omega)]
  have hA := polar_aniso_minusHyp (K := K) hn hirr 3
  refine (isEnnolaFrame_minus (by omega : 2 ≤ r) hirr).top_le_iSup_perfectCore_of_hypPair E
    (by omega) hP.hypPair ?_ ?_ ?_
  · intro i hi
    rw [he]
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
    · rw [minusFrameA_zero, minusFrameA'_zero]
      exact ⟨hA.1, hA.2.2.1⟩
    · rw [minusFrameA_succ, minusFrameA'_succ]
      have hj : j.val < 2 := by
        rw [Fin.val_succ] at hi
        omega
      obtain ⟨h1, -, h3, -⟩ := hS.polar_blockVec_of_ne j.val (l := 3) (by omega) (by omega)
      exact ⟨h1, h3⟩
  · intro i hi
    rw [hf]
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
    · rw [minusFrameA_zero, minusFrameA'_zero]
      exact ⟨hA.2.1, hA.2.2.2⟩
    · rw [minusFrameA_succ, minusFrameA'_succ]
      have hj : j.val < 2 := by
        rw [Fin.val_succ] at hi
        omega
      obtain ⟨-, h2, -, h4⟩ := hS.polar_blockVec_of_ne j.val (l := 3) (by omega) (by omega)
      exact ⟨h2, h4⟩
  · rw [minusFrameA_zero, minusFrameA'_zero, ← pairPerpOf_eq_fixVecBar]
    exact Subgroup.isPerfect_iff.mp (isQuasisimple_anisoPerp (n := r + 2) (by omega) hirr).1

end Minus

theorem omegaMinusTwoEnnolaModelInputAt_of_three_le {r : ℕ} (hr : 3 ≤ r) :
    OmegaMinusTwoEnnolaModelInputAt r hr := by
  intro K _ _ _ b c hirr hK2 F _ _ _ hF σ hσ k₀ _ hσk φ
  have hone : ∀ x : K, x ≠ 0 → x = 1 := fun x hx => by
    have := Fintype.ofFinite K
    have h := FiniteField.pow_card x
    rw [Fintype.card_eq_nat_card, hK2, _root_.sq] at h
    exact mul_left_cancel₀ hx (by rw [h, mul_one])
  obtain rfl : b = 1 := hone b (coeff_ne_zero_of_irreducible' hirr)
  obtain rfl : c = 1 := hone c (fun h0 => hirr 0 (by rw [h0]; ring))
  obtain ⟨E, hE⟩ := exists_ennolaParam hK2 hF hσ hσk φ
  set hFr := isEnnolaFrame_minus (K := K) (by omega : 2 ≤ r) hirr
  refine ⟨hFr.torus E, map_rootParam_minusTorus E (by omega) hirr,
    fun k => hFr.exists_weyl E (Fin.cycleRange k), ?_, top_le_iSup_minusTorus_of_three_le E hr hirr⟩
  obtain ⟨g, hg, hgt⟩ := minus_chart E (by omega : 2 ≤ r) hirr φ hE
  exact ⟨g, hg, fun t ht => hgt t ht⟩

theorem omegaMinusTwoEnnolaModelInputAt_three : OmegaMinusTwoEnnolaModelInputAt 3 le_rfl :=
  omegaMinusTwoEnnolaModelInputAt_of_three_le le_rfl

end CFSG.SeitzReduction.OmegaPilot
