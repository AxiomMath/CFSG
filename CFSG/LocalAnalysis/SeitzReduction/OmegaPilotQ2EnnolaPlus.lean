module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotQ2EnnolaBlock
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotQ2TenFrame

public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap Module
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadMinus
  coordinateQuadPlus minusIndexEquiv plusIndexEquiv)
open CFSG.Quasithin (perfectCore)

theorem IsAnisoCoord.isUnitPlane {K : Type} [Field K] [CharP K 2] {d : ℕ}
    {Q : QuadraticForm K (Fin d → K)} {a a' : Fin d} (h : IsAnisoCoord Q a a' 1 1) :
    IsUnitPlane Q (Pi.single a 1) (Pi.single a' 1) :=
  ⟨h.map_left, h.map_right, by rw [h.polar_left, Pi.single_eq_same, one_mul]⟩

section Plus

variable {K : Type} [Field K] [CharP K 2] {m : ℕ}

@[expose] noncomputable def plusHypE (l : ℕ) : Fin (2 * (m + 2)) → K :=
  if h : l < m then Pi.single (plusIndexEquiv (m + 2) (.inl (⟨l, h⟩ : Fin m).succ.succ)) 1 else 0

@[expose] noncomputable def plusHypF (l : ℕ) : Fin (2 * (m + 2)) → K :=
  if h : l < m then Pi.single (plusIndexEquiv (m + 2) (.inr (⟨l, h⟩ : Fin m).succ.succ)) 1 else 0

theorem plusHypE_of_lt {l : ℕ} (h : l < m) :
    plusHypE (K := K) (m := m) l =
      Pi.single (plusIndexEquiv (m + 2) (.inl (⟨l, h⟩ : Fin m).succ.succ)) 1 := by
  rw [plusHypE, dite_eq_left_of_eq_true (eq_true h)]

theorem plusHypF_of_lt {l : ℕ} (h : l < m) :
    plusHypF (K := K) (m := m) l =
      Pi.single (plusIndexEquiv (m + 2) (.inr (⟨l, h⟩ : Fin m).succ.succ)) 1 := by
  rw [plusHypF, dite_eq_left_of_eq_true (eq_true h)]

theorem plusHypE_of_not_lt {l : ℕ} (h : ¬l < m) : plusHypE (K := K) (m := m) l = 0 := by
  rw [plusHypE, dite_eq_right_of_eq_false (eq_false h)]

theorem plusHypF_of_not_lt {l : ℕ} (h : ¬l < m) : plusHypF (K := K) (m := m) l = 0 := by
  rw [plusHypF, dite_eq_right_of_eq_false (eq_false h)]

theorem plusIndex_ne {s s' : Fin (m + 2) ⊕ Fin (m + 2)} (h : s ≠ s') :
    plusIndexEquiv (m + 2) s ≠ plusIndexEquiv (m + 2) s' :=
  (plusIndexEquiv (m + 2)).injective.ne h

theorem isHypSystem_plus (b c : K) :
    IsHypSystem (plusAnisoQuad K m b c) m (plusHypE (m := m)) (plusHypF (m := m)) where
  map_e l := by
    by_cases h : l < m
    · rw [plusHypE_of_lt h]
      exact (isHypCoord_plusAnisoQuad b c _).map_left
    · rw [plusHypE_of_not_lt h, QuadraticMap.map_zero]
  map_f l := by
    by_cases h : l < m
    · rw [plusHypF_of_lt h]
      exact (isHypCoord_plusAnisoQuad b c _).map_right
    · rw [plusHypF_of_not_lt h, QuadraticMap.map_zero]
  ee l l' := by
    by_cases h : l < m
    · by_cases h' : l' < m
      · rw [plusHypE_of_lt h, plusHypE_of_lt h', (isHypCoord_plusAnisoQuad b c _).polar_left]
        exact Pi.single_eq_of_ne (plusIndex_ne (by simp)) _
      · rw [plusHypE_of_not_lt h', polar_zero_right]
    · rw [plusHypE_of_not_lt h, polar_zero_left]
  ff l l' := by
    by_cases h : l < m
    · by_cases h' : l' < m
      · rw [plusHypF_of_lt h, plusHypF_of_lt h', (isHypCoord_plusAnisoQuad b c _).polar_right]
        exact Pi.single_eq_of_ne (plusIndex_ne (by simp)) _
      · rw [plusHypF_of_not_lt h', polar_zero_right]
    · rw [plusHypF_of_not_lt h, polar_zero_left]
  ef l l' hll := by
    by_cases h : l < m
    · by_cases h' : l' < m
      · rw [plusHypE_of_lt h, plusHypF_of_lt h', (isHypCoord_plusAnisoQuad b c _).polar_left]
        refine Pi.single_eq_of_ne (plusIndex_ne ?_) _
        simp only [ne_eq, Sum.inr.injEq, Fin.succ_inj, Fin.mk.injEq]
        exact fun h'' => hll h''
      · rw [plusHypF_of_not_lt h', polar_zero_right]
    · rw [plusHypE_of_not_lt h, polar_zero_left]
  ef_self l h := by
    rw [plusHypE_of_lt h, plusHypF_of_lt h, (isHypCoord_plusAnisoQuad b c _).polar_left,
      Pi.single_eq_same]

theorem polar_aniso_plusHyp {b c : K} {i : Fin (m + 2)}
    (hA : IsAnisoCoord (plusAnisoQuad K m b c) (plusIndexEquiv (m + 2) (.inl i))
      (plusIndexEquiv (m + 2) (.inr i)) b c) (hi : ∀ j : Fin m, j.succ.succ ≠ i) (l : ℕ) :
    (polar (plusAnisoQuad K m b c) (Pi.single (plusIndexEquiv (m + 2) (.inl i)) 1)
        (plusHypE l) = 0 ∧
      polar (plusAnisoQuad K m b c) (Pi.single (plusIndexEquiv (m + 2) (.inl i)) 1)
        (plusHypF l) = 0) ∧
    (polar (plusAnisoQuad K m b c) (Pi.single (plusIndexEquiv (m + 2) (.inr i)) 1)
        (plusHypE l) = 0 ∧
      polar (plusAnisoQuad K m b c) (Pi.single (plusIndexEquiv (m + 2) (.inr i)) 1)
        (plusHypF l) = 0) := by
  by_cases h : l < m
  · have hl : (Sum.inl i : Fin (m + 2) ⊕ Fin (m + 2)) ≠ Sum.inl (⟨l, h⟩ : Fin m).succ.succ :=
      fun h' => hi ⟨l, h⟩ (Sum.inl_injective h').symm
    have hr : (Sum.inr i : Fin (m + 2) ⊕ Fin (m + 2)) ≠ Sum.inr (⟨l, h⟩ : Fin m).succ.succ :=
      fun h' => hi ⟨l, h⟩ (Sum.inr_injective h').symm
    rw [plusHypE_of_lt h, plusHypF_of_lt h, hA.polar_left, hA.polar_left, hA.polar_right,
      hA.polar_right, Pi.single_eq_of_ne (plusIndex_ne (by simp)),
      Pi.single_eq_of_ne (plusIndex_ne hr), Pi.single_eq_of_ne (plusIndex_ne hl),
      Pi.single_eq_of_ne (plusIndex_ne (by simp)), mul_zero]
    exact ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩
  · rw [plusHypE_of_not_lt h, plusHypF_of_not_lt h, polar_zero_right, polar_zero_right]
    exact ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

theorem fin_succ_succ_ne_zero' (j : Fin m) : (j.succ.succ : Fin (m + 2)) ≠ 0 :=
  Fin.succ_ne_zero _

end Plus

section Frame

variable {K : Type} [Field K] [CharP K 2] {m' : ℕ}

@[expose] noncomputable def plusFrameA (m' : ℕ) : Fin (m' + 2) → Fin (2 * (m' + 1 + 2)) → K :=
  Fin.cons (Pi.single (plusIndexEquiv (m' + 1 + 2) (.inl 0)) 1)
    (Fin.cons (Pi.single (plusIndexEquiv (m' + 1 + 2) (.inl 1)) 1)
      fun i : Fin m' => blockVec (plusHypE (K := K) (m := m' + 1)) plusHypF i)

@[expose] noncomputable def plusFrameA' (m' : ℕ) : Fin (m' + 2) → Fin (2 * (m' + 1 + 2)) → K :=
  Fin.cons (Pi.single (plusIndexEquiv (m' + 1 + 2) (.inr 0)) 1)
    (Fin.cons (Pi.single (plusIndexEquiv (m' + 1 + 2) (.inr 1)) 1)
      fun i : Fin m' => blockVec' (plusHypE (K := K) (m := m' + 1)) plusHypF i)

theorem plusFrameA_zero :
    plusFrameA (K := K) m' 0 = Pi.single (plusIndexEquiv (m' + 1 + 2) (.inl 0)) 1 :=
  Fin.cons_zero _ _

theorem plusFrameA'_zero :
    plusFrameA' (K := K) m' 0 = Pi.single (plusIndexEquiv (m' + 1 + 2) (.inr 0)) 1 :=
  Fin.cons_zero _ _

theorem plusFrameA_succ (k : Fin (m' + 1)) :
    plusFrameA (K := K) m' k.succ =
      (Fin.cons (Pi.single (plusIndexEquiv (m' + 1 + 2) (.inl 1)) 1)
        (fun i : Fin m' => blockVec (plusHypE (K := K) (m := m' + 1)) plusHypF i) :
          Fin (m' + 1) → Fin (2 * (m' + 1 + 2)) → K) k :=
  Fin.cons_succ _ _ _

theorem plusFrameA'_succ (k : Fin (m' + 1)) :
    plusFrameA' (K := K) m' k.succ =
      (Fin.cons (Pi.single (plusIndexEquiv (m' + 1 + 2) (.inr 1)) 1)
        (fun i : Fin m' => blockVec' (plusHypE (K := K) (m := m' + 1)) plusHypF i) :
          Fin (m' + 1) → Fin (2 * (m' + 1 + 2)) → K) k :=
  Fin.cons_succ _ _ _

theorem isOrthUnitFamily_plusFrame (hirr : ∀ s : K, s ^ 2 + 1 * s + 1 ≠ 0) :
    IsOrthUnitFamily (plusAnisoQuad K (m' + 1) 1 1) (plusFrameA m') (plusFrameA' m') := by
  have hS := isHypSystem_plus (K := K) (m := m' + 1) 1 1
  have hB := hS.isOrthUnitFamily_blocks (n := m') fun i hi => by omega
  have hA0 : IsAnisoCoord (plusAnisoQuad K (m' + 1) 1 1) (plusIndexEquiv (m' + 1 + 2) (.inl 0))
      (plusIndexEquiv (m' + 1 + 2) (.inr 0)) 1 1 := isAnisoCoord_plusAnisoQuad hirr
  have hA1 := isAnisoCoord_plusAnisoQuad_one (K := K) (m := m' + 1) hirr
  have h0 := polar_aniso_plusHyp hA0 (fun j => fin_succ_succ_ne_zero' j)
  have h1 := polar_aniso_plusHyp hA1 (fun j => fin_succ_succ_ne_one j)
  have hp : ∀ (w : Fin (2 * (m' + 1 + 2)) → K), (∀ l,
      polar (plusAnisoQuad K (m' + 1) 1 1) w (plusHypE l) = 0 ∧
        polar (plusAnisoQuad K (m' + 1) 1 1) w (plusHypF l) = 0) →
      ∀ i : Fin m', polar (plusAnisoQuad K (m' + 1) 1 1) w
          (blockVec (plusHypE (m := m' + 1)) plusHypF i) = 0 ∧
        polar (plusAnisoQuad K (m' + 1) 1 1) w
          (blockVec' (plusHypE (m := m' + 1)) plusHypF i) = 0 :=
    fun w hw i => hS.polar_blockVec_of_perp i fun l _ => hw l
  have hU1 := hp _ fun l => (h1 l).1
  have hV1 := hp _ fun l => (h1 l).2
  have hU0 := hp _ fun l => (h0 l).1
  have hV0 := hp _ fun l => (h0 l).2
  have hI := hB.cons hA1.isUnitPlane (fun k => (hU1 k).1) (fun k => (hU1 k).2) (fun k => (hV1 k).1)
    (fun k => (hV1 k).2)
  have e01 : polar (plusAnisoQuad K (m' + 1) 1 1)
      (Pi.single (plusIndexEquiv (m' + 1 + 2) (.inl 0)) 1)
      (Pi.single (plusIndexEquiv (m' + 1 + 2) (.inl 1)) 1) = 0 := by
    rw [hA0.polar_left, Pi.single_eq_of_ne (plusIndex_ne (by simp)), mul_zero]
  have e01' : polar (plusAnisoQuad K (m' + 1) 1 1)
      (Pi.single (plusIndexEquiv (m' + 1 + 2) (.inl 0)) 1)
      (Pi.single (plusIndexEquiv (m' + 1 + 2) (.inr 1)) 1) = 0 := by
    rw [hA0.polar_left, Pi.single_eq_of_ne (plusIndex_ne (by simp [fin_one_ne_zero'.symm])),
      mul_zero]
  have e0'1 : polar (plusAnisoQuad K (m' + 1) 1 1)
      (Pi.single (plusIndexEquiv (m' + 1 + 2) (.inr 0)) 1)
      (Pi.single (plusIndexEquiv (m' + 1 + 2) (.inl 1)) 1) = 0 := by
    rw [hA0.polar_right, Pi.single_eq_of_ne (plusIndex_ne (by simp [fin_one_ne_zero'.symm])),
      mul_zero]
  have e0'1' : polar (plusAnisoQuad K (m' + 1) 1 1)
      (Pi.single (plusIndexEquiv (m' + 1 + 2) (.inr 0)) 1)
      (Pi.single (plusIndexEquiv (m' + 1 + 2) (.inr 1)) 1) = 0 := by
    rw [hA0.polar_right, Pi.single_eq_of_ne (plusIndex_ne (by simp)), mul_zero]
  refine hI.cons hA0.isUnitPlane (fun k => ?_) (fun k => ?_) (fun k => ?_) (fun k => ?_) <;>
    rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨i, rfl⟩
  · exact e01
  · rw [Fin.cons_succ]
    exact (hU0 i).1
  · exact e01'
  · rw [Fin.cons_succ]
    exact (hU0 i).2
  · exact e0'1
  · rw [Fin.cons_succ]
    exact (hV0 i).1
  · exact e0'1'
  · rw [Fin.cons_succ]
    exact (hV0 i).2

variable [Finite K]

theorem isEnnolaFrame_plus (hirr : ∀ s : K, s ^ 2 + 1 * s + 1 ≠ 0) :
    IsEnnolaFrame (plusAnisoQuad K (m' + 1) 1 1) (plusFrameA m') (plusFrameA' m') :=
  (isOrthUnitFamily_plusFrame hirr).isEnnolaFrame
    (regular_plusAnisoQuad (K := K) (m := m' + 1) one_ne_zero (by omega)).1
    (regular_plusAnisoQuad (K := K) (m := m' + 1) one_ne_zero (by omega)).2

variable {F : Type} [Field F] (E : EnnolaParam K F)

theorem map_rootParam_plusTorus (hirr : ∀ s : K, s ^ 2 + 1 * s + 1 ≠ 0) :
    (rootParam (K := F) 0).map ((isEnnolaFrame_plus (m' := m') hirr).torus E) =
      plusAnisoTorus (m' + 1) hirr :=
  (isEnnolaFrame_plus hirr).map_rootParam_torus_eq_anisoTorusOf E
    (isAnisoCoord_plusAnisoQuad (K := K) (m := m' + 1) hirr) plusFrameA_zero plusFrameA'_zero

theorem top_le_iSup_plusTorus (hm : 3 ≤ m') (hirr : ∀ s : K, s ^ 2 + 1 * s + 1 ≠ 0) :
    ⊤ ≤ ⨆ k, perfectCore (centralizer ((rootParam (K := F) k).map
      ((isEnnolaFrame_plus (m' := m') hirr).torus E) :
        Set (matrixProjectiveDerived (plusAnisoQuad K (m' + 1) 1 1)))) := by
  refine (isEnnolaFrame_plus hirr).top_le_iSup_perfectCore E (by omega) ?_
  rw [plusFrameA_zero, plusFrameA'_zero, ← pairPerpOf_eq_fixVecBar]
  exact Subgroup.isPerfect_iff.mp (isQuasisimple_plusAnisoPerp (m := m' + 1) (by omega) hirr).1

end Frame

end CFSG.SeitzReduction.OmegaPilot
