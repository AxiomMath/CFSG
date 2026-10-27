module

public import CFSG.GH74.Filter.Orthogonal.EvenEichler
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataReindexGroups
public import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I107L

open CFSG.Open CFSG.Assembly

variable {K : Type} [Field K]

@[expose] def minusSigma (m : ℕ) :
    CFSG.Assembly.LargeEvenMinusIdx m ≃ (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) :=
  Equiv.sumAssoc _ _ _

@[expose] noncomputable def minusQF (m : ℕ) (b c : K) : QuadraticForm K (CFSG.Assembly.LargeEvenMinusIdx m → K) :=
  (CFSG.LieType.Universal.Spin.quadMinus (m + 1) K b c).comp
    (LinearMap.funLeft K K (minusSigma m).symm)

theorem minusQF_apply (m : ℕ) (b c : K) (v : CFSG.Assembly.LargeEvenMinusIdx m → K) :
    minusQF m b c v = CFSG.Assembly.LargeEvenQMinus m b c v := by
  simp only [minusQF, QuadraticMap.comp_apply, LinearMap.funLeft_apply, CFSG.LieType.Universal.Spin.quadMinus_apply,
    CFSG.Assembly.LargeEvenQMinus, minusSigma, Equiv.sumAssoc_symm_apply_inl, Equiv.sumAssoc_symm_apply_inr_inl, Equiv.sumAssoc_symm_apply_inr_inr,
    Function.comp_apply]
  simp

theorem minusQF_eq (m : ℕ) (b c : K) :
    ⇑(minusQF m b c) = CFSG.Assembly.LargeEvenQMinus m b c :=
  funext (minusQF_apply m b c)

theorem pRank_minus_eichler_ge {m n : ℕ} (hn : 1 ≤ n) (hm : 3 ≤ m) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ n) (b c : K) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    n * (2 * m) ≤ CFSG.Open.pRank 2 (⊤ : Subgroup (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c)))) := by
  haveI : CharP K 2 := CFSG.SectionRank.ClassicalOdd.charP_of_card (p := 2) (f := n) hK
  have hlib : n * (2 * m) ≤ CFSG.Open.pRank 2
      (⊤ : Subgroup (StatedProj (StatedOmega (⇑(CFSG.LieType.Universal.Spin.quadMinus (m + 1) K b c))))) := by
    have h := CFSG.GH74.Filter.le_pRank_statedProj_statedOmega (K := K)
      (Q := CFSG.LieType.Universal.Spin.quadMinus (m + 1) K b c) hK rfl
      (CFSG.ClassicalGroups.Orthogonal.minusPair K b c (⟨0, by omega⟩ : Fin (m + 1 - 1)))
      (CFSG.ClassicalGroups.Orthogonal.commutator_orthogonalGroup_quadMinus (n := m + 1) (by omega) hirr)
    have hcard : Fintype.card (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) - 2 = 2 * m := by
      simp only [Fintype.card_sum, Fintype.card_fin]
      omega
    rw [hcard] at h
    exact h
  let e : CFSG.Assembly.LargeEvenMinusIdx m ≃ Fin (Fintype.card (CFSG.Assembly.LargeEvenMinusIdx m)) :=
    Fintype.equivFin _
  let e' : (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) ≃ Fin (Fintype.card (CFSG.Assembly.LargeEvenMinusIdx m)) :=
    (minusSigma m).symm.trans e
  have hform : CFSG.ComponentClassification.CatalogueBOrthogonalPointData.reindexQuadraticForm e (minusQF m b c) =
      CFSG.ComponentClassification.CatalogueBOrthogonalPointData.reindexQuadraticForm e'
        (CFSG.LieType.Universal.Spin.quadMinus (m + 1) K b c) :=
    QuadraticMap.ext fun w => rfl
  have hP1 := CFSG.ComponentClassification.CatalogueBOrthogonalPointData.statedMatrixProjectiveEquiv e
    (minusQF m b c)
  have hP2 := CFSG.ComponentClassification.CatalogueBOrthogonalPointData.statedMatrixProjectiveEquiv e'
    (CFSG.LieType.Universal.Spin.quadMinus (m + 1) K b c)
  have step1 := CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 2) hP1
  have step2 := CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 2) hP2
  have htrans : CFSG.Open.pRank 2 (⊤ : Subgroup (StatedProj (StatedOmega (⇑(minusQF m b c))))) =
      CFSG.Open.pRank 2 (⊤ : Subgroup (StatedProj (StatedOmega (⇑(CFSG.LieType.Universal.Spin.quadMinus (m + 1) K b c))))) := by
    rw [step1, hform, ← step2]
  rw [minusQF_eq] at htrans
  rw [← htrans] at hlib
  exact hlib

end CFSG.LocalAnalysis.GLTheoremA.I107L

end
