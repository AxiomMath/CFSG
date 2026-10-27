module

public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldBY

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open Matrix QuadraticMap CFSG.Assembly.LowTwoRank CFSG.ComponentClassification
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KCOrthogonalSubfield
open CFSG.LieType.Universal.Spin (quadOdd quadPlus quadMinus coe_quadPlus coe_quadOdd coe_quadMinus)
open CFSG.RankThree.PartOne.KCOrthogonalAut
  (matrixProjectiveImage_eq_top_odd matrixProjectiveImage_eq_top_plus
    matrixProjectiveImage_eq_top_minus)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
  (statedProjectiveReindexEquiv)

theorem orthPlus_subfield_any {n ℓ e p : ℕ} (hadm : StatedLieAdmissible .POmegaPlus n ℓ e)
    (hp : p.Prime) (hp2 : p ≠ 2) (K : Type) [Field K] [Finite K] (k : Subfield K)
    (hk : Nat.card k = ℓ ^ e) (hK : Nat.card K = ℓ ^ (e * p)) (σ : K ≃+* K)
    (hσ : orderOf σ = p) (hσk : ∀ x, x ∈ k ↔ σ x = x) :
    StatedClassicalModel (matrixProjectiveDerived (coordinateQuadPlus n K)) .POmegaPlus n ℓ
        (e * p) ∧
      SubfieldConclusion k (coordinateQuadPlus n k) (coordinateQuadPlus n K) σ p
        (coordinateQuadPlus_isExtension k n) (coordinateQuadPlus_fieldAut n σ) := by
  obtain ⟨hℓ, he, hn4⟩ := hadm
  have hf : 1 ≤ e * p := Nat.mul_pos he hp.pos
  have S := subfieldSetup_plus k hσk hp hp2 hσ (by omega : 3 ≤ n)
  have hmodel : StatedClassicalModel (matrixProjectiveDerived (coordinateQuadPlus n K))
      .POmegaPlus n ℓ (e * p) :=
    ⟨⟨hℓ, hf, hn4⟩, K, inferInstance, inferInstance, hK, ⟨(statedProjectiveReindexEquiv
      (plusIndexEquiv n) (quadPlus n K) (coe_quadPlus n K)).symm⟩⟩
  refine ⟨hmodel, subfield_conclusion orthogonal_high_Witt_subfield_pointwise_centralizer S ?_⟩
  by_cases hn : n = 4
  · subst hn
    intro β hβ
    exact mem_matrixProjectiveImage_plus_four k hK hmodel (statedProjectiveReindexEquiv
      (plusIndexEquiv 4) (quadPlus 4 K) (coe_quadPlus 4 K)).symm S.hext S.hnd₀ S.hT₀ β hβ
  · intro β _
    rw [matrixProjectiveImage_eq_top_plus K n (by omega)]
    exact Subgroup.mem_top β

theorem three_dvd_card_subfieldDerivedImage {K : Type} [Field K] [Finite K] (k : Subfield K)
    {ℓ e : ℕ} (hadm : StatedLieAdmissible .POmegaPlus 4 ℓ e) (hk : Nat.card k = ℓ ^ e)
    {Q : QuadraticForm K (Fin (2 * 4) → K)} (hext : IsExtension k (coordinateQuadPlus 4 k) Q)
    (hinj : Function.Injective (incl k hext)) :
    3 ∣ Nat.card (subfieldDerivedImage k hext) := by
  have hmod : StatedClassicalModel (matrixProjectiveDerived (coordinateQuadPlus 4 k))
      .POmegaPlus 4 ℓ e :=
    ⟨hadm, k, inferInstance, inferInstance, hk, ⟨(statedProjectiveReindexEquiv
      (plusIndexEquiv 4) (quadPlus 4 k) (coe_quadPlus 4 k)).symm⟩⟩
  have h3 := (CFSG.RankThree.Classical.orthogonal_model_exists_orderOf_eq_three
    (Or.inr (Or.inl rfl)) hmod).2
  have hc : Nat.card (subfieldDerivedImage k hext) =
      Nat.card (matrixProjectiveDerived (coordinateQuadPlus 4 k)) :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  rw [hc]
  exact h3

end CFSG.LocalAnalysis.GLTheoremA
