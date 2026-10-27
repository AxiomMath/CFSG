module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofA6Cent
public import CFSG.RankThree.Classical.SteinbergBYOrthogonalGates

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalLinearFixed
open CFSG.ComponentClassification.CatalogueBOrthogonalFixedTransfer
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalInvolutionRepresentation

theorem a6_inner_omega
    {K : Type} [Field K] [Finite K] {d p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card K = p ^ f) (hd : 1 ≤ d) {Q : QuadraticForm K (Fin d → K)}
    (hQ : Q.polarBilin.Nondegenerate)
    (hker : ∀ g' : similarityPairs Q, matrixProjectiveConjugationHom Q g' = 1 ↔
      g'.val.right = 1 ∧ ∃ a : Kˣ, g'.val.left = GeneralLinearGroup.scalar (Fin d) a)
    (g : similarityPairs Q) (hg : g.val.right = 1)
    (hord : orderOf (matrixProjectiveConjugationHom Q g) = 2) :
    A6CentreForm (fixedSubgroup (matrixProjectiveConjugationHom Q g)) := by
  intro L hL
  show A6Safe L
  have : Nontrivial (Fin d → K) :=
    Module.nontrivial_of_finrank_pos (R := K) (by rw [Module.finrank_fin_fun]; omega)
  obtain ⟨-, c, hc⟩ := (hker (g * g)).mp (by
    rw [map_mul, ← pow_two, ← hord, pow_orderOf_eq_one])
  have hsq : ∀ x, matrixLinearEquiv g.val.left (matrixLinearEquiv g.val.left x) = (c : K) • x := by
    intro x
    have h := coordinateSemilinearMap_sq_apply g.val c (by rw [hg, one_pow]) hc x
    rwa [coordinateSemilinearMap_eq_matrix g.val hg] at h
  have hns : ∀ a : Kˣ, GeneralLinearGroup.scalar (Fin d) a ≠ g.val.left := by
    intro a ha
    have h1 : matrixProjectiveConjugationHom Q g = 1 := (hker g).mpr ⟨hg, a, ha.symm⟩
    rw [h1, orderOf_one] at hord
    exact absurd hord (by norm_num)
  have hnonscalar := matrixLinearEquiv_ne_smul_one g.val.left hns
  set A := matrixLinearEquiv g.val.left with hAdef
  have hsim := matrix_similarity Q g hg
  let Φ := linearFixedEquiv Q (exists_ne_zero_of_polarBilin_nondegenerate Q hQ (by omega)) g hg
  have hL' := LocalCores.isComponent_map_mulEquiv Φ hL
  obtain ⟨M, hM, σ, hσ, hker'⟩ := exists_component_cover_of_normalQuotientFixed
    (orthogonalDerived Q)
    (scalarSigns Q) (scalarSigns_central Q) (similarityConjugation Q A (multiplier Q g) hsim)
    (orthogonalDerived_invariant Q A (multiplier Q g) hsim)
    (scalarSigns_invariant Q A (multiplier Q g) hsim) hL'
  have hMo : A6Safe M :=
    a6CentreForm_of_mulEquiv (fixedCentralizerEquiv Q A (multiplier Q g) hsim)
      (a6CentreForm_orthogonalOperatorCentralizer hp hp2 hf hK Q hQ A c
        (multiplier Q g) hsq (polar_similarity Q A (multiplier Q g) hsim) hnonscalar) M hM
  exact a6Safe_of_mulEquiv (L.equivMapOfInjective Φ.toMonoidHom Φ.injective)
    (a6Safe_of_cover hM.1 σ hσ hker' hMo)

theorem a6_omegaOdd_linear
    (n : ℕ) (K : Type) [Field K] [Finite K] (p f : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) (hadm : StatedLieAdmissible .POmegaOdd n p f)
    (g : similarityPairs (coordinateQuadOdd n K)) (hg : g.val.right = 1)
    (hord : orderOf (matrixProjectiveConjugationHom (coordinateQuadOdd n K) g) = 2) :
    A6CentreForm (fixedSubgroup (matrixProjectiveConjugationHom (coordinateQuadOdd n K) g)) := by
  have hstated : StatedClassicalModel (StatedProj (StatedOmega (StatedQuadOdd n K))) .POmegaOdd
      n p f := ⟨hadm, K, inferInstance, inferInstance, hK, ⟨MulEquiv.refl _⟩⟩
  obtain ⟨-, hnd, hT, -, hAP, -⟩ := coordinate_model_witness_odd hstated K hK (MulEquiv.refl _)
  exact a6_inner_omega hp hp2 hadm.2.1 hK (by omega) hnd
    (RankThree.Classical.SteinbergBY.matrixProjectiveConjugationHom_eq_one_iff _ hnd hT hAP) g
    hg hord

theorem a6_omegaPlus_linear
    (n : ℕ) (K : Type) [Field K] [Finite K] (p f : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) (hadm : StatedLieAdmissible .POmegaPlus n p f)
    (g : similarityPairs (coordinateQuadPlus n K)) (hg : g.val.right = 1)
    (hord : orderOf (matrixProjectiveConjugationHom (coordinateQuadPlus n K) g) = 2) :
    A6CentreForm (fixedSubgroup (matrixProjectiveConjugationHom (coordinateQuadPlus n K) g)) := by
  have hstated : StatedClassicalModel (StatedProj (StatedOmega (StatedQuadPlus n K))) .POmegaPlus
      n p f := ⟨hadm, K, inferInstance, inferInstance, hK, ⟨MulEquiv.refl _⟩⟩
  obtain ⟨-, hnd, hT, -, hAP, -⟩ := coordinate_model_witness_plus hstated K hK (MulEquiv.refl _)
  have hn : 4 ≤ n := hadm.2.2
  exact a6_inner_omega hp hp2 hadm.2.1 hK (by omega) hnd
    (RankThree.Classical.SteinbergBY.matrixProjectiveConjugationHom_eq_one_iff _ hnd hT hAP) g
    hg hord

theorem a6_omegaMinus_linear
    (n : ℕ) (hn : 1 ≤ n) (K : Type) [Field K] [Finite K] (p f : ℕ) (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) (hadm : StatedLieAdmissible .POmegaMinus n p f)
    (b c : K) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (g : similarityPairs (coordinateQuadMinus n K hn b c)) (hg : g.val.right = 1)
    (hord : orderOf (matrixProjectiveConjugationHom (coordinateQuadMinus n K hn b c) g) = 2) :
    A6CentreForm (fixedSubgroup
      (matrixProjectiveConjugationHom (coordinateQuadMinus n K hn b c) g)) := by
  have hstated : StatedClassicalModel (StatedProj (StatedOmega (StatedQuadMinus n K b c)))
      .POmegaMinus n p f := ⟨hadm, K, inferInstance, inferInstance, hK, b, c, hirr,
        ⟨MulEquiv.refl _⟩⟩
  obtain ⟨-, hnd, hT, -, hAP, -⟩ :=
    coordinate_model_witness_minus hstated K hK b c hirr (MulEquiv.refl _)
  exact a6_inner_omega hp hp2 hadm.2.1 hK (by omega) hnd
    (RankThree.Classical.SteinbergBY.matrixProjectiveConjugationHom_eq_one_iff _ hnd hT hAP) g
    hg hord

theorem a6CentreForm_of_semilinearRepresentation {J : Type} [Group J] {K : Type}
    [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)} (hrep : SemilinearRepresentation Q)
    (ψ : J ≃* matrixProjectiveDerived Q)
    (h : ∀ g : similarityPairs Q, g.val.right ^ 2 = 1 →
      orderOf (matrixProjectiveConjugationHom Q g) = 2 →
      A6CentreForm (fixedSubgroup (matrixProjectiveConjugationHom Q g)))
    (α : MulAut J) (hα : orderOf α = 2) : A6CentreForm (fixedSubgroup α) := by
  set α' := MulAut.congr ψ α with hα'def
  have hα' : orderOf α' = 2 :=
    (orderOf_injective (MulAut.congr ψ).toMonoidHom (MulAut.congr ψ).injective α).trans hα
  have h2 : α' * α' = 1 := by
    have h2 := pow_orderOf_eq_one α'
    rw [hα'] at h2
    rw [← pow_two]
    exact h2
  have h1 : α' ≠ 1 := fun h => by
    rw [h, orderOf_one] at hα'
    exact absurd hα' (by norm_num)
  obtain ⟨β, g, hg, hσ2, -, -, -⟩ := hrep.2 α' h2 h1
  have hc : MulAut.congr β⁻¹ α' = β⁻¹ * α' * β := MulEquiv.ext fun _ => rfl
  have hord : orderOf (matrixProjectiveConjugationHom Q g) = 2 := by
    rw [← hg, ← hc]
    exact (orderOf_injective (MulAut.congr β⁻¹).toMonoidHom (MulAut.congr β⁻¹).injective
      α').trans hα'
  exact a6CentreForm_of_mulEquiv ((fixedSubgroupCongrEquiv ψ α).trans
    (((fixedSubgroupCongrEquiv β⁻¹ α').trans
      (MulEquiv.subgroupCongr (congrArg fixedSubgroup hc))).trans
        (MulEquiv.subgroupCongr (congrArg fixedSubgroup hg)))) (h g hσ2 hord)

end CFSG.ComponentClassification.CatLeafProof
