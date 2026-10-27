module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddInnerOCent
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofComponentLift
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalLinearFixed
open CFSG.ComponentClassification.CatalogueBOrthogonalFixedTransfer

theorem oddLie_inner_omega {K : Type} [Field K] [Finite K] {d p f : ℕ}
    (hO : OddInner.OrthogonalComponentsLie p) (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card K = p ^ f) (hd : 1 ≤ d) {Q : QuadraticForm K (Fin d → K)}
    (hQ : Q.polarBilin.Nondegenerate)
    (hker : ∀ g' : similarityPairs Q, matrixProjectiveConjugationHom Q g' = 1 ↔
      g'.val.right = 1 ∧ ∃ a : Kˣ, g'.val.left = GeneralLinearGroup.scalar (Fin d) a)
    (g : similarityPairs Q) (hg : g.val.right = 1)
    (hord : orderOf (matrixProjectiveConjugationHom Q g) = 2)
    {L : Subgroup (fixedSubgroup (matrixProjectiveConjugationHom Q g))} (hL : IsComponent L) :
    OddLieCentralQuotient p L := by
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
  obtain ⟨M, hM, ⟨eLM⟩⟩ := exists_component_of_normalQuotientFixed (orthogonalDerived Q)
    (scalarSigns Q) (scalarSigns_central Q) (similarityConjugation Q A (multiplier Q g) hsim)
    (orthogonalDerived_invariant Q A (multiplier Q g) hsim)
    (scalarSigns_invariant Q A (multiplier Q g) hsim) hL'
  have hMo : OddLieCentralQuotient p M :=
    oddLieCentralQuotient_of_component_equiv (fixedCentralizerEquiv Q A (multiplier Q g) hsim)
      (fun N hN => OddInner.oddLie_orthogonalOperatorCentralizer hO hp hp2 hf hK Q hQ A c
        (multiplier Q g) hsq (polar_similarity Q A (multiplier Q g) hsim) hnonscalar hN) hM
  exact oddLieCentralQuotient_of_mulEquiv (L.equivMapOfInjective Φ.toMonoidHom Φ.injective)
    (oddLieCentralQuotient_of_centerQuotient_equiv eLM hMo)

end CFSG.ComponentClassification.CatLeafProof
