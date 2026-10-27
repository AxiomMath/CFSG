module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.H81Orth.Triality

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H81Orth

open Matrix Polynomial Module CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal CFSG.Assembly.LowTwoRank
  CFSG.RankThree.PartOne QuadraticMap CFSG.LieType.Universal.Spin

variable {K : Type} [Field K] [Finite K] {p ℓ f : ℕ}

theorem exists_eq_conj_odd {n : ℕ} (hadm : StatedLieAdmissible .POmegaOdd n ℓ f)
    (hK : Nat.card K = ℓ ^ f) (hK2 : ringChar K ≠ 2) (hp : p.Prime) (hp2 : p ≠ 2)
    {y : ↥(orthDerived (quadOdd n K))}
    (hy : OddOrderIsometry (quadOdd n K) p (y : (Fin n ⊕ Fin n ⊕ Unit → K) ≃ₗ[K] _))
    (hR : finrank K (othersSpace (y : (Fin n ⊕ Fin n ⊕ Unit → K) ≃ₗ[K] _).toLinearMap
      (X - 1)) = 2)
    (hW : 5 ≤ finrank K (fixedSpace (y : (Fin n ⊕ Fin n ⊕ Unit → K) ≃ₗ[K] _)))
    (α : MulAut (ProjOrthDerived (quadOdd n K))) (hα : α ^ p = 1)
    (hαJ : ∀ j ∈ fixedComponentImage (quadOdd n K) (y : (Fin n ⊕ Fin n ⊕ Unit → K) ≃ₗ[K] _),
      α j = j) :
    ∃ k : ℤ, α = MulAut.conj (projT (quadOdd n K) y ^ k) :=
  exists_eq_conj_of_stated (coe_quadOdd n K)
    (nondegenerate_polarBilin_quadOdd n K (Ring.two_ne_zero hK2)) hK2 hp hp2 hy hR hW α hα hαJ
    (CFSG.ClassicalInvolution.ModelFacts.OrthAut.exists_similarity_odd hadm hK _)

theorem exists_eq_conj_minus {n : ℕ} (hadm : StatedLieAdmissible .POmegaMinus n ℓ f)
    (hK : Nat.card K = ℓ ^ f) (hK2 : ringChar K ≠ 2) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hp : p.Prime) (hp2 : p ≠ 2)
    {y : ↥(orthDerived (quadMinus n K b c))}
    (hy : OddOrderIsometry (quadMinus n K b c) p
      (y : (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) ≃ₗ[K] _))
    (hR : finrank K (othersSpace (y : (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) ≃ₗ[K] _).toLinearMap
      (X - 1)) = 2)
    (hW : 5 ≤ finrank K (fixedSpace (y : (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) ≃ₗ[K] _)))
    (α : MulAut (ProjOrthDerived (quadMinus n K b c))) (hα : α ^ p = 1)
    (hαJ : ∀ j ∈ fixedComponentImage (quadMinus n K b c)
      (y : (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) ≃ₗ[K] _), α j = j) :
    ∃ k : ℤ, α = MulAut.conj (projT (quadMinus n K b c) y ^ k) :=
  exists_eq_conj_of_stated (coe_quadMinus n K b c)
    (nondegenerate_polarBilin_quadMinus_of_finite n K hirr) hK2 hp hp2 hy hR hW α hα hαJ
    (CFSG.ClassicalInvolution.ModelFacts.OrthAut.exists_similarity_minus hadm hK hirr _)

theorem exists_eq_conj_plus_four (hadm : StatedLieAdmissible .POmegaPlus 4 ℓ f)
    (hK : Nat.card K = ℓ ^ f) (hK2 : ringChar K ≠ 2) (hp : p.Prime) (hp2 : p ≠ 2)
    {y : ↥(orthDerived (quadPlus 4 K))}
    (hy : OddOrderIsometry (quadPlus 4 K) p (y : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] _))
    (hR : finrank K (othersSpace (y : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] _).toLinearMap (X - 1)) = 2)
    (hW : 5 ≤ finrank K (fixedSpace (y : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] _)))
    (α : MulAut (ProjOrthDerived (quadPlus 4 K))) (hα : α ^ p = 1)
    (hαJ : ∀ j ∈ fixedComponentImage (quadPlus 4 K) (y : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] _),
      α j = j) :
    ∃ k : ℤ, α = MulAut.conj (projT (quadPlus 4 K) y ^ k) :=
  exists_eq_conj_of_stated (coe_quadPlus 4 K) (nondegenerate_polarBilin_quadPlus 4 K) hK2 hp hp2
    hy hR hW α hα hαJ
    (exists_similarity_plus_four_of_family hadm hK _
      (smul_statedPointFamily_eq_of_fixes hadm hK hK2 hy hW α hαJ))

end CFSG.LocalAnalysis.GLTheoremA.H81Orth
