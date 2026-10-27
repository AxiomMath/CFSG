module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.OrthD4Family

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross

open CFSG.Open (IsElemAbelian)
open CFSG.HardMathSupport.Solomon.LocalBalance Module
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.RankThree.PartOne
  CFSG.RankThree.Classical2 CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Census
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.LieType.Universal.Spin
  CFSG.RankThree.Classical.SteinbergBY CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.HardMathSupport.Timmesfeld.DefChar CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
  CFSG.HardMathSupport.Timmesfeld.CrossChar

theorem d4_plane_trichotomy (G : Type) [Group G] {ℓ f : ℕ}
    (h : StatedClassicalModel G .POmegaPlus 4 ℓ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = ℓ ^ f) (e : G ≃* StatedProj (StatedOmega (StatedQuadPlus 4 K)))
    (D : Subgroup (MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K))))
    (hD : IsElemAbelian 3 D) (hcard : Nat.card D = 3 ^ 2) :
    D ≤ innerAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)) ∨
    (∃ a ∈ D, a ∈ matrixProjectiveImage (coordinateQuadPlus 4 K) ∧
      a ∉ (linearConjugationHom (coordinateQuadPlus 4 K)).range ∧ orderOf a = 3) ∨
    (∃ t ∈ D, t ∉ matrixProjectiveImage (coordinateQuadPlus 4 K) ∧
      D ⊓ matrixProjectiveImage (coordinateQuadPlus 4 K) ≤
        innerAut (matrixProjectiveDerived (coordinateQuadPlus 4 K))) := by
  classical
  clear hcard
  have hgates := orthogonal_large_prime_semilinear_field_and_diagonal_gates G .POmegaPlus
    (Or.inr (Or.inl rfl)) 4 ℓ f h K hK e
  obtain ⟨-, -, ⟨-, k, hrel⟩, -⟩ := hgates
  have hinn : ∀ a ∈ D, a ∈ matrixProjectiveImage (coordinateQuadPlus 4 K) →
      a ∈ (linearConjugationHom (coordinateQuadPlus 4 K)).range →
      a ∈ innerAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)) := by
    intro a haD _ haL
    refine mem_of_pow_mem_of_relIndex_two_pow hrel haL (j := 1) ?_
    rw [pow_one, hD.2 a haD]
    exact Subgroup.one_mem _
  by_cases hex : ∃ a ∈ D ⊓ matrixProjectiveImage (coordinateQuadPlus 4 K),
      a ∉ (linearConjugationHom (coordinateQuadPlus 4 K)).range
  · right
    left
    obtain ⟨a, ⟨haD, haE⟩, hanot⟩ := hex
    have ha1 : a ≠ 1 := fun h1 => hanot (h1 ▸ Subgroup.one_mem _)
    exact ⟨a, haD, haE, hanot, orderOf_eq_prime (hD.2 a haD) ha1⟩
  · push Not at hex
    have hin : D ⊓ matrixProjectiveImage (coordinateQuadPlus 4 K) ≤
        innerAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)) := by
      intro a ha
      exact hinn a ha.1 ha.2 (hex a ha)
    by_cases hDE : D ≤ matrixProjectiveImage (coordinateQuadPlus 4 K)
    · left
      intro a ha
      exact hin (show a ∈ D ⊓ matrixProjectiveImage (coordinateQuadPlus 4 K) from ⟨ha, hDE ha⟩)
    · right
      right
      obtain ⟨t, ht, htE⟩ : ∃ t ∈ D, t ∉ matrixProjectiveImage (coordinateQuadPlus 4 K) := by
        by_contra hc
        push Not at hc
        exact hDE hc
      exact ⟨t, ht, htE, hin⟩

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
