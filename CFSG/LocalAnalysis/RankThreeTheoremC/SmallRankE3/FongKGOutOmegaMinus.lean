module

public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergOmegaMinus
public import CFSG.RankThree.PartTwo.Sec21.Item224KFactsProofLie

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongOut

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

theorem isCyclic_outer_matrixDerived_minus {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hn : 4 ≤ n) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {f : ℕ}
    (hf : Nat.card K = 2 ^ f) :
    IsCyclic (CFSG.ComponentClassification.OuterAutomorphisms.Outer
      (matrixDerived (CFSG.RankThree.PartOne.AUTSL.Qm n hn b c))) := by
  refine isCyclic_iff_exists_zpowers_eq_top.2
    ⟨QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner
      (matrixDerived (CFSG.RankThree.PartOne.AUTSL.Qm n hn b c)))
      (CFSG.StandardType.AutOm.frobAut hn hirr), ?_⟩
  rw [eq_top_iff]
  intro x _
  obtain ⟨α, rfl⟩ := QuotientGroup.mk'_surjective
    (CFSG.ComponentClassification.OuterAutomorphisms.inner
      (matrixDerived (CFSG.RankThree.PartOne.AUTSL.Qm n hn b c))) x
  obtain ⟨ι, hι, k, rfl⟩ := CFSG.StandardType.AutOm.exists_inner_mul_frobAut_pow hn hirr hf α
  have hι1 : QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner
      (matrixDerived (CFSG.RankThree.PartOne.AUTSL.Qm n hn b c))) ι = 1 := by
    rw [QuotientGroup.mk'_apply]
    exact (QuotientGroup.eq_one_iff ι).2 hι
  rw [map_mul, hι1, one_mul, map_pow]
  exact Subgroup.npow_mem_zpowers _ _

theorem outTwoCyclic_matrixDerived_minus {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hn : 4 ≤ n) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {f : ℕ}
    (hf : Nat.card K = 2 ^ f) :
    CFSG.RankThree.PartTwo.Sec21.Item224KFactsProof.OutTwoCyclic
      (matrixDerived (CFSG.RankThree.PartOne.AUTSL.Qm n hn b c)) :=
  CFSG.RankThree.PartTwo.Sec21.Item224KFactsProof.outTwoCyclic_of_isCyclic_outer
    (isCyclic_outer_matrixDerived_minus hn hirr hf)

theorem outTwoCyclic_POmegaMinus {X : Type} [Group X] {n m : ℕ} (hn4 : 4 ≤ n)
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel X .POmegaMinus n 2 m) :
    CFSG.RankThree.PartTwo.Sec21.Item224KFactsProof.OutTwoCyclic X := by
  obtain ⟨-, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := id h
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 :=
    charP_of_card_eq_prime_pow (f := m) (by rw [← Nat.card_eq_fintype_card, hK])
  have hQ : ∃ v, CFSG.RankThree.PartOne.AUTSL.Qm n hn4 b c v ≠ 0 :=
    ⟨CFSG.StandardType.AutOm.tailVec n (by omega),
      CFSG.StandardType.AutOm.tailVec_form_ne_zero n (by omega) b c⟩
  exact CFSG.RankThree.PartTwo.Sec21.Item224KFactsProof.outTwoCyclic_of_mulEquiv
    ((CFSG.ComponentClassification.CatalogueBOrthogonalPointData.coordinateMinusWitnessEquiv K
      (by omega) b c e).trans
      (CFSG.RankThree.PartOne.AUTSL.derivedProjEquiv (CFSG.RankThree.PartOne.AUTSL.Qm n hn4 b c)
        hQ).symm)
    (outTwoCyclic_matrixDerived_minus hn4 hirr hK)

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongOut
