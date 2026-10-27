module

public import CFSG.Open.StatedDefs
public import CFSG.RankThree.Classical2.OrthogonalIsotropicUnipotent
import CFSG.RankThree.Classical.SteinbergBJOrthogonalHighWitt
import CFSG.GroupTheory.WeirSylow.OrthogonalModels
import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.OrthBlocks
import CFSG.RankThree.PartOne.KC.OrthogonalFieldDescentSimilarity
import CFSG.RankThree.PartOne.S11d.LieCentralizerPSL
public import CFSG.ClassicalGroups.Orthogonal.ProjectiveSimple
public import CFSG.LocalAnalysis.SectionRank.SignLines
import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
import CFSG.RankThree.LocalRank.SelectorCases
import CFSG.RankThree.PartOne.Assembly
import CFSG.RankThree.PartOne.S9.Sylow.ExclusionBasic
import CFSG.RankThree.Theta.ThreeComponentOrbitCover
import Certificates.Certificate116
import Certificates.Certificate119
import Certificates.Certificate122
import Certificates.Certificate123

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GInnOrthModel

open CFSG.Open CFSG.RankThree.Classical2

theorem exists_statedClassicalModel_quotCenter_orthDerived {X : Type} [Group X] {K : Type}
    [Field K] [Fintype K] {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} {f : ℕ} (hK : Nat.card K = 2 ^ f)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hd : 7 ≤ Module.finrank K V)
    (hT : ∃ U : Submodule K V, Module.finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    (e : X ≃* ↥(orthDerived Q)) :
    ∃ s : ℕ, StatedClassicalModel (X ⧸ Subgroup.center X) .POmegaPlus s 2 f ∨
      StatedClassicalModel (X ⧸ Subgroup.center X) .POmegaMinus s 2 f := by
  haveI : Finite K := Finite.of_fintype K
  haveI : CharP K 2 := CFSG.RankThree.PartOne.charP_two_of_card_eq_pow hK
  have heven : Even (Module.finrank K V) :=
    CFSG.ComponentClassification.UnbalancedCatalog.even_finrank_of_charTwo Q hQ
  obtain ⟨s, hs⟩ := heven
  have hdim : Module.finrank K V = 2 * s := by omega
  have hs1 : 1 ≤ s := by omega
  have hs4 : 4 ≤ s := by omega
  have hf1 : 1 ≤ f := by
    by_contra hf
    have hf0 : f = 0 := by omega
    subst hf0
    have h2 : 1 < Nat.card K := Finite.one_lt_card
    rw [hK] at h2
    exact absurd h2 (by norm_num)
  obtain ⟨-, hcenter, -⟩ :=
    CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hQ hT
  let e1 : X ⧸ Subgroup.center X ≃* orthDerived Q ⧸ Subgroup.center ↥(orthDerived Q) :=
    QuotientGroup.congr (Subgroup.center X) (Subgroup.center ↥(orthDerived Q)) e
      (Subgroup.map_center_eq e)
  let e2 : orthDerived Q ⧸ Subgroup.center ↥(orthDerived Q) ≃* ProjOrthDerived Q :=
    QuotientGroup.quotientMulEquivOfEq hcenter
  rcases CFSG.GroupTheory.WeirSylow.exists_isometry_quadPlus_or_quadMinus Q hQ hs1 hdim with
    he' | hminus
  · obtain ⟨e'⟩ := he'
    have hS : ∀ v : V,
        CFSG.LieType.Universal.Spin.quadPlus s K (e'.toLinearEquiv v) = (1 : Kˣ) * Q v := by
      intro v
      rw [Units.val_one, one_mul]
      exact e'.map_app v
    refine ⟨s, Or.inl ⟨⟨Nat.prime_two, hf1, hs4⟩, ?_⟩⟩
    refine ⟨K, inferInstance, inferInstance, hK, ?_⟩
    exact ⟨(e1.trans e2).trans
      ((CFSG.RankThree.PartOne.KCOrthogonalDescent.projOrthDerivedEquiv e'.toLinearEquiv 1 hS).trans
        (CFSG.HardMathSupport.Dickson.Sec6.OrthBlocks.projOrthEquiv
          (CFSG.LieType.Universal.Spin.coe_quadPlus s K)).symm)⟩
  · obtain ⟨b, c, hirr, ⟨e'⟩⟩ := hminus
    have hS : ∀ v : V,
        CFSG.LieType.Universal.Spin.quadMinus s K b c (e'.toLinearEquiv v) = (1 : Kˣ) * Q v := by
      intro v
      rw [Units.val_one, one_mul]
      exact e'.map_app v
    refine ⟨s, Or.inr ⟨⟨Nat.prime_two, hf1, hs4⟩, ?_⟩⟩
    refine ⟨K, inferInstance, inferInstance, hK, b, c, hirr, ?_⟩
    exact ⟨(e1.trans e2).trans
      ((CFSG.RankThree.PartOne.KCOrthogonalDescent.projOrthDerivedEquiv e'.toLinearEquiv 1 hS).trans
        (CFSG.HardMathSupport.Dickson.Sec6.OrthBlocks.projOrthEquiv
          (CFSG.LieType.Universal.Spin.coe_quadMinus s K b c)).symm)⟩

end CFSG.LocalAnalysis.GLTheoremA.Y10GInnOrthModel

end
