module

public import CFSG.LocalAnalysis.GL83PartI.I713.Basic
public import CFSG.Open.StatedDefs
import CFSG.LocalAnalysis.RankThreeTheoremC.OutCyclicLift
import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.OrthOdd
import CFSG.RankThree.PartOne.MB3.OddOutOrthogonal
import CFSG.HardMathSupport.Timmesfeld.DFour.OddRank
import CFSG.LocalAnalysis.SectionRank.ClassicalEven.Orthogonal
import CFSG.LocalAnalysis.SectionRank.ClassicalOdd.Orthogonal
import CFSG.Assembly.QuasithinDefs
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
import CFSG.LocalAnalysis.SectionRank.ClassicalEven
import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
import CFSG.Quasithin.Background.Basic
import CFSG.RankThree.PartOne.KC.OrthogonalHighWittFixedSpace
import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldFixed
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

namespace GL83.I713

open CFSG.Open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LocalAnalysis.RankThreeTheoremC (pRank_outer_le_one_of_outPChain)
open CFSG.HardMathSupport.Timmesfeld.Tables.T1b
  (outPNice_POmegaMinus_all outPNice_POmegaOdd_all outPNice_POmegaPlus_all_ge_five)
open CFSG.RankThree.PartOne.OutStructure (outPChain_POmegaPlus_four_gen)

theorem two_le_pRank_three_statedProj_plus {K : Type} [Field K] [Finite K] {p f : ℕ}
    (hp : p.Prime) (hf : 1 ≤ f) (hK : Nat.card K = p ^ f) {n : ℕ} (hn : 4 ≤ n) :
    2 ≤ pRank 3 (⊤ : Subgroup (StatedProj (StatedOmega (StatedQuadPlus n K)))) := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype K := Fintype.ofFinite K
  have hchar : CharP K p := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
  by_cases hp2 : p = 2
  · subst hp2
    have := CFSG.SectionRank.ClassicalEven.omegaPlus_three_le_pRank_three (K := K) hn
    omega
  · by_cases hp3 : p = 3
    · subst hp3
      have := CFSG.SectionRank.ClassicalOdd.four_mul_le_pRank_omegaPlus (K := K) hn hp2 hK
      omega
    · have h2 : (2 : K) ≠ 0 := by
        intro h
        have : p ∣ 2 := (CharP.cast_eq_zero_iff K p 2).mp (by exact_mod_cast h)
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)
      have h4 : (2 : K) ^ 2 ≠ 1 := by
        intro h
        have h3 : (3 : K) = 0 := by linear_combination h
        have : p ∣ 3 := (CharP.cast_eq_zero_iff K p 3).mp (by exact_mod_cast h3)
        exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp this)
      have := CFSG.HardMathSupport.Timmesfeld.DFour.three_le_pRank_plus_of_char (K := K) hn h2 h4
      omega

theorem two_le_pRank_three_classical_POmegaPlus {S : Type} [Group S] [Finite S] {n p f : ℕ}
    (h : StatedClassicalModel S .POmegaPlus n p f) : 2 ≤ pRank 3 (⊤ : Subgroup S) := by
  obtain ⟨⟨hp, hf, hn⟩, K, _, _, hK, ⟨e⟩⟩ := h
  have : Finite (StatedProj (StatedOmega (StatedQuadPlus n K))) := Finite.of_equiv S e.toEquiv
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e]
  exact two_le_pRank_three_statedProj_plus hp hf hK hn

theorem outClauseFor_classical_POmegaOdd {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (_hnonab : ∃ a b : S, a * b ≠ b * a) {n p f : ℕ}
    (h : StatedClassicalModel S .POmegaOdd n p f) : OutClauseFor S := fun ℓ hℓ hℓ2 _ =>
  pRank_outer_le_one_of_outPChain hℓ (outPNice_POmegaOdd_all hℓ hℓ2 h).toChain

theorem outClauseFor_classical_POmegaMinus {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (_hnonab : ∃ a b : S, a * b ≠ b * a) {n p f : ℕ}
    (h : StatedClassicalModel S .POmegaMinus n p f) : OutClauseFor S := fun ℓ hℓ hℓ2 _ =>
  pRank_outer_le_one_of_outPChain hℓ (outPNice_POmegaMinus_all hℓ hℓ2 h).toChain

theorem outClauseFor_classical_POmegaPlus {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (_hnonab : ∃ a b : S, a * b ≠ b * a) {n p f : ℕ}
    (h : StatedClassicalModel S .POmegaPlus n p f) : OutClauseFor S := by
  intro ℓ hℓ hℓ2 hrank
  have hn : 4 ≤ n := h.1.2.2
  by_cases hn5 : 5 ≤ n
  · exact pRank_outer_le_one_of_outPChain hℓ (outPNice_POmegaPlus_all_ge_five hℓ hℓ2 hn5 h).toChain
  · obtain rfl : n = 4 := by omega
    by_cases hℓ5 : 5 ≤ ℓ
    · exact pRank_outer_le_one_of_outPChain hℓ (outPChain_POmegaPlus_four_gen hℓ hℓ5 h)
    · obtain rfl : ℓ = 3 := by
        have h2 := hℓ.two_le
        interval_cases ℓ
        · exact absurd rfl hℓ2
        · rfl
        · exact absurd hℓ (by norm_num)
      have := two_le_pRank_three_classical_POmegaPlus h
      omega

end GL83.I713
