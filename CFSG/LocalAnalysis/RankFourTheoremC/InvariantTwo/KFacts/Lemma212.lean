module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma212Aut
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma212Center
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Reduced
import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Comp212

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeTheoremC Subgroup
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator (sporadicMultipliers_holds)

section CertificateInstances

theorem kFactLemma212Red_four_of_not_le (hB : GL83OutDiagPowerMap)
    (hnle : ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → ∀ (K : Type) [Group K] [Finite K],
      CFSG.AGLEmbedding.CatalogSimpleSections K → primeComplementCore (G := K) p = ⊥ →
      ∀ (P : Sylow p K) (z : K) (D L : Subgroup K), Lemma212ConfigGe 4 p P z D →
        Lemma212Component p z D L → IsLinearOrUnitaryAt p (L ⧸ center L) → ¬ D ≤ L) :
    KFactLemma212Red 4 := by
  intro p hp hp2 K _ _ hcat hcore P z D hconf hgex
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ := hgex
  have h5 : 5 ≤ p := hconf.five_le hp hp2 le_rfl
  by_cases hnc : ∃ Q : Subgroup K, Q.Normal ∧ IsPGroup p Q ∧ centralizer (Q : Set K) ≤ Q
  · exact Or.inl hnc
  by_cases hpc : CFSG.pCore p K = ⊥
  · exact Or.inr hpc
  exfalso
  obtain ⟨L, hL, hLn, hLu, hzL, hzc, -, hZne, hZp, -, hΩ, hDL⟩ :=
    hconf.exists_component_of_five_le hp h5 hcat hcore hnc hpc
  have hLc : Lemma212Component p z D L := ⟨hL, hLn, hLu, hzL, hzc, hZne, hZp, hΩ, hDL⟩
  have hbar : IsLinearOrUnitaryAt p (L ⧸ center L) :=
    isLinearOrUnitaryAt_of_tables
      CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds
      sporadicMultipliers_holds hp h5 hL.2.2 (hcat.isCatalogGroup_center_quotient hL) hZne hZp
  exact hLc.false_of_not_le hconf h5 hcore hg hbar hB
    (hnle p h5 K hcat hcore P z D L hconf hLc hbar)

theorem kFactLemma212Red_four (hR : GL83PElementCentralizerRank) (hB : GL83OutDiagPowerMap) :
    KFactLemma212Red 4 :=
  kFactLemma212Red_four_of_not_le hB fun p _ h5 _ _ _ _ _ _ _ _ _ h hL hbar hDL =>
    hL.false_of_le h h5 hDL hbar hR

theorem kFactLemma212Ge_four (hR : GL83PElementCentralizerRank) (hB : GL83OutDiagPowerMap) :
    KFactLemma212Ge 4 :=
  (kFactLemma212Red_four hR hB).toGe

end CertificateInstances

end CFSG.LocalAnalysis.RankFourTheoremC
