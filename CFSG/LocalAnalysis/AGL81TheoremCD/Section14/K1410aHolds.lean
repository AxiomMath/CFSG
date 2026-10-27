module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CaseOneFourteenTen
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrModel
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsLie
public import CFSG.RankThree.PartOne.S11d.OutAbstract
public import CFSG.Open.StatedDefs
public import CFSG.Open.LocalVocabulary
public import CFSG.Adapters.TauCetiExceptional.EvenBridgeG2
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.K1410aOut
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.K1410aL3U3
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.RankFourLin
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.RankFourOrth
import CFSG.RankThree.PartOne.S11d.OutClassicalTwo
import CFSG.RankThree.PartOne.S11d.OutLinear
import CFSG.RankThree.PartOne.S11d.OutUnitary
import CFSG.RankThree.PartOne.S11d.OutSymplectic
import CFSG.RankThree.PartOne.S11d.OutOrthogonal
import CFSG.LieType.Chevalley.ExceptionalG2F4ModelSchreier
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenAutomorphisms
import CFSG.LocalAnalysis.ComponentInitial.DiagonalSemilinear
import CFSG.LocalAnalysis.SectionRank.SubgroupRank
import CFSG.HardMathSupport.Cooperstein.Proving.NineThreeTransfer
import CFSG.Blueprint.Catalog
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpSuzukiCentralizer
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bPairs
import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.CrossPSU
import CFSG.RankThree.PartOne.KC.OrthogonalHighWittFixedSpace
import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldFixed
import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open Subgroup
open CFSG.RankThree.PartOne.OutStructure
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott

theorem outPNice_three_G2_even
    (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.G2 q).Valid) (hp2 : q.p = 2) {Y : Type}
    [Group Y] (e : Y ≃* (TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩).Group) :
    CFSG.RankThree.PartOne.OutStructure.OutPNice 3 Y := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hq3 : 3 ≤ q.card :=
    (TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have hK : Nat.card (GaloisField q.p q.exponent) = q.card := by
    rw [GaloisField.card _ _ q.exponent_pos.ne', TauCeti.PrimePower.card_def]
  obtain ⟨e0⟩ := CFSG.TauCetiBridge.Even.untwistedBridgeEven_G2 q hv hp2
    (GaloisField q.p q.exponent) hK
  have hce : CFSG.Blueprint.ChevalleyExceptionalModel (TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩).Group
      .G2 q.p q.exponent := by
    refine ⟨⟨q.prime_p, q.exponent_pos, rfl, ?_⟩, GaloisField q.p q.exponent,
      inferInstance, inferInstance, ?_, ⟨e0.symm⟩⟩
    · rw [← TauCeti.PrimePower.card_def]
      exact hq3
    · rw [hK, TauCeti.PrimePower.card_def]
  rw [hp2] at hce
  obtain ⟨⟨-, hf1, -, h3⟩, hm⟩ := hce
  have hf2 : 2 ≤ q.exponent := by
    by_contra hlt
    have h1 : q.exponent = 1 := by omega
    rw [h1] at h3
    norm_num at h3
  obtain ⟨K, _, _, hK', ⟨e1⟩⟩ :=
    CFSG.LieType.Chevalley.nonempty_mulEquiv_adjointGroup .G2 hm
  obtain ⟨-, Θ, -, -, hker, -⟩ :=
    CFSG.ComponentClassification.UnbalancedCatalog.even_G2_exact_automorphism_normal_form
      hf2 K hK'
  have hcard := CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic
    Nat.prime_two K hK'
  have : Finite (RingAut K) := Nat.finite_of_card_ne_zero (by rw [hcard.1]; omega)
  have := hcard.2
  exact CFSG.RankThree.PartOne.OutStructure.OutPNice.of_mulEquiv e
    (CFSG.RankThree.PartOne.OutStructure.OutPNice.of_mulEquiv e1
      (CFSG.RankThree.PartOne.OutStructure.outPNice_of_hom_cyclic Nat.prime_three Θ hker))

private theorem isThreeOnePlusFour_map_conjNormal {X : Type} [Group X] {L : Subgroup X}
    [L.Normal] (hC : Subgroup.centralizer (L : Set X) = ⊥) {R : Subgroup X}
    (hR : CFSG.LocalAnalysis.RankThreeUC.S15.IsThreeOnePlusFour ↥R) :
    CFSG.LocalAnalysis.RankThreeUC.S15.IsThreeOnePlusFour
      ↥(R.map (MulAut.conjNormal (H := L))) := by
  refine isThreeOnePlusFour_map_of_injOn (MulAut.conjNormal (H := L)) ?_ hR
  intro x _ hx
  have hx' : x ∈ Subgroup.centralizer (L : Set X) :=
    (CFSG.LocalAnalysis.RankThreeUC.S15.K4143K2.conjNormal_eq_one_iff_mem_centralizer L).mp hx
  rw [hC] at hx'
  exact Subgroup.mem_bot.mp hx'

private theorem three_le_pRank_of_four_le_top {X : Type} [Group X] [Finite X]
    {L : Subgroup X}
    (h : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥L)) : 3 ≤ CFSG.Open.pRank 3 L := by
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup L]
  omega

private theorem three_le_pRank_of_psl_model {X : Type} [Group X] [Finite X] {L : Subgroup X}
    [L.Normal] (hC : Subgroup.centralizer (L : Set X) = ⊥) {n f : ℕ}
    (hm : CFSG.Open.StatedClassicalModel ↥L .PSL n 2 f) {R : Subgroup X}
    (hR : CFSG.LocalAnalysis.RankThreeUC.S15.IsThreeOnePlusFour ↥R) :
    3 ≤ CFSG.Open.pRank 3 L := by
  have hadm := hm.1
  unfold CFSG.Open.StatedLieAdmissible at hadm
  obtain ⟨-, -, hn2, -⟩ := hadm
  rcases Nat.lt_or_ge n 3 with h3 | h3
  · have hn : n = 2 := by omega
    subst hn
    exact three_le_pRank_of_outPNice (outPNice_PSL_two Nat.prime_three hm) hC hR
  · rcases Nat.lt_or_ge n 4 with h4 | h4
    · have hn : n = 3 := by omega
      subst hn
      exact (false_of_statedClassicalModel_psl_three hm
        (isThreeOnePlusFour_map_conjNormal hC hR)).elim
    · by_cases hdiag : 3 ∣ Nat.gcd n (2 ^ f - 1)
      · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hm
        have hn5 : 5 ≤ n := by
          obtain ⟨k, rfl⟩ := (Nat.dvd_gcd_iff.mp hdiag).1
          omega
        have h1 : 3 ∣ Nat.card K - 1 := by
          rw [hK]
          exact (Nat.dvd_gcd_iff.mp hdiag).2
        have h4' : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (StatedProj (StatedSL n K))) :=
          four_le_pRank_projSL_of_dvd hn5 h1
        have h4'' : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥L) := by
          rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3) e]
          exact h4'
        exact three_le_pRank_of_four_le_top h4''
      · exact three_le_pRank_of_outPNice
          (outPNice_PSL_ge_three Nat.prime_three (by norm_num) (by omega) hm hdiag) hC hR

private theorem three_le_pRank_of_psu_model {X : Type} [Group X] [Finite X] {L : Subgroup X}
    [L.Normal] (hC : Subgroup.centralizer (L : Set X) = ⊥) {n f : ℕ}
    (hm : CFSG.Open.StatedClassicalModel ↥L .PSU n 2 f) {R : Subgroup X}
    (hR : CFSG.LocalAnalysis.RankThreeUC.S15.IsThreeOnePlusFour ↥R) :
    3 ≤ CFSG.Open.pRank 3 L := by
  have hadm := hm.1
  unfold CFSG.Open.StatedLieAdmissible at hadm
  obtain ⟨-, -, hn3, -⟩ := hadm
  rcases Nat.lt_or_ge n 4 with h4 | h4
  · have hn : n = 3 := by omega
    subst hn
    exact (false_of_statedClassicalModel_psu_three hm
      (isThreeOnePlusFour_map_conjNormal hC hR)).elim
  · by_cases hdiag : 3 ∣ Nat.gcd n (2 ^ f + 1)
    · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hm
      have hn5 : 5 ≤ n := by
        obtain ⟨k, rfl⟩ := (Nat.dvd_gcd_iff.mp hdiag).1
        omega
      have h1 : 3 ∣ 2 ^ f + 1 := (Nat.dvd_gcd_iff.mp hdiag).2
      have h4' : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (StatedProj (StatedSU n (2 ^ f) K))) :=
        four_le_pRank_projSU_of_dvd_add (L := K) (q := 2 ^ f) hK hn5 h1
      have h4'' : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥L) := by
        rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3) e]
        exact h4'
      exact three_le_pRank_of_four_le_top h4''
    · exact three_le_pRank_of_outPNice (outPNice_PSU Nat.prime_three hm hdiag) hC hR

private theorem three_le_pRank_of_psp_model {X : Type} [Group X] [Finite X] {L : Subgroup X}
    [L.Normal] (hC : Subgroup.centralizer (L : Set X) = ⊥) {n f : ℕ}
    (hm : CFSG.Open.StatedClassicalModel ↥L .PSp n 2 f) {R : Subgroup X}
    (hR : CFSG.LocalAnalysis.RankThreeUC.S15.IsThreeOnePlusFour ↥R) :
    3 ≤ CFSG.Open.pRank 3 L := by
  have hadm := hm.1
  unfold CFSG.Open.StatedLieAdmissible at hadm
  obtain ⟨-, -, hn2, -⟩ := hadm
  rcases Nat.lt_or_ge n 3 with h3 | h3
  · have hn : n = 2 := by omega
    subst hn
    exact three_le_pRank_of_outPNice (outPNice_PSp_two Nat.prime_three hm) hC hR
  · exact three_le_pRank_of_outPNice (outPNice_PSp_ge_three Nat.prime_three h3 hm) hC hR

private theorem three_le_pRank_of_pomegaPlus_model {X : Type} [Group X] [Finite X]
    {L : Subgroup X} {n f : ℕ}
    (hm : CFSG.Open.StatedClassicalModel ↥L .POmegaPlus n 2 f) :
    3 ≤ CFSG.Open.pRank 3 L := by
  have hadm := hm.1
  unfold CFSG.Open.StatedLieAdmissible at hadm
  obtain ⟨-, -, hn4⟩ := hadm
  exact three_le_pRank_of_four_le_top
    (four_le_pRank_three_orth hm (Or.inr (Or.inl ⟨rfl, hn4⟩)) (by norm_num : (2 : ℕ) ≠ 3))

private theorem three_le_pRank_of_pomegaMinus_model {X : Type} [Group X] [Finite X]
    {L : Subgroup X} [L.Normal] (hC : Subgroup.centralizer (L : Set X) = ⊥) {n f : ℕ}
    (hm : CFSG.Open.StatedClassicalModel ↥L .POmegaMinus n 2 f) {R : Subgroup X}
    (hR : CFSG.LocalAnalysis.RankThreeUC.S15.IsThreeOnePlusFour ↥R) :
    3 ≤ CFSG.Open.pRank 3 L := by
  have hadm := hm.1
  unfold CFSG.Open.StatedLieAdmissible at hadm
  obtain ⟨-, -, hn4⟩ := hadm
  exact three_le_pRank_of_outPNice
    (outPNice_POmegaMinus Nat.prime_three (by norm_num) hn4 hm) hC hR

theorem three_le_pRank_of_classicalModel {X : Type} [Group X] [Finite X] {L : Subgroup X}
    [L.Normal] (hC : Subgroup.centralizer (L : Set X) = ⊥) {t : CFSG.Open.StatedLieTag} {n f : ℕ}
    (ht : CFSG.AGLEmbedding.ParabAutIrr.ClassicalTag t)
    (hm : CFSG.Open.StatedClassicalModel ↥L t n 2 f) {R : Subgroup X}
    (hR : CFSG.LocalAnalysis.RankThreeUC.S15.IsThreeOnePlusFour ↥R) :
    3 ≤ CFSG.Open.pRank 3 L := by
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · exact three_le_pRank_of_psl_model hC hm hR
  · exact three_le_pRank_of_psu_model hC hm hR
  · exact three_le_pRank_of_psp_model hC hm hR
  · exact three_le_pRank_of_pomegaPlus_model hm
  · exact three_le_pRank_of_pomegaMinus_model hC hm hR

theorem kFact1410a_holds :
    KFact1410a := by
  intro X _ _ L hLn hq hZ hC hcl R hR
  haveI : L.Normal := hLn
  let e0 : ↥L ⧸ Subgroup.center ↥L ≃* ↥L :=
    (QuotientGroup.quotientMulEquivOfEq (G := ↥L) hZ).trans
      (QuotientGroup.quotientBot (G := ↥L))
  have hclL : CFSG.AGLEmbedding.IsClassicalTwoOrG2 ↥L :=
    CFSG.HardMathSupport.Cooperstein.Proving.isClassicalTwoOrG2_of_mulEquiv e0 hcl
  rcases hclL with ⟨d, hd, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨d, hd, ⟨e⟩⟩
  · rcases CFSG.AGLEmbedding.ParabAutIrr.classical_model_or_g2 d hd e with
      ⟨t, n, f, ht, hm⟩ | ⟨q, hv, hq2, hdq⟩
    · exact three_le_pRank_of_classicalModel hC ht hm hR
    · subst hdq
      exact three_le_pRank_of_outPNice (outPNice_three_G2_even q hv hq2 e) hC hR
  · have hT := isThreeOnePlusFour_map_conjNormal hC hR
    refine (false_of_le_mulAut_small (T := R.map (MulAut.conjNormal (H := L)))
      (Or.inl ⟨n, hn, ⟨e⟩⟩) ?_ ?_).elim
    · simpa using hT.1
    · intro t ht
      simpa using congrArg Subtype.val (hT.2.1 ⟨t, ht⟩)
  · have hT := isThreeOnePlusFour_map_conjNormal hC hR
    refine (false_of_le_mulAut_small (T := R.map (MulAut.conjNormal (H := L)))
      (Or.inr ⟨d, hd, ⟨e⟩⟩) ?_ ?_).elim
    · simpa using hT.1
    · intro t ht
      simpa using congrArg Subtype.val (hT.2.1 ⟨t, ht⟩)

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
