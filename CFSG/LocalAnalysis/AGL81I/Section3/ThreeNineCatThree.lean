module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineCatFiveMain
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineCatThreeAlt
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineCatThreeDef
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineCatThreeSpor
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineCatThreeCross
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.SeitzRest5Even

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3

open CFSG.Open TauCeti
open CFSG.LocalAnalysis.AGL81TheoremCD.Section12 (gammaOver)

@[expose] def Catalogue24_12Three : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K E : Subgroup X),
    CFSG.IsQuasisimple ↥K → CFSG.pPrimeCore 3 ↥K = ⊥ → CFSG.SectionRank.IsKGroupCat ↥K →
    K.Normal → IsElemAbelian 3 E → Nat.card E = 3 ^ 2 → CFSG.Open.pRank 3 (K ⊔ E) ≤ 3 →
    ¬ K ≤ gammaOver 1 3 E K → KGroupLowRank24_12 3 ↥K

@[expose] def Catalogue24_12 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K E : Subgroup X) (p : ℕ), p.Prime → p ≠ 2 →
    CFSG.IsQuasisimple ↥K → CFSG.pPrimeCore p ↥K = ⊥ → CFSG.SectionRank.IsKGroupCat ↥K →
    K.Normal → IsElemAbelian p E → Nat.card E = p ^ 2 → CFSG.Open.pRank p (K ⊔ E) ≤ 3 →
    ¬ K ≤ gammaOver 1 p E K → KGroupLowRank24_12 p ↥K

theorem catalogue24_12_of_five_three (h5 : Catalogue24_12Five) (h3 : Catalogue24_12Three) :
    Catalogue24_12 := by
  intro X _ _ K E p hp hp2 hKq hOp hKcat hKn hE hEc hrk hΓ
  have h2 := hp.two_le
  rcases (show p = 3 ∨ p = 4 ∨ 5 ≤ p by omega) with rfl | rfl | hp5
  · exact h3 X K E hKq hOp hKcat hKn hE hEc hrk hΓ
  · exact absurd hp (by norm_num)
  · exact h5 X K E p hp hp5 hKq hOp hKcat hKn hE hEc hrk hΓ

theorem catalogue24_12Three_of
    (hSG : SporadicGen24_12Three) (hCR : CrossCoverResidual24_12Three) :
    Catalogue24_12Three := by
  intro X _ _ K E hKq hOp hKcat hKn hE hEc hrk hΓ
  have hGA : CFSG.Open.GriessAllModelsStatement :=
    CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
  have hPC : GL83.I243.PCoverList :=
    GL83.I243.pCoverList_of_tables hGA
      CFSG.Alternating.Multipliers.schurAlternatingMultiplierInput
      CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.sporadicMultipliers_holds
  have : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hKq.2.1
  have hcat : CFSG.Blueprint.Catalog (↥K ⧸ Subgroup.center ↥K) :=
    CFSG.SectionRank.catalog_of_isKGroupCat_of_surjective hKcat ⊤
      ((QuotientGroup.mk' (Subgroup.center ↥K)).comp
        (Subgroup.topEquiv : (⊤ : Subgroup ↥K) ≃* ↥K).toMonoidHom)
      ((QuotientGroup.mk'_surjective _).comp
        (Subgroup.topEquiv : (⊤ : Subgroup ↥K) ≃* ↥K).surjective)
  obtain ⟨i, ⟨e⟩⟩ := CFSG.Open.QTFaithfulEmptyTauCeti.inCatalog_of_catalog _ hcat
  cases i with
  | cyclic r hr =>
    exfalso
    obtain ⟨a, b, hab⟩ := hKq.2.2
    exact hab (e.injective (by rw [map_mul, map_mul, mul_comm]))
  | alternating n hn =>
    exact kGroupLowRank24_12_three_of_alt hPC hKq hOp hKcat hKn hE hEc hrk hΓ hn e
  | lie d =>
    by_cases hpd : 3 = d.1.characteristic
    · have hrkK : CFSG.Open.pRank 3 (⊤ : Subgroup ↥K) ≤ 3 := by
        rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup K]
        exact (CFSG.SectionRank.pRank_mono (by norm_num) le_sup_left).trans hrk
      exact kGroupLowRank24_12_three_of_lieDef hPC hGA CFSG.LieType.defCharRankFourExc
        CFSG.TauCetiBridge.untwistedBridge_G2 hKq hOp hKcat hrkK hpd e
    · exact kGroupLowRank24_12_three_of_cross
        CFSG.LieType.SeitzGeneration.kFactSeitzRankTwo_holds hGA
        CFSG.LocalAnalysis.GLTheoremB.MovingAround.SeitzRest5.twE6ThreeOpenDiag_holds hCR hKq hOp
        hKcat hKn hE hEc hrk hΓ hpd e
  | sporadic s =>
    exact kGroupLowRank24_12_three_of_sporadic hSG hGA hKq hOp hKcat hKn hE hEc hrk hΓ e

end CFSG.LocalAnalysis.AGL81I.Section3
