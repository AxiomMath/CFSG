module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineCatFive
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineCatAlt
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineCatDef
public import CFSG.LocalAnalysis.GL83PartI.I_24_3.List
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.TableComplete
public import CFSG.Adapters.CatalogAgree
public import CFSG.LieType.SeitzGeneration.SeitzStatus

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3

open CFSG.Open TauCeti
open CFSG.LocalAnalysis.AGL81TheoremCD.Section12 (gammaOver)

@[expose] def Catalogue24_12Five : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K E : Subgroup X) (p : ℕ), p.Prime → 5 ≤ p →
    CFSG.IsQuasisimple ↥K → CFSG.pPrimeCore p ↥K = ⊥ → CFSG.SectionRank.IsKGroupCat ↥K →
    K.Normal → IsElemAbelian p E → Nat.card E = p ^ 2 → CFSG.Open.pRank p (K ⊔ E) ≤ 3 →
    ¬ K ≤ gammaOver 1 p E K → KGroupLowRank24_12 p ↥K

theorem catalogue24_12Five_of_sporadicGen
    (hSG : SporadicGen24_12Five) :
    Catalogue24_12Five := by
  intro X _ _ K E p hp hp5 hKq hOp hKcat hKn hE hEc hrk hΓ
  have hp2 : p ≠ 2 := by omega
  have hPC : GL83.I243.PCoverList :=
    GL83.I243.pCoverList_of_tables
      CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
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
    refine ⟨hp, hp2, hKq, hKcat, Or.inl ?_⟩
    rcases alt_of_catalogue24_12_five hPC hp hp5 hKq hOp hKn hE hEc hrk hΓ hn e with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  | lie d =>
    by_cases hpd : p = d.1.characteristic
    · refine ⟨hp, hp2, hKq, hKcat, ?_⟩
      rcases lieDef_of_catalogue24_12_five hPC hp hp5 hKq hOp hKn hE hEc hrk hΓ hpd e with
        h | h | h | h | h | h
      · exact Or.inl (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl h))))
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))
      · exact Or.inr (Or.inl ⟨by omega, h⟩)
    · exact kGroupLowRank24_12_of_lie_cross_five
        CFSG.LieType.SeitzGeneration.kFactSeitzRankTwo_holds
        CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement hp hp5 hKq hOp hKcat
        hKn hE hEc hrk hΓ hpd e
  | sporadic s =>
    exact kGroupLowRank24_12_of_sporadic_five hSG hPC hp hp5 hKq hOp hKcat hKn hE hEc hrk hΓ e

end CFSG.LocalAnalysis.AGL81I.Section3
