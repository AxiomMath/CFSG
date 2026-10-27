module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineCatCross
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineCatalogue
public import CFSG.LieType.OutStructureCoverCenterFive
public import CFSG.LocalAnalysis.StandardType.ChevTwoLieModel
public import CFSG.LieType.SeitzGeneration.ExcVacuousSuzuki
public import CFSG.LocalAnalysis.GL83PartI.I_24_3.ListDefs
public import CFSG.Sporadic.Bridge.Catalogue

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3

open CFSG.Open TauCeti
open CFSG.LocalAnalysis.AGL81TheoremCD.Section12 (gammaOver)
open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

theorem pRank_top_le_three_of_sup {X : Type} [Group X] [Finite X] {K E : Subgroup X} {p : ℕ}
    (hp : p.Prime) (hrk : CFSG.Open.pRank p (K ⊔ E) ≤ 3) :
    CFSG.Open.pRank p (⊤ : Subgroup ↥K) ≤ 3 := by
  rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup K]
  exact (CFSG.SectionRank.pRank_mono hp.one_lt le_sup_left).trans hrk

theorem kGroupLowRank24_12_of_lie_cross_five
    (hS : CFSG.AGLEmbeddingD2.KFactSeitzRankTwo) (hGA : CFSG.Open.GriessAllModelsStatement)
    {X : Type} [Group X] [Finite X] {K E : Subgroup X} {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hKq : CFSG.IsQuasisimple ↥K) (hOp : CFSG.pPrimeCore p ↥K = ⊥)
    (hKcat : CFSG.SectionRank.IsKGroupCat ↥K) (hKn : K.Normal) (hE : IsElemAbelian p E)
    (hEc : Nat.card E = p ^ 2) (hrk : CFSG.Open.pRank p (K ⊔ E) ≤ 3)
    (hΓ : ¬ K ≤ gammaOver 1 p E K) {d : ValidLieTypeIndex} (hpd : p ≠ d.1.characteristic)
    (e : (↥K ⧸ Subgroup.center ↥K) ≃* (CFSGIndex.lie d).Group) :
    KGroupLowRank24_12 p ↥K := by
  have hp2 : p ≠ 2 := by omega
  have hZ := CFSG.LieType.OutStructure.center_eq_bot_of_lieIndex_of_five_le hGA hKq hp hp5 hOp e
    (pRank_top_le_three_of_sup hp hrk)
  let φ : ↥K ≃* (CFSGIndex.lie d).Group :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans e
  by_cases hexc : CFSG.AGLEmbeddingD2.IsD2SeitzException p d.1
  · rcases hexc with ⟨rfl, -⟩ | ⟨rfl, hd⟩
    · omega
    refine ⟨hp, hp2, hKq, hKcat, Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, ?_⟩)))⟩
    obtain ⟨d, hv⟩ := d
    rcases hd with hd | hd <;> simp only at hd <;> subst hd
    · exact Or.inr (Or.inl (CFSG.StandardType.ChevTwo.reeTitsModel_of_tits hv φ))
    · exact Or.inl (CFSG.SectionRank.suzukiModel_of_mulEquiv φ
        (CFSG.LieType.SeitzGeneration.suzukiModel_cat hv))
  · exact absurd (le_gammaOver_of_seitz hS hp hp2 hKn hpd hexc φ hE hEc) hΓ

@[expose] def SporadicIn24_12 (p : ℕ) (s : SporadicName) : Prop :=
  (p = 5 ∧ (s = .McL ∨ s = .HS ∨ s = .Fi22 ∨ s = .Co1 ∨ s = .Co2 ∨ s = .Co3 ∨ s = .Ly ∨
      s = .Ru ∨ s = .B ∨ s = .HN)) ∨
    (p = 7 ∧ (s = .He ∨ s = .ONan ∨ s = .Fi24Prime ∨ s = .M)) ∨ (p = 11 ∧ s = .J4)

@[expose] def SporadicGen24_12Five : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K E : Subgroup X) (p : ℕ) (s : SporadicName),
    p.Prime → 5 ≤ p → ¬ SporadicIn24_12 p s → K.Normal → Nonempty (↥K ≃* s.Group) →
    IsElemAbelian p E → Nat.card E = p ^ 2 → CFSG.Open.pRank p (K ⊔ E) ≤ 3 →
    K ≤ gammaOver 1 p E K

theorem center_eq_bot_of_not_lie_five (hPC : GL83.I243.PCoverList) {K : Type} [Group K]
    [Finite K] (hq : CFSG.IsQuasisimple K) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hOp : CFSG.pPrimeCore p K = ⊥) {i : CFSGIndex} (hi : ∀ d, i ≠ .lie d)
    (e : (K ⧸ Subgroup.center K) ≃* i.Group) : Subgroup.center K = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  have hZp : IsPGroup p (Subgroup.center K) :=
    CFSG.isPGroup_of_nilpotent_normal (Subgroup.center K) inferInstance inferInstance hOp
  by_contra hne
  have hdvd : p ∣ Nat.card (Subgroup.center K) :=
    hZp.card_eq_or_dvd.resolve_left fun h => hne (Subgroup.card_eq_one.mp h)
  have hq' : CFSG.Open.IsQuasisimple K := ⟨Group.isPerfect_def.mp hq.1, hq.2.1⟩
  rcases hPC K hq' p hp (by omega) hdvd i ⟨e⟩ with ⟨d, rfl, -⟩ | ⟨h3, -⟩
  · exact hi d rfl
  · omega

theorem kGroupLowRank24_12_of_sporadic_five
    (hSG : SporadicGen24_12Five) (hPC : GL83.I243.PCoverList)
    {X : Type} [Group X] [Finite X] {K E : Subgroup X} {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hKq : CFSG.IsQuasisimple ↥K) (hOp : CFSG.pPrimeCore p ↥K = ⊥)
    (hKcat : CFSG.SectionRank.IsKGroupCat ↥K) (hKn : K.Normal) (hE : IsElemAbelian p E)
    (hEc : Nat.card E = p ^ 2) (hrk : CFSG.Open.pRank p (K ⊔ E) ≤ 3)
    (hΓ : ¬ K ≤ gammaOver 1 p E K) {s : SporadicName}
    (e : (↥K ⧸ Subgroup.center ↥K) ≃* (CFSGIndex.sporadic s).Group) :
    KGroupLowRank24_12 p ↥K := by
  have hp2 : p ≠ 2 := by omega
  have hZ := center_eq_bot_of_not_lie_five hPC hKq hp hp5 hOp (i := .sporadic s)
    (fun d h => CFSGIndex.noConfusion h) e
  let φ : ↥K ≃* s.Group :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans e
  by_cases hin : SporadicIn24_12 p s
  · obtain ⟨ψ⟩ := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group s
    have hspor : IsSporadic ↥K s := ⟨φ.trans ψ.symm⟩
    refine ⟨hp, hp2, hKq, hKcat, ?_⟩
    rcases hin with ⟨rfl, hs⟩ | ⟨rfl, hs⟩ | ⟨rfl, rfl⟩
    · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, ?_⟩)))
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact Or.inr (Or.inr (Or.inl hspor))
      · exact Or.inr (Or.inr (Or.inr (Or.inl hspor)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hspor))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hspor)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hspor))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hspor)))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inl hspor))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inl hspor)))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inl hspor))))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr hspor))))))))))
    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, ?_⟩))))
      rcases hs with rfl | rfl | rfl | rfl
      · exact Or.inl hspor
      · exact Or.inr (Or.inl hspor)
      · exact Or.inr (Or.inr (Or.inl hspor))
      · exact Or.inr (Or.inr (Or.inr hspor))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, hspor⟩))))
  · exact absurd (hSG X K E p s hp hp5 hin hKn ⟨φ⟩ hE hEc hrk) hΓ

end CFSG.LocalAnalysis.AGL81I.Section3
