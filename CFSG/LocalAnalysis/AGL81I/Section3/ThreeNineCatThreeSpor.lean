module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineCatalogue
public import CFSG.Sporadic.Bridge.Catalogue
public import CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.ThreeNineStatements

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3

open CFSG.Open TauCeti
open CFSG.LocalAnalysis.AGL81TheoremCD.Section12 (gammaOver)
open CFSG.Blueprint.NativeSporadic

@[expose] def SporadicIn24_12Three (s : SporadicName) : Prop :=
  s = .M11 ∨ s = .M12 ∨ s = .J3

@[expose] def SporadicGen24_12Three : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K E : Subgroup X) (s : SporadicName),
    K.Normal → CFSG.IsQuasisimple ↥K → CFSG.pPrimeCore 3 ↥K = ⊥ →
    Nonempty (↥K ⧸ Subgroup.center ↥K ≃* s.Group) → s ≠ .McL →
    (Subgroup.center ↥K = ⊥ → ¬ SporadicIn24_12Three s) →
    IsElemAbelian 3 E → Nat.card E = 3 ^ 2 → CFSG.Open.pRank 3 (K ⊔ E) ≤ 3 →
    K ≤ gammaOver 1 3 E K

theorem kGroupLowRank24_12_three_of_sporadic
    (hSG : SporadicGen24_12Three) (hGA : CFSG.Open.GriessAllModelsStatement)
    {X : Type} [Group X] [Finite X] {K E : Subgroup X} (hKq : CFSG.IsQuasisimple ↥K)
    (hOp : CFSG.pPrimeCore 3 ↥K = ⊥) (hKcat : CFSG.SectionRank.IsKGroupCat ↥K) (hKn : K.Normal)
    (hE : IsElemAbelian 3 E) (hEc : Nat.card E = 3 ^ 2) (hrk : CFSG.Open.pRank 3 (K ⊔ E) ≤ 3)
    (hΓ : ¬ K ≤ gammaOver 1 3 E K) {s : SporadicName}
    (e : (↥K ⧸ Subgroup.center ↥K) ≃* (CFSGIndex.sporadic s).Group) :
    KGroupLowRank24_12 3 ↥K := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ψ⟩ := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group s
  refine ⟨Nat.prime_three, by norm_num, hKq, hKcat, ?_⟩
  by_cases hs : s = .McL
  · subst hs
    by_cases hZ : Subgroup.center ↥K = ⊥
    · let φ : ↥K ≃* SporadicName.McL.Group :=
        ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans e
      refine Or.inr (Or.inr (Or.inl ⟨rfl, ?_⟩))
      iterate 10 right
      left
      exact ⟨φ.trans ψ.symm⟩
    · have hZp : IsPGroup 3 (Subgroup.center ↥K) :=
        CFSG.isPGroup_of_nilpotent_normal (Subgroup.center ↥K) inferInstance inferInstance hOp
      have h3 : Nat.card (Subgroup.center ↥K) ∣ 3 :=
        CFSG.RankThree.PartTwo.Sec4.Census.coverCenterThree_of_rest
          (CFSG.RankThree.PartTwo.Sec4.Census.coverCenterThreeRest_of hGA) ↥K hKq hZp
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e.trans ψ.symm⟩))))))
      have hcard : Nat.card (Subgroup.center ↥K) = 3 := by
        rcases (Nat.dvd_prime Nat.prime_three).1 h3 with h1 | h1
        · exact absurd (Subgroup.card_eq_one.mp h1) hZ
        · exact h1
      refine Or.inr (Or.inr (Or.inl ⟨rfl, ?_⟩))
      iterate 13 right
      left
      exact ⟨hcard, ⟨e.trans ψ.symm⟩⟩
  · by_cases hin : Subgroup.center ↥K = ⊥ ∧ SporadicIn24_12Three s
    · obtain ⟨hZ, hs'⟩ := hin
      let φ : ↥K ≃* s.Group :=
        ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans e
      have hspor : IsSporadic ↥K s := ⟨φ.trans ψ.symm⟩
      refine Or.inr (Or.inr (Or.inl ⟨rfl, ?_⟩))
      rcases hs' with rfl | rfl | rfl
      · iterate 7 right
        left
        exact hspor
      · iterate 8 right
        left
        exact hspor
      · iterate 9 right
        left
        exact hspor
    · exact absurd (hSG X K E s hKn hKq hOp ⟨e⟩ hs (fun hZ hs' => hin ⟨hZ, hs'⟩) hE hEc hrk) hΓ

end CFSG.LocalAnalysis.AGL81I.Section3
