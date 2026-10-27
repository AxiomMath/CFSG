module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lTCQuot
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lFixedComp
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.FStarFacts
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.LeavesR

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open Subgroup CFSG.Blueprint CFSG.ComponentClassification
open CFSG.Open (StatedLieTag)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem a2l_pPrimeCore_ne_top_of_quasisimple {K : Type} [Group K] [Finite K]
    (hK : CFSG.IsQuasisimple K) : pPrimeCore 2 K ≠ ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro htop
  have hodd : Odd (Nat.card K) := by
    have h := pPrimeCore_coprime_card (G := K) (p := 2)
    rw [htop, Subgroup.card_top] at h
    exact Nat.coprime_two_left.1 h
  haveI : Group.IsSolvable K := CFSG.Milestones.odd_order_solvable hodd
  haveI : Nontrivial K := CFSG.LocalCores.isQuasisimple_nontrivial hK
  haveI : Group.IsPerfect K := hK.1
  exact Group.IsPerfect.not_isSolvable K inferInstance

theorem a2l_exc_reduce {K : Type} [Group K] [Finite K] (hK : CFSG.IsQuasisimple K)
    (hnF : ¬ HypA2.FStarSimple (K ⧸ center K)) {σ : MulAut K} (hσ : ∀ y, σ (σ y) = y)
    {X : Subgroup K} (hXσ : X ≤ fixedSubgroup σ)
    (hXc : IsPComponent 2 (X.subgroupOf (fixedSubgroup σ))) (hXF : HypA2.IsFStar ↥X) :
    ∃ (σ' : MulAut (K ⧸ center K)) (P : Subgroup (K ⧸ center K)),
      CatLeaf.ProperFixedComponent σ' P ∧ HypA2.FStarSimple (↥P ⧸ Open.fusionZStar ↥P) := by
  by_cases hXtop : X = ⊤
  · exfalso
    subst hXtop
    apply hnF
    obtain ⟨eZ⟩ := GrSLit.nonempty_fusionZStar_equiv_of_mulEquiv'
      (Subgroup.topEquiv : ↥(⊤ : Subgroup K) ≃* K)
    have h2 := (HypA2.fStarSimple_congr eZ).1 (HypA2.fStarSimple_of_isFStar hXF)
    have hZ := CatLeaf.fusionZStar_eq_center_of_quasisimple hK
      (a2l_pPrimeCore_ne_top_of_quasisimple hK)
    exact (HypA2.fStarSimple_congr (QuotientGroup.quotientMulEquivOfEq hZ)).1 h2
  · obtain ⟨σ', -, hPF, ⟨e⟩⟩ := a2l_properFixedComponent_quotient hK hσ hXσ hXc hXtop
    exact ⟨σ', _, hPF, (HypA2.fStarSimple_congr e).1 (HypA2.fStarSimple_of_isFStar hXF)⟩

theorem a2l_exc_component {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hq : CatLeaf.FixedTwoComponentsQuasisimple S) {σ : MulAut S} {P : Subgroup S}
    (h : CatLeaf.ProperFixedComponent σ P)
    (hF : HypA2.FStarSimple (↥P ⧸ Open.fusionZStar ↥P)) :
    HypA2.ProperFixedComp σ P ∧ HypA2.FStarSimple (↥P ⧸ center ↥P) := by
  have hσσ : σ * σ = 1 := MulEquiv.ext fun y => h.1 y
  have hqP := hq σ hσσ h.ne_one _ h.2.2.1
  obtain ⟨hcomp, -⟩ := h.fusionZStar_equiv_of_quasisimple hqP
  have hP : HypA2.ProperFixedComp σ P := ⟨h.1, h.2.1, h.2.2.2, hcomp⟩
  obtain ⟨e⟩ := a2l_fusionZStar_equiv hP
  exact ⟨hP, (HypA2.fStarSimple_congr e).1 hF⟩

theorem a2l_fStarSimple_model {Q : Type} [Group Q] (h : HypA2.FStarSimple Q) :
    ∃ (τ : StatedLieTag) (n d : ℕ), LieModel Q τ n 3 d ∧ (d = 1 ∨ d = 2 ∨ d = 4) := by
  unfold HypA2.FStarSimple at h
  rcases h with h1 | h2 | h3 | h4 | h5
  · exact ⟨.PSL, 2, 2, h1, by omega⟩
  · exact ⟨.PSL, 2, 4, h2, by omega⟩
  · exact ⟨.PSL, 3, 1, h3, by omega⟩
  · exact ⟨.PSU, 3, 1, h4, by omega⟩
  · unfold SmallF3OmegaQuotient at h5
    rcases h5 with h | h | h | h | h | h
    · exact ⟨.PSp, 2, 1, h, by omega⟩
    · exact ⟨.PSL, 4, 1, h, by omega⟩
    · exact ⟨.PSU, 4, 1, h, by omega⟩
    · exact ⟨.POmegaOdd, 3, 1, h, by omega⟩
    · exact ⟨.POmegaPlus, 4, 1, h, by omega⟩
    · exact ⟨.POmegaMinus, 4, 1, h, by omega⟩

theorem a2l_fieldExp_of_fStar (hCL2 : HypA2.ClosureFieldExp) {S : Type} [Group S] [Finite S]
    [IsSimpleGroup S] (hq : CatLeaf.FixedTwoComponentsQuasisimple S) {τ : StatedLieTag}
    {n c : ℕ} (hS : LieModel S τ n 3 c) {σ : MulAut S} {P : Subgroup S}
    (h : CatLeaf.ProperFixedComponent σ P)
    (hF : HypA2.FStarSimple (↥P ⧸ Open.fusionZStar ↥P)) :
    c = 1 ∨ c = 2 ∨ c = 4 ∨ c = 8 := by
  obtain ⟨hP, hF'⟩ := a2l_exc_component hq h hF
  obtain ⟨τ', n', d, hm, hd⟩ := a2l_fStarSimple_model hF'
  have hrel := hCL2 S σ P hP τ n c hS τ' n' d hm
  omega

end CFSG.OddStandard.SmallF3.HypA2Leaves
