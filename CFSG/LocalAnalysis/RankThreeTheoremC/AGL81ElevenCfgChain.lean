module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenTwelveA6

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.Open CFSG.Quasithin CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

@[expose] def AGL81ElevenFiveOne (p : ℕ) (H : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)) (L : Subgroup G) : Prop :=
  p = 3 ∧ IsAltTwoP 3 K ∧ ∃ I₀ ∈ cZero (H ⊓ L),
    CFSG.ComponentClassification.AS76b.oUpperTwo I₀ ≤ hyp111Pre p H K

variable (G) in
@[expose] def AGL81ElevenSixCfg : Prop :=
  Setting G → ∀ (p : ℕ) (P : Sylow p G) (M H Q : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)),
    p ∈ rankThreeSigmaA G → AGL81CfgData p P M H Q K → ¬ HasPrimeConstraint (G := H) p →
    ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      (L.subgroupOf M).Normal ∨ AGL81ElevenFiveOne p H K L

variable (G) in
@[expose] def AGL81ElevenSevenCfg : Prop :=
  Setting G → ∀ (p : ℕ) (P : Sylow p G) (M H Q : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)),
    p ∈ rankThreeSigmaA G → AGL81CfgData p P M H Q K → ¬ HasPrimeConstraint (G := H) p →
    ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L → (L.subgroupOf M).Normal →
    ¬ AGL81ElevenFiveOne p H K L →
      (∀ I₀ ∈ cZero (H ⊓ L),
        CFSG.ComponentClassification.AS76b.oUpperTwo I₀ ≤ d1PlusCore p H K) ∧
      Open.pRank p (d1PlusCore p H K) = 1 ∧
      (jZero H L ≤ d1PlusCore p H K ∨ (p = 3 ∧ IsLinThreeFour K)) ∧
      (jZero H L ≤ d1PlusCore p H K → ∀ b ∈ d1LiftX p H Q K, ∀ x ∈ jZero H L,
        b * x * b⁻¹ * x⁻¹ ∈ pCoreOf 2 (jZero H L))

variable (G) in
@[expose] def AGL81ElevenSevenCfgThree : Prop :=
  Setting G → ∀ (P : Sylow 3 G) (M H Q : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)),
    3 ∈ rankThreeSigmaA G → AGL81CfgData 3 P M H Q K → ¬ HasPrimeConstraint (G := H) 3 →
    ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L → (L.subgroupOf M).Normal →
    ¬ AGL81ElevenFiveOne 3 H K L →
      (∀ I₀ ∈ cZero (H ⊓ L),
        CFSG.ComponentClassification.AS76b.oUpperTwo I₀ ≤ d1PlusCore 3 H K) ∧
      Open.pRank 3 (d1PlusCore 3 H K) = 1 ∧
      (jZero H L ≤ d1PlusCore 3 H K ∨ IsLinThreeFour K) ∧
      (jZero H L ≤ d1PlusCore 3 H K → ∀ b ∈ d1LiftX 3 H Q K, ∀ x ∈ jZero H L,
        b * x * b⁻¹ * x⁻¹ ∈ pCoreOf 2 (jZero H L))

variable (G) in
@[expose] def AGL81ElevenElevenCfg : Prop :=
  Setting G → ∀ (P : Sylow 3 G) (M H Q : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)),
    3 ∈ rankThreeSigmaA G → AGL81CfgData 3 P M H Q K → IsAltTwoP 3 K →
    ¬ HasPrimeConstraint (G := H) 3 →
    ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L → (L.subgroupOf M).Normal →
    ¬ AGL81ElevenFiveOne 3 H K L →
      IsAGLQ 3 M (d1LiftX 3 H Q K) ∧ ⁅d1LiftX 3 H Q K, L⁆ ≤ pCoreOf 2 L

theorem agl81ElevenCfgChain_of (h6 : AGL81ElevenSixCfg G) (h11 : AGL81ElevenElevenCfg G)
    (h4 : AGL81ElevenTwelveOne G) (hS : Setting G) {P : Sylow 3 G} {M H Q : Subgroup G}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)} (hσ : 3 ∈ rankThreeSigmaA G)
    (hd : AGL81CfgData 3 P M H Q K)
    (hA : IsAltTwoP 3 K) (hnc : ¬ HasPrimeConstraint (G := H) 3) (h3 : 3 ≤ Open.pRank 3 H)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L) :
    (L.subgroupOf M).Normal ∧ IsAGLQ 3 M (d1LiftX 3 H Q K) ∧
      ⁅d1LiftX 3 H Q K, L⁆ ≤ pCoreOf 2 L := by
  have hno : ¬ AGL81ElevenFiveOne 3 H K L := by
    rintro ⟨-, -, hI⟩
    have := h4 hS P M H Q K hσ hd hA hnc L hL hI
    omega
  have hN : (L.subgroupOf M).Normal := (h6 hS 3 P M H Q K hσ hd hnc L hL).resolve_right hno
  exact ⟨hN, h11 hS P M H Q K hσ hd hA hnc L hL hN hno⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
