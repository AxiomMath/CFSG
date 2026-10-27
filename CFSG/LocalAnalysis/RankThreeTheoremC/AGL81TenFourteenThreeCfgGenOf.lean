module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenElevenOtherCfgOf
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenFourteenThreeAll
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenFourteenThreeProof

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

variable (G) in
@[expose] def AGL81TenFourteenThreeCfgFive : Prop :=
  Setting G → ∀ (P : Sylow 5 G) (M H Q : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 5)),
    AGL81CfgData 5 P M H Q K → ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
    5 ∣ Nat.card L → ∀ a : G, a ∈ M → orderOf a = 5 →
    ¬ Subgroup.centralizer ({a} : Set G) ≤ M →
    (∃ U : Subgroup G, U ≤ Subgroup.centralizer ({a} : Set G) ∧ IsAGLQ 5 M U) →
    ¬ ⁅Subgroup.zpowers a, L⁆ ≤ pCoreOf 2 L

variable (G) in
@[expose] def AGL81TenOneNoAFiveCfg : Prop :=
  Setting G → ∀ (p : ℕ) (P : Sylow p G) (M H Q : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)),
    AGL81CfgData p P M H Q K → ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      IsEmpty (↥(barM M L) ≃* alternatingGroup (Fin 5))

theorem agl81TenFourteenThreeCfgFive_of (h2 : AGL81TenFourteenTwoPerfectA5 G)
    (h101 : AGL81TenOneNoAFiveCfg G) : AGL81TenFourteenThreeCfgFive G := by
  intro hS P M H Q K hd L hL h5L a ha hao hC hU hcomm
  obtain ⟨H₁, R₁, hesc⟩ := hd.escape
  obtain ⟨I, hI, -, ⟨eIL⟩, hdvd⟩ := TenFourteenThree.exists_isTwoPrimeComponent_centralizer_iso
    hL.toIsTwoPrimeComponent (by norm_num) (by norm_num) ha hao hcomm
  obtain ⟨-, ⟨eA⟩⟩ := h2 hS 5 P M H₁ R₁ hesc a ha hao hC hU I hI
    (hdvd 5 (by norm_num) (by norm_num) h5L)
  obtain ⟨eB⟩ := CFSG.RankThree.PartTwo.Sec19.Item194Proof.nonempty_barM_mulEquiv hL.le
    hL.toIsTwoPrimeComponent.inf_twoCore
  exact (h101 hS 5 P M H Q K hd L hL).false ((eB.symm.trans eIL.symm).trans eA)

theorem agl81TenFourteenThreeCfgGen_of (h2 : AGL81TenFourteenTwoPerfect G)
    (h5 : AGL81TenFourteenThreeCfgFive G) : AGL81TenFourteenThreeCfgGen G := by
  intro hS p P M H Q K hd L hL hpL a ha hao hC hU hcomm
  by_cases hp5 : p = 5
  · subst hp5
    exact h5 hS P M H Q K hd L hL hpL a ha hao hC hU hcomm
  obtain ⟨H₁, R₁, hesc⟩ := hd.escape
  obtain ⟨I, hI, -, hdvd⟩ := TenFourteenThree.exists_isTwoPrimeComponent_centralizer
    hL.toIsTwoPrimeComponent hesc.prime hesc.ne_two ha hao hcomm
  exact hp5 (h2 hS p P M H₁ R₁ hesc a ha hao hC hU I hI
    (hdvd p hesc.prime hesc.ne_two hpL))

theorem agl81TenFourteenThreeCfgGen_of_A5 (h2 : AGL81TenFourteenTwoPerfectA5 G)
    (h101 : AGL81TenOneNoAFiveCfg G) : AGL81TenFourteenThreeCfgGen G :=
  agl81TenFourteenThreeCfgGen_of (agl81TenFourteenTwoPerfect_of_A5 h2)
    (agl81TenFourteenThreeCfgFive_of h2 h101)

end CFSG.LocalAnalysis.RankThreeTheoremC
