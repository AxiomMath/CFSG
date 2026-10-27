module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLZeroThreeWrap

public section
namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ComponentClassification.OuterAutomorphisms

@[expose] def D1SmallSPLZeroIaThree : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (P : Sylow 3 G) (M H R : Subgroup G)
    (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)), D1OneSmallData 3 P M H R Rbar K →
    D1UniqueOver H R (nclIn H (d1LiftX 3 H R K)) → ∀ z : G, D1SmallCZElt 3 H R K z →
    IsSPLFamily 3 K → D1CzSP 3 z → D1CzOutside 3 z → d1MapPCore 3 M H = ⊥ →
    CFSG.pCore 3 (↥M ⧸ CFSG.pCore 2 ↥M) = ⊥ → D1SmallIa 3 H K → False

@[expose] def D1SmallSPLZeroIbThreeCore : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (P : Sylow 3 G) (M H R : Subgroup G)
    (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)), D1OneSmallData 3 P M H R Rbar K →
    D1UniqueOver H R (nclIn H (d1LiftX 3 H R K)) → ∀ z : G, D1SmallCZElt 3 H R K z →
    IsSPLFamily 3 K → D1CzSP 3 z → D1CzOutside 3 z → d1MapPCore 3 M H = ⊥ →
    ¬ D1SmallIa 3 H K → CFSG.pCore 3 (↥M ⧸ CFSG.pCore 2 ↥M) = ⊥ →
    (∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      d1LiftX 3 H R K ≤ Subgroup.normalizer (L : Set G)) →
    ∃ X₁ : Subgroup G, X₁ ≤ d1LiftX 3 H R K ∧ X₁ ≠ ⊥ ∧
      (∀ L : Subgroup G, IsTwoPrimeComponent M L →
        (IsWeakSBlock M (pCoreOf 2 H) L ∨ L ≤ GLBPrimeCore 3 H) →
        barM M X₁ ≤ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) ∧
      ∀ s : ℕ, s.Prime → s ≠ 2 → s ≠ 3 →
        barM M X₁ ≤ Subgroup.centralizer
          ((CFSG.pCore s (↥M ⧸ CFSG.pCore 2 ↥M) : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) :
            Set (↥M ⧸ CFSG.pCore 2 ↥M)) ∨
        4 ≤ CFSG.Open.pRank s (((CFSG.pCore s (↥M ⧸ CFSG.pCore 2 ↥M)).comap
          (QuotientGroup.mk' (CFSG.pCore 2 ↥M))).map M.subtype)

theorem d1SmallSPLZeroIbRest4_of_split (hUP : KFactUPrimeSmall) (hSTO : KFactSmallThreeOrders)
    (hSch : KFactCatalogSchreier) (h84 : Asc81bEightFour) (hD2 : D1NoXBlock)
    (hIa : D1SmallSPLZeroIaThree) (hIb : D1SmallSPLZeroIbThreeCore) : D1SmallSPLZeroIbRest4 := by
  intro G _ _ P M H R Rbar K hd huniq z hz hspl hSP hout hV hOp hXL
  by_cases hIa' : D1SmallIa 3 H K
  · exact hIa G P M H R Rbar K hd huniq z hz hspl hSP hout hV hOp hIa'
  obtain ⟨X₁, hX₁X, hX₁, hcompX₁, hodd⟩ :=
    hIb G P M H R Rbar K hd huniq z hz hspl hSP hout hV hIa' hOp (hXL hIa')
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨T, hT, h3, hUPK, houtK, hsT⟩ := hd.exists_kFacts_three hUP hSTO hSch hspl
  have hXK : d1LiftX 3 H R K ≤ H ⊓ M := (d1LiftX_le 3 H R K).trans h3.le_inf
  have hperf : ∀ L : Subgroup G, L ≤ H ⊓ M → ⁅L, L⁆ = L → L ≤ d1PlusCore 3 H K := by
    intro L hL' hLL
    exact le_d1PlusCore_of_map_le (hL'.trans inf_le_left)
      (hd.le_centralizer_of_perfect hT hUPK houtK hsT
        (Subgroup.map_mono (Subgroup.subgroupOf_mono H hL'))
        (commutator_map_eq_self (hL'.trans inf_le_left) hLL))
  have hcompall : ∀ Lb : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), IsComponentOf Lb ⊤ →
      barM M X₁ ≤ Subgroup.centralizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    intro Lb hLb
    obtain ⟨L, hL2, rfl, hw | hle⟩ := h3.exists_weakSBlock_or_le_inf hLb
    · exact hcompX₁ L hL2 (Or.inl hw)
    · by_cases hLN : L ≤ GLBPrimeCore 3 H
      · exact hcompX₁ L hL2 (Or.inr hLN)
      · exact (barM_mono hX₁X).trans (barM_le_centralizer_of_commutator_mem h3 hL2
          (hle.trans inf_le_left) hLN (hXK.trans inf_le_right) (hXK.trans inf_le_left)
          (fun x hx l hl => hd.commutator_mem_primeCore_of_mem_d1PlusCore hx
            (hperf L hle hL2.perfect hl)))
  have hY := hd.pCorePreimage_inf_ne_bot_of_core h3 hUPK h84 hD2 hX₁X hX₁ hcompall hodd
  obtain ⟨-, -, -, -, hWiff⟩ := hd.d1MapPCore_facts h3 h84 hD2
  apply hWiff.mp hY
  rw [hV, bot_inf_eq]

theorem d1SmallSPLZeroIbRest2_of_split
    (hK7 : KFactOneLieSmallLie) (hK8 : KFactSmallBorelSolvable)
    (hβ : KFactBeta) (hKO : KFactOneLie) (hΓ : KFactOneLieBorelSolvable)
    (hSch : KFactCatalogSchreier) (hα : KFactThreeOrFiveDvd) (h84 : Asc81bEightFour)
    (h85 : Asc81bEightFive) (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hK2 : KFactParabolicThree) (hC3' : CitedBlockThreeTransvection)
    (hK5' : KFactBlockThreeAltSeven) (hKF : KFactBlockCentCycIb)
    (hK3 : CitedBlockTransvectionCyclic) (hK4 : CitedBlockAltNormalizerSq)
    (hUP : KFactUPrimeSmall) (hSTO : KFactSmallThreeOrders) (hSE : KFactSmallSylowExp)
    (hShp : KFactSmallSylowShape) (hIa : D1SmallSPLZeroIaThree)
    (hIb : D1SmallSPLZeroIbThreeCore) : D1SmallSPLZeroIbRest2 :=
  d1SmallSPLZeroIbRest2_of_rest3' hK7 hK8 hβ hKO hΓ hSch hα h84 h85 h86 h93 hD2 hK2 hC3' hK5' hKF
    hK3 hK4 (d1SmallSPLZeroIbRest3_of_rest4 hUP hSTO hSE hShp hβ hKO hΓ hSch h84 h85 h86 h93 hD2
      hK2 hC3' hK5' (d1SmallSPLZeroIbRest4_of_split hUP hSTO hSch h84 hD2 hIa hIb))

end CFSG.AGLEmbedding
