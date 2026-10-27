module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3Sp62
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3Sp62RankDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

@[expose] def Sp62Omega8Shape (M H R L : Subgroup G) : Prop :=
  Sp62BlockShape M H R L ∧ ∃ d : TauCeti.ValidLieTypeIndex, IsOmegaMinusTwoIndex 4 d ∧
    Nonempty (barM M L ≃* CatGroup d)

theorem pRank_barM_le_three_of_setting (hS : Setting G) {M L : Subgroup G} (hM : IsTwoLocal M)
    (hLM : L ≤ M) : Open.pRank 3 (barM M L) ≤ 3 := by
  have h1 := pRank_barM_le Nat.prime_three (by norm_num) M L hLM
  have h2 := pRank_mono 3 Nat.prime_three.one_lt hLM
  have h3 := local_pRank_le_evenRank 3 Nat.prime_three (by norm_num) M hM
  rw [hS.rank] at h3
  omega

theorem sp62Omega8Shape_of_blockShape (hU : KFactU62ThreeRank) (hΩ : KFactOmegaMinusThreeRank)
    (hS : Setting G) {M H R L : Subgroup G} (hM : IsTwoLocal M) (hL : Sp62BlockShape M H R L) :
    Sp62Omega8Shape M H R L := by
  have h3 := pRank_barM_le_three_of_setting hS hM hL.1.le
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup] at h3
  rcases hL.2.2.2.2.2 with ⟨d, hd, e, -⟩ | ⟨m, d, hm, hd, e, -⟩
  · exact absurd (hU _ d hd e) (by omega)
  · by_cases hm4 : m = 4
    · subst hm4
      exact ⟨hL, d, hd, e⟩
    · exact absurd (hΩ _ m d (by omega) hd e) (by omega)

@[expose] def D1Sp62Omega8Residue3 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)), D1ComponentConfig3 p P M H R Rbar →
    ∀ K : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf K ⊤ →
      (∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ → L = K) →
      ¬ IsCyclic ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
        Subgroup (H ⧸ primeComplementCore (G := H) p)) →
      (∀ c ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓
          Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)),
        orderOf c = p → c ∈ (Subgroup.center K).map K.subtype) →
      ¬ HasKlingenData p Rbar
        (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) →
      ∀ d : TauCeti.ValidLieTypeIndex, p = 3 → IsSpSixTwoIndex d →
        Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group) →
        ∀ L : Subgroup G, Sp62Omega8Shape M H R L → False

theorem d1Sp62BlockResidue3_of_omega8 (hU : KFactU62ThreeRank) (hΩ : KFactOmegaMinusThreeRank)
    (h : D1Sp62Omega8Residue3 G) : D1Sp62BlockResidue3 G := by
  intro p _ P M H R Rbar hcfg K hK huniq hnc hcent hKD d hp3 hd e L hL
  exact h p P M H R Rbar hcfg K hK huniq hnc hcent hKD d hp3 hd e L
    (sp62Omega8Shape_of_blockShape hU hΩ hcfg.glob hcfg.loc.isCoreMaxLocal.1.1 hL)

end CFSG.LocalAnalysis.RankThreeTheoremC
