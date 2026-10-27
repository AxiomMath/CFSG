module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3Sp48
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3Sp48Rank7Bar
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3Sp48Rank7Block
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3Sp48Rank7Rank

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.Quasithin CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding

variable {G : Type} [Group G] [Finite G]

theorem d1Sp48NonsolvResidue3_closed (hSchur : KFactChevTwoSurvivorSchur)
    (hK48 : KFactSp48Local) (hKN : KFactSp48NonsolvLocal) (h84 : Asc81bEightFour)
    (h85 : Asc81bEightFive) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock) (hB3 : StmtBlockThree)
    (hK3c : KFactBlockL28Transvection) (hK3r1 : KFactBlockL28Rank) (hK3r2 : KFactBlockL28TwoRank) :
    D1Sp48NonsolvResidue3 G := by
  intro p _ P M H R Rbar hcfg K hK huniq hnc hcent hKD d hp3 hd e hns
  subst hp3
  obtain ⟨hZ, -, ⟨eK⟩, hsoc⟩ := stmtChevTwoSocle3_of hSchur 3 P M H R Rbar hcfg K hK huniq hcent
    d (Or.inr (Or.inl ⟨rfl, hd⟩)) e
  obtain ⟨hS, -⟩ := stmtSp48Surv_of hK48 hd ⟨eK⟩ hsoc
  have h3 := hS.ph3
  have hC := hcfg.centralizer_eq_bot hK huniq hcent hZ
  obtain ⟨A₀, V₀, hI⟩ := hKN _ K d hd (normal_of_forall_isComponentOf_eq hK huniq) ⟨eK⟩ hC Rbar _
    hcfg.red.three_le_pRank hcfg.red.weakCore_le hcfg.red.ne_top hns
  obtain ⟨L, hL⟩ := h3.exists_weakSBlock h84 hD2
  obtain ⟨V₁, V₂, L₁, L₂, hL₁, hL₂, hH₁, hH₂, hp1, -, hcomm, hc₁, hc₂, hV₁, hV₂, hn₁, hn₂,
    hsep⟩ := exists_localized_factors h3 hL hB3 hI
  have hyps : ∀ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' →
      BlockL28Hyps M (pCoreOf 2 H) L' := fun L' hL' =>
    ⟨h3.isKGroup.1, h3.asc81bHyp, hL', h3.nineThree h93 hL', (h3.nineThree_not_one h85 hD2 hL').1,
      h3.not_isSylowTwoOf_inf h85 hD2 hL'⟩
  have hrank := hcfg.glob.rank
  have hsig := hcfg.loc.sigma
  have hM2 : IsTwoLocal M := hcfg.loc.isCoreMaxLocal.1.1
  by_cases hLeq : L₁ = L₂
  ·
    subst hLeq
    have hsec := hasL28Quot2_of_normal hH₁ hV₁ hV₂ hn₁ hp1 hcomm hc₁ hc₂
    exact false_of_three_le_pRank_barM hrank hsig hM2 hL₁.le
      (hK3r2 G M _ L₁ (hyps L₁ hL₁)
        (nineThreeTwo_of_hasL28Quot hK3c (hyps L₁ hL₁) hsec.hasL28Quot) hsec)
  ·
    obtain ⟨hn₁', hn₂'⟩ := hsep hLeq
    have hE : ∀ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' →
        HasL28Quot (pCoreOf 2 H) L' → ∃ E : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M),
          E ≤ barM M L' ∧ IsElemAbelian 7 E ∧ Nat.card E = 7 ^ 2 ∧
          E ⊓ Subgroup.centralizer (barM M L' : Set (↥M ⧸ CFSG.pCore 2 ↥M)) = ⊥ := by
      intro L' hL' hs
      exact hK3r1 G M _ L' (hyps L' hL') (nineThreeTwo_of_hasL28Quot hK3c (hyps L' hL') hs) hs
    obtain ⟨E₁, hE₁, he₁, hc₁', hz₁⟩ := hE L₁ hL₁ (hasL28Quot_of_normal hH₁ hV₁ hn₁' hc₁)
    obtain ⟨E₂, hE₂, he₂, hc₂', -⟩ := hE L₂ hL₂ (hasL28Quot_of_normal hH₂ hV₂ hn₂' hc₂)
    exact false_of_two_blocks hrank hsig hM2 hL₁.toIsTwoPrimeComponent hL₂.toIsTwoPrimeComponent
      hLeq hE₁ hE₂ he₁ he₂ hc₁' hc₂' hz₁

end CFSG.LocalAnalysis.RankThreeTheoremC
