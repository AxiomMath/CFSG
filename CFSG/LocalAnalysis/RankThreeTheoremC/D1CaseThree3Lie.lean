module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3Residues
public import CFSG.LocalAnalysis.AGLEmbedding.ReeFacts
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoBorel

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbedding (IsLinTwoIndex IsP1ChevTwoIndex IsReeGTwoIndex KFactReeSchur PSL2GF
  card_ne_nine_of_isLinTwoIndex center_eq_bot_of_center_quotient_psl2
  isElemAbelian_sylow_inf_of_psl2GF nonempty_mulEquiv_psl2GF_of_isLinTwoIndex
  normal_of_forall_isComponentOf_eq pRank_top_le_of_psl2GF)

variable {G : Type} [Group G] [Finite G]

@[expose] def KFactReeSylowElemAbelian : Prop :=
  ∀ (L : Type) [Group L] [Finite L] (d : TauCeti.ValidLieTypeIndex), IsReeGTwoIndex 3 d →
    Nonempty (L ≃* (TauCeti.CFSGIndex.lie d).Group) → ∀ U : Sylow 3 L,
    ∃ E : Subgroup L, E ≤ (U : Subgroup L) ∧ IsElemAbelian 3 E ∧
      Nat.card E = 3 ^ (2 * d.1.fieldExponent)

theorem d1CaseThreeRee3_of_kFacts (hschur : KFactReeSchur) (hsyl : KFactReeSylowElemAbelian) :
    D1CaseThreeLieAt3 G IsReeGTwoIndex := by
  intro p _ P M H R Rbar hcfg K hK huniq hnc hcent hKD d hd ⟨e₁⟩
  obtain ⟨hp3, -⟩ := hd.exists_eq
  subst hp3
  have hZ : Subgroup.center K = ⊥ := hschur K d hd hK.2.2 (hcfg.isPGroup_center hK) ⟨e₁⟩
  have eK : K ≃* K ⧸ Subgroup.center K :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
  obtain ⟨T₀, hT₀⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal Rbar
    (CFSG.ComponentClassification.Components.mathlib_subnormal_of_chain hK.2.1
      Subgroup.IsSubnormal.top)
  obtain ⟨E, hET, hE, hEcard⟩ := hsyl K d hd ⟨eK.trans e₁⟩ T₀
  have hER : E.map K.subtype ≤ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) := by
    rintro _ ⟨x, hx, rfl⟩
    exact (hT₀.le ⟨x, hET hx, rfl⟩).1
  have hge : 2 * d.1.fieldExponent ≤
      Open.pRank 3 (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) :=
    le_csSup (pRank_bddAbove 3 Nat.prime_three _) ⟨_, hER, elementary_abelian_map 3 hE _, by
      rw [Subgroup.card_map_of_injective K.subtype_injective, hEcard]⟩
  have h3 := hcfg.pRank_rbar_eq_three
  have := hd.three_le_fieldExponent
  omega

theorem d1CaseThreeLinTwo3_of_three
    (h : D1CaseThreeLieAt3 G fun p d => IsLinTwoIndex p 3 d) :
    D1CaseThreeLieAt3 G fun p d => ∃ n, IsLinTwoIndex p n d := by
  intro p _ P M H R Rbar hcfg K hK huniq hnc hcent hKD d ⟨n, hd⟩ ⟨e₁⟩
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := hcfg.red.ne_two
  have hn1 : 1 ≤ n := by
    obtain ⟨q, -, -, hqn⟩ := hd
    rw [← hqn]
    exact q.exponent_pos
  have : K.Normal := normal_of_forall_isComponentOf_eq hK huniq
  obtain ⟨eP⟩ := nonempty_mulEquiv_psl2GF_of_isLinTwoIndex hd
  have hZ : Subgroup.center K = ⊥ :=
    center_eq_bot_of_center_quotient_psl2 hp2 (by omega) (card_ne_nine_of_isLinTwoIndex hd) hK.2.2
      (hcfg.isPGroup_center hK) (e₁.trans eP)
  have eK : K ≃* PSL2GF p n :=
    (QuotientGroup.quotientBot.symm.trans
      (QuotientGroup.quotientMulEquivOfEq hZ.symm)).trans (e₁.trans eP)
  have hC := hcfg.centralizer_eq_bot hK huniq hcent hZ
  have hrank := pRank_top_le_of_psl2GF hp2 hn1 ⟨eK⟩ hC
  have hle := pRank_mono p hp (le_top : (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ≤ ⊤)
  have h3 := hcfg.pRank_rbar_eq_three
  obtain ⟨hUab, hUcard⟩ := isElemAbelian_sylow_inf_of_psl2GF hn1 eK Rbar
  have hge : n ≤ Open.pRank p ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
      Subgroup (H ⧸ primeComplementCore (G := H) p)) :=
    le_csSup (pRank_bddAbove p hp _) ⟨_, le_rfl, hUab, hUcard⟩
  have hmono := pRank_mono p hp
    (inf_le_left : (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K ≤ Rbar)
  have hn3 : n = 3 := by omega
  subst hn3
  exact h p P M H R Rbar hcfg K hK huniq hnc hcent hKD d hd ⟨e₁⟩

structure D1CaseThreeReeFacts3 : Prop where
  schur : KFactReeSchur
  sylow : KFactReeSylowElemAbelian

structure D1CaseThreeNarrowResidues3 (G : Type) [Group G] [Finite G] : Prop where
  a9 : D1CaseThreeA3pAt3 G (· = 3)
  a15 : D1CaseThreeA3pAt3 G (· = 5)
  a3p : D1CaseThreeA3pAt3 G (7 ≤ ·)
  j3 : D1CaseThreeJ33 G
  linTwo : D1CaseThreeLieAt3 G fun p d => IsLinTwoIndex p 3 d
  chevTwo : D1CaseThreeLieAt3 G IsP1ChevTwoIndex

theorem D1CaseThreeNarrowResidues3.toResidues3 (hk : D1CaseThreeReeFacts3)
    (h : D1CaseThreeNarrowResidues3 G) : D1CaseThreeResidues3 G :=
  { a9 := h.a9, a15 := h.a15, a3p := h.a3p, j3 := h.j3,
    linTwo := d1CaseThreeLinTwo3_of_three h.linTwo,
    ree := d1CaseThreeRee3_of_kFacts hk.schur hk.sylow, chevTwo := h.chevTwo }

theorem D1CaseThreeNarrowResidues3.notKlingen (hk : D1CaseThreeKFacts3)
    (hr : D1CaseThreeReeFacts3) (h : D1CaseThreeNarrowResidues3 G) : D1CaseThreeNotKlingen3 G :=
  (h.toResidues3 hr).notKlingen hk

theorem d1CaseThreeNarrowResidues3_of_residues3 (h : D1CaseThreeResidues3 G) :
    D1CaseThreeNarrowResidues3 G where
  a9 := h.a9
  a15 := h.a15
  a3p := h.a3p
  j3 := h.j3
  linTwo := by
    intro p _ P M H R Rbar hcfg K hK huniq hnc hcent hKD d hd e
    exact h.linTwo p P M H R Rbar hcfg K hK huniq hnc hcent hKD d ⟨3, hd⟩ e
  chevTwo := h.chevTwo

theorem d1CaseThreeNarrowResidues3_of_theoremD1 (hD1 : TheoremD1 G) :
    D1CaseThreeNarrowResidues3 G :=
  d1CaseThreeNarrowResidues3_of_residues3 (d1CaseThreeResidues3_of_theoremD1 hD1)

end CFSG.LocalAnalysis.RankThreeTheoremC
