module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3Lie
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3Closure
import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3A3p

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.AGLEmbedding (IsChevTwoInnerIndex IsChevTwoOuterIndex IsLinTwoIndex IsP1ChevTwoIndex
  KFactChevTwoOuterGen le_of_weakCore_eq_top false_of_le_of_normal_sup
  false_of_le_of_three_le_pRank mem_map_center_of_mem_of_mem_centralizer
  normal_of_forall_isComponentOf_eq normal_sup_of_outer three_le_pRank_of_weakCore_eq_top)

variable {G : Type} [Group G] [Finite G]

namespace D1ComponentConfig3

variable {p : ℕ} [Fact p.Prime] {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

omit [Fact p.Prime] in
theorem mem_center_of_mem_centralizer (hcfg : D1ComponentConfig3 p P M H R Rbar)
    (hK : IsComponentOf K ⊤)
    (huniq : ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ → L = K)
    (hcent : ∀ c ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓
        Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)),
      orderOf c = p → c ∈ (Subgroup.center K).map K.subtype) :
    ∀ c ∈ Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)), orderOf c = p →
      c ∈ (Subgroup.center K).map K.subtype := fun c hc hcp =>
  mem_map_center_of_mem_of_mem_centralizer (hcfg.mem_of_mem_centralizer hK huniq hcent c hc hcp) hc

theorem false_of_le_weakCore {T : Type*} [Group T] (hcfg : D1ComponentConfig3 p P M H R Rbar)
    (hK : IsComponentOf K ⊤)
    (huniq : ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ → L = K)
    (hcent : ∀ c ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓
        Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)),
      orderOf c = p → c ∈ (Subgroup.center K).map K.subtype)
    (e : K ⧸ Subgroup.center K ≃* T)
    (hOut : ∀ S : Sylow p (Outer T), (S : Subgroup (Outer T)).Normal)
    (hW : K ≤ GLBWeakCore p (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p))) : False := by
  have hKn : K.Normal := normal_of_forall_isComponentOf_eq hK huniq
  have : Group.IsPerfect K := ⟨hK.2.2.1⟩
  have hCR := IsPGroup.le_sylow_of_normal (hcfg.isPGroup_centralizer hK huniq hcent) Rbar
  exact false_of_le_of_normal_sup hcfg.red (hW.trans hcfg.red.weakCore_le)
    (normal_sup_of_outer K e Rbar hCR hOut)

end D1ComponentConfig3

@[expose] def KFactChevTwoInnerRank : Prop :=
  ∀ d : TauCeti.ValidLieTypeIndex, IsChevTwoInnerIndex d →
    ∀ (K : Type) [Group K] [Finite K], Open.IsQuasisimple K →
      Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group) →
      IsPGroup 3 (Subgroup.center K) → IsCyclic (Subgroup.center K) →
      ∀ T : Sylow 3 K, 4 ≤ Open.pRank 3 (T : Subgroup K)

structure D1CaseThreeChevFacts3 : Prop where
  innerRank : KFactChevTwoInnerRank
  outer : KFactChevTwoOuterGen
  g28a15 : D1CaseThreeG28A15Facts

structure D1CaseThreeSurvivors3 (G : Type) [Group G] [Finite G] : Prop where
  sp62 : D1CaseThreeLieAt3 G fun p d =>
    p = 3 ∧ ∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 1 ∧ d.1 = .B 3 q
  sp48 : D1CaseThreeLieAt3 G fun p d =>
    p = 3 ∧ ∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 3 ∧ d.1 = .B 2 q
  reeF4 : D1CaseThreeLieAt3 G fun p d => p = 5 ∧ d.1 = .reeF4 2

theorem D1CaseThreeSurvivors3.chevTwo (hk : D1CaseThreeChevFacts3) (h : D1CaseThreeSurvivors3 G) :
    D1CaseThreeLieAt3 G IsP1ChevTwoIndex := by
  intro p _ P M H R Rbar hcfg K hK huniq hnc hcent hKD d hd e
  have hinner : p = 3 → IsChevTwoInnerIndex d → False := by
    rintro rfl hdi
    obtain ⟨T⟩ : Nonempty (Sylow 3 K) := inferInstance
    have h4 := hk.innerRank d hdi K hK.2.2 e (hcfg.isPGroup_center hK)
      (hcfg.isCyclic_center hK huniq) T
    have h3 := hcfg.pRank_sylow_le_three T
    omega
  have houter : p = 3 → IsChevTwoOuterIndex d → False := by
    rintro rfl hdo
    obtain ⟨e'⟩ := e
    exact hcfg.false_of_le_weakCore hK huniq hcent e' (hk.outer.1 d hdo)
      (hk.outer.2 d hdo _ K (normal_of_forall_isComponentOf_eq hK huniq) hK.2.2 ⟨e'⟩
        (hcfg.isPGroup_centralizer hK huniq hcent)
        (hcfg.mem_center_of_mem_centralizer hK huniq hcent) Rbar hcfg.red.three_le_pRank)
  rcases hd with ⟨hp, q, hq, hq1, h' | h' | h' | h' | h' | h' | h' | h'⟩ |
    ⟨hp, q, hq, hq3, h' | h' | h' | h'⟩ | ⟨hp, h'⟩
  · exact h.sp62 p P M H R Rbar hcfg K hK huniq hnc hcent hKD d ⟨hp, q, hq, hq1, h'⟩ e
  · exact hinner hp ⟨q, hq, hq1, Or.inl h'⟩
  · exact hinner hp ⟨q, hq, hq1, Or.inr (Or.inl h')⟩
  · exact hinner hp ⟨q, hq, hq1, Or.inr (Or.inr (Or.inl h'))⟩
  · exact hinner hp ⟨q, hq, hq1, Or.inr (Or.inr (Or.inr (Or.inl h')))⟩
  · exact hinner hp ⟨q, hq, hq1, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h'))))⟩
  · exact hinner hp ⟨q, hq, hq1, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h'))))⟩
  · exact houter hp (Or.inl ⟨q, hq, hq1, h'⟩)
  · exact h.sp48 p P M H R Rbar hcfg K hK huniq hnc hcent hKD d ⟨hp, q, hq, hq3, h'⟩ e
  · exact hk.g28a15.g28 p P M H R Rbar hcfg K hK huniq hnc hcent hKD d ⟨hp, q, hq, hq3, h'⟩ e
  · exact houter hp (Or.inr ⟨q, hq, hq3, Or.inl h'⟩)
  · exact houter hp (Or.inr ⟨q, hq, hq3, Or.inr h'⟩)
  · exact h.reeF4 p P M H R Rbar hcfg K hK huniq hnc hcent hKD d ⟨hp, h'⟩ e

theorem d1CaseThreeSurvivors3_of_chevTwo (h : D1CaseThreeLieAt3 G IsP1ChevTwoIndex) :
    D1CaseThreeSurvivors3 G where
  sp62 := by
    intro p _ P M H R Rbar hcfg K hK huniq hnc hcent hKD d ⟨hp, q, hq, hq1, hd⟩ e
    exact h p P M H R Rbar hcfg K hK huniq hnc hcent hKD d
      (Or.inl ⟨hp, q, hq, hq1, Or.inl hd⟩) e
  sp48 := by
    intro p _ P M H R Rbar hcfg K hK huniq hnc hcent hKD d ⟨hp, q, hq, hq3, hd⟩ e
    exact h p P M H R Rbar hcfg K hK huniq hnc hcent hKD d
      (Or.inr (Or.inl ⟨hp, q, hq, hq3, Or.inl hd⟩)) e
  reeF4 := by
    intro p _ P M H R Rbar hcfg K hK huniq hnc hcent hKD d ⟨hp, hd⟩ e
    exact h p P M H R Rbar hcfg K hK huniq hnc hcent hKD d (Or.inr (Or.inr ⟨hp, hd⟩)) e

structure D1CaseThreeFineResidues3 (G : Type) [Group G] [Finite G] : Prop where
  a9 : D1CaseThreeA3pAt3 G (· = 3)
  j3 : D1CaseThreeJ33 G
  linTwo : D1CaseThreeLieAt3 G fun p d => IsLinTwoIndex p 3 d
  survivors : D1CaseThreeSurvivors3 G

theorem D1CaseThreeFineResidues3.toNarrow (hc : D1CaseThreeChevFacts3)
    (h : D1CaseThreeFineResidues3 G) : D1CaseThreeNarrowResidues3 G :=
  ⟨h.a9, hc.g28a15.a15, d1CaseThreeA3pSeven3, h.j3, h.linTwo, h.survivors.chevTwo hc⟩

theorem D1CaseThreeFineResidues3.notKlingen (hk : D1CaseThreeKFacts3)
    (hr : D1CaseThreeReeFacts3) (hc : D1CaseThreeChevFacts3) (h : D1CaseThreeFineResidues3 G) :
    D1CaseThreeNotKlingen3 G :=
  (h.toNarrow hc).notKlingen hk hr

theorem d1CaseThreeFineResidues3_of_narrow (h : D1CaseThreeNarrowResidues3 G) :
    D1CaseThreeFineResidues3 G :=
  ⟨h.a9, h.j3, h.linTwo, d1CaseThreeSurvivors3_of_chevTwo h.chevTwo⟩

theorem d1CaseThreeFineResidues3_of_theoremD1 (hD1 : TheoremD1 G) :
    D1CaseThreeFineResidues3 G :=
  d1CaseThreeFineResidues3_of_narrow (d1CaseThreeNarrowResidues3_of_theoremD1 hD1)

end CFSG.LocalAnalysis.RankThreeTheoremC
