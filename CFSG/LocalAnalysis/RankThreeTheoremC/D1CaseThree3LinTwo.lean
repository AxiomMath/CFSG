module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3Residues
public import CFSG.LocalAnalysis.AGLEmbedding.IIIaResidualDefs
public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCompetitor
public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoJConfig
import CFSG.LocalAnalysis.AGLEmbedding.GapROneBS
import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3JStar
import CFSG.LocalAnalysis.RankThreeTheoremC.D1ConfigU3

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding

variable {G : Type} [Group G] [Finite G]

namespace D1ComponentConfig3

variable {p : ℕ} [Fact p.Prime] {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem d1L2Config3 (hcfg : D1ComponentConfig3 p P M H R Rbar) (hK : IsComponentOf K ⊤)
    (huniq : ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ → L = K)
    (hcent : ∀ c ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓
        Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)),
      orderOf c = p → c ∈ (Subgroup.center K).map K.subtype)
    {n : ℕ} {d : TauCeti.ValidLieTypeIndex} (hd : IsLinTwoIndex p n d)
    (e : Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group))
    (hR1a : ((d1LiftX p H R K ⊔ pCoreOf 2 M).subgroupOf M).Normal) :
    D1L2Config p n P M H R (d1LiftX p H R K) :=
  hcfg.ext.d1L2Config hcfg.glob.toU.toAGLGlobal hcfg.red hK huniq hcent hd e hR1a

theorem d1L2Data3 (hcfg : D1ComponentConfig3 p P M H R Rbar) (hK : IsComponentOf K ⊤)
    (huniq : ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ → L = K)
    (hcent : ∀ c ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓
        Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)),
      orderOf c = p → c ∈ (Subgroup.center K).map K.subtype)
    {n : ℕ} {d : TauCeti.ValidLieTypeIndex} (hd : IsLinTwoIndex p n d)
    (e : Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group)) :
    D1L2Data p n P M H R (d1LiftX p H R K) :=
  hcfg.ext.d1L2Data hcfg.glob.toU.toAGLGlobal
    (fun q hq _ => absurd (four_le_evenRank_of_mem_betaFour hq) (by rw [hcfg.glob.rank]; omega))
    hcfg.rbar hcfg.red hK huniq hcent hd e

end D1ComponentConfig3

theorem stmtL2ConfigOfComponent3 :
    ∀ {p : ℕ} [Fact p.Prime] {P : Sylow p G} {M H R : Subgroup G}
      {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}, D1ComponentConfig3 p P M H R Rbar →
      ∀ {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}, IsComponentOf K ⊤ →
        (∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ → L = K) →
        (∀ c ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓
            Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)),
          orderOf c = p → c ∈ (Subgroup.center K).map K.subtype) →
        ∀ {n : ℕ} {d : TauCeti.ValidLieTypeIndex}, IsLinTwoIndex p n d →
          Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group) →
          ((d1LiftX p H R K ⊔ pCoreOf 2 M).subgroupOf M).Normal →
          D1L2Config p n P M H R (d1LiftX p H R K) := by
  intro p _ P M H R Rbar hcfg K hK huniq hcent n d hd e hR1a
  exact hcfg.d1L2Config3 hK huniq hcent hd e hR1a

@[expose] def StmtL2Data3 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)), D1ComponentConfig3 p P M H R Rbar →
    ∀ K : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf K ⊤ →
      (∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ → L = K) →
      (∀ c ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓
          Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)),
        orderOf c = p → c ∈ (Subgroup.center K).map K.subtype) →
      ∀ (n : ℕ) (d : TauCeti.ValidLieTypeIndex), IsLinTwoIndex p n d →
        Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group) →
        D1L2Data p n P M H R (d1LiftX p H R K)

theorem stmtL2Data3 : StmtL2Data3 G := by
  intro p _ P M H R Rbar hcfg K hK huniq hcent n d hd e
  exact hcfg.d1L2Data3 hK huniq hcent hd e

@[expose] def D1CaseThreeLinTwoResidual3 (G : Type) [Group G] [Finite G] : Prop :=
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
      ∀ d : TauCeti.ValidLieTypeIndex, (∃ n, IsLinTwoIndex p n d) →
        Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group) →
        ¬ ((d1LiftX p H R K ⊔ pCoreOf 2 M).subgroupOf M).Normal → False

theorem d1CaseThreeLinTwoAt3_of
    (hC : StmtCompetitor) (hCGT : AschbacherLocalCGTBlock) (hD2 : D1NoXBlock)
    (hres : D1CaseThreeLinTwoResidual3 G) :
    D1CaseThreeLieAt3 G fun p d => ∃ n, IsLinTwoIndex p n d := by
  have hA := @stmtL2ConfigOfComponent3
  have hB := @stmtToD1JConfig
  intro p _ P M H R Rbar hcfg K hK huniq hnc hcent hKD d ⟨n, hd⟩ e
  by_cases hR1a : ((d1LiftX p H R K ⊔ pCoreOf 2 M).subgroupOf M).Normal
  · exact false_of_competitorsOn (C := fun H' => D1L2Config p n P M H' R (d1LiftX p H R K))
      (fun _ h => hB h) hC (hA hcfg hK huniq hcent hd e hR1a) hCGT hD2
  · exact hres p P M H R Rbar hcfg K hK huniq hnc hcent hKD d ⟨n, hd⟩ e hR1a

@[expose] def D1CaseThreeLinTwoResidualAt3 (G : Type) [Group G] [Finite G] (S : ℕ → Prop) :
    Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)), D1ComponentConfig3 p P M H R Rbar →
    S p → ∀ K : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf K ⊤ →
      (∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ → L = K) →
      ¬ IsCyclic ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
        Subgroup (H ⧸ primeComplementCore (G := H) p)) →
      (∀ c ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓
          Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)),
        orderOf c = p → c ∈ (Subgroup.center K).map K.subtype) →
      ¬ HasKlingenData p Rbar
        (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) →
      ∀ d : TauCeti.ValidLieTypeIndex, (∃ n, IsLinTwoIndex p n d) →
        Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group) →
        ¬ ((d1LiftX p H R K ⊔ pCoreOf 2 M).subgroupOf M).Normal → False

@[expose] def StmtLemmaP3LinTwo3 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)), D1ComponentConfig3 p P M H R Rbar →
    p = 3 → ∀ K : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf K ⊤ →
      (∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ → L = K) →
      ¬ IsCyclic ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
        Subgroup (H ⧸ primeComplementCore (G := H) p)) →
      (∀ c ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓
          Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)),
        orderOf c = p → c ∈ (Subgroup.center K).map K.subtype) →
      ¬ HasKlingenData p Rbar
        (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) →
      ∀ d : TauCeti.ValidLieTypeIndex, (∃ n, IsLinTwoIndex p n d) →
        Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group) →
        ((d1LiftX p H R K ⊔ pCoreOf 2 M).subgroupOf M).Normal

theorem lemmaP3LinTwo3_of (hD : StmtL2Data3 G) (h3 : StmtP3OfData) : StmtLemmaP3LinTwo3 G := by
  intro p _ P M H R Rbar hcfg hp3 K hK huniq _ hcent _ d hd e
  obtain ⟨n, hd⟩ := hd
  exact h3 (hD p P M H R Rbar hcfg K hK huniq hcent n d hd e) hp3

theorem lemmaP3LinTwo3_of_inputs (hD : StmtL2Data3 G) (h84 : Asc81bEightFour)
    (h85 : Asc81bEightFive) (hD2 : D1NoXBlock) (hB3 : StmtBlockThree) (hLB : StmtLemmaB)
    (hT1 : StmtPPDElement) : StmtLemmaP3LinTwo3 G :=
  lemmaP3LinTwo3_of hD (stmtP3OfData_of_inputs h84 h85 hD2 hB3 hLB hT1)

theorem residualAt3_three_of_lemmaP3 (hP3 : StmtLemmaP3LinTwo3 G) :
    D1CaseThreeLinTwoResidualAt3 G (· = 3) := by
  intro p _ P M H R Rbar hcfg hp3 K hK huniq hnc hcent hKD d hd e hR1a
  exact hR1a (hP3 p P M H R Rbar hcfg hp3 K hK huniq hnc hcent hKD d hd e)

@[expose] def GapR1bs3 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)), D1ComponentConfig3 p P M H R Rbar →
    5 ≤ p → ∀ K : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf K ⊤ →
      (∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ → L = K) →
      ¬ IsCyclic ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
        Subgroup (H ⧸ primeComplementCore (G := H) p)) →
      (∀ c ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓
          Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)),
        orderOf c = p → c ∈ (Subgroup.center K).map K.subtype) →
      ¬ HasKlingenData p Rbar
        (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) →
      ∀ d : TauCeti.ValidLieTypeIndex, (∃ n, IsLinTwoIndex p n d) →
        Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group) →
        (∀ Lbar : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), IsComponentOf Lbar ⊤ →
          barM M (d1LiftX p H R K) ≤ Subgroup.centralizer (Lbar : Set _)) →
        (∀ s : ℕ, s.Prime → s ≠ 2 → s ≠ p →
          ¬ barM M (d1LiftX p H R K) ≤ Subgroup.centralizer
            ((CFSG.pCore s (↥M ⧸ CFSG.pCore 2 ↥M) : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) : Set _) →
          p < s) →
        ¬ ((d1LiftX p H R K ⊔ pCoreOf 2 M).subgroupOf M).Normal → False

theorem residualAt3_five_of (hD : StmtL2Data3 G) (h5 : StmtFiveReduce) (hgap : GapR1bs3 G) :
    D1CaseThreeLinTwoResidualAt3 G (5 ≤ ·) := by
  intro p _ P M H R Rbar hcfg hp5 K hK huniq hnc hcent hKD d hd e hR1a
  obtain ⟨n, hdn⟩ := hd
  obtain ⟨hE, hO⟩ := h5 (hD p P M H R Rbar hcfg K hK huniq hcent n d hdn e) hp5
  refine hgap p P M H R Rbar hcfg hp5 K hK huniq hnc hcent hKD d ⟨n, hdn⟩ e hE ?_ hR1a
  intro s hs hs2 hsp hns
  by_contra hle
  exact hns (hO s hs hs2 (lt_of_le_of_ne (not_lt.mp hle) hsp))

theorem d1CaseThreeLinTwoResidual3_of (h3 : D1CaseThreeLinTwoResidualAt3 G (· = 3))
    (h5 : D1CaseThreeLinTwoResidualAt3 G (5 ≤ ·)) : D1CaseThreeLinTwoResidual3 G := by
  intro p _ P M H R Rbar hcfg K hK huniq hnc hcent hKD d hd e hR1a
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := hcfg.red.ne_two
  rcases (show p = 3 ∨ 5 ≤ p by
      have := hp.two_le
      rcases Nat.lt_or_ge p 5 with h | h
      · interval_cases p
        · exact absurd rfl hp2
        · exact Or.inl rfl
        · exact absurd hp (by decide)
      · exact Or.inr h) with h | h
  · exact h3 p P M H R Rbar hcfg h K hK huniq hnc hcent hKD d hd e hR1a
  · exact h5 p P M H R Rbar hcfg h K hK huniq hnc hcent hKD d hd e hR1a

theorem gapR1bs3_of (h84 : Asc81bEightFour) (hD2 : D1NoXBlock) : GapR1bs3 G := by
  intro p _ P M H R Rbar hcfg _ K hK huniq _ hcent _ d hd e hcomp _ hnorm
  obtain ⟨n, hdn⟩ := hd
  have h := stmtL2Data3 (G := G) p P M H R Rbar hcfg K hK huniq hcent n d hdn e
  obtain ⟨s, hs, hs2, hsp, hns⟩ := h.exists_oddCore_not_centralized h84 hD2 hcomp hnorm
  exact h.false_of_oddCore_not_centralized h84 hD2 hs hs2 hsp hns

theorem d1CaseThreeLinTwoResidual3_closed (h84 : Asc81bEightFour) (h85 : Asc81bEightFive)
    (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hK2 : KFactParabolicThree) (hC3 : CitedBlockThreeTransvection)
    (hK5 : KFactBlockThreeAltSeven) (hLB : StmtLemmaB) (hα : KFactThreeOrFiveDvd)
    (hβ : KFactOutElemRank) (hgap : GapR1bs3 G) : D1CaseThreeLinTwoResidual3 G :=
  have hB3 : StmtBlockThree := stmtBlockThree_of h85 h86 h93 hD2 hK2 hC3 hK5
  d1CaseThreeLinTwoResidual3_of
    (residualAt3_three_of_lemmaP3
      (lemmaP3LinTwo3_of_inputs stmtL2Data3 h84 h85 hD2 hB3 hLB stmtPPDElement))
    (residualAt3_five_of stmtL2Data3
      (stmtFiveReduce_of
        (stmtFiveComponents_of
          (stmtROne_of hB3 hLB stmtPPDElement stmtNormalizeBlocks h85 hD2)
          (stmtFiveKComponents_of hα hβ stmtPPDElement stmtComponentRank stmtBarPRankLift))
        (stmtFiveOddCore_of h84 hD2))
      hgap)

theorem d1CaseThreeLinTwoAt3_closed (hβ : KFactBetaRank2) (hP1L : KFactP1ThreeLie)
    (hP1A : KFactP1ThreeAlt) (hP1S : KFactP1ThreeSpor) (hEL : KFactJStarElimLie)
    (hEA : KFactJStarElimAlt) (hES : KFactJStarElimSpor) (hCGT : AschbacherLocalCGTBlock)
    (hD2 : D1NoXBlock) (h84 : Asc81bEightFour) (h85 : Asc81bEightFive) (h86 : Asc81bEightSix)
    (h93 : Asc81bNineThree) (hK2 : KFactParabolicThree) (hC3 : CitedBlockThreeTransvection)
    (hK5 : KFactBlockThreeAltSeven) (hLB : StmtLemmaB) (hα : KFactThreeOrFiveDvd)
    (hβo : KFactOutElemRank) :
    D1CaseThreeLieAt3 G fun p d => ∃ n, IsLinTwoIndex p n d :=
  d1CaseThreeLinTwoAt3_of
    (stmtCompetitor3 hβ hP1L hP1A hP1S hEL hEA hES) hCGT hD2
    (d1CaseThreeLinTwoResidual3_closed h84 h85 h86 h93 hD2 hK2 hC3 hK5 hLB hα hβo
      (gapR1bs3_of h84 hD2))

end CFSG.LocalAnalysis.RankThreeTheoremC
