module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3Residues
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3Socle
public import CFSG.LocalAnalysis.AGLEmbedding.Sp62Data
public import CFSG.LocalAnalysis.AGLEmbedding.Sp62MSide
import CFSG.LocalAnalysis.AGLEmbedding.Sp62Closed
import CFSG.LocalAnalysis.RankThreeTheoremC.D1ConfigU3

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding

variable {G : Type} [Group G] [Finite G]

@[expose] def StmtSp62Data3 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ [Fact (Nat.Prime 3)] (P : Sylow 3 G) (M H R : Subgroup G)
    (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)), D1ComponentConfig3 3 P M H R Rbar →
    ∀ K : Subgroup (H ⧸ primeComplementCore (G := H) 3), IsComponentOf K ⊤ →
    (∀ L : Subgroup (H ⧸ primeComplementCore (G := H) 3), IsComponentOf L ⊤ → L = K) →
    (∀ c ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) ⊓
        Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) 3)),
      orderOf c = 3 → c ∈ (Subgroup.center K).map K.subtype) →
    ¬ HasKlingenData 3 Rbar
      (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 3))) →
    ∀ d : TauCeti.ValidLieTypeIndex, IsSpSixTwoIndex d →
    Nonempty (K ⧸ Subgroup.center K ≃* CatGroup d) → ∃ V : Subgroup G, D1Sp62Data P M H R V

theorem stmtSp62Data3_of (hSoc : StmtChevTwoSocle3 G) (hKF : KFactSp62Local) :
    StmtSp62Data3 G := by
  intro _ P M H R Rbar hcfg K hK huniq hcent hKD d hd e
  obtain ⟨hZ, -, ⟨eK⟩, -⟩ := hSoc 3 P M H R Rbar hcfg K hK huniq hcent d (Or.inl ⟨rfl, hd⟩) e
  exact exists_sp62Data_of hKF hcfg.glob.toU.toAGLGlobal hcfg.ext hcfg.rbar hcfg.red hK huniq
    (hcfg.centralizer_eq_bot hK huniq hcent hZ) hKD hd eK

@[expose] def D1Sp62BlockResidue3 (G : Type) [Group G] [Finite G] : Prop :=
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
        ∀ L : Subgroup G, Sp62BlockShape M H R L → False

theorem d1CaseThreeSp62At3_of (hDat : StmtSp62Data3 G) (hM : StmtSp62MSide)
    (hres : D1Sp62BlockResidue3 G) :
    D1CaseThreeLieAt3 G fun p d =>
      p = 3 ∧ ∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 1 ∧ d.1 = .B 3 q := by
  intro p _ P M H R Rbar hcfg K hK huniq hnc hcent hKD d hd e
  obtain ⟨hp3, hd'⟩ := hd
  subst hp3
  obtain ⟨V, hV⟩ := hDat P M H R Rbar hcfg K hK huniq hcent hKD d hd' e
  obtain ⟨L, hL⟩ := hM hV
  exact hres 3 P M H R Rbar hcfg K hK huniq hnc hcent hKD d rfl hd' e L hL

theorem d1CaseThreeSp62At3_closed (hSchur : KFactChevTwoSurvivorSchur) (hKF : KFactSp62Local)
    (h84 : Asc81bEightFour) (h85 : Asc81bEightFive) (h86 : Asc81bEightSix)
    (h93 : Asc81bNineThree) (hD2 : D1NoXBlock) (hB3 : StmtBlockThree)
    (hb : StmtBlockInnerNormalizer) (hLevi : KFactBlockLeviU42)
    (hres : D1Sp62BlockResidue3 G) :
    D1CaseThreeLieAt3 G fun p d =>
      p = 3 ∧ ∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 1 ∧ d.1 = .B 3 q :=
  d1CaseThreeSp62At3_of (stmtSp62Data3_of (stmtChevTwoSocle3_of hSchur) hKF)
    (stmtSp62MSide_of h84 h85 h86 h93 hD2 hB3 hb hLevi) hres

end CFSG.LocalAnalysis.RankThreeTheoremC
