module

public import CFSG.LocalAnalysis.AGLEmbedding.Sp62BlockOmega
public import CFSG.LocalAnalysis.AGLEmbedding.Sp62BlockEscape
public import CFSG.LocalAnalysis.AGLEmbedding.Sp62BlockEscMSide

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def D1Sp62EscResidue : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) [Fact p.Prime] (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)), D1ComponentConfig p P M H R Rbar →
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
        ∀ L : Subgroup G, Sp62BlockShape M H R L →
          blockCentralizer M L ≤ GLBPrimeCore p H →
          (∀ d' : TauCeti.ValidLieTypeIndex, IsOmegaMinusTwoIndex 4 d' →
            IsEmpty (barM M L ≃* CatGroup d')) →
          ∀ x ∈ R, orderOf x = p → ¬ Subgroup.centralizer ({x} : Set G) ⊓ H ≤ M →
            pCoreOf 2 (Subgroup.centralizer ({x} : Set G)) = ⊥ →
            (∃ A : Subgroup G, A ≤ R ⊓ Subgroup.centralizer ({x} : Set G) ∧
              IsElemAbelian p A ∧ Nat.card A = p ^ 3) →
            (∃ E : Subgroup G, E ≤ M ⊓ Subgroup.centralizer ({x} : Set G) ∧
              IsElemAbelian p E ∧ Nat.card E = p ^ 4) →
            (∃ Y : Subgroup G, Y ≤ M ⊓ Subgroup.centralizer ({x} : Set G) ∧ IsPGroup p Y ∧
              p ^ 5 ≤ Nat.card Y ∧ 4 ≤ CFSG.Open.pRank p Y) →
            (∃ (W : Subgroup G) (φ : W →* alternatingGroup (Fin 6)),
              W ≤ Subgroup.centralizer ({x} : Set G) ⊓ H ∧ Function.Surjective φ) →
            False

theorem d1Sp62BlockResidueBig_of_esc (hDat : StmtSp62Data) (hEsc : StmtSp62Escape)
    (h84 : Asc81bEightFour) (h85 : Asc81bEightFive) (h86 : Asc81bEightSix)
    (h93 : Asc81bNineThree) (hD2 : D1NoXBlock) (hB3 : StmtBlockThree)
    (hb : StmtBlockInnerNormalizer) (hLC : KFactBlockLeviU42Cent)
    (hres : D1Sp62EscResidue) : D1Sp62BlockResidueBig := by
  intro G _ _ p _ P M H R Rbar hcfg K hK huniq hnc hcent hKD d hp3 hd e L hL hCL h4
  subst hp3
  obtain ⟨V, hV⟩ := hDat G P M H R Rbar hcfg K hK huniq hcent hKD d hd e
  obtain ⟨x, hxR, hx3, hxH, hA, hW⟩ := hEsc G P M H R Rbar hcfg K hK huniq hcent hKD d hd e
  obtain ⟨⟨E, hEC, hE, hEc⟩, Y, hYC, hY3, hYc⟩ :=
    hV.exists_cent h84 h85 h86 h93 hD2 hB3 hb hLC hL h4 hxR hx3
  obtain ⟨Z, hZC, hZ3, hYZ, hZr⟩ := Sp62Block.exists_large_of_elem hEC hE hEc hYC hY3
  have hZR : Nat.card R < Nat.card Z := by
    rw [hV.card_R]; exact lt_of_lt_of_le (by norm_num) (hYc.trans hYZ)
  have hO := hcfg.ext.twoCore_centralizer_eq_bot hxH hZC hZ3 hZR
    ((by norm_num : 3 ≤ 4).trans hZr)
  exact hres G 3 P M H R Rbar hcfg K hK huniq hnc hcent hKD d rfl hd e L hL hCL h4 x hxR hx3
    hxH hO hA ⟨E, hEC, hE, hEc⟩ ⟨Z, hZC, hZ3, hYc.trans hYZ, hZr⟩ hW

theorem d1Sp62BlockResidue_closed_esc (hSchur : KFactChevTwoSurvivorSchur)
    (hKF : KFactSp62Local) (hKA : KFactOmegaEightMinusAutElemRank) (hKE : KFactSp62Escape)
    (hLC : KFactBlockLeviU42Cent) (h84 : Asc81bEightFour) (h85 : Asc81bEightFive)
    (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock) (hB3 : StmtBlockThree)
    (hb : StmtBlockInnerNormalizer) (hres : D1Sp62EscResidue) : D1Sp62BlockResidue :=
  d1Sp62BlockResidue_closed hSchur hKF h84 hD2 hKA
    (d1Sp62BlockResidueBig_of_esc (stmtSp62Data_of (stmtChevTwoSocle_of hSchur) hKF)
      (stmtSp62Escape_of (stmtChevTwoSocle_of hSchur) hKE) h84 h85 h86 h93 hD2 hB3 hb hLC hres)

end CFSG.AGLEmbedding
