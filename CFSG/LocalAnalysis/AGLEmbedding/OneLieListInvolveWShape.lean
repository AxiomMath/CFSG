module

public import CFSG.LocalAnalysis.AGLEmbedding.OneLieZZK0Shape
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieListInvolveW
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieZZK0ShapeFacts
public import CFSG.LocalAnalysis.AGLEmbedding.ReeFacts
public import CFSG.LocalAnalysis.AGLEmbedding.UnitaryFacts
import CFSG.LocalAnalysis.AGLEmbedding.OneLieConfig

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.ComponentClassification.OuterAutomorphisms

namespace D1OneLieKZeroData

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} {P' : Sylow p G} {H₁ S : Subgroup G}


theorem center_eq_bot_of_caseThree_of_listInvolveW
    (hc : D1OneLieKZeroData p P M H R Rbar K P' H₁ S)
    (h4 : 4 ≤ evenRank G) (hβ : KFactBeta) (hα : KFactAlphaW) (hP1L : KFactP1ThreeLie)
    (hP1A : KFactP1ThreeAlt) (hKl : KFactKlingenSpFour) (hin : KFactChevTwoInnerGen)
    (hout : KFactChevTwoOuterGen)
    (hOutS : ∀ s : TauCeti.SporadicName, ∀ p : ℕ, p.Prime → p ≠ 2 →
      ¬ p ∣ Nat.card (Outer (TauCeti.CFSGIndex.sporadic s).Group))
    (hSF : SporCaseThreeKFacts) (hLIW : KFactOneLieListInvolveW)
    (hRC : KFactRankOneCoreProper) (hKU1 : KFactUnitarySchur) (hKR1 : KFactReeSchur)
    {Rb₁ : Sylow p (H₁ ⧸ primeComplementCore (G := H₁) p)}
    (hRb₁ : (Rb₁ : Subgroup _) =
      (S.subgroupOf H₁).map (QuotientGroup.mk' (primeComplementCore (G := H₁) p)))
    (hred₁ : ReducedNongeneration p (H₁ ⧸ primeComplementCore (G := H₁) p) Rb₁
      (((H₁ ⊓ M).subgroupOf H₁).map (QuotientGroup.mk' (primeComplementCore (G := H₁) p))))
    (hcat₁ : CatalogSimpleSections (H₁ ⧸ primeComplementCore (G := H₁) p))
    {L : Subgroup (H₁ ⧸ primeComplementCore (G := H₁) p)} (hL : IsComponentOf L ⊤)
    (hLn : L.Normal)
    (hJL : ((nclIn H (d1LiftX p H R K)).subgroupOf H₁).map
      (QuotientGroup.mk' (primeComplementCore (G := H₁) p)) ≤ L)
    (hnc : ¬ IsCyclic ((Rb₁ : Subgroup (H₁ ⧸ primeComplementCore (G := H₁) p)) ⊓ L :
      Subgroup (H₁ ⧸ primeComplementCore (G := H₁) p)))
    (hcent : ∀ c ∈ (Rb₁ : Subgroup (H₁ ⧸ primeComplementCore (G := H₁) p)) ⊓
        Subgroup.centralizer (L : Set (H₁ ⧸ primeComplementCore (G := H₁) p)),
      orderOf c = p → c ∈ (Subgroup.center L).map L.subtype)
    (T₁ : Sylow p L) (hT₁ : (T₁ : Subgroup L).map L.subtype =
      (Rb₁ : Subgroup (H₁ ⧸ primeComplementCore (G := H₁) p)) ⊓ L) :
    Subgroup.center L = ⊥ ∧ GLBCore p 1 (T₁ : Subgroup L) ≠ ⊤ := by
  have hd := hc.data
  have hp := hc.escape.prime
  have hp2 := hc.escape.ne_two
  have : Fact p.Prime := ⟨hp⟩
  have huniq : ∀ L' : Subgroup (H₁ ⧸ primeComplementCore (G := H₁) p), IsComponentOf L' ⊤ →
      L' = L := fun L' hL' => hred₁.eq_of_forall_mem_center hL hL' hcent
  have hZp : IsPGroup p (Subgroup.center L) :=
    isPGroup_center_of_isComponentOf hp hred₁.core_eq_bot hL
  obtain ⟨hKs, hKnab⟩ := hd.isSimpleGroup
  obtain ⟨T, -, hKcat, hTnc, hΓ, -⟩ := hd.exists_kFactHyps
  obtain ⟨Y, φ, hφs, hφk⟩ := hc.exists_hom_center_quotient hL hLn hJL
  have hLs : IsSimpleGroup (L ⧸ Subgroup.center L) := hL.2.2.2
  have hInv := fun hlist =>
    hLIW K hKs hKnab hKcat p hp hp2 T hTnc hΓ hd.big (L ⧸ Subgroup.center L) hLs hlist Y φ hφs
      hφk
  have hrk1 : ∀ d : TauCeti.ValidLieTypeIndex,
      ((∃ n, IsLinTwoIndex p n d) ∨ IsUnitaryIndex p d ∨ IsReeGTwoIndex p d) →
      (L ⧸ Subgroup.center L ≃* (TauCeti.CFSGIndex.lie d).Group) →
      Subgroup.center L = ⊥ ∧ GLBCore p 1 (T₁ : Subgroup L) ≠ ⊤ := by
    intro d hd1 e
    have hZ : Subgroup.center L = ⊥ := by
      rcases hd1 with ⟨n, hn⟩ | hU | hRee
      · obtain ⟨e₂⟩ := nonempty_mulEquiv_psl2GF_of_isLinTwoIndex hn
        have hn0 : n ≠ 0 := by
          obtain ⟨q, -, -, hqn⟩ := hn
          have := q.exponent_pos
          omega
        exact center_eq_bot_of_center_quotient_psl2 hp2 hn0 (card_ne_nine_of_isLinTwoIndex hn)
          hL.2.2 hZp (e.trans e₂)
      · exact hKU1 L p d hU hL.2.2 hZp ⟨e⟩
      · have hp3 : p = 3 := hRee.1
        subst hp3
        exact hKR1 L d hRee hL.2.2 hZp ⟨e⟩
    let e₀ : L ≃* L ⧸ Subgroup.center L :=
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm
    exact ⟨hZ, hRC L p hp hp2 d hd1 ⟨e₀.trans e⟩ T₁⟩
  have hloc : D1Local p P' M :=
    (⟨hd.cfg.loc.sigma, hc.escape.maxTwoLocal_M, hc.escape.weakCore_le⟩ :
      D1LocalU p P' M).toD1Local h4
  rcases hc.escape.caseThree_cases hβ hα (hd.cfg.glob.toD1Global h4) hloc Rb₁ hRb₁ hred₁ hcat₁
      hP1L hP1A hKl hin hout hOutS hSF hL huniq hnc hcent with ⟨d, hd1, ⟨e⟩⟩ |
      ⟨d, hsurv, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨hp3, -, ⟨e⟩⟩
  · exact hrk1 d hd1 e
  · exact (hInv (Or.inl ⟨d, hsurv, ⟨e⟩⟩)).elim
  · exact (hInv (Or.inr (Or.inl ⟨e⟩))).elim
  · exact (hInv (Or.inr (Or.inr ⟨hp3, ⟨e⟩⟩))).elim

theorem exists_comp_of_listInvolveW (hc : D1OneLieKZeroData p P M H R Rbar K P' H₁ S)
    (hT : KFactOneLieTorus) (hSch : KFactCatalogSchreier) (hβ : KFactBeta) (hα : KFactAlphaW)
    (hP1L : KFactP1ThreeLie) (hP1A : KFactP1ThreeAlt) (hKl : KFactKlingenSpFour)
    (hin : KFactChevTwoInnerGen) (hout : KFactChevTwoOuterGen)
    (hOutS : ∀ s : TauCeti.SporadicName, ∀ p : ℕ, p.Prime → p ≠ 2 →
      ¬ p ∣ Nat.card (Outer (TauCeti.CFSGIndex.sporadic s).Group))
    (hSF : SporCaseThreeKFacts) (hLIW : KFactOneLieListInvolveW)
    (hRC : KFactRankOneCoreProper) (hKU1 : KFactUnitarySchur) (hKR1 : KFactReeSchur)
    (hcon : ¬ HasPrimeConstraint (G := H₁) p) :
    ∃ (Rb₁ : Sylow p (H₁ ⧸ primeComplementCore (G := H₁) p))
      (L : Subgroup (H₁ ⧸ primeComplementCore (G := H₁) p)) (T₁ : Sylow p L),
      D1OneLieKZeroComp p P M H R Rbar K P' H₁ S Rb₁ L T₁ :=
  hc.exists_comp_of_shape hT hSch hcon fun _ hRb₁ hred₁ hcat₁ _ hL hLn hJL hnc _ hcent T₁ hT₁ =>
    hc.center_eq_bot_of_caseThree_of_listInvolveW (hc.data.four_le_evenRank hT) hβ hα hP1L hP1A
      hKl hin hout hOutS hSF hLIW hRC hKU1 hKR1 hRb₁ hred₁ hcat₁ hL hLn hJL hnc hcent T₁ hT₁

end D1OneLieKZeroData

end CFSG.AGLEmbedding
