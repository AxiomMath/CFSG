module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineSeventeenCaseTwo
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111InnerSliceIndexBase
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1KappaInnerNotQJSites
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3Kappa
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3Main

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding
open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open Hyp111 CFSG.AGLEmbeddingD2

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)} {z : H}
  {L : Subgroup (H ⧸ primeComplementCore (G := H) p)} {E : Subgroup G}

theorem InnerNotQConfig.component_facts (hk : D1CaseTwoKFacts3 G)
    (hC : InnerNotQConfig p P M H R Rbar z L E) :
    IsSimpleGroup L ∧ (∃ a b : L, a * b ≠ b * a) ∧ (∃ x : L, x ≠ 1 ∧ ∃ k : ℕ, x ^ p ^ k = 1) ∧
      IsCaseTwoGroup p L ∧ p ^ 2 ∣ Nat.card L := by
  have hp := hC.cfg.ext.prime
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hKs, hKnab, -⟩ :=
    hC.cfg.red.isSimpleGroup_of_isCyclic hC.cfg.catalog hC.isComponent (hC.cyclic _ hC.isComponent)
  have hiso : IsCaseTwoGroup p L :=
    hC.cfg.red.isCaseTwoGroup_of_not_le3 hC.cfg.catalog hk.out hk.seitzCyc hC.cyclic
      hC.cfg.pRank_rbar_eq_three hC.isComponent hC.not_le
  obtain ⟨T⟩ : Nonempty (Sylow p L) := inferInstance
  have hT := hk.sylow p L hiso T
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp T.isPGroup'
  have hK2 : p ^ 2 ∣ Nat.card L := by
    refine dvd_trans ?_ (Subgroup.card_subgroup_dvd_card (T : Subgroup L))
    rw [hn] at hT ⊢
    refine pow_dvd_pow p ?_
    by_contra hlt
    push Not at hlt
    have := Nat.pow_lt_pow_right hp.one_lt hlt
    omega
  exact ⟨hKs, hKnab, exists_pElem_of_dvd ((dvd_pow_self p two_ne_zero).trans hK2), hiso, hK2⟩

theorem InnerNotQConfig.hyp917Ext (hk : D1CaseTwoKFacts3 G) (h3 : D1CaseThreeNotKlingen3 G)
    (hother : D1CaseThreeKlingenOther3 G) (hkl : KFactKlingenLocal) (hmod : StmtKlingenModel)
    (hC : InnerNotQConfig p P M H R Rbar z L E) (B : Subgroup G) :
    Hyp917Ext p M H B (innerNotQJ p H L) := by
  obtain ⟨hKs, hKnab, hKp, hiso, hK2⟩ := hC.component_facts hk
  have hκ := hC.d1Kappa_eq_card_innerNotQJ hk.out
  rw [hC.innerNotQJ_eq hk.out] at hκ ⊢
  exact hyp917Ext_of_caseTwoGroup h3 hother hk.schreier hkl hmod hk.out hk.seitzCyc hk.inv.toIn
    hC.cfg.glob hC.cfg.loc.sigma hC.cfg.ind hKs hKnab hKp hiso hK2 hC.not_le hκ.le

theorem InnerNotQConfig.false_of_base_ih_ext {H₀ : Subgroup G}
    (hC : InnerNotQConfig p P M H R Rbar z L E) (hCGT : AschbacherLocalCGTBlock)
    (hD2 : D1NoXBlock)
    (hih : ∀ (P' : Sylow p G) (N R' : Subgroup G), D1Extremal p P' M N R' →
      d1Kappa p M H₀ < d1Kappa p M N → False)
    (hk : d1Kappa p M H₀ ≤ d1Kappa p M H) {B : Subgroup G} (hEB : E ≤ B) (hBR : B ≤ R)
    (hidx : Nat.card R = p * Nat.card B)
    (hb3 : Hyp111B3 p H B (innerNotQJ p H L))
    (h93 : Hyp111NineThree p M H (innerNotQJ p H L))
    (h917 : Hyp917Ext p M H B (innerNotQJ p H L))
    (h2 : AGLRankTwoFactorAt p M H B (innerNotQJ p H L))
    (hblock : ∃ Lm : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) Lm ∧ (Lm.subgroupOf M).Normal ∧
      ∀ b ∈ B, ∀ l ∈ Lm, b * l * b⁻¹ * l⁻¹ ∈ pCoreOf 2 M) : False := by
  have hext : D1Extremal p P M H R := hC.cfg.ext
  have he : D1Escape p P M H R := hext.toD1Escape
  have hglob : AGLGlobal G := hC.cfg.glob.toU.toAGLGlobal
  have hBH : B ≤ H := hBR.trans he.le_H
  have hBM : B ≤ M := hBR.trans he.le_M
  have hBQ : IsAGLQ p M B := ⟨hBM, P.isPGroup'.to_le (hBR.trans he.le_P),
    Or.inr ⟨E, hEB, hC.fieldOmega.2.1, hC.fieldOmega.2.2.1, hC.gamma⟩⟩
  have htc : pCoreOf 2 (H ⊓ M) = pCoreOf 2 H := twoCore_inf_eq h93 hb3 hBH hBM he.twoCore_le
  have hOM : (primeComplementCore (G := H) p).map H.subtype ≤ M := by
    rw [map_primeComplementCore_eq]
    exact he.primeCore_le
  have hR3 : Open.pRank p R ≤ 3 :=
    (CFSG.SectionRank.pRank_mono hext.prime.one_lt hext.le_P).trans hC.cfg.pRank_eq_three.le
  obtain ⟨Lm, hLm, hLmn, hcomm⟩ := hblock
  exact false_of_centralizing_base_of_ih_ext ⟨he, hglob, htc⟩ hext hih hk hCGT (hD2 G hglob)
    (fun h => hC.not_le ((le_innerNotQJ p H L).trans h)) hOM h93.factor h93.plusCore_le hLm hLmn
    hBQ hBR hidx hR3 h917 h2 hb3 hcomm

theorem InnerNotQConfig.false_of_base_native (hk : D1CaseTwoKFacts3 G)
    (h3 : D1CaseThreeNotKlingen3 G) (hother : D1CaseThreeKlingenOther3 G)
    (hkl : KFactKlingenLocal) (hmod : StmtKlingenModel)
    (hC : InnerNotQConfig p P M H R Rbar z L E) (hih : D1KappaIH p M H) {B : Subgroup G}
    (hEB : E ≤ B) (hBR : B ≤ R) (hidx : Nat.card R = p * Nat.card B)
    (h2 : AGLRankTwoFactorAt p M H B (innerNotQJ p H L))
    (hblock : ∃ Lm : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) Lm ∧ (Lm.subgroupOf M).Normal ∧
      ∀ b ∈ B, ∀ l ∈ Lm, b * l * b⁻¹ * l⁻¹ ∈ pCoreOf 2 M) : False :=
  hC.false_of_base_ih_ext (H₀ := H) hk.localCGT hk.noXBlock
    (fun P' N R' hN hlt => hih P' M N R' hN hlt) le_rfl hEB hBR hidx
    ((hC.b3 hk.out hk.seitzCyc hk.noTwo).mono hEB)
    (innerNotQNineThree_of_out hk.out p P M H R Rbar z L E hC)
    (hC.hyp917Ext hk h3 hother hkl hmod B) h2 hblock

variable (G) in
@[expose] def InnerNotQRankTwoA : Prop :=
  ∀ (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)) (z : H)
    (L : Subgroup (H ⧸ primeComplementCore (G := H) p)) (E : Subgroup G),
    InnerNotQConfig p P M H R Rbar z L E → D1KappaIH p M H →
    Nat.card R = p * Nat.card (innerNotQBaseA p H R L E) →
    AGLRankTwoFactorAt p M H (innerNotQBaseA p H R L E) (innerNotQJ p H L)

variable (G) in
@[expose] def InnerNotQIndexBigK : Prop :=
  ∀ (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)) (z : H)
    (L : Subgroup (H ⧸ primeComplementCore (G := H) p)) (E : Subgroup G),
    InnerNotQConfig p P M H R Rbar z L E → D1KappaIH p M H →
    Nat.card R ≠ p * Nat.card (innerNotQBaseA p H R L E) → False

theorem d1CaseTwoCentral3InnerNotQK_of_baseA (hk : D1CaseTwoKFacts3 G)
    (h3 : D1CaseThreeNotKlingen3 G) (hother : D1CaseThreeKlingenOther3 G)
    (hkl : KFactKlingenLocal) (hmod : StmtKlingenModel) (h2 : InnerNotQRankTwoA G)
    (hBlock : InnerNotQBlockA G) (hBig : InnerNotQIndexBigK G) :
    D1CaseTwoCentral3InnerNotQK G := by
  intro p P M H R Rbar hcfg hcyc hih z hz hcen hα L hL hLX E hE hΓ
  have hC : InnerNotQConfig p P M H R Rbar z L E := ⟨hcfg, hcyc, hz, hcen, hα, hL, hLX, hE, hΓ⟩
  by_cases hidx : Nat.card R = p * Nat.card (innerNotQBaseA p H R L E)
  · exact hC.false_of_base_native hk h3 hother hkl hmod hih (le_innerNotQBaseA p H R L E)
      (innerNotQBaseA_le hE.1) hidx (h2 p P M H R Rbar z L E hC hih hidx)
      (hBlock p P M H R Rbar z L E hC)
  · exact hBig p P M H R Rbar z L E hC hih hidx

end CFSG.LocalAnalysis.RankThreeTheoremC
