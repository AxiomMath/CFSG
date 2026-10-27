module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111BaseIndexKappa
public import CFSG.LocalAnalysis.RankThreeTheoremC.TwoRest3A6Reduction
import CFSG.LocalAnalysis.RankThreeTheoremC.TwoRest3A6Prop3
import CFSG.GH74.Uniqueness.SU.SU1Basic
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.L28AutThree
import CFSG.LocalAnalysis.AGLEmbedding.BlockFactReductionsIIASix
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3HexRest
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3Main
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3ThreeA6Sylow

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111 CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

theorem Hyp111.factorAt_of_relIndex_le {p : ℕ} {P : Sylow p G} {M H R H₀ B : Subgroup G}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}
    (hih : ∀ (P' : Sylow p G) (N R' : Subgroup G), D1Extremal p P' M N R' →
      d1Kappa p M H₀ < d1Kappa p M N → False)
    (hk : d1Kappa p M H₀ ≤ d1Kappa p M H) (hext : D1Extremal p P M H R)
    (hBQ : IsAGLQ p M B) (hBR : B ≤ R) (hidx : B.relIndex R ≤ p) (hR3 : Open.pRank p R ≤ 3)
    (h917 : Hyp917R p M H B K) (h2 : AGLRankTwoFactorAt p M H B K) :
    AGLCompetitorFactorAt p M H K B := by
  have hp := hext.prime
  have : Fact p.Prime := ⟨hp⟩
  have hmul := Subgroup.relIndex_mul_card (H := B) (K := R)
  rw [inf_of_le_left hBR] at hmul
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hext.isPGroup
  obtain ⟨k, hk', hkc⟩ := (Nat.dvd_prime_pow hp).mp (hn ▸ Dvd.intro _ hmul)
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · interval_cases k
    ·
      rw [hkc, pow_zero, one_mul] at hmul
      have hBReq : B = R := Subgroup.eq_of_le_of_card_ge hBR hmul.ge
      subst hBReq
      exact factorAt_of_kMax (d1KMaxR_of_ih hext (fun N R' hN hlt => hih P N R' hN hlt) hk) h917
    · rw [hkc, pow_one] at hmul
      exact factorAt_base_of_ih hih hk hext hBR hmul.symm
        (fun U hBU hUM hU => normalizer_le_of_isAGLQ hext (isAGLQ_of_le hBQ hBU hUM hU)) hR3
        h917 h2
  · exfalso
    have : p ^ 2 ≤ p := (Nat.pow_le_pow_right hp.pos hk2).trans (hkc ▸ hidx)
    nlinarith [hp.two_le]

@[expose] def TwoRestCentralizingInputsK (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)), D1CaseTwoData3 p P M H R Rbar →
    ∀ z : H, D1CaseTwoCand p M H R z → ¬ D1CzSP p (z : G) → D1CzOutside p (z : G) →
      D1CzB0 p R (z : G) → pCoreOf 2 M ⊓ Subgroup.centralizer ({(z : G)} : Set G) ≠ ⊥ →
      D1CzEven p (z : G) → D1CaseTwoKAxis p P M R (z : G) →
      Subgroup.normalizer (pCoreOf 2 (GLBPrimeCore p
        (Subgroup.centralizer ({(z : G)} : Set G))) : Set G) ≤ H →
      p = 3 →
      ∀ L : Subgroup G, ∀ hL : IsWeakSBlock M (pCoreOf 2 H) L,
        Nat.card (Subgroup.center ↥(barM M L)) = 3 →
        Nonempty (↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃* alternatingGroup (Fin 6)) →
        CenterCentralizesBlockV M (pCoreOf 2 H) L hL.le → ¬ IsShort2 L →
        ∀ hRM : R ≤ M,
          (L.subgroupOf M).Normal ∧
          (∀ a ∈ centBase M R L hRM, a ≠ 1 → a ^ 3 = 1 →
            (∃ E : Subgroup G, E ≤ R ∧ IsElemAbelian 3 E ∧ Nat.card E = 27 ∧ a ∈ E) →
            Subgroup.normalizer (Subgroup.zpowers a : Set G) ≤ M) ∧
          ∃ K : Subgroup (H ⧸ primeComplementCore (G := H) p), ¬ K ≤ d1X0 p M H ∧
            (primeComplementCore (G := H) p).map H.subtype ≤ M ∧
            (∀ x ∈ H, ∃ m ∈ H ⊓ M, ∃ k : H,
              QuotientGroup.mk' (primeComplementCore (G := H) p) k ∈ K ∧ x = m * k) ∧
            Hyp917R p M H (centBase M R L hRM) K ∧
            AGLRankTwoFactorAt p M H (centBase M R L hRM) K ∧ d1PlusCore p H K ≤ M ∧
            ∀ S : Subgroup G, IsPGroup 2 S → S ≤ H →
              centBase M R L hRM ≤ Subgroup.normalizer (S : Set G) → S ≤ d1PlusCore p H K

theorem d1CaseTwoRest3A6Residual_of_inputsK (hk : D1CaseTwoKFacts3 G)
    (hS : KFactBlockThreeASixCubeShort) (hI : TwoRestCentralizingInputsK G) :
    ∀ (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
      (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)), D1CaseTwoData3 p P M H R Rbar →
      ∀ H₀ : Subgroup G, (∀ (P' : Sylow p G) (N R' : Subgroup G), D1Extremal p P' M N R' →
        d1Kappa p M H₀ < d1Kappa p M N → False) → d1Kappa p M H₀ ≤ d1Kappa p M H →
      ∀ z : H, D1CaseTwoCand p M H R z → ¬ D1CzSP p (z : G) → D1CzOutside p (z : G) →
        D1CzB0 p R (z : G) → pCoreOf 2 M ⊓ Subgroup.centralizer ({(z : G)} : Set G) ≠ ⊥ →
        D1CzEven p (z : G) → D1CaseTwoKAxis p P M R (z : G) →
        Subgroup.normalizer (pCoreOf 2 (GLBPrimeCore p
          (Subgroup.centralizer ({(z : G)} : Set G))) : Set G) ≤ H →
        p = 3 → (∃ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L ∧ ∃ ζ ∈ barM M L,
            ζ ∈ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ∧ ζ ^ 3 = 1 ∧
              ζ ≠ 1) →
        ∀ L : Subgroup G, ∀ hL : IsWeakSBlock M (pCoreOf 2 H) L,
          Nat.card (Subgroup.center ↥(barM M L)) = 3 →
          Nonempty (↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃* alternatingGroup (Fin 6)) →
          CenterCentralizesBlockV M (pCoreOf 2 H) L hL.le → False := by
  intro p P M H R Rbar hd H₀ hih hκ z hz hnSP hout hB0 hQ hEv hKax hNH hp3 hW L hL hZ hA6 hc
  have hI' := hI p P M H R Rbar hd z hz hnSP hout hB0 hQ hEv hKax hNH hp3 L hL hZ hA6 hc
  subst hp3
  obtain ⟨h, hzM, hzP, hz3, hCz, hrk, hcyc, hin⟩ := D1CaseTwoData3.nf_inputs hk.out hk.seitzCyc
    hk.caseTwoLocal hk.inv hk.schreier hk.sylow hk.eightFour hk.eightFive hk.eightSix
    hk.nineThree hk.noXBlock hk.toralThree hd hz hnSP hout hB0 hNH
  by_cases hs : IsShort2 L
  · obtain ⟨w, hwR, hwC, hwK, hwo, -, -, -, hΩP, -, -⟩ := hKax
    have hstr := D1CaseTwoData3.rstruct hk.out hk.seitzCyc hk.caseTwoLocal hk.inv hk.schreier
      hk.sylow kFactL28AutThree hd hz hnSP hout hB0 hwR hwC hwK hwo
    refine false_of_threeASix_cubeN h kFactBlockThreeASix_holds hcyc hzM hz3 hCz hin hrk hL hZ
      hA6 (fun a ha haS haL hpow h3 =>
        hS G M (pCoreOf 2 H) L h.isKGroup.1 h.asc81bHyp hL hZ hA6 hs a ha haS haL hpow h3)
      hd.cfg.ext.le_P h.toD1Escape.le_H hwR hwo hΩP ?_
    rcases hstr with hcu | ⟨-, a, haR, ha3w, ha31, -⟩
    · exact Or.inl hcu
    · exact Or.inr ⟨a, haR, ha3w, ha31⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hRP : R ≤ (P : Subgroup G) := h.toD1Escape.le_P
  have hRM : R ≤ M := hRP.trans h.toD1Escape.sylow_le
  obtain ⟨hLn, hG2, K, hKX, hOM, hHfac, h917, h2, hXM, hb3⟩ := hI' hs hRM
  set B := centBase M R L hRM with hBdef
  have hBR : B ≤ R := centBase_le hRM
  have hidx : B.relIndex R ≤ 3 := by
    have e : B.subgroupOf R = (Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))).comap
        ((QuotientGroup.mk' (CFSG.pCore 2 ↥M)).comp
          (Subgroup.inclusion (hRP.trans h.toD1Escape.sylow_le))) :=
      Subgroup.comap_map_eq_self_of_injective R.subtype_injective _
    show (B.subgroupOf R).index ≤ 3
    rw [e]
    exact TwoRest3A6.index_centralizer_barM_le_three h kFactBlockThreeASix_holds
      hk.eightFive hk.eightSix hk.nineThree hk.noXBlock hcyc hzM hz3 hCz hin hrk hL hZ hA6 hc hs
      hRP
  obtain ⟨E, hER, hE, hEcard⟩ := CFSG.GH74.Uniqueness.SU.SU1.exists_isElemAbelian_of_le_pRank
    Nat.prime_three h.toD1Escape.three_le_pRank
  have hrelE : B.relIndex E ≤ 3 := (Subgroup.relIndex_le_of_le_right hER
    (CFSG.GH74.Uniqueness.SU.SU1.relIndex_ne_zero_of_finite B R)).trans hidx
  have hmul := Subgroup.relIndex_mul_card (H := B) (K := E)
  rw [hEcard] at hmul
  obtain ⟨j, hj, hcj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp
    (hEcard ▸ Subgroup.card_dvd_of_le (inf_le_right : B ⊓ E ≤ E))
  have hj2 : 2 ≤ j := by
    by_contra hlt
    interval_cases j <;> rw [hcj] at hmul <;> omega
  obtain ⟨F, hFBE, hF, hFcard⟩ := CFSG.GH74.Uniqueness.SU.SU1.exists_subgroup_card
    Nat.prime_three (CFSG.GH74.Uniqueness.SU.SU1.IsElemAbelian.mono inf_le_right hE) hj2 hcj
  have hFP : F ≤ (P : Subgroup G) := (hFBE.trans inf_le_left).trans (hBR.trans hRP)
  have hEC : E ≤ F ⊔ ((P : Subgroup G) ⊓ Subgroup.centralizer (F : Set G)) := fun x hx =>
    Subgroup.mem_sup_right ⟨hRP (hER hx), Subgroup.mem_centralizer_iff.mpr fun f hf => by
      have := hE.1.is_comm.comm ⟨f, (hFBE hf).2⟩ ⟨x, hx⟩
      exact congrArg Subtype.val this⟩
  have hNF : Subgroup.normalizer (F : Set G) ≤ M := by
    refine le_trans ?_ h.toD1Escape.weakCore_le
    unfold GLBWeakCore rankThreeAschCore
    exact le_sSup ⟨F, hFP, CFSG.SectionRank.le_pRank (by norm_num) le_rfl hF hFcard,
      CFSG.SectionRank.le_pRank (by norm_num) hEC hE hEcard, rfl⟩
  have hΓ : rankThreeGamma 1 3 F ≤ M := TwoRest3A6.rankThreeGamma_le hF hFcard hNF
    fun a ha ha1 =>
      hG2 a (hFBE ha).1 ha1 (hF.2 a ha) ⟨E, hER, hE, by rw [hEcard]; norm_num, (hFBE ha).2⟩
  have hBM : B ≤ M := hBR.trans hRM
  have hBQ : IsAGLQ 3 M B := ⟨hBM, P.isPGroup'.to_le (hBR.trans hRP),
    Or.inr ⟨F, hFBE.trans inf_le_left, hF, hFcard, hΓ⟩⟩
  have hR3 : Open.pRank 3 R ≤ 3 :=
    (CFSG.SectionRank.pRank_mono (by norm_num) hRP).trans hd.cfg.pRank_eq_three.le
  have hfacB := factorAt_of_relIndex_le hih hκ hd.cfg.ext hBQ hBR hidx hR3 h917 h2
  exact false_of_centralizing_base_of_factorAtB h hk.localCGT (hk.noXBlock G h.glob) hKX hOM
    hHfac hfacB hXM hL hLn hBQ.2.1 (hBR.trans h.toD1Escape.le_H) hBM hb3 (centBase_comm hRM hL.le)

end CFSG.LocalAnalysis.RankThreeTheoremC
