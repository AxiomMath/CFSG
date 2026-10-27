module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1ConstrainedPhase3Unique
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1BetaVacuous3
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockStructure

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbedding (D1Extremal D1Escape D1PhaseThree Asc81bEightFour D1NoXBlock IsWeakSBlock
  glbPrimeCore_le le_normalizer_glbPrimeCore le_of_le_of_isPGroup_of_not_dvd_index)

variable {G : Type} [Group G] [Finite G]

theorem exists_centralizerInput3_mem {p : ℕ} [Fact p.Prime] {P : Sylow p G} {M H R : Subgroup G}
    (hP : Open.pRank p (P : Subgroup G) = 3) (h : D1Extremal p P M H R)
    (hcon : HasPrimeConstraint (G := H) p) : ∃ z : G, z ∈ R ∧ D1CentralizerInput3 p P M z := by
  obtain ⟨z, D, hDR, hD, hDcard, hzD, -, hDrank, hzp, hzc, huniq, hCM, hcoreM, -⟩ :=
    exists_isolated_vertex3 h hcon
  obtain ⟨E, hER, hEcard, hEexp, hEZ, e, hSL⟩ :=
    h.toD1Escape.exists_sl_two_of_hasPrimeConstraint hcon (hDR hzD)
      (Subgroup.centralizer_le h.le_P hzc) hzp
  exact ⟨z, hDR hzD, h.ne_two, h.sylow_le, h.weakCore_le, hP, hzp, hzc, huniq, hCM, hcoreM,
    ⟨D, hDR.trans h.le_P, hD, hDcard, hzD, hDrank⟩,
    ⟨E, hER.trans h.le_P, hEcard, hEexp, hEZ, e,
      hSL.trans (Subgroup.map_mono (Subgroup.comap_mono inf_le_right))⟩⟩

theorem layer_centralizer_eq_bot (hS : Setting G) {p : ℕ} (hp : p ∈ rankThreeSigmaA G)
    [Fact p.Prime] {P : Sylow p G} {M H R : Subgroup G} (hM : IsCoreMaxLocal p P M)
    (h : D1Extremal p P M H R) {z : G} (hz : D1CentralizerInput3 p P M z)
    (hcompC : D1CentralizerComponentCase3 G) (hcompS : D1SylowComponentCase3 G) :
    CFSG.layer (ReducedCentralizer p z) = ⊥ := by
  by_contra hl
  by_cases hRP : R = (P : Subgroup G)
  · subst hRP
    exact hcompS hS p hp P M hM H h inferInstance z hz hl
  · exact hcompC hS p hp P M hM H R h hRP inferInstance z hz (hz.odd_of_ne_sylow h hRP) hl

theorem _root_.CFSG.AGLEmbedding.D1Extremal.normalizer_le_and_eq_sylow {p : ℕ} [Fact p.Prime]
    {P : Sylow p G} {M H R : Subgroup G} (h : D1Extremal p P M H R)
    (huniq : ∀ K : Subgroup G, GLBIsMaxTwoLocal K → R ≤ K → ¬ K ≤ M → K = H) :
    Subgroup.normalizer (R : Set G) ≤ H ∧ R = (P : Subgroup G) := by
  have hN : Subgroup.normalizer (R : Set G) ≤ H := by
    intro n hn
    have hnM : n ∈ M := h.toD1Escape.normalizer_le hn
    have hHmem : H ∈ twoLocalsOver M R := ⟨h.maxTwoLocal_H, h.le_H, h.not_le⟩
    have hK := map_conj_mem_twoLocalsOver hHmem hnM hn
    have heq := huniq _ hK.1 hK.2.1 hK.2.2
    have hnH : n ∈ Subgroup.normalizer (H : Set G) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq
    have := normalizer_localGroup_le_normalizer_pCoreOf 2 H hnH
    rwa [h.toD1Escape.normalizer_twoCore_H] at this
  refine ⟨hN, ?_⟩
  by_contra hne
  have hlt : R < (P : Subgroup G) := lt_of_le_of_ne h.le_P hne
  obtain ⟨x, hxP, hxN, hxR⟩ := exists_mem_normalizer_not_mem_of_lt P.isPGroup' hlt
  have hXP : R ⊔ Subgroup.zpowers x ≤ (P : Subgroup G) :=
    sup_le h.le_P (Subgroup.zpowers_le.mpr hxP)
  have hXH : R ⊔ Subgroup.zpowers x ≤ H :=
    sup_le h.le_H (Subgroup.zpowers_le.mpr (hN hxN))
  have := le_of_le_of_isPGroup_of_not_dvd_index le_sup_left hXH (P.isPGroup'.to_le hXP)
    h.toD1Escape.not_dvd_index_R
  exact hxR (this (Subgroup.mem_sup_right (Subgroup.mem_zpowers x)))

theorem _root_.CFSG.AGLEmbedding.D1Extremal.normalizer_le_of_char {p : ℕ} [Fact p.Prime]
    {P : Sylow p G} {M H R : Subgroup G} (h : D1Extremal p P M H R)
    (huniq : ∀ K : Subgroup G, GLBIsMaxTwoLocal K → R ≤ K → ¬ K ≤ M → K = H) {T : Subgroup G}
    (hTN : T ≤ GLBPrimeCore p H) (hT2 : IsPGroup 2 T)
    (hTidx : ¬ 2 ∣ (T.subgroupOf (GLBPrimeCore p H)).index)
    (hRT : R ≤ Subgroup.normalizer (T : Set G)) {C : Subgroup G} (hCT : C ≤ T) (hC : C ≠ ⊥)
    (hchar : (C.subgroupOf T).Characteristic) : Subgroup.normalizer (C : Set G) ≤ H := by
  have hTC : Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (C : Set G) := by
    have h1 := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (H := T) (C.subgroupOf T)
    rwa [Subgroup.map_subgroupOf_eq_of_le hCT] at h1
  have hNM : ¬ Subgroup.normalizer (C : Set G) ≤ M := by
    intro hle
    apply h.not_le
    intro x hx
    obtain ⟨n, hn, m, hmH, hmN, rfl⟩ := mem_primeCore_mul_normalizer hTN hT2 hTidx hx
    exact M.mul_mem (h.toD1Escape.primeCore_le hn) (hle (hTC hmN))
  obtain ⟨K, hK, hKmax⟩ := exists_maximal_twoLocal
    (⟨C, hC, hT2.to_le hCT, rfl⟩ : IsTwoLocal (Subgroup.normalizer (C : Set G)))
  have hKM : ¬ K ≤ M := fun hle => hNM (hK.trans hle)
  have hRK : R ≤ K := hRT.trans (hTC.trans hK)
  exact huniq K hKmax hRK hKM ▸ hK

@[expose] def D1ConstrainedCaseInd3 (G : Type) [Group G] [Finite G] : Prop :=
  Setting G → ∀ p ∈ rankThreeSigmaA G, (∀ q ∈ rankThreeSigmaA G, q < p → D1At3 G q) →
    ∀ (P : Sylow p G) (M : Subgroup G), IsCoreMaxLocal p P M → ∀ H R : Subgroup G,
      D1Extremal p P M H R → HasPrimeConstraint (G := H) p → False

theorem d1ExtremalCase3_of_cases_ind' (hcon : D1ConstrainedCaseInd3 G)
    (hcomp : D1ComponentCaseInd3 G) : D1ExtremalCase3 G := by
  refine d1ExtremalCase3_iff_forall_extremalAt3.mpr fun hS => ?_
  intro p
  induction p using Nat.strong_induction_on with
  | _ p ih =>
    intro hp P M hM H R hext
    have hind : ∀ q ∈ rankThreeSigmaA G, q < p → D1At3 G q := fun q hq hqp =>
      d1At3_of_extremalAt3 hq (ih q hqp hq)
    by_cases hc : HasPrimeConstraint (G := H) p
    · exact hcon hS p hp hind P M hM H R hext hc
    · exact hcomp hS p hp hind P M hM H R hext hc

@[expose] def D1ConstrainedWeakBlockResidue3 (G : Type) [Group G] [Finite G] : Prop :=
  Setting G → ∀ p ∈ rankThreeSigmaA G, ∀ (P : Sylow p G) (M : Subgroup G),
    IsCoreMaxLocal p P M → ∀ H : Subgroup G, D1Extremal p P M H (P : Subgroup G) →
      ∀ (_ : Fact p.Prime) (z : G), D1CentralizerInput3 p P M z →
      CFSG.layer (Subgroup.centralizer ({z} : Set G) ⧸
        primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p) = ⊥ →
      ∀ (Pbar : Sylow p (ReducedCentralizer p z)) (zbar : ReducedCentralizer p z)
        (E C : Subgroup (ReducedCentralizer p z)) (_ : E.Normal)
        (e : E ⧸ Subgroup.center E ≃* Multiplicative (Fin 2 → ZMod p)),
        D1ConstrainedReducedData3 p P M z Pbar zbar →
        ReducedStructure3 p Pbar (reducedMeet p M z) zbar E C e →
      HasPrimeConstraint (G := H) p → D1PhaseThree p P M H (P : Subgroup G) →
      z ∈ (P : Subgroup G) → Subgroup.centralizer ({z} : Set G) ≤ H →
      (∀ K : Subgroup G, GLBIsMaxTwoLocal K → (P : Subgroup G) ≤ K → ¬ K ≤ M → K = H) →
      Subgroup.normalizer ((P : Subgroup G) : Set G) ≤ H →
      ∀ T : Subgroup G, T ≤ GLBPrimeCore p H → IsPGroup 2 T →
        ¬ 2 ∣ (T.subgroupOf (GLBPrimeCore p H)).index →
        (P : Subgroup G) ≤ Subgroup.normalizer (T : Set G) → pCoreOf 2 H ≤ T →
        (∀ U : Subgroup G, U ≤ T → U ≠ ⊥ → (U.subgroupOf T).Characteristic →
          Subgroup.normalizer (U : Set G) ≤ H) →
        ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L → False

theorem d1ConstrainedCaseInd3_of_phase3 (hK3 : KFactsA3 G) (hnone : D1ComponentAlphaNone3 G)
    (hcomp : D1ComponentCaseInd3 G) (h84 : Asc81bEightFour) (hD2 : D1NoXBlock)
    (hres : D1ConstrainedWeakBlockResidue3 G) : D1ConstrainedCaseInd3 G := by
  intro hS p hp hind P M hM H R h hcon
  have : Fact p.Prime := ⟨sigmaA_prime p hp⟩
  have hcompC : D1CentralizerComponentCase3 G :=
    d1CentralizerComponentCase3_of_cases hK3 d1CentralizerBetaSmallCase3 hnone.centralizer
  have hcompS : D1SylowComponentCase3 G :=
    d1SylowComponentCase3_of_cases hK3 d1SylowBetaSmallCase3 hnone.sylow
  have hall : ∀ K : Subgroup G, GLBIsMaxTwoLocal K → R ≤ K → ¬ K ≤ M →
      HasPrimeConstraint (G := K) p := by
    intro K hK hRK hKM
    by_contra hnot
    exact hcomp hS p hp hind P M hM K R (h.of_maxTwoLocal_ge hK hRK hKM) hnot
  obtain ⟨z, hzR, hz⟩ := exists_centralizerInput3_mem (sylow_le_of_isCoreMaxLocal hS hp hM).2 h hcon
  have hlayer := layer_centralizer_eq_bot hS hp hM h hz hcompC hcompS
  have huniq : ∀ K : Subgroup G, GLBIsMaxTwoLocal K → R ≤ K → ¬ K ≤ M → K = H :=
    fun K hK hRK hKM => hz.eq_of_maxTwoLocal_ge hS hlayer hzR h hall hK hRK hKM
  obtain ⟨hNH, hRP⟩ := h.normalizer_le_and_eq_sylow huniq
  subst hRP
  have hph := h.toPhaseThree3 hS hcon
  obtain ⟨T, hTN, hT2, hTidx, hPT, hST⟩ := h.exists_invariantSylowTwo hS hcon
  obtain ⟨L, hL⟩ := hph.exists_weakSBlock h84 hD2
  obtain ⟨Pbar, zbar, E, C, hEn, e, hdata, hstr⟩ :=
    hz.exists_reducedStructure3 hS.simple hS.nonab hS.kProper hlayer
  exact hres hS p hp P M hM H h inferInstance z hz hlayer Pbar zbar E C hEn e hdata hstr hcon hph
    hzR (hz.centralizer_le_of_eq_sylow hS hlayer h hcon hzR) huniq hNH T hTN hT2 hTidx hPT hST
    (fun U hUT hU hchar => h.normalizer_le_of_char huniq hTN hT2 hTidx hPT hUT hU hchar) L hL

theorem d1ConstrainedWeakBlockResidue3_of_theoremD1 (hD1 : TheoremD1 G) :
    D1ConstrainedWeakBlockResidue3 G := by
  intro hS p hp P M hM H h
  intros
  exact false_of_extremal_of_theoremD1 hD1 hS hp hM h

end CFSG.LocalAnalysis.RankThreeTheoremC
