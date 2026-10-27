module

public import CFSG.LocalAnalysis.RankFourTheoremC.RelativePair.Signalizer
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.RelativePairGeometry
public import CFSG.LocalAnalysis.RankFourTheoremC.RelativePair.Candidate
public import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2_Facts

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools
  CFSG.LocalAnalysis.RankThreeTheoremC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem ObstructionSetting.not_dvd_card_invariantTwoJoinIn_normalizer (hS : ObstructionSetting G)
    (hD1 : TheoremD1 G) {p : ℕ} (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G}
    {M D R T H V : Subgroup G} (hext : ExtremalObstruction p P M D)
    (hPD : ¬ (P : Subgroup G) ≤ normalizer (D : Set G)) (hR : TransitivityReduction G)
    (h13 : GL83InvariantTwoSylow G) (hopt : IsOptimalRelPair p M D R T H V) {Y : Subgroup G}
    (hYV : Y ≤ V) (hY1 : Y ≠ ⊥) (hY : normalizer (V : Set G) ≤ normalizer (Y : Set G)) :
    ¬ p ∣ Nat.card (invariantTwoJoinIn D (H ⊓ normalizer (Y : Set G))) := by
  classical
  intro hdvd
  have hprime := sigmaA_prime p hp
  have hfact : Fact p.Prime := ⟨hprime⟩
  obtain ⟨hDab, z, hzD, hz1, hzc, hzp, hN₀M, hCD, hglob⟩ :=
    hS.transitivity_data hD1 hp hext hPD hR h13
  obtain ⟨hM, hDP, -, -⟩ := hext.obstruction
  have hPM := hS.sylow_le hp hM
  have hP3 := hS.three_le_pRank p hp P
  have hPN₀ := le_normalizer_zpowers_of_le_centralizer hzc
  have hpair := hopt.pair
  have hVHM : V ≤ H ⊓ M := hpair.maximal.1
  have hV2 : IsPGroup 2 V := hpair.maximal.2.1
  have hDV : D ≤ normalizer (V : Set G) := hpair.maximal.2.2.1
  have hVM : V ≤ M := hVHM.trans inf_le_right
  set X := CFSG.ABGTheoremB.pPrimeCoreIn p M ⊔ CFSG.ABGTheoremB.pPrimeCoreIn p
    (normalizer ((zpowers z : Subgroup G) : Set G)) with hX
  have hXc : p.Coprime (Nat.card X) := coprime_card_pPrimeCoreIn_sup hN₀M
  have hPX : (P : Subgroup G) ≤ normalizer (X : Set G) := le_normalizer_pPrimeCoreIn_sup hPM hPN₀
  have hXM : X ≤ M := sup_le (CFSG.ABGTheoremB.pPrimeCoreIn_le p M)
    ((CFSG.ABGTheoremB.pPrimeCoreIn_le p _).trans hN₀M)
  have hDp : IsPGroup p D := P.isPGroup'.to_le hDP
  have hXall : ∀ A : Subgroup G, A ≤ M → IsPGroup 2 A → D ≤ normalizer (A : Set G) → A ≤ X := by
    intro A hAM hA2 hDA
    obtain ⟨T₁, hAT₁, hT₁⟩ := exists_invariantTwoMaximalWithin_containing D M A hAM hA2 hDA
    exact hAT₁.trans (h13 p hp P M D hext hPD hDab z hzD hz1 hzc hzp T₁ hT₁).le
  obtain ⟨A, hVA, hA⟩ := exists_invariantTwoMaximalWithin_containing D M V hVM hV2 hDV
  have hAS : IsSylowOf 2 A X := h13 p hp P M D hext hPD hDab z hzD hz1 hzc hzp A hA
  obtain ⟨A₀, hA₀S, hPA₀⟩ := exists_isSylowOf_normalized_by_pGroup hprime P.isPGroup' hPX hXc
  obtain ⟨c, hcX, -, hc⟩ := exists_mem_centralizer_conj_eq_of_isSylowOf hprime hDp
    (hDP.trans hPX) hXc hA₀S hAS (hDP.trans hPA₀) hA.2.2.1
  set P' := (P : Subgroup G).map (MulAut.conj c).toMonoidHom with hP'
  have hP'A : P' ≤ normalizer (A : Set G) := by
    rw [hP', ← hc, ← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono hPA₀
  have hP'M : P' ≤ M :=
    (conjugate_subgroup_le_iff_of_conjugator_mem (P : Subgroup G) M c (hXM hcX)).mpr hPM
  have hP'3 : 3 ≤ CFSG.Open.pRank p P' := by
    rw [hP', pRank_map_automorphism p hprime.one_lt]
    exact hP3
  set H' := normalizer (Y : Set G) with hH'
  have hVH' : V ≤ H' := le_normalizer.trans hY
  have hDH' : D ≤ H' := hDV.trans hY
  have hcand : IsRelPairCandidate p D R T H' :=
    ⟨⟨Y, hY1, hV2.to_le hYV, rfl⟩, sup_le (hpair.base_le.trans hVH') hDH',
      hdvd.trans (Subgroup.card_dvd_of_le (invariantTwoJoinIn_mono inf_le_right))⟩
  have hNA2 : IsPGroup 2 (A ⊓ normalizer (V : Set G) : Subgroup G) := hA.2.1.to_inf_left
  have hDNA : D ≤ normalizer ((A ⊓ normalizer (V : Set G) : Subgroup G) : Set G) :=
    common_normalizer_le_normalizer_inf D A _ hA.2.2.1 (hDV.trans le_normalizer)
  have hNAle : (A ⊓ normalizer (V : Set G) : Subgroup G) ≤ H' ⊓ M :=
    le_inf (inf_le_right.trans hY) (inf_le_left.trans hA.1)
  obtain ⟨V', hNAV', hV'⟩ := exists_invariantTwoMaximalWithin_containing D (H' ⊓ M)
    (A ⊓ normalizer (V : Set G)) hNAle hNA2 hDNA
  have hVNA : V ≤ A ⊓ normalizer (V : Set G) := le_inf hVA le_normalizer
  have hpair' : IsRelPairCandidatePair p M D R T H' V' :=
    ⟨hcand, hV', hpair.base_le.trans (hVNA.trans hNAV')⟩
  have hcard := hopt.card_le H' V' hpair'
  have hNAeq : A ⊓ normalizer (V : Set G) = V := by
    refine (Subgroup.eq_of_le_of_card_ge hVNA ?_).symm
    exact (Subgroup.card_le_of_le hNAV').trans hcard
  have hVAeq : V = A := by
    by_contra hne
    exact (pGroup_proper_subgroup_lt_internal_normalizer 2 Nat.prime_two A V hA.2.1
      (lt_of_le_of_ne hVA hne)).ne' hNAeq
  have hP'H : P' ≤ H' ⊓ M := le_inf (by rw [← hVAeq] at hP'A; exact hP'A.trans hY) hP'M
  have hH'M : H' ≤ M := le_of_three_le_pRank_inf hD1 hp hM hcand.twoLocal (by
    have := pRank_mono p hprime.one_lt hP'H
    omega)
  have hjoin : invariantTwoJoinIn D (H ⊓ H') ≤ X :=
    invariantTwoJoinIn_le_of_forall fun B hBH hB2 hDB => hXall B
      (hBH.trans (inf_le_right.trans hH'M)) hB2 hDB
  exact (hprime.coprime_iff_not_dvd.mp hXc) (hdvd.trans (Subgroup.card_dvd_of_le hjoin))

theorem KFactSetting.optimalRelPairFacts {n : ℕ} (hS : KFactSetting n G) (hD1 : TheoremD1 G)
    (hK : KFactLemma212Ge n) {p : ℕ} (hp : p ∈ rankThreeSigmaA G) (hR : TransitivityReduction G)
    (h13 : GL83InvariantTwoSylow G) {P : Sylow p G} {M D R T H V : Subgroup G}
    (hd : MaximalRelativePair p P M D R T) (hopt : IsOptimalRelPair p M D R T H V) :
    OptimalRelPairFacts p M D H V where
  not_constrained := hS.obstruction.not_hasPrimeConstraint hD1 hp hd.ext hd.not_le_normalizer hR
    h13 hopt.pair.cand
  exists_component := by
    have := hS.simple
    exact CFSG.AGLEmbedding.isKProper_not_hasPrimeConstraint_catalog_component hS.kProper H
      (twoLocal_ne_top hS.nonab H hopt.pair.cand.twoLocal) p (sigmaA_prime p hp)
      (hS.obstruction.not_hasPrimeConstraint hD1 hp hd.ext hd.not_le_normalizer hR h13
        hopt.pair.cand)
  pCore_quotient := hS.pCore_quotient_eq_bot hD1 hK hp hd.ext hd.not_le_normalizer hR h13
    hopt.pair.cand
  pRank_eq := hS.obstruction.pRank_eq_two hD1 hp hd.ext hd.not_le_normalizer hR h13
    hopt.pair.cand
  normalizer_pCore := hopt.normalizer_pCoreOf_eq
  sylow := hopt.isSylowOf_pCoreOf (sigmaA_prime p hp) (sigmaA_odd p hp)
    (P.isPGroup'.to_le hd.ext.obstruction.2.1)
  pCore_le := hopt.pCoreOf_le_V hd
  le_M := (hopt.invariantTwoMaximalWithin_H hd).1
  maximal := (hopt.invariantTwoMaximalWithin_H hd).2
  not_dvd := fun _ hYV hY1 hY => hS.obstruction.not_dvd_card_invariantTwoJoinIn_normalizer hD1 hp
    hd.ext hd.not_le_normalizer hR h13 hopt hYV hY1 hY
  signalizer := fun _ hdD hd1 => hS.exists_normal_coprime_signalizer hD1 hK hp hd.ext
    hd.not_le_normalizer hR h13 hdD hd1

end CFSG.LocalAnalysis.RankFourTheoremC
