module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.Local.SupportedPlaneSylowNormalizer
import CFSG.FeitThompson.Local.ExceptionalInvariantSylowSeparation
import CFSG.FeitThompson.Local.SigmaCoreNontrivial
import CFSG.FeitThompson.Local.SigmaComplementPrimeData
import CFSG.FeitThompson.Local.GlobalMaximalPlaneGeometry
import CFSG.FeitThompson.Local.OutsideSigmaPlaneGloballyMaximal
import CFSG.FeitThompson.Local.HighRankAbelianUniquenessCentralizers
import CFSG.FeitThompson.Local.LowRankFittingDerivedNilpotent
import CFSG.FeitThompson.Local.AlphaCoreNormalHall
import CFSG.FeitThompson.Local.AbelianSylowNormalPrimeCentralizerFitting
import CFSG.FeitThompson.Local.CompetingMaximalFittingPrimeSupport
import CFSG.FeitThompson.Local.PrimeFreeFactorizationFixedSubgroupTransport
import CFSG.FeitThompson.Local.CyclicCentralizerFactorRestriction
import CFSG.FeitThompson.Local.FixedMaximalElementaryAbelianTrivialAction
import CFSG.FeitThompson.OddOrder.SharedSylowNormalizedByIntersection
import CFSG.FeitThompson.OddOrder.NontrivialPSubgroupProper
import CFSG.FeitThompson.OddOrder.SigmaSylowIsAmbientSylow
import CFSG.FeitThompson.Local.AlphaPrimesInSigmaPrimes
public import CFSG.FeitThompson.Representations.AlgebraicIntegersRing
public import CFSG.FeitThompson.Representations.NormalInducedSupportBasis
public import CFSG.FeitThompson.Representations.SchurLemmaIntertwiningMaps
import CFSG.FeitThompson.Foundations.NilpotentSubgroupNilpotent

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open CFSG.FeitThompson CFSG.FeitThompson Subgroup

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

universe u

theorem exists_injective_zmodAddHom_of_dvd {r p : ℕ} (hp : p ≠ 0) (hrp : r ∣ p) :
    ∃ ψ : ZMod r →+ ZMod p, Function.Injective ψ := by
  set a : ZMod p := ((p / r : ℕ) : ZMod p) with ha
  have hdvd : (p / r) ∣ p := Nat.div_dvd_of_dvd hrp
  have horder : addOrderOf a = r := by
    rw [ha, ZMod.addOrderOf_coe _ hp, Nat.gcd_eq_right hdvd, Nat.div_div_self hrp hp]
  have hzero : (zmultiplesHom (ZMod p) a) (r : ℤ) = 0 := by
    simp only [zmultiplesHom_apply]
    rw [← addOrderOf_dvd_iff_zsmul_eq_zero, horder]
  refine ⟨ZMod.lift r ⟨zmultiplesHom (ZMod p) a, hzero⟩, ?_⟩
  rw [ZMod.lift_injective]
  intro m hm
  simp only [zmultiplesHom_apply] at hm
  rw [← addOrderOf_dvd_iff_zsmul_eq_zero, horder] at hm
  rwa [ZMod.intCast_zmod_eq_zero_iff_dvd]

theorem exists_injective_piMultiplicativeHom_of_dvd {r p : ℕ} (d : ℕ) (hp : p ≠ 0) (hrp : r ∣ p) :
    ∃ ι : (Fin d → Multiplicative (ZMod r)) →* (Fin d → Multiplicative (ZMod p)),
      Function.Injective ι := by
  obtain ⟨ψ, hψ⟩ := exists_injective_zmodAddHom_of_dvd hp hrp
  refine ⟨(AddMonoidHom.toMultiplicative ψ).compLeft (Fin d), ?_⟩
  intro x y hxy
  funext i
  have h := congrFun hxy i
  simp only [MonoidHom.compLeft_apply] at h
  exact Multiplicative.ofAdd.injective (congrArg Multiplicative.ofAdd
    (hψ (Multiplicative.ofAdd.injective h)))

theorem elementaryAbelianRanks_subset_of_dvd {X : Type*} [Group X] {r p d : ℕ} (hp : p ≠ 0)
    (hrp : r ∣ p) (hd : d ∈ elementaryAbelianRanks p X) : d ∈ elementaryAbelianRanks r X := by
  rw [mem_elementaryAbelianRanks] at hd ⊢
  obtain ⟨H, ⟨f⟩⟩ := hd
  obtain ⟨ι, hι⟩ := exists_injective_piMultiplicativeHom_of_dvd d hp hrp
  have hjinj : Function.Injective (H.subtype.comp (f.symm.toMonoidHom.comp ι)) :=
    H.subtype_injective.comp (f.symm.injective.comp hι)
  exact ⟨_, ⟨(MonoidHom.ofInjective hjinj).symm⟩⟩

theorem elementaryAbelianRanks_eq_setOf (p : ℕ) (X : Type*) [Group X] :
    elementaryAbelianRanks p X =
      {d | ∃ H : Subgroup X, Nonempty (H ≃* (Fin d → Multiplicative (ZMod p)))} := by
  ext d; exact mem_elementaryAbelianRanks

theorem elementaryAbelianPRank_zero {X : Type*} [Group X] [Finite X] :
    elementaryAbelianPRank 0 X = 0 := by
  refine Nat.le_antisymm (elementaryAbelianPRank_le fun d hd => ?_) (Nat.zero_le _)
  rw [mem_elementaryAbelianRanks] at hd
  obtain ⟨H, ⟨f⟩⟩ := hd
  by_contra hd1
  have : Finite (Fin d → Multiplicative (ZMod 0)) := Finite.of_equiv _ f.toEquiv
  have : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  have : Infinite (Fin d → Multiplicative (ZMod 0)) := inferInstance
  exact not_finite (Fin d → Multiplicative (ZMod 0))

theorem elementaryAbelianPRank_one {X : Type*} [Group X] : elementaryAbelianPRank 1 X = 0 := by
  have hnb : ¬ BddAbove (elementaryAbelianRanks 1 X) := by
    rintro ⟨n, hn⟩
    have hmem : n + 1 ∈ elementaryAbelianRanks 1 X := by
      rw [mem_elementaryAbelianRanks]; exact ⟨⊥, ⟨MulEquiv.ofUnique⟩⟩
    exact absurd (hn hmem) (by omega)
  rw [elementaryAbelianPRank_eq_sSup, ← elementaryAbelianRanks_eq_setOf,
    Nat.sSup_of_not_bddAbove hnb]

theorem elementaryAbelianPRank_le_of_forall_prime {X : Type*} [Group X] [Finite X] {n : ℕ}
    (h : ∀ r : ℕ, r.Prime → elementaryAbelianPRank r X ≤ n) (p : ℕ) :
    elementaryAbelianPRank p X ≤ n := by
  rcases Nat.lt_or_ge p 2 with hp2 | hp2
  · interval_cases p
    · rw [elementaryAbelianPRank_zero]; exact Nat.zero_le n
    · rw [elementaryAbelianPRank_one]; exact Nat.zero_le n
  · have hr : p.minFac.Prime := Nat.minFac_prime (by omega)
    refine le_trans (elementaryAbelianPRank_le fun d hd => ?_) (h _ hr)
    exact le_elementaryAbelianPRank hr.one_lt
      (elementaryAbelianRanks_subset_of_dvd (by omega) (Nat.minFac_dvd p) hd)

theorem natCard_eq_pow_factorization_of_le {G : Type u} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) {P N : Subgroup G} (hPN : P ≤ N)
    (hP : Nat.card ↥P = p ^ (Nat.card G).factorization p) :
    Nat.card ↥P = p ^ (Nat.card ↥N).factorization p := by
  have h1 : (Nat.card ↥P).factorization p = (Nat.card G).factorization p := by
    rw [hP, Nat.Prime.factorization_pow hp]; simp
  have h2 : (Nat.card ↥P).factorization p ≤ (Nat.card ↥N).factorization p :=
    (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').2
      (Subgroup.card_dvd_of_le hPN) p
  have h3 : (Nat.card ↥N).factorization p ≤ (Nat.card G).factorization p :=
    (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').2
      N.card_subgroup_dvd_card p
  rw [hP]; congr 1; omega

theorem elementaryAbelianPRank_inf_centralizer_sigmaCore_le_one_of_prime
    (h₁ : Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : Statements.FPL_global_sylow_normalizer_derived.{u})
    (h₃ : Statements.FTS_proper_subgroup_p_length_one.{u})
    {G : Type u} [Group G] [Finite G] (hG : Prep08.IsMinimalSimpleOddOrder G)
    {M K : Subgroup G} (hM : IsCoatom M) (hKM : K ≤ M)
    (hK : ∀ r : ℕ, r.Prime → r ∣ Nat.card ↥K → r ∉ sigmaPrimes M)
    {p : ℕ} (hp : p.Prime) :
    elementaryAbelianPRank p ↥(K ⊓ centralizer ((sigmaCore M : Subgroup G) : Set G)) ≤ 1 := by
  classical
  have := hG.isSimpleGroup
  have hna := hG.not_isMulCommutative
  have hodd := hG.odd_natCard
  have hsolv := hG.isSolvable_of_ne_top
  have hfin : Fintype G := Fintype.ofFinite G
  have hpf := Fact.mk hp
  have hMin2 : IsOddOrderMinimalSimple G := ⟨hodd, hG.isSimpleGroup, hna, hsolv⟩
  have hMin9 : Prep09.IsMinimalSimpleOddOrder G := ⟨hodd, hG.isSimpleGroup, hna, hsolv⟩
  obtain ⟨hHallM, hHallG, hSM'⟩ := h₁ G hMin2 M hM
  by_contra hcon
  have h2 : 2 ≤ elementaryAbelianPRank p ↥(K ⊓ centralizer ((sigmaCore M : Subgroup G) : Set G)) :=
    by omega
  obtain ⟨A, hAC, hAeq⟩ := exists_le_nonempty_mulEquiv_of_le_elementaryAbelianPRank hp h2
  have hAea : IsElementaryAbelian p A :=
    isElementaryAbelian_of_nonempty_mulEquiv_multiplicative_pi hAeq
  have hAcard : Nat.card ↥A = p ^ 2 := by
    obtain ⟨f⟩ := (nonempty_mulEquiv_multiplicative_pi_iff A).1 hAeq
    exact (isElementaryAbelianSubgroup_of_mulEquiv f).2
  have hAK : A ≤ K := hAC.trans inf_le_left
  have hAM : A ≤ M := hAK.trans hKM
  have hACS : A ≤ centralizer ((sigmaCore M : Subgroup G) : Set G) := hAC.trans inf_le_right
  have hpdvdA : p ∣ Nat.card ↥A := by rw [hAcard]; exact dvd_pow_self p two_ne_zero
  have hpσ : p ∉ sigmaPrimes M :=
    hK p hp (hpdvdA.trans (Subgroup.card_dvd_of_le hAK))
  have hSCA : sigmaCore M ≤ centralizer (A : Set G) := le_centralizer_iff.mp hACS
  have hZ : ∀ q : ℕ, q.Prime → elementaryAbelianPRank q ↥(centralizer (A : Set G)) ≤ 2 :=
    fun q hq => elementaryAbelianPRank_centralizer_le_two_of_plane_of_notMem_sigmaPrimes hp hq hna
      hodd hsolv hM hAM hpσ hAea hAcard
  have hAmax : Prep09.IsMaximalElementaryAbelianPlane p A := by
    refine ⟨?_, hAcard⟩
    rw [maximal_isElementaryAbelianSubgroup_iff,
      ← CFSG.FeitThompson.maximal_isElementaryAbelian_iff]
    exact maximal_isElementaryAbelian_of_plane_of_notMem_sigmaPrimes hp hna hodd hsolv hM hAM hpσ
      hAea hAcard
  have hBZ : (alphaCore ↥M).map M.subtype ≤ centralizer (A : Set G) :=
    (map_subtype_alphaCore_le_sigmaCore hna hodd hsolv hM).trans hSCA
  have hrankM : ∀ r : ℕ, r.Prime → elementaryAbelianPRank r ↥M ≤ 2 := by
    intro r hr
    by_contra h3
    have hrα : r ∈ alphaPrimes ↥M := mem_alphaPrimes.2 ⟨hr, by omega⟩
    have hHallA : IsHallPiSubgroup (alphaPrimes ↥M) (alphaCore ↥M) :=
      (isHallSubgroup_alphaCore hna hodd hsolv hM).isHallPiSubgroup
    have hfac : (Nat.card ↥(alphaCore ↥M)).factorization r = (Nat.card ↥M).factorization r := by
      simpa using factorization_natCard_eq_of_isHallPiSubgroup hr hHallA hrα
    have hrankimg : elementaryAbelianPRank r ↥((alphaCore ↥M).map M.subtype)
        = elementaryAbelianPRank r ↥(alphaCore ↥M) :=
      elementaryAbelianPRank_eq_of_mulEquiv hr.one_lt
        (Subgroup.equivMapOfInjective _ M.subtype M.subtype_injective).symm
    have key : elementaryAbelianPRank r ↥(alphaCore ↥M) = elementaryAbelianPRank r ↥M := by
      have h := elementaryAbelianPRank_eq_of_le_of_factorization_eq
        (G := ↥M) hr (K := alphaCore ↥M) (M := ⊤) le_top (by simpa using hfac)
      rw [h]; exact elementaryAbelianPRank_eq_of_mulEquiv hr.one_lt Subgroup.topEquiv
    have hle := elementaryAbelianPRank_le_of_le (X := G) hr.one_lt hBZ
    rw [hrankimg, key] at hle
    have := hZ r hr
    omega
  have hnil : Group.IsNilpotent ↥(⁅M, M⁆ : Subgroup G) := by
    have : Group.IsSolvable ↥M := hsolv M hM.1
    have hoddM : Odd (Nat.card ↥M) := hodd.of_dvd_nat M.card_subgroup_dvd_card
    have hrankF : ∀ r : ℕ, r.Prime → elementaryAbelianPRank r ↥(fittingRaw ↥M) ≤ 2 := fun r hr =>
      le_trans (elementaryAbelianPRank_subgroup_le hr.one_lt _) (hrankM r hr)
    have himg : (⁅M, M⁆ : Subgroup G) ≤ (fittingRaw ↥M).map M.subtype := by
      rw [← Prep06.map_subtype_derivedOf M, Prep06.derivedOf_eq]
      exact Subgroup.map_mono (commutator_le_fittingRaw hoddM hrankF)
    exact isNilpotent_of_le_of_isNilpotent himg (isNilpotent_map_fittingRaw M)
  obtain ⟨q, hqσ⟩ := sigmaPrimes_nonempty hMin2 hM
  have hq : q.Prime := prime_of_mem_sigmaPrimes hqσ
  have hqf := Fact.mk hq
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow q ↥(sigmaCore M)))
  set Q : Subgroup G := (S : Subgroup ↥(sigmaCore M)).map (sigmaCore M).subtype with hQdef
  have hQS : Q ≤ sigmaCore M := Subgroup.map_subtype_le _
  have hQcard : Nat.card ↥Q = q ^ (Nat.card G).factorization q := by
    rw [hQdef, Subgroup.card_subtype, S.card_eq_multiplicity,
      factorization_natCard_eq_of_isHallPiSubgroup hq hHallG hqσ]
  have hvq : 0 < (Nat.card G).factorization q :=
    hq.factorization_pos_of_dvd Nat.card_pos.ne'
      ((dvd_natCard_of_mem_sigmaPrimes hqσ).trans M.card_subgroup_dvd_card)
  have hQCA : Q ≤ centralizer (A : Set G) := hQS.trans hSCA
  have hAQ : A ≤ normalizer (Q : Set G) :=
    (le_centralizer_iff.mp hQCA).trans (centralizer_le_normalizer _)
  have hQmem : Q ∈ maximalNormalizedPSubgroups A q :=
    mem_maximalNormalizedPSubgroups_of_natCard hq hQcard hAQ
  have hqCA : q ∣ Nat.card ↥(centralizer (A : Set G)) :=
    (dvd_pow_self q hvq.ne').trans (hQcard ▸ Subgroup.card_dvd_of_le hQCA)
  have hNQM : normalizer (Q : Set G) ≤ M := by
    have hcardM : Nat.card ↥Q = q ^ (Nat.card ↥M).factorization q := by
      rw [hQcard, factorization_eq_of_mem_sigmaPrimes hqσ]
    obtain ⟨S', hS'⟩ := (exists_sylow_map_subtype_eq_iff hq (P := Q)).2
      ⟨hQS.trans (sigmaCore_le M), hcardM⟩
    have h := ((mem_sigmaPrimes_iff_forall hq).1 hqσ).2 S'
    rwa [hS'] at h
  obtain ⟨P, hAP, -, hPNQ⟩ := FTS_supported_plane_sylow_normalizer h₂ h₃ G hMin9 p q hp hq
    (fun h => hpσ (h ▸ hqσ)) A hAmax Q (IsPGroup.of_card hQcard) hAQ hQmem hqCA
  have hPM' : (P : Subgroup G) ≤ (⁅M, M⁆ : Subgroup G) :=
    hPNQ.trans (commutator_mono hNQM hNQM)
  have hPcard : Nat.card ↥(P : Subgroup G) = p ^ (Nat.card G).factorization p :=
    P.card_eq_multiplicity
  have hPbot : (P : Subgroup G) ≠ ⊥ := fun h => by
    have hAbot : A = ⊥ := le_bot_iff.1 (le_trans hAP h.le)
    rw [hAbot, Subgroup.card_bot] at hAcard
    exact hp.one_lt.ne' (by nlinarith [hAcard, hp.two_le])
  have hPle : (P : Subgroup G) ≤ M := hPM'.trans (commutator_le_self M)
  have hMN : M ≤ normalizer ((P : Subgroup G) : Set G) := fun g hg =>
    mem_normalizer_iff_map_conj_eq.2 (map_conj_eq_self_of_mem_normalizer hnil hPM'
      (natCard_eq_pow_factorization_of_le hp hPM' hPcard)
      (normalizer_commutator_ge_right M M hg))
  have hlt : normalizer ((P : Subgroup G) : Set G) < ⊤ :=
    normalizer_lt_top_of_isPGroup hna hp hPbot P.isPGroup'
  have hNM : normalizer ((P : Subgroup G) : Set G) = M := by
    by_contra hne
    exact hlt.ne (hM.2 _ (lt_of_le_of_ne hMN (Ne.symm hne)))
  exact hpσ ((mem_sigmaPrimes_iff_exists_subgroup hp).2
    ⟨hpdvdA.trans (Subgroup.card_dvd_of_le hAM), P, hPle,
      natCard_eq_pow_factorization_of_le hp hPle hPcard, hNM.le⟩)

theorem FTS_outside_sigma_core_centralizer_rank_one
    (h₁ : Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : Statements.FPL_global_sylow_normalizer_derived.{u})
    (h₃ : Statements.FTS_proper_subgroup_p_length_one.{u}) :
    Statements.FTS_outside_sigma_core_centralizer_rank_one.{u} := by
  intro G _ _ hG M K hM hKM hK p
  exact elementaryAbelianPRank_le_of_forall_prime
    (fun r hr => elementaryAbelianPRank_inf_centralizer_sigmaCore_le_one_of_prime h₁ h₂ h₃ hG hM
      hKM hK hr) p

end

end CFSG.FeitThompson.Proofs
