module

public import CFSG.FeitThompson.Statements.FittingOverlapKappaStatements
public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.BetaCoreHallQuotient
import CFSG.FeitThompson.Local.TauOneLineRegularSylowCentralizerBound
import CFSG.FeitThompson.Local.SigmaTauThreePrimesDerivedContainment
import CFSG.FeitThompson.Local.NilpotentDerivedQuotientSylowNormalizer
import CFSG.FeitThompson.Local.BetaPrimesSigmaCompatibility
import CFSG.FeitThompson.Local.AlphaPrimesInSigmaPrimes
import CFSG.FeitThompson.Local.FrattiniArgumentNormalSylow
import CFSG.FeitThompson.Local.NilpotentDerivedNormalizerFactorization
import CFSG.FeitThompson.Local.PComplementQuotientSylowRank
import CFSG.FeitThompson.OddOrder.RankThreeUniquenessMaximalOvergroup
import CFSG.FeitThompson.Definitions.TheWitnessedPConfiguration
import CFSG.FeitThompson.Definitions.AlphaCore
import CFSG.FeitThompson.Foundations.NormalHallContainsPiSubgroups
public import CFSG.FeitThompson.Definitions.FittingSubgroupAndNormalSylowHallCore
public import CFSG.FeitThompson.Foundations.CharacteristicSubgroupInvariance
public import CFSG.FeitThompson.Foundations.HallImageQuotient
public import CFSG.FeitThompson.Foundations.HomPreservesGeneratedCommutators
public import CFSG.FeitThompson.Foundations.NilpotenceEquivalentDefinitions
public import CFSG.FeitThompson.Foundations.SolvableHomImageSolvable
public import CFSG.FeitThompson.Foundations.SubgroupOrderAndIndex
public import CFSG.FeitThompson.Local.CoprimeSolvableFixedCosetLifting
public import CFSG.FeitThompson.Representations.AlgebraicIntegersRing
public import CFSG.FeitThompson.Representations.NormalInducedSupportBasis
public import CFSG.FeitThompson.Representations.SchurLemmaIntertwiningMaps
public import Mathlib

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open CFSG.FeitThompson Subgroup Pointwise

universe u

variable {G : Type u} [Group G] {M T : Subgroup G} {p q : ℕ}

theorem normal_subgroupOf_subgroupOf {A B : Subgroup G} (hBM : B ≤ M)
    (hnorm : (A.subgroupOf B).Normal) :
    ((A.subgroupOf M).subgroupOf (B.subgroupOf M)).Normal := by
  have h := hnorm.comap (Subgroup.subgroupOfEquivOfLe hBM).toMonoidHom
  rwa [← map_subgroupOf_subgroupOfEquivOfLe hBM, Subgroup.comap_map_eq_self_of_injective
    (Subgroup.subgroupOfEquivOfLe hBM).injective] at h

theorem isNilpotent_quotient_subgroupOf_subgroupOf {A B : Subgroup G} (hBM : B ≤ M)
    [((A.subgroupOf M).subgroupOf (B.subgroupOf M)).Normal] [(A.subgroupOf B).Normal]
    (hnil : Group.IsNilpotent (↥B ⧸ A.subgroupOf B)) :
    Group.IsNilpotent
      (↥(B.subgroupOf M) ⧸ ((A.subgroupOf M).subgroupOf (B.subgroupOf M))) :=
  (Group.isNilpotent_congr (QuotientGroup.congr _ _
    (Subgroup.subgroupOfEquivOfLe hBM) (map_subgroupOf_subgroupOfEquivOfLe hBM))).2 hnil

omit [Group G] in
theorem eq_of_isCoatom_of_le {L : Type*} [Lattice L] [OrderTop L] {M T : L} (hM : IsCoatom M)
    (hT : IsCoatom T) (hMT : M ≤ T) : M = T := by
  rcases eq_or_lt_of_le hMT with h | h
  · exact h
  · exact absurd (hM.2 T h) hT.1

variable [Finite G]

theorem elementaryAbelianPRank_mono (hp : 1 < p) {A B : Subgroup G} (hAB : A ≤ B) :
    elementaryAbelianPRank p ↥A ≤ elementaryAbelianPRank p ↥B := by
  have h := elementaryAbelianPRank_subgroup_le (X := ↥B) hp (A.subgroupOf B)
  rwa [elementaryAbelianPRank_eq_of_mulEquiv hp (Subgroup.subgroupOfEquivOfLe hAB)] at h

theorem elementaryAbelianPRank_eq_of_natCard_eq_pow (hp : p.Prime) {P : Subgroup G}
    (hPM : P ≤ M) (hcard : Nat.card P = p ^ (Nat.card ↥M).factorization p) :
    elementaryAbelianPRank p ↥P = elementaryAbelianPRank p ↥M := by
  have h1 : Nat.card ↥(P.subgroupOf M) = p ^ (Nat.card ↥M).factorization p := by
    rw [natCard_subgroupOf_of_le hPM]; exact hcard
  rw [← elementaryAbelianPRank_eq_of_natCard_eq_pow_factorization (p := p) hp h1]
  exact (elementaryAbelianPRank_eq_of_mulEquiv hp.one_lt
    (Subgroup.subgroupOfEquivOfLe hPM)).symm

theorem eq_of_three_le_elementaryAbelianPRank
    (hG : CFSG.FeitThompson.IsFBGAmbient G)
    {X : Subgroup G} (hp : p.Prime) (hM : IsCoatom M) (hT : IsCoatom T)
    (hXM : X ≤ M) (hXT : X ≤ T) (hrank : 3 ≤ elementaryAbelianPRank p ↥X) : M = T := by
  have := hG.isSimpleGroup
  have hXtop : X ≠ ⊤ := fun h => hM.1 (top_le_iff.1 (h ▸ hXM))
  obtain ⟨N, -, huniq⟩ := existsUnique_isCoatom_ge_of_three_le_maxElementaryAbelianPRank
    hG.not_isMulCommutative hG.odd_natCard hG.isSolvable hXtop
    (hrank.trans (elementaryAbelianPRank_le_maxElementaryAbelianPRank hp))
  rw [huniq M ⟨hM, hXM⟩, huniq T ⟨hT, hXT⟩]

theorem factorization_natCard_eq_of_isHallPiSubgroup_subgroupOf {π : Set ℕ} {K : Subgroup G}
    (hp : p.Prime) (hKM : K ≤ M) (hHall : IsHallPiSubgroup π (K.subgroupOf M)) (hpπ : p ∈ π) :
    (Nat.card ↥M).factorization p = (Nat.card ↥K).factorization p := by
  have hmul := Subgroup.card_mul_index (K.subgroupOf M)
  have hidx : ¬ p ∣ (K.subgroupOf M).index := fun hdvd =>
    hHall.notMem_of_mem_primeFactors_index p
      (Nat.mem_primeFactors.2 ⟨hp, hdvd, Subgroup.index_ne_zero_of_finite⟩) hpπ
  rw [← hmul, Nat.factorization_mul Nat.card_pos.ne' Subgroup.index_ne_zero_of_finite]
  simp only [Finsupp.coe_add, Pi.add_apply, Nat.factorization_eq_zero_of_not_dvd hidx, add_zero]
  rw [natCard_subgroupOf_of_le hKM]

theorem alphaCoreIn_eq_betaCore_of_alphaPrimes_eq (h : alphaPrimes ↥M = betaPrimes ↥M) :
    CFSG.FeitThompson.alphaCoreIn M = betaCore M := by
  rw [CFSG.FeitThompson.alphaCoreIn, alphaCore_eq_piCore,
    betaCore_eq_map_piCore, h]

section Sylow

variable (hM : IsCoatom M) (hq : q.Prime) (Q : Sylow q G)
  (hNQ : normalizer ((Q : Subgroup G) : Set G) ≤ M ⊓ T)

omit [Finite G] in
include hM hNQ in
theorem sylow_ne_bot : (Q : Subgroup G) ≠ ⊥ := by
  intro h
  have hnorm : normalizer ((Q : Subgroup G) : Set G) = ⊤ := by
    rw [h]; exact Subgroup.normalizer_eq_top ⊥
  exact hM.1 (top_le_iff.1 (hnorm ▸ (hNQ.trans inf_le_left)))

include hM hq hNQ in
theorem dvd_natCard_sylow : q ∣ Nat.card ↥(Q : Subgroup G) := by
  have := Fact.mk hq
  have h1 : Nat.card ↥(Q : Subgroup G) ≠ 1 := fun h =>
    sylow_ne_bot hM Q hNQ (Subgroup.card_eq_one.1 h)
  obtain ⟨n, hn⟩ := Q.isPGroup'.exists_card_eq
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · rw [pow_zero] at hn; exact absurd hn h1
  · exact hn ▸ dvd_pow_self q hn0.ne'

include hM hq hNQ in
theorem mem_sigmaPrimes_of_normalizer_le : q ∈ sigmaPrimes M := by
  have := Fact.mk hq
  have hQM : (Q : Subgroup G) ≤ M := Subgroup.le_normalizer.trans (hNQ.trans inf_le_left)
  refine (mem_sigmaPrimes_iff_exists_subgroup hq).2
    ⟨(dvd_natCard_sylow hM hq Q hNQ).trans (Subgroup.card_dvd_of_le hQM), (Q : Subgroup G), hQM,
      natCard_eq_pow_factorization_of_le hq hQM Q.card_eq_multiplicity, hNQ.trans inf_le_left⟩

include hq in
theorem isPiSubgroup_sylow {π : Set ℕ} (hqπ : q ∈ π) : IsPiSubgroup π (Q : Subgroup G) := by
  have := Fact.mk hq
  refine isPiSubgroup_iff.2 fun r hr => ?_
  obtain ⟨n, hn⟩ := Q.isPGroup'.exists_card_eq
  have hrq : r = q :=
    (Nat.prime_dvd_prime_iff_eq (Nat.prime_of_mem_primeFactors hr) hq).1
      ((Nat.prime_of_mem_primeFactors hr).dvd_of_dvd_pow (hn ▸ Nat.dvd_of_mem_primeFactors hr))
  rw [hrq]; exact hqπ

end Sylow

theorem sup_inf_eq_of_sup_normalizer_subgroupOf_eq_top {Q : Subgroup G} (hQM : Q ≤ M)
    (hNQ : normalizer (Q : Set G) ≤ M ⊓ T)
    (hkey : ((betaCore M).subgroupOf M) ⊔ normalizer ((Q.subgroupOf M) : Set ↥M) = ⊤) :
    betaCore M ⊔ (M ⊓ T) = M := by
  have hBM : betaCore M ≤ M := betaCore_le M
  have hmap := congrArg (fun K : Subgroup ↥M => K.map M.subtype) hkey
  simp only [Subgroup.map_sup] at hmap
  rw [Subgroup.map_subgroupOf_eq_of_le hBM, ← Subgroup.subgroupOf_normalizer_eq hQM,
    Subgroup.subgroupOf_map_subtype] at hmap
  have htop : (⊤ : Subgroup ↥M).map M.subtype = M := by ext x; simp
  rw [htop] at hmap
  refine le_antisymm (sup_le hBM inf_le_left) (hmap.ge.trans ?_)
  exact sup_le_sup_left
    (le_inf inf_le_right (inf_le_left.trans (hNQ.trans inf_le_right))) _

theorem coe_eq_mul_of_sup_eq (hsup : betaCore M ⊔ (M ⊓ T) = M) :
    (M : Set G) = (betaCore M : Set G) * ((M ⊓ T : Subgroup G) : Set G) := by
  rw [← Subgroup.coe_mul_of_right_le_normalizer_left (betaCore M) (M ⊓ T)
    (inf_le_left.trans (le_normalizer_betaCore M)), hsup]

theorem sup_inf_eq_of_sylow (hq : q.Prime) (Q : Sylow q G)
    (hNQ : normalizer ((Q : Subgroup G) : Set G) ≤ M ⊓ T)
    (hQMp : (Q : Subgroup G) ≤ (⁅M, M⁆ : Subgroup G))
    (hBMp : betaCore M ≤ (⁅M, M⁆ : Subgroup G))
    (hNnil : ((betaCore M).subgroupOf (⁅M, M⁆ : Subgroup G)).Normal)
    (hnil : Group.IsNilpotent
      (↥(⁅M, M⁆ : Subgroup G) ⧸ (betaCore M).subgroupOf (⁅M, M⁆ : Subgroup G))) :
    betaCore M ⊔ (M ⊓ T) = M := by
  have := Fact.mk hq
  have hMpM : (⁅M, M⁆ : Subgroup G) ≤ M := Subgroup.commutator_le_self M
  have hQM : (Q : Subgroup G) ≤ M := hQMp.trans hMpM
  have := hNnil
  have := betaCore_normal_subgroupOf M
  have := normal_subgroupOf_commutator_self M
  have hnormBB := normal_subgroupOf_subgroupOf (M := M) hMpM hNnil
  have := hnormBB
  have hnil2 :=
    isNilpotent_quotient_subgroupOf_subgroupOf (M := M) (A := betaCore M)
      (B := (⁅M, M⁆ : Subgroup G)) hMpM hnil
  have hYcard : Nat.card ↥((Q : Subgroup G).subgroupOf M) =
      q ^ (Nat.card ↥((⁅M, M⁆ : Subgroup G).subgroupOf M)).factorization q := by
    rw [natCard_subgroupOf_of_le hQM, natCard_subgroupOf_of_le hMpM]
    exact natCard_eq_pow_factorization_of_le hq hQMp Q.card_eq_multiplicity
  exact sup_inf_eq_of_sup_normalizer_subgroupOf_eq_top hQM hNQ
    (sup_normalizer_eq_top_of_isNilpotent_quotient (X := ↥M)
      (B := (betaCore M).subgroupOf M) (Y := (Q : Subgroup G).subgroupOf M)
      (L := (⁅M, M⁆ : Subgroup G).subgroupOf M) hq (Subgroup.comap_mono hBMp) hnil2
      (Subgroup.comap_mono hQMp) hYcard)

theorem FBG_common_sylow_normalizer_beta_factor
    (h₁ : CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : Statements.FTS_beta_prime_centralizing_sylow.{u})
    (h₃ : Statements.FTS_proper_subgroup_p_length_one.{u}) :
    Statements.FBG_common_sylow_normalizer_beta_factor.{u} := by
  intro G _ _ hG M T hM hT hMT q hq Q hNQ
  have : Fintype G := Fintype.ofFinite G
  have := Fact.mk hq
  have := hG.isSimpleGroup
  have hG2 : CFSG.FeitThompson.IsOddOrderMinimalSimple G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable⟩
  have hG6 : Prep06.IsMinimalOddSimple G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable⟩
  obtain ⟨hHallOf, -, hSMp⟩ := h₁ G hG2 M hM
  obtain ⟨-, -, -, hBMp, -, hNnil, hnil⟩ := FTS_beta_core_hall_quotient h₁ h₃ G hG6 M hM
  have hMpM : (⁅M, M⁆ : Subgroup G) ≤ M := Subgroup.commutator_le_self M
  have hQM : (Q : Subgroup G) ≤ M := Subgroup.le_normalizer.trans (hNQ.trans inf_le_left)
  have hQT : (Q : Subgroup G) ≤ T := Subgroup.le_normalizer.trans (hNQ.trans inf_le_right)
  have hqσ : q ∈ sigmaPrimes M := mem_sigmaPrimes_of_normalizer_le hM hq Q hNQ
  have hQMp : (Q : Subgroup G) ≤ (⁅M, M⁆ : Subgroup G) :=
    (le_sigmaCore_of_isPiSubgroup hHallOf hQM (isPiSubgroup_sylow hq Q hqσ)).trans hSMp
  have hsup : betaCore M ⊔ (M ⊓ T) = M := sup_inf_eq_of_sylow hq Q hNQ hQMp hBMp hNnil hnil
  have hoddq : Odd q := hG.odd_natCard.of_dvd_nat
    ((dvd_natCard_sylow hM hq Q hNQ).trans (Subgroup.card_subgroup_dvd_card _))
  have hqcardM : Nat.card ↥(Q : Subgroup G) = q ^ (Nat.card ↥M).factorization q :=
    natCard_eq_pow_factorization_of_le hq hQM Q.card_eq_multiplicity
  have hqα : q ∉ alphaPrimes ↥M := fun hmem =>
    hMT (eq_of_three_le_elementaryAbelianPRank hG hq hM hT hQM hQT
      ((elementaryAbelianPRank_eq_of_natCard_eq_pow hq hQM hqcardM) ▸
        three_le_elementaryAbelianPRank_of_mem_alphaPrimes hmem))
  have hqβ : q ∉ betaPrimes ↥M := fun h => hqα (betaPrimes_subset_alphaPrimes h)
  have hαβ : alphaPrimes ↥M = betaPrimes ↥M := by
    refine Set.Subset.antisymm (fun r hr => ?_) betaPrimes_subset_alphaPrimes
    by_contra hrβ
    have hrp : r.Prime := prime_of_mem_alphaPrimes hr
    have hrq : r ≠ q := fun h => hqα (h ▸ hr)
    have hrrank : 3 ≤ elementaryAbelianPRank r ↥M :=
      three_le_elementaryAbelianPRank_of_mem_alphaPrimes hr
    have hrdvd : r ∣ Nat.card ↥M := by
      by_contra hd
      rw [(elementaryAbelianPRank_eq_zero_iff hrp).2 hd] at hrrank; omega
    have hoddr : Odd r :=
      hG.odd_natCard.of_dvd_nat (hrdvd.trans (Subgroup.card_subgroup_dvd_card M))
    obtain ⟨n, hn⟩ := Q.isPGroup'.exists_card_eq
    obtain ⟨R, hR, hcomm⟩ := h₂ G hG6 M hM r q hrp hq hoddr hoddq hrq hrβ hqβ
      (Q : Subgroup G) n hQM hn (Or.inl hQMp)
    have hrσ : r ∈ sigmaPrimes M :=
      alphaPrimes_subset_sigmaPrimes hG.not_isMulCommutative hG.odd_natCard hG.isSolvable hM hr
    have hfac := factorization_natCard_eq_of_isHallPiSubgroup_subgroupOf (M := M) hrp
      (sigmaCore_le M) hHallOf.2 hrσ
    have hRM : R ≤ M := hR.1.trans (sigmaCore_le M)
    have hRcard : Nat.card ↥R = r ^ (Nat.card ↥M).factorization r := by rw [hR.2, hfac]
    have hRrank : 3 ≤ elementaryAbelianPRank r ↥R := by
      rw [elementaryAbelianPRank_eq_of_natCard_eq_pow hrp hRM hRcard]; exact hrrank
    have hRcent : R ≤ M ⊓ centralizer ((Q : Subgroup G) : Set G) :=
      le_inf hRM (le_centralizer_iff.1 (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm))
    have hCT : (M ⊓ centralizer ((Q : Subgroup G) : Set G) : Subgroup G) ≤ T :=
      (inf_le_right.trans (Subgroup.centralizer_le_normalizer _)).trans (hNQ.trans inf_le_right)
    exact hMT (eq_of_three_le_elementaryAbelianPRank hG hrp hM hT inf_le_left hCT
      (hRrank.trans (elementaryAbelianPRank_mono hrp.one_lt hRcent)))
  refine ⟨coe_eq_mul_of_sup_eq hsup, hαβ, alphaCoreIn_eq_betaCore_of_alphaPrimes_eq hαβ, ?_⟩
  intro hBbot
  rw [hBbot, bot_sup_eq] at hsup
  exact hMT (eq_of_isCoatom_of_le hM hT (hsup.ge.trans inf_le_right))

end

end CFSG.FeitThompson.Proofs
