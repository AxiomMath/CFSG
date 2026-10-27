module

public import CFSG.FeitThompson.Statements.KappaCandidateStatements
public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.TauTwoFullCentralHall
import CFSG.FeitThompson.Local.SigmaComplementPrimeData
import CFSG.FeitThompson.Local.RankOnePrimesRegularKappaComplement
import CFSG.FeitThompson.Local.KappaHallThirdFactorSupportedComplement
import CFSG.FeitThompson.Local.KappaPositiveMultipleCoreTrivialResidual
import CFSG.FeitThompson.Local.DerivedComplementCentralizesBetaPrimeHall
import CFSG.FeitThompson.Local.OutsideSigmaKappaSylowCoreNilpotent
import CFSG.FeitThompson.Local.NonabelianAmbientNormalHallFreeComplement
import CFSG.FeitThompson.Local.NormalHallInertiaContainer
import CFSG.FeitThompson.Local.HallComponentsFixedPointFreeSubgroup
import CFSG.FeitThompson.Local.PComplementQuotientSylowRank
import CFSG.FeitThompson.Local.ControlledNormalElementaryPlane
import CFSG.FeitThompson.Local.FittingSplitsNormalHall
import CFSG.FeitThompson.Foundations.SolvableHallExistence
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

open CFSG.FeitThompson Subgroup
open CFSG.FeitThompson
open CFSG.FeitThompson.Prep03

universe u

variable {G : Type u} [Group G]

theorem factorization_natCard_eq_of_isHallPiSubgroup_mem {X : Type*} [Group X] [Finite X]
    {π : Set ℕ} {H : Subgroup X} (hH : IsHallPiSubgroup π H) {p : ℕ} (hp : p.Prime) (hpπ : p ∈ π) :
    (Nat.card ↥H).factorization p = (Nat.card X).factorization p :=
  factorization_natCard_eq_of_not_dvd_index fun hd =>
    hH.notMem_of_mem_primeFactors_index p
      (Nat.mem_primeFactors.2 ⟨hp, hd, Subgroup.index_ne_zero_of_finite⟩) hpπ

theorem exponent_subgroupOf_eq_exponent {X Y : Subgroup G} (h : Y ≤ X) :
    Monoid.exponent ↥(Y.subgroupOf X) = Monoid.exponent ↥Y :=
  Monoid.exponent_eq_of_mulEquiv (subgroupOfEquivOfLe h)

theorem le_normalizer_inf_of_le_normalizer {X A B : Subgroup G}
    (hA : X ≤ normalizer (A : Set G)) (hB : X ≤ normalizer (B : Set G)) :
    X ≤ normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  intro g hg
  simp only [Subgroup.mem_normalizer_iff] at hA hB ⊢
  intro n
  exact ⟨fun h => ⟨(hA hg n).1 h.1, (hB hg n).1 h.2⟩,
    fun h => ⟨(hA hg n).2 h.1, (hB hg n).2 h.2⟩⟩

theorem FNI_abelian_ambient_normal_hall_inertia_and_exponent
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FNI_abelian_normal_hall_full_exponent_cycle.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_complement_normalizer.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FPL_global_sylow_normalizer_derived.{u})
    (h₆ : _root_.CFSG.FeitThompson.Statements.FTS_proper_subgroup_p_length_one.{u}) :
    _root_.CFSG.FeitThompson.Statements.FNI_abelian_ambient_normal_hall_inertia_and_exponent.{u} := by
  intro G _ _ hG M E K U hsetup hUbot hab
  have hfin : Finite G := Finite.of_fintype G
  have hG2 : IsOddOrderMinimalSimple G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.forall_isSolvable⟩
  have hG4 : IsOddSimpleMinimal G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.forall_isSolvable⟩
  obtain ⟨hfreeτ, hUHallE, hEnormU⟩ :=
    FNI_kappa_complement_rank_one_prime_regularity h₁ G hG M E K U hsetup
  obtain ⟨-, hM, hdecomp, hKE, hHallK, hUE, hdecompE⟩ := hsetup
  have hEM : E ≤ M := hdecomp.2.1
  have hUM : U ≤ M := hUE.trans hEM
  have hEtop : E ≠ ⊤ := fun h => hM.1 (top_le_iff.1 (h ▸ hEM))
  have hUtop : U ≠ ⊤ := fun h => hM.1 (top_le_iff.1 (h ▸ hUM))
  have hEsolv : Group.IsSolvable ↥E := hG.forall_isSolvable E hEtop
  have hUsolv : Group.IsSolvable ↥U := hG.forall_isSolvable U hUtop
  obtain ⟨hπE, hrankE, -, -, -, -, -, -⟩ :=
    FNI_sigma_complement_prime_data h₁ G hG4 M E
      ⟨hM, isInternalSemidirectProduct_of_isSemidirect hdecomp⟩
  obtain ⟨X₂, hX₂⟩ := exists_isHallSubgroup (X := ↥E) (tauTwoPrimes M)
  set E₂ : Subgroup G := X₂.map E.subtype with hE₂def
  have hE₂E : E₂ ≤ E := map_subtype_le _
  have hE₂sub : E₂.subgroupOf E = X₂ := comap_map_eq_self_of_injective E.subtype_injective X₂
  have hE₂Hall : IsHallPiSubgroup (tauTwoPrimes M) (E₂.subgroupOf E) := by
    rw [hE₂sub]; exact isHallSubgroup_iff_isHallPiSubgroup.1 hX₂
  have hE₂π : ∀ r ∈ (Nat.card ↥E₂).primeFactors, r ∈ tauTwoPrimes M := by
    intro r hr
    refine isPiSubgroup_iff.1 hE₂Hall.isPiSubgroup r ?_
    rwa [natCard_subgroupOf_eq_natCard_of_le hE₂E]
  have hFBG : ∀ p ∈ tauTwoPrimes M,
      IsMulCommutative ↥E₂ ∧ (E₂.subgroupOf E).Normal ∧
        IsHallPiSubgroup (tauTwoPrimes M) E₂ := by
    intro p hp
    have hfp : Fact p.Prime := ⟨prime_of_mem_tauTwoPrimes hp⟩
    have habp : ∀ R : Sylow p G, IsMulCommutative ↥(R : Subgroup G) := fun R =>
      hab p hp (R : Subgroup G) R.card_eq_multiplicity
    obtain ⟨-, hc1, hc2, hc3⟩ := FBG_tau_two_full_central_hall h₁ h₃ h₄ h₅ h₆ G hG2 M hM E
      (isInternalSemidirectProduct_of_isSemidirect hdecomp) p hp habp E₂ ⟨hE₂E, hE₂Hall⟩
    exact ⟨hc1, hc2, hc3⟩
  have hE₂bot : tauTwoPrimes M = ∅ → E₂ = ⊥ := by
    intro hτ
    refine Subgroup.card_eq_one.1 ?_
    by_contra hne
    obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hne
    have hmem := hE₂π q (Nat.mem_primeFactors.2 ⟨hq, hqd, Nat.card_pos.ne'⟩)
    rw [hτ] at hmem
    exact hmem
  have hE₂ab : IsMulCommutative ↥E₂ := by
    rcases Set.eq_empty_or_nonempty (tauTwoPrimes M) with hτ | ⟨p, hp⟩
    · rw [hE₂bot hτ]; infer_instance
    · exact (hFBG p hp).1
  have hE₂normal : (E₂.subgroupOf E).Normal := by
    rcases Set.eq_empty_or_nonempty (tauTwoPrimes M) with hτ | ⟨p, hp⟩
    · rw [hE₂bot hτ, Subgroup.bot_subgroupOf]; infer_instance
    · exact (hFBG p hp).2.1
  have hEnormE₂ : E ≤ normalizer (E₂ : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hE₂E).1 hE₂normal
  have hUHall' : IsHallPiSubgroup (kappaPrimes M)ᶜ (U.subgroupOf E) :=
    isHallPiSubgroup_subgroupOf_of_isHallPiOf hUHallE
  have hUnormal : (U.subgroupOf E).Normal := (normal_subgroupOf_iff_le_normalizer hUE).2 hEnormU
  set U₁ : Subgroup G := E₂ ⊓ U with hU₁def
  have hU₁U : U₁ ≤ U := inf_le_right
  have hUnormU₁ : U ≤ normalizer (U₁ : Set G) :=
    le_normalizer_inf_of_le_normalizer (hUE.trans hEnormE₂) le_normalizer
  have hU₁Hall : IsHallPiSubgroupOf (tauTwoPrimes M) U₁ U :=
    isHallPiSubgroupOf_inf_of_normal hUE hE₂E hUnormal (isPiSubgroup_iff.2 hUHallE.2.1)
      hUHallE.2.2 (isPiSubgroup_iff.2 hE₂π) hE₂Hall.notMem_of_mem_primeFactors_index
  set A : Subgroup ↥U := U₁.subgroupOf U with hAdef
  have hA : IsHallPiSubgroup (tauTwoPrimes M) A := hU₁Hall.2
  have hAnormal : A.Normal := (normal_subgroupOf_iff_le_normalizer hU₁U).2 hUnormU₁
  have hcardA : Nat.card ↥A = Nat.card ↥U₁ := natCard_subgroupOf_eq_natCard_of_le hU₁U
  have hfree : ∀ q : ℕ, q.Prime → q ∉ tauTwoPrimes M → ∀ v ∈ U, orderOf v = q →
      sigmaCore M ⊓ centralizer ({v} : Set G) = ⊥ := by
    intro q hq hqτ v hv hvq
    have hqU : q ∣ Nat.card ↥U := hvq ▸ Subgroup.orderOf_dvd_natCard U hv
    have hqE : q ∣ Nat.card ↥E := hqU.trans (card_dvd_of_le hUE)
    have hqπE : q ∈ primeDivisorsOf ↥E := ⟨hq, hqE⟩
    have hqπE' : q ∈ primeDivisorsOf ↥M \ sigmaPrimes M := hπE ▸ hqπE
    have hrk1 : elementaryAbelianPRank q ↥M = 1 := by
      obtain ⟨-, hrk2⟩ := hrankE q hqπE
      have hge : 1 ≤ elementaryAbelianPRank q ↥M :=
        (one_le_elementaryAbelianPRank_iff hq).2 hqπE'.1.2
      have hne2 : elementaryAbelianPRank q ↥M ≠ 2 := fun h =>
        hqτ (mem_tauTwoPrimes_iff.2 ⟨hq, hqπE'.2, h⟩)
      omega
    have hmem : q ∈ tau1Primes M ∪ tau3Primes M := by
      rw [tau1Primes_union_tau3Primes]
      exact ⟨hq, hqπE'.1.2, hqπE'.2, hrk1⟩
    exact hfreeτ q hmem v hv hvq
  have hinertia : ∀ h ∈ sigmaCore M, h ≠ 1 → U ⊓ centralizer ({h} : Set G) ≤ U₁ := by
    intro h hh hh1
    have hle := inf_centralizer_le_map_subtype_of_isHallPiSubgroup (π := tauTwoPrimes M)
      (H := sigmaCore M) (U := U) (A := A) hA hfree hh hh1
    rwa [hAdef, map_subgroupOf_eq_of_le hU₁U] at hle
  have hkey : ∀ p : ℕ, ∃ Sp Zp : Subgroup ↥U,
      p ∈ (Nat.card ↥A).primeFactors →
        (Sp ≤ A ∧ Nat.card ↥Sp = p ^ (Nat.card ↥A).factorization p) ∧ Zp ≤ Sp ∧ Zp.Normal ∧
        Monoid.exponent ↥Zp = Monoid.exponent ↥Sp ∧
        ∀ z ∈ Zp, ((z : ↥U) : G) ≠ 1 →
          sigmaCore M ⊓ centralizer ({((z : ↥U) : G)} : Set G) = ⊥ := by
    intro p
    by_cases hp : p ∈ (Nat.card ↥A).primeFactors
    · have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hfp : Fact p.Prime := ⟨hpp⟩
      have hpτ : p ∈ tauTwoPrimes M := isPiSubgroup_iff.1 hA.isPiSubgroup p hp
      obtain ⟨Q, hQ⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥U₁) p
        (n := (Nat.card ↥U₁).factorization p) (Nat.ordProj_dvd _ _)
      have hPU₁ : Q.map U₁.subtype ≤ U₁ := map_subtype_le _
      set P : Subgroup G := Q.map U₁.subtype with hPdef
      have hPU : P ≤ U := hPU₁.trans hU₁U
      have hPcard : Nat.card ↥P = p ^ (Nat.card ↥U₁).factorization p := by
        rw [hPdef, Subgroup.card_subtype, hQ]
      have hfacU₁ : (Nat.card ↥U₁).factorization p = (Nat.card G).factorization p := by
        have e1 : (Nat.card ↥A).factorization p = (Nat.card ↥U).factorization p :=
          factorization_natCard_eq_of_isHallPiSubgroup_mem hA hpp hpτ
        have hpκ : p ∉ kappaPrimes M :=
          notMem_kappaPrimes_of_elementaryAbelianPRank_eq_two hpp
            (elementaryAbelianPRank_eq_two_of_mem_tauTwoPrimes hpτ)
        have e2 : (Nat.card ↥(U.subgroupOf E)).factorization p = (Nat.card ↥E).factorization p :=
          factorization_natCard_eq_of_isHallPiSubgroup_mem hUHall' hpp hpκ
        have e3 : (Nat.card ↥(E₂.subgroupOf E)).factorization p = (Nat.card ↥E).factorization p :=
          factorization_natCard_eq_of_isHallPiSubgroup_mem hE₂Hall hpp hpτ
        have e4 : (Nat.card ↥E₂).factorization p = (Nat.card G).factorization p :=
          factorization_natCard_eq_of_isHallPiSubgroup_mem (hFBG p hpτ).2.2 hpp hpτ
        rw [natCard_subgroupOf_eq_natCard_of_le hUE] at e2
        rw [natCard_subgroupOf_eq_natCard_of_le hE₂E] at e3
        rw [← hcardA, e1, e2, ← e3, e4]
      have hPtop : IsSylowTop p P := by
        change Nat.card ↥P = p ^ (Nat.card G).factorization p
        rw [hPcard, hfacU₁]
      have hPab : IsMulCommutative ↥P := hab p hpτ P hPtop
      have hrkM : elementaryAbelianPRank p ↥M = 2 :=
        elementaryAbelianPRank_eq_two_of_mem_tauTwoPrimes hpτ
      have hrkG : 2 ≤ elementaryAbelianPRank p G := by
        obtain ⟨H, hH⟩ := mem_elementaryAbelianRanks.1
          ((le_elementaryAbelianPRank_iff hpp.one_lt).1 hrkM.ge)
        obtain ⟨e⟩ := hH
        refine (le_elementaryAbelianPRank_iff hpp.one_lt).2
          (mem_elementaryAbelianRanks.2 ⟨H.map M.subtype, ?_⟩)
        exact ⟨(H.equivMapOfInjective M.subtype M.subtype_injective).symm.trans e⟩
      have hrkP : 2 ≤ elementaryAbelianPRank p ↥P := by
        rw [elementaryAbelianPRank_eq_of_natCard_eq_pow_factorization hpp hPtop]
        exact hrkG
      obtain ⟨A₀, hA₀P, hA₀plane⟩ := exists_isElementaryAbelianPlane_le hpp hrkP
      have hsetupPlane : IsPlaneSetup G p M A₀ E :=
        ⟨hG, hM, hpp, notMem_sigmaPrimes_of_mem_tauTwoPrimes hpτ,
          (hA₀P.trans hPU).trans hUM, hA₀plane, hdecomp, (hA₀P.trans hPU).trans hUE⟩
      obtain ⟨Z, hZP, hZcyc, hUnormZ, hZexp, hZfree⟩ :=
        h₂ G hG p M A₀ E K U P hsetupPlane hHallK hKE hUE hdecompE hPtop hPab hA₀P hPU
      refine ⟨P.subgroupOf U, Z.subgroupOf U, fun _ => ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩⟩
      · exact Subgroup.comap_mono hPU₁
      · rw [natCard_subgroupOf_eq_natCard_of_le hPU, hPcard, hcardA]
      · exact Subgroup.comap_mono hZP
      · exact (normal_subgroupOf_iff_le_normalizer (hZP.trans hPU)).2 hUnormZ
      · rw [exponent_subgroupOf_eq_exponent (hZP.trans hPU), exponent_subgroupOf_eq_exponent hPU]
        exact hZexp
      · intro z hz hz1
        exact hZfree (z : G) (mem_subgroupOf.1 hz) hz1
    · exact ⟨⊥, ⊥, fun hc => absurd hc hp⟩
  choose Sf Zf hSZ using hkey
  obtain ⟨U₀, hU₀U, -, hU₀exp, hU₀free⟩ :=
    exists_le_ne_bot_exponent_eq_of_isHallPiSubgroup (H := sigmaCore M) (U := U) (A := A)
      (S := Sf) (Z := Zf) (π := tauTwoPrimes M) hUbot hA hfree
      (fun p hp => (hSZ p hp).1) (fun p hp => (hSZ p hp).2.1)
      (fun p hp => (hSZ p hp).2.2.1) (fun p hp => (hSZ p hp).2.2.2.1)
      (fun p hp => (hSZ p hp).2.2.2.2)
  exact ⟨U₁, U₀, hU₁U, hU₀U, isMulCommutative_of_le (A := E₂) inf_le_left, hUnormU₁, hinertia,
    hU₀exp, hU₀free⟩

end

end CFSG.FeitThompson.Proofs
