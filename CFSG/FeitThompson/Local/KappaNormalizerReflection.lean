module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.KappaCandidateStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.Local.KappaFixedPrimeCentralizerSylowUnique
import CFSG.FeitThompson.Local.TauTwoSubgroupCentralizerUnique
import CFSG.FeitThompson.Local.SigmaHallCentralizerExcludesKappa
import CFSG.FeitThompson.Local.KappaPrimeLineFixedEquivalence
import CFSG.FeitThompson.Local.ThreePrimeComplementDecomposition
import CFSG.FeitThompson.Local.CriticalSubgroupFixedLine
import CFSG.FeitThompson.Local.PComplementQuotientSylowRank
import CFSG.FeitThompson.OddOrder.SigmaPrimesWellDefined

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

variable {G : Type*} [Group G] {q : ℕ}

theorem sigmaPrimes_map_conj [Finite G] (M : Subgroup G) (g : G) :
    sigmaPrimes (M.map (MulAut.conj g : G →* G)) = sigmaPrimes M := by
  have h := sigmaPrimes_conj_smul M g
  rwa [Subgroup.pointwise_smul_def] at h

theorem sigmaPrimes_prep09_conjSub [Finite G] (M : Subgroup G) (g : G) :
    sigmaPrimes (CFSG.FeitThompson.Prep09.conjSub g M) = sigmaPrimes M :=
  sigmaPrimes_map_conj M g⁻¹

theorem sigmaPrimes_prep03_conjSub [Finite G] (M : Subgroup G) (g : G) :
    sigmaPrimes (CFSG.FeitThompson.Prep03.conjSub M g) = sigmaPrimes M :=
  sigmaPrimes_map_conj M g⁻¹

theorem elementaryAbelianPRank_le_two_of_notMem_sigmaPrimes [Finite G] [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ Y : Subgroup G, Y ≠ ⊤ → Group.IsSolvable ↥Y) {T : Subgroup G} (hT : IsCoatom T)
    (hq : q.Prime) (hqσ : q ∉ sigmaPrimes T) : elementaryAbelianPRank q ↥T ≤ 2 := by
  by_contra h
  exact hqσ (alphaPrimes_subset_sigmaPrimes hna hodd hsolv hT (mem_alphaPrimes.2 ⟨hq, by omega⟩))

theorem exists_isCyclic_sylow_of_elementaryAbelianPRank_le_one [Finite G] (T : Subgroup G)
    (hq : q.Prime) (hodd : Odd q) (hrank : elementaryAbelianPRank q ↥T ≤ 1) :
    ∃ S : Sylow q ↥T, IsCyclic ((S : Subgroup ↥T).map T.subtype : Subgroup G) := by
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨S⟩ : Nonempty (Sylow q ↥T) := inferInstance
  refine ⟨S, (isCyclic_map_subtype_iff _).2 ?_⟩
  refine isCyclic_of_elementaryAbelianPRank_le_one hq hodd S.isPGroup' ?_
  rwa [elementaryAbelianPRank_eq_of_natCard_eq_pow_factorization hq S.card_eq_multiplicity]

end

end CFSG.FeitThompson

namespace CFSG.FeitThompson.Proofs

public section

open Subgroup CFSG.FeitThompson
open CFSG.FeitThompson
open CFSG.FeitThompson.Prep03

universe u

theorem FNI_kappa_normalizer_reflection
    (h₁ : Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : Statements.FBG_tau_two_hall_abelian.{u})
    (h₃ : Statements.FNI_kappa_normalizer_centralizer_structure.{u})
    (h₄ : Statements.FNI_kappa_semiprime_complement_existence.{u})
    (h₅ : Statements.FNI_outside_sigma_plane_core_disjoint.{u})
    (h₆ : Statements.FTS_sigma_prime_separation.{u})
    (h₇ : Statements.FTS_tau_one_fixed_line_centralizer_unique.{u}) :
    Statements.FNI_kappa_normalizer_reflection.{u} := by
  intro G _ _ M K A Z hsetup X T hXK hXp hT hNXT
  have hamb := hsetup.ambient
  have hM := hsetup.isCoatom
  have hKH := hsetup.isHall_K
  have hAeq := hsetup.A_eq
  have hZeq := hsetup.Z_eq
  have hsimple := hamb.isSimpleGroup
  have hsolv := hamb.forall_isSolvable
  have hodd := hamb.odd_natCard
  have hna := hamb.not_isMulCommutative
  have hmin : Prep09.IsMinimalSimpleOddOrder G := ⟨hodd, hsimple, hna, hsolv⟩
  obtain ⟨hdir, -, hprimeX⟩ := h₃ G M K A Z hsetup
  obtain ⟨-, hNeq, hXS⟩ := hprimeX X hXK hXp
  have hXT : X ≤ sigmaCore T := hXS T hT hNXT
  have hZT : Z ≤ T := by
    rw [hZeq, hdir.2.2.1, ← hNeq]
    exact le_trans inf_le_left hNXT
  have hpT : Nat.card ↥X ∈ sigmaPrimes T :=
    isPiSubgroup_iff.1 (isPiSubgroup_sigmaCore T) _
      (Nat.mem_primeFactors.2 ⟨hXp, Subgroup.card_dvd_of_le hXT, Nat.card_pos.ne'⟩)
  have hpκM : Nat.card ↥X ∈ kappaPrimes M :=
    hKH.2.1 _ (Nat.mem_primeFactors.2 ⟨hXp, Subgroup.card_dvd_of_le hXK, Nat.card_pos.ne'⟩)
  have hpM : Nat.card ↥X ∉ sigmaPrimes M := notMem_sigmaPrimes_of_mem_kappaPrimes hpκM
  have hnc : ¬ ∃ g : G, conjSub T g = M := by
    rintro ⟨g, hg⟩
    exact hpM (hg ▸ (sigmaPrimes_prep03_conjSub T g).symm ▸ hpT)
  have hdisj : sigmaPrimes M ∩ sigmaPrimes T = ∅ := by
    refine h₆ G hmin M T hM hT fun g hg => hpM ?_
    rw [hg, sigmaPrimes_prep09_conjSub] at hpT
    exact hpT
  have hAS : A ≤ sigmaCore M := by rw [hAeq]; exact inf_le_left
  have hAC : A ≤ Subgroup.centralizer (K : Set G) := by rw [hAeq]; exact inf_le_right
  have hKC : K ≤ Subgroup.centralizer (A : Set G) := Subgroup.le_centralizer_iff.1 hAC
  have hAZ : A ≤ Z := by rw [hZeq]; exact le_sup_right
  have hAT : A ≤ T := hAZ.trans hZT
  obtain ⟨hAbot, hcentA, -⟩ :=
    FNI_kappa_fixed_prime_centralizer_and_sylow_uniqueness h₁ h₄ h₇ G M K A Z hsetup
  have hkey : ∀ r : ℕ, r.Prime → r ∣ Nat.card ↥A → r ∈ kappaPrimes T := by
    intro r hr hrA
    obtain ⟨y, hyA, hyord⟩ := exists_mem_orderOf_eq_of_dvd hr hrA
    have hYA : zpowers y ≤ A := zpowers_le.2 hyA
    have hYcard : Nat.card ↥(zpowers y) = r := by rw [Nat.card_zpowers, hyord]
    have hYT : zpowers y ≤ T := hYA.trans hAT
    have hrσM : r ∈ sigmaPrimes M :=
      isPiSubgroup_iff.1 (isPiSubgroup_sigmaCore M) r
        (Nat.mem_primeFactors.2 ⟨hr, hrA.trans (Subgroup.card_dvd_of_le hAS), Nat.card_pos.ne'⟩)
    have hrσT : r ∉ sigmaPrimes T := by
      intro hrT
      have hmem : r ∈ sigmaPrimes M ∩ sigmaPrimes T := ⟨hrσM, hrT⟩
      rw [hdisj] at hmem
      exact hmem
    have hXY : X ≤ Subgroup.centralizer ((zpowers y : Subgroup G) : Set G) :=
      hXK.trans (hKC.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hYA)))
    have hXbot : X ≠ ⊥ := fun h => hXp.ne_one (by rw [h]; simp)
    have hcentY : sigmaCore T ⊓ Subgroup.centralizer ((zpowers y : Subgroup G) : Set G) ≠ ⊥ :=
      fun hc => hXbot (le_bot_iff.1 (hc ▸ le_inf hXT hXY))
    have hYbot : (zpowers y : Subgroup G) ≠ ⊥ := fun h => hr.ne_one (by rw [← hYcard, h]; simp)
    have hrτ : r ∉ tauTwoPrimes T := by
      intro hrτ
      obtain ⟨hcle, -⟩ := FTS_tau_two_subgroup_centralizer_unique h₂ h₅ G hmin T hT
        (zpowers y) hYT hYbot (fun s hs => by
          rw [hYcard, hr.primeFactors, Finset.mem_singleton] at hs
          exact hs ▸ hrτ) hcentY
      have hTM : T = M := (hcentA r (zpowers y) hr hYA hYcard).2 T hT hcle
      exact hpM (hTM ▸ hpT)
    have hrdvdT : r ∣ Nat.card ↥T := hYcard ▸ Subgroup.card_dvd_of_le hYT
    have hrank1 : 1 ≤ elementaryAbelianPRank r ↥T :=
      (one_le_elementaryAbelianPRank_iff hr).2 hrdvdT
    have hrank2 : elementaryAbelianPRank r ↥T ≤ 2 :=
      elementaryAbelianPRank_le_two_of_notMem_sigmaPrimes hna hodd hsolv hT hr hrσT
    have hrankne : elementaryAbelianPRank r ↥T ≠ 2 := fun h =>
      hrτ (mem_tauTwoPrimes_iff.2 ⟨hr, hrσT, h⟩)
    have hrodd : Odd r := Odd.of_dvd_nat hodd (hrdvdT.trans T.card_subgroup_dvd_card)
    obtain ⟨S, hScyc⟩ :=
      exists_isCyclic_sylow_of_elementaryAbelianPRank_le_one T hr hrodd (by omega)
    exact (mem_kappaPrimes_iff_inf_centralizer_ne_bot hr hrσT ⟨S, hScyc⟩ hYT hYcard).2 hcentY
  obtain ⟨q₀, hq₀, hq₀A⟩ := Nat.exists_prime_and_dvd (n := Nat.card ↥A)
    (fun h => hAbot (Subgroup.card_eq_one.1 h))
  have hκT : (kappaPrimes T).Nonempty := ⟨q₀, hkey q₀ hq₀ hq₀A⟩
  have hTsolv : Group.IsSolvable ↥T := hsolv T hT.1
  have hApi : IsPiSubgroup (kappaPrimes T) (A.subgroupOf T) := by
    refine isPiSubgroup_iff.2 fun r hr => ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAT).toEquiv] at hr
    exact hkey r (Nat.prime_of_mem_primeFactors hr) (Nat.dvd_of_mem_primeFactors hr)
  obtain ⟨H, hH, hAH⟩ := exists_isHallSubgroup_ge_of_isPiSubgroup hApi
  have hL : IsHallPiOf (kappaPrimes T) (H.map T.subtype) T := isHallPiOf_map_subtype T hH
  have hAL : A ≤ H.map T.subtype := by
    have h := Subgroup.map_mono (f := T.subtype) hAH
    rwa [Subgroup.map_subgroupOf_eq_of_le hAT] at h
  refine ⟨hnc, hZT, hκT, ⟨H.map T.subtype, hL, hAL⟩, fun Y hYA hYp => ?_⟩
  have hsetupT : IsKappaSetup G T (H.map T.subtype)
      (cent (sigmaCore T) ((H.map T.subtype : Subgroup G) : Set G))
      ((H.map T.subtype) ⊔ cent (sigmaCore T) ((H.map T.subtype : Subgroup G) : Set G)) :=
    { ambient := hamb, isCoatom := hT, kappa_nonempty := hκT, isHall_K := hL,
      A_eq := rfl, Z_eq := rfl }
  obtain ⟨-, -, hprimeT⟩ := h₃ G T (H.map T.subtype) _ _ hsetupT
  have hLY := (hprimeT Y (hYA.trans hAL) hYp).1
  refine le_inf ?_ hZT
  rw [hZeq]
  exact sup_le (hKC.trans ((Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hYA)).trans
    (Subgroup.centralizer_le_normalizer _))) (hAL.trans hLY)

end

end CFSG.FeitThompson.Proofs
