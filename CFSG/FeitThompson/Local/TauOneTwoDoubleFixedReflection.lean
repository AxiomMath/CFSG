module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.NonregularPlaneLineUniqueCentralizer
import CFSG.FeitThompson.Local.RankOnePlaneCentralizerRegular
import CFSG.FeitThompson.Local.TauOnePrimeCentralizerInclusion
import CFSG.FeitThompson.Local.PlaneNormalizerRankTwoPrimesInSigma
import CFSG.FeitThompson.Local.OutsideSigmaPlanePrimesTauOneOrTwo
import CFSG.FeitThompson.Local.SigmaTauThreePrimesDerivedContainment
import CFSG.FeitThompson.OddOrder.FittingSplitsOverHallCore
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

open CFSG.FeitThompson CFSG.FeitThompson Subgroup

universe u

variable {G : Type*} [Group G]

theorem le_normalizer_inf' {K X Y : Subgroup G} (hX : K ≤ normalizer (X : Set G))
    (hY : K ≤ normalizer (Y : Set G)) : K ≤ normalizer ((X ⊓ Y : Subgroup G) : Set G) :=
  fun _ hg => Subgroup.inf_normalizer_le_normalizer_inf (Subgroup.mem_inf.2 ⟨hX hg, hY hg⟩)

theorem inf_eq_bot_of_natCard_prime [Finite G] {p : ℕ} {P C : Subgroup G} (hp : p.Prime)
    (hP : Nat.card P = p) (h : ¬ P ≤ C) : P ⊓ C = ⊥ := by
  have hdvd : Nat.card ↥(P ⊓ C) ∣ p := hP ▸ Subgroup.card_dvd_of_le (inf_le_left : P ⊓ C ≤ P)
  rcases (Nat.dvd_prime hp).1 hdvd with h1 | h2
  · exact Subgroup.card_eq_one.1 h1
  · exact absurd ((Subgroup.eq_of_le_of_card_ge (H := P ⊓ C) (K := P) inf_le_left
      (by rw [hP, h2])) ▸ (inf_le_right : P ⊓ C ≤ C)) h

theorem dvd_relIndex_of_natCard_prime [Finite G] {p : ℕ} {E C P : Subgroup G} (hp : p.Prime)
    (hCnormal : E ≤ normalizer (C : Set G)) (hPE : P ≤ E) (hPcard : Nat.card P = p)
    (hPC : ¬ P ≤ C) : p ∣ C.relIndex E := by
  have hn : (C.subgroupOf E).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hCnormal
  have hPC' : P ⊓ C = ⊥ := inf_eq_bot_of_natCard_prime hp hPcard hPC
  have hdisj : Disjoint (C.subgroupOf E) (P.subgroupOf E) := by
    refine disjoint_iff.2 (le_bot_iff.1 fun x hx => ?_)
    obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.1 hx
    have h1 : (x : G) ∈ C := Subgroup.mem_subgroupOf.1 hx1
    have h2 : (x : G) ∈ P := Subgroup.mem_subgroupOf.1 hx2
    have hb : (x : G) = 1 := Subgroup.mem_bot.1 (hPC' ▸ Subgroup.mem_inf.2 ⟨h2, h1⟩)
    exact Subgroup.mem_bot.2 (Subtype.ext hb)
  have h := natCard_dvd_index_of_disjoint (C.subgroupOf E) (P.subgroupOf E) hdisj
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPE).toEquiv, hPcard,
    ← Subgroup.relIndex] at h

theorem FNI_tau12_double_fixed_reflection
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FBG_tau_two_hall_abelian.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_complement_normalizer.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_core_disjoint.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₆ : _root_.CFSG.FeitThompson.Statements.FTS_admissible_tau_one_prime_centralizer_inclusion.{u})
    (h₇ : _root_.CFSG.FeitThompson.Statements.FTS_outside_sigma_plane_structure.{u}) :
    _root_.CFSG.FeitThompson.Statements.FNI_tau12_double_fixed_reflection.{u} := by
  intro G _ _ hG p q M E P A hE hp hPE hPcard hq hAE hAplane hCA hCS
  have := hG.isSimpleGroup
  let _ : Fintype G := Fintype.ofFinite G
  have hG2 : IsOddOrderMinimalSimple G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hG9 : Prep09.IsMinimalSimpleOddOrder G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  obtain ⟨hqprime, hqσ, hqrank⟩ := mem_tauTwoPrimes_iff.1 hq
  obtain ⟨hpprime, -, hpσ, hprank, -⟩ := mem_tau1Primes_iff.1 hp
  have hOSP : _root_.CFSG.FeitThompson.IsOutsideSigmaPlane q M A :=
    ⟨hE.isCoatom, hqprime, hqσ, hAE.trans hE.le, hAplane⟩
  have hAnormE : E ≤ normalizer (A : Set G) := (h₃ G hG q M A E hOSP hE hAE).1
  have hPnc : ¬ A ≤ centralizer (P : Set G) := fun hle =>
    hCS (FNI_rank_one_plane_centralizer_regular h₄ G hG q M A E hOSP hE hAE p P
      hpprime hpσ hprank (le_inf hPE (Subgroup.le_centralizer_iff.1 hle)) hPcard)
  have hYcard : Nat.card (A ⊓ centralizer (P : Set G) : Subgroup G) = q := by
    have hdvd : Nat.card (A ⊓ centralizer (P : Set G) : Subgroup G) ∣ q ^ 2 :=
      hAplane.natCard' ▸ Subgroup.card_dvd_of_le inf_le_left
    obtain ⟨k, hk, hcard⟩ := (Nat.dvd_prime_pow hqprime).1 hdvd
    interval_cases k
    · rw [pow_zero] at hcard
      exact absurd (Subgroup.card_eq_one.1 hcard) hCA
    · rwa [pow_one] at hcard
    · exfalso
      have heq : (A ⊓ centralizer (P : Set G) : Subgroup G) = A :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hcard, hAplane.natCard'])
      exact hPnc (heq ▸ (inf_le_right : (A ⊓ centralizer (P : Set G) : Subgroup G) ≤ _))
  refine ⟨hYcard, ?_, ?_⟩
  ·
    have hincl := FTS_tau_one_prime_centralizer_inclusion h₆ G hG9 M hE.isCoatom E hE.le
      hE.isInternalSemidirectProduct p q hpprime hqprime hp P hPE hPcard
      (A ⊓ centralizer (P : Set G)) (le_inf (inf_le_left.trans hAE) inf_le_right) hYcard
    rw [Prep09.centIn_def, Prep09.centIn_def] at hincl
    exact (FNI_nonregular_plane_line_unique_centralizer h₃ h₄ G hG q M A E
      (A ⊓ centralizer (P : Set G)) hOSP hE hAE (inf_le_left.trans hAE) hYcard
      fun hbot => hCS (le_bot_iff.1 (hbot ▸ hincl))).1
  · intro T hT hNT
    obtain ⟨hTM, hτσ⟩ := FNI_plane_normalizer_rank_two_primes_in_sigma h₁ h₂ h₃ h₄ h₅ h₇ G hG
      q M A E T hOSP hE hAE hT hNT
    have hET : E ≤ T := hAnormE.trans hNT
    have hAT : A ≤ T := le_trans le_normalizer hNT
    have hqσT : q ∈ sigmaPrimes T := hτσ hq
    refine ⟨hTM, hET, le_sigmaCore_of_isPiSubgroup (h₁ G hG2 T hT).1 hAT
      (isPiSubgroup_of_plane hqprime hqσT hAplane), ?_⟩
    have hCnorm : E ≤ normalizer ((E ⊓ centralizer (A : Set G) : Subgroup G) : Set G) :=
      le_normalizer_inf' le_normalizer (hAnormE.trans (normalizer_le_normalizer_centralizer A))
    have hPnotin : ¬ P ≤ E ⊓ centralizer (A : Set G) := fun hle =>
      hPnc (Subgroup.le_centralizer_iff.1 (hle.trans inf_le_right))
    exact FNI_plane_normalizer_action_prime_transfer h₁ h₂ h₃ h₄ h₅ h₇ G hG q M A E T hOSP hE
      hAE hT hNT p hpprime
      (dvd_relIndex_of_natCard_prime hpprime hCnorm hPE hPcard hPnotin)

end

end CFSG.FeitThompson.Proofs
