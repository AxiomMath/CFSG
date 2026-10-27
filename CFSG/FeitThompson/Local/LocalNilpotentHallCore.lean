module

public import CFSG.FeitThompson.Statements.FittingOverlapKappaStatements
public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.KappaCandidateStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.Local.NilpotentSigmaCoreFittingStructure
import CFSG.FeitThompson.Local.NonnilpotentSigmaCoreHallStructure
import CFSG.FeitThompson.Local.ResidualComplementNilpotentCore
import CFSG.FeitThompson.Local.KappaDerivedComplement
import CFSG.FeitThompson.Local.SigmaCoreNontrivial
import CFSG.FeitThompson.Local.HallKappaSubgroupTI
import CFSG.FeitThompson.Local.MaximalTauTwoNonemptyTypeIOrII
import CFSG.FeitThompson.Local.FittingOverlapPrimeCentralizerSmall
import CFSG.FeitThompson.Local.FittingSharpTISetNormalizer
import CFSG.FeitThompson.Local.HallCoreInSigmaCore
import CFSG.FeitThompson.Foundations.NormalHallContainsPiSubgroups

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup Pointwise _root_.CFSG.FeitThompson

universe u

variable {G : Type u} [Group G]

theorem kappaPrimes_nonempty_of_isHallPiSubgroup_ne_bot [Finite G] {M K : Subgroup G} (hKM : K ≤ M)
    (hK : IsHallPiSubgroup (kappaPrimes M) (K.subgroupOf M)) (hKbot : K ≠ ⊥) :
    (kappaPrimes M).Nonempty := by
  obtain ⟨p, hp, hpK⟩ := Nat.exists_prime_and_dvd (n := Nat.card ↥K)
    (fun h => hKbot (Subgroup.card_eq_one.1 h))
  refine ⟨p, isPiSubgroup_iff.1 hK.isPiSubgroup p ?_⟩
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv]
  exact Nat.mem_primeFactors.2 ⟨hp, hpK, Nat.card_pos.ne'⟩

theorem natCard_eq_commutator_mul_of_isLocalKappaSetup
    (h₃ : _root_.CFSG.FeitThompson.Statements.FNI_kappa_local_pair.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FNI_kappa_semiprime_complement_existence.{u})
    [Finite G] (hG : IsFBGAmbient G) {M K U : Subgroup G}
    (hsetup : IsLocalKappaSetup M K U) (hKbot : K ≠ ⊥) :
    Nat.card ↥M = Nat.card ↥(⁅M, M⁆ : Subgroup G) * Nat.card ↥K := by
  have _i : Fintype G := Fintype.ofFinite G
  have hamb : Prep03.IsAmbient G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable⟩
  have hsetup03 : Prep03.IsKappaSetup G M K (Prep03.cent (sigmaCore M) (K : Set G))
      (K ⊔ Prep03.cent (sigmaCore M) (K : Set G)) :=
    { ambient := hamb
      isCoatom := hsetup.isCoatom
      kappa_nonempty :=
        kappaPrimes_nonempty_of_isHallPiSubgroup_ne_bot hsetup.le_M_K hsetup.hall_K hKbot
      isHall_K := isHallPiOf_of_isHallPiSubgroupOf ⟨hsetup.le_M_K, hsetup.hall_K⟩
      A_eq := rfl
      Z_eq := rfl }
  obtain ⟨hmain, -, -⟩ :=
    _root_.CFSG.FeitThompson.Proofs.FNI_kappa_derived_complement h₃ h₅ G M K _ _ hsetup03
  exact natCard_of_isSemidirect hmain

theorem le_commutator_of_forall_notMem_kappaPrimes [Finite G] {M K Y : Subgroup G}
    (hKM : K ≤ M) (hK : IsHallPiSubgroup (kappaPrimes M) (K.subgroupOf M))
    (hcard : Nat.card ↥M = Nat.card ↥(⁅M, M⁆ : Subgroup G) * Nat.card ↥K)
    (hYM : Y ≤ M) (hY : ∀ p ∈ (Nat.card ↥Y).primeFactors, p ∉ kappaPrimes M) :
    Y ≤ ⁅M, M⁆ := by
  have hmap : (_root_.commutator ↥M).map M.subtype = (⁅M, M⁆ : Subgroup G) :=
    Subgroup.map_subtype_commutator M
  have hcardC : Nat.card ↥(_root_.commutator ↥M) = Nat.card ↥(⁅M, M⁆ : Subgroup G) := by
    rw [← hmap, Subgroup.card_map_of_injective M.subtype_injective]
  have hcardK : Nat.card ↥(K.subgroupOf M) = Nat.card ↥K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv
  have hidx : (_root_.commutator ↥M).index = Nat.card ↥K := by
    have h1 : Nat.card ↥(_root_.commutator ↥M) * (_root_.commutator ↥M).index = Nat.card ↥M :=
      Subgroup.card_mul_index _
    rw [hcardC, hcard] at h1
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h1
  have hidxK : (K.subgroupOf M).index = Nat.card ↥(⁅M, M⁆ : Subgroup G) := by
    have h1 : Nat.card ↥(K.subgroupOf M) * (K.subgroupOf M).index = Nat.card ↥M :=
      Subgroup.card_mul_index _
    rw [hcardK, hcard, mul_comm (Nat.card ↥(⁅M, M⁆ : Subgroup G))] at h1
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h1
  have hHall : IsHallPiSubgroup ((kappaPrimes M)ᶜ) (_root_.commutator ↥M) := by
    constructor
    · refine isPiSubgroup_iff.2 fun p hp => ?_
      refine hK.notMem_of_mem_primeFactors_index p ?_
      rw [hidxK, ← hcardC]; exact hp
    · intro p hp hpc
      rw [hidx] at hp
      exact hpc (isPiSubgroup_iff.1 hK.isPiSubgroup p (by rwa [hcardK]))
  have hYpi : IsPiSubgroup ((kappaPrimes M)ᶜ) (Y.subgroupOf M) := by
    refine isPiSubgroup_iff.2 fun p hp => ?_
    exact hY p (by rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYM).toEquiv] at hp)
  have hle := hHall.le_of_isPiSubgroup hYpi
  have hmapped := Subgroup.map_mono (f := M.subtype) hle
  rwa [Subgroup.map_subgroupOf_eq_of_le hYM, hmap] at hmapped

theorem ne_bot_mixedFitting_of_coe_eq_mul [Finite G] {M : Subgroup G}
    (hprod : (mixedFitting M : Set G) = (hallCoreIn M : Set G) *
      ((centralizerWithin M (hallCoreIn M) : Subgroup G) : Set G))
    (hH : ⊥ < hallCoreIn M) : mixedFitting M ≠ ⊥ := by
  obtain ⟨x, hx⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 (bot_lt_iff_ne_bot.1 hH)
  intro hbot
  have hmem : (x : G) ∈ (mixedFitting M : Set G) := by
    rw [hprod]
    simpa using Set.mul_mem_mul x.2 (one_mem (centralizerWithin M (hallCoreIn M)))
  rw [hbot] at hmem
  exact hx (Subtype.ext (by simpa using hmem))

theorem structure_of_isNilpotent_sigmaCore
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FBG_tau_two_hall_abelian.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FNI_kappa_local_pair.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FNI_kappa_normalizer_centralizer_structure.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FNI_kappa_semiprime_complement_existence.{u})
    (h₇ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₈ : _root_.CFSG.FeitThompson.Statements.FTS_outside_sigma_plane_structure.{u})
    (h₉ : _root_.CFSG.FeitThompson.Statements.FTS_tau_one_fixed_line_centralizer_unique.{u})
    [Finite G] (hG : IsFBGAmbient G) {M K U : Subgroup G}
    (hsetup : IsLocalKappaSetup M K U) (hnil : Group.IsNilpotent ↥(sigmaCore M)) :
    ⊥ < hallCoreIn M ∧ hallCoreIn M ≤ sigmaCore M ∧ sigmaCore M ≤ ⁅M, M⁆ ∧
      IsNilpotentQuotient (⁅M, M⁆ : Subgroup G) (hallCoreIn M) ∧
      ⁅(⁅M, M⁆ : Subgroup G), (⁅M, M⁆ : Subgroup G)⁆ ≤ mixedFitting M ∧
      ((mixedFitting M : Set G) = (hallCoreIn M : Set G) *
        ((centralizerWithin M (hallCoreIn M) : Subgroup G) : Set G)) ∧
      (K ≠ ⊥ → mixedFitting M ≤ ⁅M, M⁆) := by
  have _i : Fintype G := Fintype.ofFinite G
  have hGmin : IsOddOrderMinimalSimple G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable⟩
  obtain ⟨Y, hY⟩ :=
    exists_isSylowProduct (mixedFitting M) {p : ℕ | p.Prime ∧ p ∉ sigmaPrimes M}
  obtain ⟨hHS, -, -, hYτ, hdir, hprod, -, hquot, hM''⟩ :=
    _root_.CFSG.FeitThompson.Proofs.FBG_nilpotent_sigma_core_fitting_structure h₁ h₂ h₄ h₅ h₇ h₈ h₉
      G hG M hsetup.isCoatom hnil Y hY
  have hSle : sigmaCore M ≤ (⁅M, M⁆ : Subgroup G) := (h₁ G hGmin M hsetup.isCoatom).2.2
  have hSne : sigmaCore M ≠ ⊥ :=
    (_root_.CFSG.FeitThompson.Proofs.FBG_sigma_core_nontrivial h₁ G hGmin M hsetup.isCoatom).2
  refine ⟨by rw [hHS]; exact bot_lt_iff_ne_bot.2 hSne, hHS.le, hSle,
    hquot.isNilpotentQuotient, hM''.trans hdir.left_le, by rw [hHS]; exact hprod,
    fun hKbot => ?_⟩
  have hcard := natCard_eq_commutator_mul_of_isLocalKappaSetup h₃ h₅ hG hsetup hKbot
  have hYM : Y ≤ M := hdir.right_le.trans (mixedFitting_le M)
  have hYle : Y ≤ (⁅M, M⁆ : Subgroup G) :=
    le_commutator_of_forall_notMem_kappaPrimes hsetup.le_M_K hsetup.hall_K hcard hYM
      fun p hp => _root_.CFSG.FeitThompson.Proofs.notMem_kappaPrimes_of_mem_tauTwoPrimes (hYτ hp)
  rw [← hdir.sup_eq]
  exact sup_le hSle hYle

theorem structure_of_not_isNilpotent_sigmaCore
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FNI_kappa_semiprime_complement_existence.{u})
    (h₆ : _root_.CFSG.FeitThompson.Statements.FNI_kappa_trivial_residual_prime_fixed_core.{u})
    (h₇ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₈ : _root_.CFSG.FeitThompson.Statements.FTS_outside_sigma_plane_structure.{u})
    [Finite G] (hG : IsFBGAmbient G) {M K U : Subgroup G}
    (hsetup : IsLocalKappaSetup M K U) (hnil : ¬ Group.IsNilpotent ↥(sigmaCore M)) :
    (⊥ < hallCoreIn M ∧ hallCoreIn M ≤ sigmaCore M ∧ sigmaCore M ≤ ⁅M, M⁆ ∧
        IsNilpotentQuotient (⁅M, M⁆ : Subgroup G) (hallCoreIn M) ∧
        ⁅(⁅M, M⁆ : Subgroup G), (⁅M, M⁆ : Subgroup G)⁆ ≤ mixedFitting M ∧
        ((mixedFitting M : Set G) = (hallCoreIn M : Set G) *
          ((centralizerWithin M (hallCoreIn M) : Subgroup G) : Set G)) ∧
        (K ≠ ⊥ → mixedFitting M ≤ ⁅M, M⁆)) ∧
      U = ⊥ ∧ (Nat.card ↥K).Prime ∧ IsTIWithNormalizer (sharp (mixedFitting M)) M := by
  have _i : Fintype G := Fintype.ofFinite G
  have hGmin : IsOddOrderMinimalSimple G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable⟩
  obtain ⟨-, hKclause, hHbot, hHS, hSeq, hquot, hcomm, hprod, hFlt, hnorm, hTI⟩ :=
    _root_.CFSG.FeitThompson.Proofs.FBG_nonnilpotent_sigma_core_hall_structure h₁ h₅ h₆ h₇ h₈
      G hG M hsetup.isCoatom hnil
  obtain ⟨-, hKprime, -⟩ := hKclause K hsetup.le_M_K hsetup.hall_K
  have hHne : hallCoreIn M ≠ sigmaCore M := fun h =>
    hnil ((_root_.CFSG.FeitThompson.Proofs.FBG_normal_hall_core_sigma_containment.{u}
      G hG M hsetup.isCoatom).2.1 h)
  have hUbot : U = ⊥ :=
    (_root_.CFSG.FeitThompson.Proofs.FBG_residual_complement_nilpotent_core h₁ h₇ h₈ G hGmin M
      hsetup.isCoatom K U ⟨hsetup.le_M_K, hsetup.hall_K⟩ hsetup.le_M_U hsetup.semidirect_M
      hsetup.semidirect_UK).2 hHne
  exact ⟨⟨hHbot, hHS.le, hSeq.le, hquot, hcomm, hprod, fun _ => hFlt.le⟩, hUbot, hKprime,
    isTIWithNormalizer_sharp_mixedFitting hnorm
      (ne_bot_mixedFitting_of_coe_eq_mul hprod hHbot) hTI⟩

end

end CFSG.FeitThompson

namespace CFSG.FeitThompson.Proofs

public section

open Subgroup CFSG.FeitThompson
open CFSG.FeitThompson

universe u

theorem FBG_local_nilpotent_hall_core
    (h₁ : Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : Statements.FBG_tau_two_hall_abelian.{u})
    (h₃ : Statements.FNI_kappa_local_pair.{u})
    (h₄ : Statements.FNI_kappa_normalizer_centralizer_structure.{u})
    (h₅ : Statements.FNI_kappa_semiprime_complement_existence.{u})
    (h₆ : Statements.FNI_kappa_trivial_residual_prime_fixed_core.{u})
    (h₇ : Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₈ : Statements.FTS_outside_sigma_plane_structure.{u})
    (h₉ : Statements.FTS_tau_one_fixed_line_centralizer_unique.{u}) :
    Statements.FBG_local_nilpotent_hall_core.{u} := by
  intro G _ _ hG M K U hsetup
  by_cases hnil : Group.IsNilpotent ↥(sigmaCore M)
  ·
    refine ⟨structure_of_isNilpotent_sigmaCore h₁ h₂ h₃ h₄ h₅ h₇ h₈ h₉ hG hsetup hnil,
      fun hHne => absurd ?_ hHne⟩
    exact (FBG_normal_hall_core_sigma_containment.{u} G hG M hsetup.isCoatom).2.2 hnil
  · obtain ⟨hmain, hrest⟩ :=
      structure_of_not_isNilpotent_sigmaCore h₁ h₅ h₆ h₇ h₈ hG hsetup hnil
    exact ⟨hmain, fun _ => hrest⟩

end

end CFSG.FeitThompson.Proofs
