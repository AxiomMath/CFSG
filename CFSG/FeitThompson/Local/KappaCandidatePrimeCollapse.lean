module

public import CFSG.FeitThompson.Statements.FittingOverlapKappaStatements
public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.KappaCandidateStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.KappaNontrivialComplementStructure
import CFSG.FeitThompson.Local.KappaFixedPrimeCentralizerSylowUnique
import CFSG.FeitThompson.Local.KappaCandidateMixedSupportCardinality
import CFSG.FeitThompson.Local.KappaResidualInPrescribedComplement
public import CFSG.FeitThompson.Definitions.FittingSubgroupAndNormalSylowHallCore
public import CFSG.FeitThompson.Foundations.CharacteristicSubgroupInvariance
public import CFSG.FeitThompson.Foundations.HallImageQuotient
public import CFSG.FeitThompson.Foundations.HomPreservesGeneratedCommutators
public import CFSG.FeitThompson.Foundations.NilpotenceEquivalentDefinitions
public import CFSG.FeitThompson.Foundations.SolvableHomImageSolvable
public import CFSG.FeitThompson.Foundations.SubgroupOrderAndIndex
public import CFSG.FeitThompson.Local.CoprimeSolvableFixedCosetLifting
public import Mathlib

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup CFSG.FeitThompson CFSG.FeitThompson

universe u

variable {G : Type u} [Group G]

theorem isCoatom_of_mem_kappaFamily {M K T : Subgroup G} (hM : IsCoatom M)
    (hT : T ∈ Prep03.kappaFamily M K) : IsCoatom T := by
  rcases hT with h | h
  · rw [Set.mem_singleton_iff] at h
    exact h ▸ hM
  · exact h.1

theorem isHallPiOf_KT [Fintype G] {M K A Z : Subgroup G} {I : Set (Subgroup G)}
    {KT : Subgroup G → Subgroup G} (hsetup : Prep03.IsKappaFamilySetup G M K A Z I KT)
    {T : Subgroup G} (hT : T ∈ I) : Prep03.IsHallPiOf (kappaPrimes T) (KT T) T := by
  by_cases h : T = M
  · subst h
    rw [hsetup.KT_self]
    exact hsetup.base.isHall_K
  · exact (hsetup.KT_hall T hT h).1

theorem eq_of_le_of_natCard_prime {X Y : Subgroup G} (hXY : X ≤ Y) (hX : X ≠ ⊥)
    (hY : (Nat.card ↥Y).Prime) : X = Y := by
  rcases hY.eq_one_or_self_of_dvd _ (Subgroup.card_dvd_of_le hXY) with h1 | h2
  · exact absurd (Subgroup.card_eq_one.1 h1) hX
  · have : Finite ↥Y := Nat.finite_of_card_ne_zero hY.pos.ne'
    exact Subgroup.eq_of_le_of_card_ge hXY (le_of_eq h2.symm)

theorem FNI_kappa_candidate_prime_collapse
    (h₁ : Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : Statements.FNI_kappa_candidate_family_common_factors.{u})
    (h₃ : Statements.FNI_kappa_candidate_has_nontrivial_residual.{u})
    (h₄ : Statements.FNI_kappa_semiprime_complement_existence.{u})
    (h₅ : Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₆ : Statements.FTS_outside_sigma_plane_structure.{u})
    (h₇ : Statements.FTS_proper_subgroup_p_length_one.{u}) :
    Statements.FNI_kappa_candidate_prime_collapse.{u} := by
  intro G _ _ M K A Z I KT hsetup
  obtain ⟨V, hVI, U, hU, hsemiV, hsemiUK⟩ := h₃ G M K A Z I KT hsetup
  obtain ⟨-, hncard, hfam, -⟩ := h₂ G M K A Z I hsetup.base hsetup.I_eq
  obtain ⟨hκne, hAprops, hpair⟩ := hfam KT hsetup.KT_self hsetup.KT_hall
  have hambient : IsFBGAmbient G :=
    ⟨hsetup.base.ambient.odd_natCard, hsetup.base.ambient.isSimpleGroup,
      hsetup.base.ambient.not_isMulCommutative, hsetup.base.ambient.forall_isSolvable⟩
  have hVcoatom : IsCoatom V :=
    isCoatom_of_mem_kappaFamily hsetup.base.isCoatom (hsetup.I_eq ▸ hVI)
  have hKVhall := isHallPiOf_KT hsetup hVI
  have hUV : U ≤ V := le_trans le_sup_left hsemiV.2.1
  have hresidual : IsKappaResidualSetup V (KT V) U :=
    ⟨hVcoatom, hκne V hVI, hKVhall.1,
      isHallPiSubgroup_subgroupOf_of_isHallPiOf hKVhall, hUV, hU,
      isInternalSemidirectProduct_of_isSemidirect hsemiV,
      isInternalSemidirectProduct_of_isSemidirect hsemiUK⟩
  obtain ⟨hKVprime, -, hnil, -⟩ :=
    FBG_kappa_nontrivial_complement_structure h₁ h₄ h₅ h₆ h₇ G hambient V (KT V) U hresidual
  obtain ⟨W, hWI, hWV⟩ := Set.exists_ne_of_one_lt_ncard (show 1 < I.ncard by omega) V
  have hAW : Prep03.kappaA KT W ≠ ⊥ := (hAprops W hWI).1
  have hAWle : Prep03.kappaA KT W ≤ KT V := (hpair W hWI V hVI hWV).2.1
  have hAWeq : Prep03.kappaA KT W = KT V := eq_of_le_of_natCard_prime hAWle hAW hKVprime
  have hIeq : I = {V, W} := by
    apply Set.eq_of_subset_of_subset
    · intro H hH
      by_contra hne
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hne
      have hAH : Prep03.kappaA KT H ≠ ⊥ := (hAprops H hH).1
      have hAHle : Prep03.kappaA KT H ≤ KT V := (hpair H hH V hVI hne.1).2.1
      have hinf : Prep03.kappaA KT H ⊓ Prep03.kappaA KT W = ⊥ := (hpair H hH W hWI hne.2).1
      rw [← hAWeq] at hAHle
      exact hAH (le_bot_iff.1 (hinf ▸ le_inf (le_refl (Prep03.kappaA KT H)) hAHle))
    · intro H hH
      rcases hH with h | h
      · exact h ▸ hVI
      · exact (Set.mem_singleton_iff.1 h) ▸ hWI
  have hZV : Nat.card ↥Z = Nat.card ↥(KT V) * Nat.card ↥(Prep03.kappaA KT V) :=
    natCard_of_isDirect (hAprops V hVI).2.1
  have hZW : Nat.card ↥Z = Nat.card ↥(KT W) * Nat.card ↥(Prep03.kappaA KT W) :=
    natCard_of_isDirect (hAprops W hWI).2.1
  have hcards : Nat.card ↥(KT V) * Nat.card ↥(Prep03.kappaA KT V)
      = Nat.card ↥(KT V) * Nat.card ↥(KT W) := by
    rw [← hZV, hZW, hAWeq, Nat.mul_comm]
  have hAVcard : Nat.card ↥(Prep03.kappaA KT V) = Nat.card ↥(KT W) :=
    Nat.eq_of_mul_eq_mul_left hKVprime.pos hcards
  have hAVle : Prep03.kappaA KT V ≤ KT W := (hpair V hVI W hWI (Ne.symm hWV)).2.1
  have hAVeq : Prep03.kappaA KT V = KT W :=
    Subgroup.eq_of_le_of_card_ge hAVle (le_of_eq hAVcard.symm)
  exact ⟨V, hVI, W, hWI, Ne.symm hWV, hIeq, U, hU, hsemiV, hsemiUK, hKVprime, hnil,
    hAWeq, hAVeq⟩

end

end CFSG.FeitThompson.Proofs
