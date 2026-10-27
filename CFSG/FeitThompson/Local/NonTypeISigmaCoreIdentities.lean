module

public import CFSG.FeitThompson.Statements.FittingOverlapKappaStatements
public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.KappaCandidateStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.TauThirteenTypeIStatements
public import CFSG.FeitThompson.Statements.KappaResidualCoreStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.KappaComplementStructure
import CFSG.FeitThompson.Local.ResidualComplementNilpotentCore
public import CFSG.FeitThompson.Definitions.FittingSubgroupAndNormalSylowHallCore
public import CFSG.FeitThompson.Definitions.KernelFilteredIrreducibleCharacters
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

open CFSG.FeitThompson Subgroup Pointwise

universe u

theorem localTypes_eq {G : Type u} [Group G] [Finite G]
    (huniq : ∀ M : Subgroup G, IsCoatom M →
      ∃! i : Fin 5, CFSG.FeitThompson.localTypes M i)
    {M : Subgroup G} (hM : IsCoatom M) {j l : Fin 5}
    (hj : CFSG.FeitThompson.localTypes M j)
    (hl : CFSG.FeitThompson.localTypes M l) : j = l := by
  obtain ⟨i, -, hu⟩ := huniq M hM
  rw [hu j hj, hu l hl]

theorem sigmaCore_eq_hallCoreOf_of_isTypeII
    (h₁ : Statements.FBG_five_type_local_classification.{u})
    (h₃ : Statements.FBG_sigma_core_normal_hall.{u})
    (h₄ : Statements.FNI_kappa_local_pair.{u})
    (h₅ : Statements.FNI_kappa_semiprime_complement_existence.{u})
    (h₆ : Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₇ : Statements.FTS_kappa_residual_prime_overgroup_intersection.{u})
    (h₈ : Statements.FTS_outside_sigma_plane_structure.{u})
    {G : Type u} [Group G] [Finite G]
    (hG : CFSG.FeitThompson.Prep05.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : IsCoatom M) (htII : IsTypeII M) :
    sigmaCore M = CFSG.FeitThompson.Prep05.hallCoreOf M := by
  have hamb : CFSG.FeitThompson.IsFBGAmbient G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  obtain ⟨K, U, hKM, -, hKhall, hUM, hsdM, hsdUK, -, -⟩ :=
    FBG_kappa_complement_structure h₄ h₅ h₇ G hamb M hM
  have hsetup : CFSG.FeitThompson.IsLocalKappaSetup M K U :=
    { isCoatom := hM
      le_M_K := hKM
      hall_K := hKhall
      le_M_U := hUM
      le_normalizer_U := hsdUK.right_le_normalizer
      semidirect_M := hsdM
      semidirect_UK := hsdUK }
  obtain ⟨-, hII, -⟩ := (h₁ G hamb).2 M K U hsetup
  obtain ⟨-, hUne⟩ := hII.1 htII
  have _fin : Fintype G := Fintype.ofFinite G
  have hG' : CFSG.FeitThompson.IsOddOrderMinimalSimple G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  obtain ⟨hmain, -⟩ := FBG_residual_complement_nilpotent_core h₃ h₆ h₈ G hG' M hM K U
    ⟨hKM, hKhall⟩ hUM hsdM hsdUK
  rw [CFSG.FeitThompson.Prep05.hallCoreOf_eq]
  exact ((hmain hUne).2.1).symm.trans
    (CFSG.FeitThompson.hallCoreIn_eq M)

theorem sigmaCore_eq_commutator_of_isTypeIII_IV_V
    (h₁ : Statements.FBG_five_type_local_classification.{u})
    (h₂ : Statements.FBG_local_p_core_centralizer.{u})
    (h₄ : Statements.FNI_kappa_local_pair.{u})
    (h₅ : Statements.FNI_kappa_semiprime_complement_existence.{u})
    (h₇ : Statements.FTS_kappa_residual_prime_overgroup_intersection.{u})
    {G : Type u} [Group G] [Finite G]
    (hG : CFSG.FeitThompson.Prep05.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : IsCoatom M)
    (htype : IsTypeIII M ∨ IsTypeIV M ∨ IsTypeV M) :
    sigmaCore M = (⁅M, M⁆ : Subgroup G) := by
  have hamb : CFSG.FeitThompson.IsFBGAmbient G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  obtain ⟨K, U, hKM, -, hKhall, hUM, hsdM, hsdUK, -, -⟩ :=
    FBG_kappa_complement_structure h₄ h₅ h₇ G hamb M hM
  have hsetup : CFSG.FeitThompson.IsLocalKappaSetup M K U :=
    { isCoatom := hM
      le_M_K := hKM
      hall_K := hKhall
      le_M_U := hUM
      le_normalizer_U := hsdUK.right_le_normalizer
      semidirect_M := hsdM
      semidirect_UK := hsdUK }
  obtain ⟨huniq, hequiv⟩ := h₁ G hamb
  obtain ⟨hI, hII, -⟩ := hequiv M K U hsetup
  have hnotI : ¬ IsTypeI M := by
    intro hIt
    rcases htype with h | h | h
    · exact absurd (localTypes_eq huniq hM (j := 0) (l := 2) hIt h) (by decide)
    · exact absurd (localTypes_eq huniq hM (j := 0) (l := 3) hIt h) (by decide)
    · exact absurd (localTypes_eq huniq hM (j := 0) (l := 4) hIt h) (by decide)
  have hnotII : ¬ IsTypeII M := by
    intro hIIt
    rcases htype with h | h | h
    · exact absurd (localTypes_eq huniq hM (j := 1) (l := 2) hIIt h) (by decide)
    · exact absurd (localTypes_eq huniq hM (j := 1) (l := 3) hIIt h) (by decide)
    · exact absurd (localTypes_eq huniq hM (j := 1) (l := 4) hIIt h) (by decide)
  have hKne : K ≠ ⊥ := fun hb => hnotI (hI.2 hb)
  have hUbot : U = ⊥ := by
    by_contra hUne
    exact hnotII (hII.2 ⟨hKne, hUne⟩)
  obtain ⟨-, -, -, -, hprod, -⟩ := h₂ G hamb M K U hsetup hKne
  refine (SetLike.coe_injective ?_).symm
  rw [hprod, hUbot]
  simp

theorem FPF_non_type_i_sigma_core_identities
    (h₁ : Statements.FBG_five_type_local_classification.{u})
    (h₂ : Statements.FBG_local_p_core_centralizer.{u})
    (h₃ : Statements.FBG_sigma_core_normal_hall.{u})
    (h₄ : Statements.FNI_kappa_local_pair.{u})
    (h₅ : Statements.FNI_kappa_semiprime_complement_existence.{u})
    (h₆ : Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₇ : Statements.FTS_kappa_residual_prime_overgroup_intersection.{u})
    (h₈ : Statements.FTS_outside_sigma_plane_structure.{u}) :
    Statements.FPF_non_type_i_sigma_core_identities.{u} :=
  fun _G _ _ hG _M hM =>
    ⟨fun htII => sigmaCore_eq_hallCoreOf_of_isTypeII h₁ h₃ h₄ h₅ h₆ h₇ h₈ hG hM htII,
      fun htype => sigmaCore_eq_commutator_of_isTypeIII_IV_V h₁ h₂ h₄ h₅ h₇ hG hM htype⟩

end

end CFSG.FeitThompson.Proofs
