module

public import CFSG.FeitThompson.Statements.KappaCandidateStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.TauThirteenTypeIStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.OddOrder.PairedCompatibleComplements
import CFSG.FeitThompson.OddOrder.MaximalOvergroupExistence
import CFSG.FeitThompson.OddOrder.SimpleSolvableNormalizerProper
import CFSG.FeitThompson.Local.PairedFullSupportForcesFieldAction
import CFSG.FeitThompson.Local.PairedFullSupportInnerNotCharacteristic
import CFSG.FeitThompson.Local.OppositeSupportingKernelEquality
import CFSG.FeitThompson.Local.OrderedFieldPairOrderEstimates
import CFSG.FeitThompson.Representations.TypeIPBridgeOrthogonality
import CFSG.FeitThompson.Local.PairedSupportingCrossedAlternatives
import CFSG.FeitThompson.Representations.ActualTypeICrossedControl
import CFSG.FeitThompson.Local.FieldPConfigurationPrimeSupport
import CFSG.FeitThompson.Local.TypePMaximalPrimeFactors
import CFSG.FeitThompson.Local.AllTypeIKernelPartition

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace OrderedPairExclusion

open Subgroup

universe u

variable {G : Type u} [Group G]

theorem prep03_hallCoreIn_eq (X : Subgroup G) :
    CFSG.FeitThompson.Prep03.hallCoreIn X = _root_.CFSG.FeitThompson.hallCoreIn X := (rfl)

theorem indFamNonprincipal_eq_hallIndFamily [Fintype G] (X : Subgroup G) :
    _root_.CFSG.FeitThompson.indFamNonprincipal X = CFSG.FeitThompson.Prep03.hallIndFamily X := by
  rw [indFamNonprincipal_eq_calLFam X, ← _root_.CFSG.FeitThompson.Proofs.hallIndFamily_eq_calLFam X]

theorem exists_isCoreCharData
    (h : _root_.CFSG.FeitThompson.Statements.FCH_type_I_frobenius_coherent_family.{u})
    (G : Type u) [Group G] [Fintype G] (hamb : CFSG.FeitThompson.Prep03.IsAmbient G)
    {X : Subgroup G} (hX : IsCoatom X) (hXI : IsTypeI X) :
    ∃ (ν : (↥X → ℂ) → (G → ℂ)) (φ : ↥X → ℂ) (β : G → ℂ),
      _root_.CFSG.FeitThompson.IsCoreCharData X ν φ β := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, ⟨ν, hν⟩, φ, hφmem, hφ1⟩ := h G hamb X hX hXI
  have hset := indFamNonprincipal_eq_hallIndFamily (G := G) X
  refine ⟨ν, φ, _, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
  · intro f g hf hg
    rw [hset] at hf hg
    exact hν.1.1 f hf g hg
  · intro f hf
    rw [hset] at hf
    exact hν.1.2.1 f hf
  · intro f g hf hg
    rw [hset] at hf hg
    refine (hν.1.2.2 f hf g hg).trans ?_
    congr 1
    exact Subsingleton.elim _ _
  · intro f hf hf1
    rw [hset] at hf
    rw [hν.2 f hf hf1, coreTau_eq_tauDade X f, _root_.CFSG.FeitThompson.Proofs.tauDade_eq_tauHall X f]
  · rw [hset]; exact hφmem
  · rw [hφ1, prep03_hallCoreIn_eq X,
      _root_.CFSG.FeitThompson.Proofs.CrossedTypeI.index_hallCore_eq_relIndex]

theorem isIrreducibleConjAction_of_isPairedSupportingSetup
    (h₅ : _root_.CFSG.FeitThompson.Statements.FCH_type_p_action_kernel_ratio.{u})
    (h₈ : _root_.CFSG.FeitThompson.Statements.FNI_type_p_elementary_core_structure.{u})
    (h₁₀ : _root_.CFSG.FeitThompson.Statements.FTS_type_II_extended_support_ti.{u})
    [Finite G] (hG : CFSG.FeitThompson.Prep05.IsMinimalSimpleOdd G)
    {S T L U V W₁ W₂ : Subgroup G} {y : G}
    (hsetup : _root_.CFSG.FeitThompson.IsPairedSupportingSetup S T L U V W₁ W₂ y) :
    CFSG.FeitThompson.IsIrreducibleConjAction U (CFSG.FeitThompson.hallCoreIn S) (Nat.card ↥W₂) := by
  have hG4 : _root_.CFSG.FeitThompson.IsOddSimpleMinimal G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hmodel := OrderedFieldPairEstimates.nonempty_mulEquiv_hallCoreOf h₈ hG
    hsetup.isCoatom_S hsetup.config_S
  have hfield := _root_.CFSG.FeitThompson.Proofs.FNI_paired_full_support_forces_field_action h₅ h₈ h₁₀
    G hG4 S T L U V W₁ W₂ y hsetup
  rw [CFSG.FeitThompson.isIrreducibleConjAction_iff]
  refine ⟨⟨Nat.card ↥W₁, Nat.one_le_iff_ne_zero.2 Nat.card_pos.ne', ?_⟩, ?_⟩
  · rw [hallCoreIn_eq_hallCoreOf S]
    exact hmodel
  · intro K hK hnorm
    have hK' : K ≤ _root_.CFSG.FeitThompson.hallCoreIn S := by
      exact hK
    have hinv : ∀ u ∈ U, _root_.CFSG.FeitThompson.conjSubgroup K u ≤ K := by
      intro u hu x hx
      rw [_root_.CFSG.FeitThompson.mem_conjSubgroup'] at hx
      exact ((Subgroup.mem_set_normalizer_iff.1 (hnorm hu)) x).2 hx
    have := hfield K hK' hinv
    exact this

theorem main
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_five_type_local_classification.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FBG_type_II_supporting_maximal_configuration.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FCH_actual_paired_support_saturation.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FCH_type_I_frobenius_coherent_family.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FCH_type_p_action_kernel_ratio.{u})
    (h₆ : _root_.CFSG.FeitThompson.Statements.FNI_ordered_pair_full_supporting_complement.{u})
    (h₇ : _root_.CFSG.FeitThompson.Statements.FNI_paired_supporting_kernel_collapse.{u})
    (h₈ : _root_.CFSG.FeitThompson.Statements.FNI_type_p_elementary_core_structure.{u})
    (h₉ : _root_.CFSG.FeitThompson.Statements.FPF_ordered_reciprocal_maxima_type_two.{u})
    (h₁₀ : _root_.CFSG.FeitThompson.Statements.FTS_type_II_extended_support_ti.{u}) :
    _root_.CFSG.FeitThompson.Statements.FPF_ordered_pair_exclusion.{u} := by
  intro G _ _ hG S T W₁ W₂ hS hT hST hW₁ hW₂ hcyc₁ hcyc₂ hdp hcs hsdS hsdT hinf hTI htS htT hII
    hcov hlt
  have _iF : Fintype G := Fintype.ofFinite G
  have _iS : IsSimpleGroup G := hG.isSimpleGroup
  have hG1 : CFSG.FeitThompson.IsFBGAmbient G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hG3 : CFSG.FeitThompson.Prep03.IsAmbient G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hG4 : _root_.CFSG.FeitThompson.IsOddSimpleMinimal G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hpair : IsTypePPair S T W₁ W₂ :=
    { odd_natCard := hG.odd_natCard
      isSimpleGroup := hG.isSimpleGroup
      not_isMulCommutative := hG.not_isMulCommutative
      isSolvable := hG.isSolvable_of_ne_top
      isCoatom_left := hS
      isCoatom_right := hT
      ne := hST
      ne_bot_left := hW₁
      ne_bot_right := hW₂
      isCyclic_left := hcyc₁
      isCyclic_right := hcyc₂
      isInternalDirectProduct := hdp
      isCyclic_sup := hcs
      sup_commutator_left := hsdS.sup_eq
      disjoint_commutator_left := hsdS.disjoint
      sup_commutator_right := hsdT.sup_eq
      disjoint_commutator_right := hsdT.disjoint
      inf_eq := hinf
      isTIWithNormalizer := hTI
      typeIIToV_left := htS
      typeIIToV_right := htT
      typeII := hII
      conj_of_not_isTypeI := fun N hN hNI =>
        (hcov N hN hNI).imp
          (fun h => isConjugateSubgroup_iff_smul.1 (isConjugateSubgroup_symm h))
          (fun h => isConjugateSubgroup_iff_smul.1 (isConjugateSubgroup_symm h)) }
  obtain ⟨U, hUS, V, hVT, ⟨hcU, -⟩, hcV, -⟩ := hpair.exists_compatible_pair
  obtain ⟨hIIS, hIIT⟩ := h₉ G hG S T U V W₁ W₂ hS hT hcU hcV hlt
  obtain ⟨-, hpp, hqp, hpo, hqo, -, hUne, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ :=
    h₈ G hG S U W₁ W₂ hS hcU (Nat.card ↥W₂) (Nat.card ↥W₁) rfl rfl
  obtain ⟨-, -, -, -, -, -, hVne, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ :=
    h₈ G hG T V W₂ W₁ hT hcV (Nat.card ↥W₁) (Nat.card ↥W₂) rfl rfl
  have hcov4 : ∀ N : Subgroup G, IsCoatom N → ¬ IsTypeI N →
      (∃ g : G, _root_.CFSG.FeitThompson.conjSubgroup S g = N) ∨
        (∃ g : G, _root_.CFSG.FeitThompson.conjSubgroup T g = N) := by
    intro N hN hNI
    rcases hcov N hN hNI with ⟨g, hg⟩ | ⟨g, hg⟩
    · exact Or.inl ⟨g⁻¹, by rw [_root_.CFSG.FeitThompson.conjSubgroup_eq, inv_inv, hg]; rfl⟩
    · exact Or.inr ⟨g⁻¹, by rw [_root_.CFSG.FeitThompson.conjSubgroup_eq, inv_inv, hg]; rfl⟩
  have hcov1 : ∀ N : Subgroup G, IsCoatom N → ¬ IsTypeI N →
      (∃ g : G, CFSG.FeitThompson.conjSubgroup N g = S) ∨ (∃ g : G, CFSG.FeitThompson.conjSubgroup N g = T) := by
    intro N hN hNI
    rcases hcov N hN hNI with ⟨g, hg⟩ | ⟨g, hg⟩
    · refine Or.inl ⟨g, ?_⟩
      rw [CFSG.FeitThompson.conjSubgroup_eq, hg]
      exact map_conj_map_conj_inv_cancel S g
    · refine Or.inr ⟨g, ?_⟩
      rw [CFSG.FeitThompson.conjSubgroup_eq, hg]
      exact map_conj_map_conj_inv_cancel T g
  have hUtop : U ≠ ⊤ := fun h => hS.1 (top_le_iff.1 (h ▸ hUS))
  have hVtop : V ≠ ⊤ := fun h => hT.1 (top_le_iff.1 (h ▸ hVT))
  have _iU : Group.IsSolvable ↥U := hG.isSolvable_of_ne_top U hUtop
  have _iV : Group.IsSolvable ↥V := hG.isSolvable_of_ne_top V hVtop
  obtain ⟨L, hL, hNUL⟩ := exists_isCoatom_ge_of_ne_top
    (ne_of_lt (normalizer_coe_lt_top_of_isSolvable_of_finite hG.not_isMulCommutative hUne))
  obtain ⟨M, hM, hNVM⟩ := exists_isCoatom_ge_of_ne_top
    (ne_of_lt (normalizer_coe_lt_top_of_isSolvable_of_finite hG.not_isMulCommutative hVne))
  obtain ⟨-, hIL, hUH, y, hyQ, hsdL, hfreeL, hidxL⟩ :=
    h₆ G hG4 S T U V W₁ W₂ L hS hT hST hcU hcV hcs hinf hcov4 hlt hL hNUL
  have hsetup : _root_.CFSG.FeitThompson.IsPairedSupportingSetup S T L U V W₁ W₂ y :=
    { isCoatom_S := hS
      isCoatom_T := hT
      ne_S_T := hST
      config_S := hcU
      config_T := hcV
      isTypeII_S := hIIS
      natCard_lt := hlt
      isCoatom_L := hL
      le_hallCoreIn_L := hUH
      mem_y := hyQ
      isInternalSemidirectProduct := hsdL
      centralizer_eq_bot := hfreeL }
  have hOSP : CFSG.FeitThompson.IsOppositeSupportingPair S T U V W₁ W₂
      (Nat.card ↥W₂) (Nat.card ↥W₁) :=
    { base :=
        { isCoatom_S := hS
          isCoatom_T := hT
          ne := hST
          pconfig_S := hcU
          pconfig_T := hcV
          natCard_W₂ := rfl
          natCard_W₁ := rfl
          prime_p := hpp
          prime_q := hqp
          odd_p := hpo
          odd_q := hqo
          lt := hlt
          irreducible :=
            isIrreducibleConjAction_of_isPairedSupportingSetup h₅ h₈ h₁₀ hG hsetup }
      isTypeII_S := hIIS
      isTypeII_T := hIIT
      isCyclic_sup := hcs
      inf_eq := hinf
      conj_of_not_isTypeI := hcov1 }
  obtain ⟨hIM, hHMV, hidxM, -⟩ :=
    _root_.CFSG.FeitThompson.Proofs.FBG_opposite_supporting_kernel_equality h₁ h₂ h₃ h₄ h₅ h₈
      G hG1 S T U V W₁ W₂ (Nat.card ↥W₂) (Nat.card ↥W₁) hOSP M hM hNVM
  have hHMV' : _root_.CFSG.FeitThompson.hallCoreIn M = V := by
    exact hHMV
  have hidxM' : (_root_.CFSG.FeitThompson.hallCoreIn M).relIndex M = Nat.card ↥W₂ * Nat.card ↥W₁ := by
    exact hidxM
  obtain ⟨νL, φL, βL, hdataL⟩ := exists_isCoreCharData h₄ G hG3 hL hIL
  obtain ⟨νM, φM, βM, hdataM⟩ := exists_isCoreCharData h₄ G hG3 hM hIM
  have hHLU : _root_.CFSG.FeitThompson.hallCoreIn L = U :=
    h₇ G hG4 S T L U V W₁ W₂ y hsetup hIL hidxL M hM hIM hHMV' hidxM' νL φL βL hdataL
      νM φM βM hdataM
  have hnotchar := _root_.CFSG.FeitThompson.Proofs.FNI_paired_full_support_inner_not_characteristic
    h₅ h₈ h₁₀ G hG4 S T L U V W₁ W₂ y hsetup
  rw [← hHLU] at hnotchar
  exact hnotchar (by rw [Subgroup.subgroupOf_self]; infer_instance)

end OrderedPairExclusion

end

end CFSG.FeitThompson

namespace CFSG.FeitThompson.Proofs

public section

universe u

theorem FPF_ordered_pair_exclusion
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_five_type_local_classification.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FBG_type_II_supporting_maximal_configuration.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FCH_actual_paired_support_saturation.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FCH_type_I_frobenius_coherent_family.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FCH_type_p_action_kernel_ratio.{u})
    (h₆ : _root_.CFSG.FeitThompson.Statements.FNI_ordered_pair_full_supporting_complement.{u})
    (h₇ : _root_.CFSG.FeitThompson.Statements.FNI_paired_supporting_kernel_collapse.{u})
    (h₈ : _root_.CFSG.FeitThompson.Statements.FNI_type_p_elementary_core_structure.{u})
    (h₉ : _root_.CFSG.FeitThompson.Statements.FPF_ordered_reciprocal_maxima_type_two.{u})
    (h₁₀ : _root_.CFSG.FeitThompson.Statements.FTS_type_II_extended_support_ti.{u}) :
    _root_.CFSG.FeitThompson.Statements.FPF_ordered_pair_exclusion.{u} :=
  CFSG.FeitThompson.OrderedPairExclusion.main h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉ h₁₀

end

end CFSG.FeitThompson.Proofs
