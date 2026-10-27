module

public import CFSG.FeitThompson.Statements.FittingOverlapKappaStatements
public import CFSG.FeitThompson.Statements.KappaCandidateStatements
public import CFSG.FeitThompson.Statements.TauThirteenTypeIStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.OddOrder.PairedCompatibleComplements
import CFSG.FeitThompson.OddOrder.PConfigAlignDerivedComplement
import CFSG.FeitThompson.OddOrder.LocalTypesConjugationInvariant
import CFSG.FeitThompson.OddOrder.SigmaSylowTransporterFusion
import CFSG.FeitThompson.Foundations.SylowNormalizerSelfNormalizing
import CFSG.FeitThompson.Local.PConfigurationKappaFactors
import CFSG.FeitThompson.Local.PairedPConfigurationsPrimeFactors

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup Pointwise

variable {G : Type*} [Group G]

theorem map_conj_map_conj_inv_cancel (Y : Subgroup G) (c : G) :
    (Y.map (MulAut.conj c : G →* G)).map (MulAut.conj c⁻¹ : G →* G) = Y := by
  rw [map_conj_map_conj, inv_mul_cancel, map_conj_eq_self (one_mem Y)]

theorem isConjugateSubgroup_of_conj_smul_eq {L S : Subgroup G} {g : G}
    (h : MulAut.conj g • L = S) : CFSG.FeitThompson.Prep05.IsConjugateSubgroup S L := by
  refine ⟨g⁻¹, ?_⟩
  rw [coe_conj_smul_eq_map] at h
  rw [show (MulAut.conj g⁻¹).toMonoidHom = (MulAut.conj g⁻¹ : G →* G) from rfl, ← h,
    map_conj_map_conj_inv_cancel]

variable [Finite G] {S T M W₁ W₂ : Subgroup G}

theorem IsTypePPair.map_conj (h : IsTypePPair S T W₁ W₂) (c : G) :
    IsTypePPair (S.map (MulAut.conj c : G →* G)) (T.map (MulAut.conj c : G →* G))
      (W₁.map (MulAut.conj c : G →* G)) (W₂.map (MulAut.conj c : G →* G)) := by
  set e : G ≃* G := MulAut.conj c
  have hinj : Function.Injective e := e.injective
  refine
  { odd_natCard := h.odd_natCard
    isSimpleGroup := h.isSimpleGroup
    not_isMulCommutative := h.not_isMulCommutative
    isSolvable := h.isSolvable
    isCoatom_left := isCoatom_map_conj h.isCoatom_left c
    isCoatom_right := isCoatom_map_conj h.isCoatom_right c
    ne := fun hc => h.ne (Subgroup.map_injective hinj hc)
    ne_bot_left := ?_
    ne_bot_right := ?_
    isCyclic_left := (MulEquiv.isCyclic (e.subgroupMap W₁)).1 h.isCyclic_left
    isCyclic_right := (MulEquiv.isCyclic (e.subgroupMap W₂)).1 h.isCyclic_right
    isInternalDirectProduct := ?_
    isCyclic_sup := ?_
    sup_commutator_left := ?_
    disjoint_commutator_left := ?_
    sup_commutator_right := ?_
    disjoint_commutator_right := ?_
    inf_eq := ?_
    isTIWithNormalizer := ?_
    typeIIToV_left := ?_
    typeIIToV_right := ?_
    typeII := ?_
    conj_of_not_isTypeI := ?_ }
  · rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ hinj]; exact h.ne_bot_left
  · rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ hinj]; exact h.ne_bot_right
  · rw [← Subgroup.map_sup]; exact h.isInternalDirectProduct.map e
  · rw [← Subgroup.map_sup]
    exact (MulEquiv.isCyclic (e.subgroupMap (W₁ ⊔ W₂))).1 h.isCyclic_sup
  · rw [← Subgroup.map_commutator, ← Subgroup.map_sup, h.sup_commutator_left]
  · rw [disjoint_iff, ← Subgroup.map_commutator, ← Subgroup.map_inf _ _ _ hinj,
      disjoint_iff.1 h.disjoint_commutator_left, Subgroup.map_bot]
  · rw [← Subgroup.map_commutator, ← Subgroup.map_sup, h.sup_commutator_right]
  · rw [disjoint_iff, ← Subgroup.map_commutator, ← Subgroup.map_inf _ _ _ hinj,
      disjoint_iff.1 h.disjoint_commutator_right, Subgroup.map_bot]
  · rw [← Subgroup.map_inf _ _ _ hinj, h.inf_eq, Subgroup.map_sup]
  · rw [← Subgroup.map_sup, ← image_cyclicTIset]
    exact h.isTIWithNormalizer.map e
  · rcases h.typeIIToV_left with hh | hh | hh | hh
    · exact Or.inl (hh.map e)
    · exact Or.inr (Or.inl (hh.map e))
    · exact Or.inr (Or.inr (Or.inl (hh.map e)))
    · exact Or.inr (Or.inr (Or.inr (hh.map e)))
  · rcases h.typeIIToV_right with hh | hh | hh | hh
    · exact Or.inl (hh.map e)
    · exact Or.inr (Or.inl (hh.map e))
    · exact Or.inr (Or.inr (Or.inl (hh.map e)))
    · exact Or.inr (Or.inr (Or.inr (hh.map e)))
  · rcases h.typeII with hh | hh
    · exact Or.inl (hh.map e)
    · exact Or.inr (hh.map e)
  · intro L hL hLI
    rcases h.conj_of_not_isTypeI L hL hLI with ⟨g, hg⟩ | ⟨g, hg⟩
    · refine Or.inl ⟨c * g, ?_⟩
      rw [coe_conj_smul_eq_map] at hg ⊢
      rw [← map_conj_map_conj, hg]
    · refine Or.inr ⟨c * g, ?_⟩
      rw [coe_conj_smul_eq_map] at hg ⊢
      rw [← map_conj_map_conj, hg]

theorem IsTypePPair.exists_fst_eq (h : IsTypePPair S T W₁ W₂) (hM : IsCoatom M)
    (hMI : ¬ IsTypeI M) : ∃ N A B : Subgroup G, IsTypePPair M N A B := by
  rcases h.conj_of_not_isTypeI M hM hMI with ⟨g, hg⟩ | ⟨g, hg⟩
  · rw [coe_conj_smul_eq_map] at hg
    have key := h.map_conj g⁻¹
    rw [← hg, map_conj_map_conj_inv_cancel] at key
    exact ⟨_, _, _, key⟩
  · rw [coe_conj_smul_eq_map] at hg
    have key := h.symm.map_conj g⁻¹
    rw [← hg, map_conj_map_conj_inv_cancel] at key
    exact ⟨_, _, _, key⟩

theorem IsTypePPair.exists_isTypePPair_of_isWitnessedPConfiguration {N A B E : Subgroup G}
    (hp : IsTypePPair M N A B) (hc : IsWitnessedPConfiguration M E W₁ W₂) :
    ∃ T : Subgroup G, IsTypePPair M T W₁ W₂ := by
  have hsolv : Group.IsSolvable ↥M := hp.isSolvable M hp.ne_top_left
  obtain ⟨U₀, -, hU₀⟩ := hp.exists_compatible_left
  obtain ⟨y, hyM, hA, hB⟩ :=
    eq_of_isWitnessedPConfiguration_of_map_conj hU₀.1 hc hc.sup_commutator_W₁
      hc.disjoint_commutator_W₁
  have h2 := hp.map_conj y⁻¹
  rw [map_conj_eq_self (inv_mem hyM), hA, hB] at h2
  exact ⟨_, h2⟩

end CFSG.FeitThompson

namespace CFSG.FeitThompson.Proofs

open CFSG.FeitThompson Subgroup

universe u

theorem FNI_type_p_prime_factors
    (h₁ : Statements.FBG_five_type_local_classification.{u})
    (h₂ : Statements.FBG_maximal_type_dichotomy.{u})
    (h₃ : Statements.FNI_kappa_local_pair.{u})
    (h₄ : Statements.FNI_kappa_semiprime_complement_existence.{u})
    (h₅ : Statements.FPF_type_iii_v_extended_dade_support.{u})
    (h₆ : Statements.FPF_type_iii_v_induced_family_noncoherence.{u})
    (h₇ : Statements.FPF_type_iii_v_second_factor_prime.{u})
    (h₈ : Statements.FTS_type_I_core_kappa_identity.{u}) :
    Statements.FNI_type_p_prime_factors.{u} := by
  intro G _ _ hG M U W₁ W₂ hM hc p q hp hq
  have hFBG : CFSG.FeitThompson.IsFBGAmbient G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hG4 : CFSG.FeitThompson.IsOddSimpleMinimal G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hG9 : CFSG.FeitThompson.Prep09.IsMinimalSimpleOddOrder G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hκ := (FNI_p_configuration_kappa_factors h₃ h₄ G hG4 M U W₁ W₂ hM hc).1
  have hMI : ¬ IsTypeI M := fun hI => Set.nonempty_iff_ne_empty.1 hκ (h₈ G hG9 M hM hI).1
  obtain ⟨S, T₀, V₁, V₂, hpair⟩ := (h₂ G hFBG).2.resolve_left fun hall => hMI (hall M hM)
  obtain ⟨N, A, B, hpM⟩ := hpair.exists_fst_eq hM hMI
  obtain ⟨T, hpair'⟩ := hpM.exists_isTypePPair_of_isWitnessedPConfiguration hc
  obtain ⟨V, hVT, hcT, -⟩ := hpair'.exists_compatible_right
  obtain ⟨hpp, hqp, hop, hoq, hne⟩ :=
    FNI_paired_p_configurations_prime_factors h₁ h₃ h₄ h₅ h₆ h₇ h₈ G hG4 M T U V W₁ W₂ hM
      hpair'.isCoatom_right hpair'.ne hc hcT
  subst hp
  subst hq
  refine ⟨hpp, hqp, hop, hoq, hne, T, hpair'.isCoatom_right, hpair'.ne.symm, V, hVT, hcT,
    hpair'.inf_eq, hpair'.typeIIToV_left, hpair'.typeIIToV_right, hpair'.typeII,
    fun L hL hLI => ?_⟩
  rcases hpair'.conj_of_not_isTypeI L hL hLI with ⟨g, hg⟩ | ⟨g, hg⟩
  · exact Or.inl (isConjugateSubgroup_of_conj_smul_eq hg)
  · exact Or.inr (isConjugateSubgroup_of_conj_smul_eq hg)

end CFSG.FeitThompson.Proofs

end
