module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.TauThirteenTypeIStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.OddOrder.PairOrientationByFactorOrder
import CFSG.FeitThompson.Local.PairedMaximalConfiguration
import CFSG.FeitThompson.Representations.NotAllMaximalSubgroupsTypeI
import CFSG.FeitThompson.Local.TypePMaximalPrimeFactors

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup Pointwise CFSG.FeitThompson
open CFSG.FeitThompson

universe u

variable {G : Type u} [Group G] [Finite G]

theorem false_of_isTypePPair {S T W₁ W₂ : Subgroup G}
    (h₃ : _root_.CFSG.FeitThompson.Statements.FPF_ordered_pair_exclusion.{u})
    (h : IsTypePPair S T W₁ W₂) : False := by
  have key : ∀ A B C D : Subgroup G, IsTypePPair A B C D → Nat.card C < Nat.card D → False := by
    intro A B C D h hlt
    exact h₃ G ⟨h.odd_natCard, h.isSimpleGroup, h.not_isMulCommutative, h.isSolvable⟩
      A B C D h.isCoatom_left h.isCoatom_right h.ne h.ne_bot_left h.ne_bot_right
      h.isCyclic_left h.isCyclic_right h.isInternalDirectProduct h.isCyclic_sup
      (isInternalSemidirectProduct_commutator_self h.sup_commutator_left
        h.disjoint_commutator_left)
      (isInternalSemidirectProduct_commutator_self h.sup_commutator_right
        h.disjoint_commutator_right)
      h.inf_eq h.isTIWithNormalizer h.typeIIToV_left h.typeIIToV_right h.typeII
      (fun L hL hLI => (h.conj_of_not_isTypeI L hL hLI).imp
        (fun hg => isConjugateSubgroup_of_conj_smul_eq hg.choose_spec)
        (fun hg => isConjugateSubgroup_of_conj_smul_eq hg.choose_spec)) hlt
  rcases h.isTypePPair_and_natCard_lt_or_swap with ⟨h', hlt⟩ | ⟨h', hlt⟩
  · exact key _ _ _ _ h' hlt
  · exact key _ _ _ _ h' hlt

theorem FT_no_minimal_odd_simple
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_maximal_type_dichotomy.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FPF_ordered_pair_exclusion.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FPF_type_I_frobenius.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FTS_canonical_signalizer_structure.{u})
    (h₆ : _root_.CFSG.FeitThompson.Statements.FTS_sigma_prime_separation.{u})
    (h₇ : _root_.CFSG.FeitThompson.Statements.FTS_type_I_core_kappa_identity.{u})
    (h₈ : _root_.CFSG.FeitThompson.Statements.FTS_type_I_dade_support.{u}) :
    _root_.CFSG.FeitThompson.Statements.FT_no_minimal_odd_simple.{u} := by
  intro G _ _ hG
  obtain ⟨M, hM, hMI⟩ :=
    FPF_not_all_type_I h₂ h₄ h₅ h₆ h₇ h₈ G ⟨hG.odd, hG.simple, hG.nonabelian, hG.solvable⟩
  obtain ⟨S, T, W₁, W₂, hpair⟩ :=
    exists_isTypePPair_of_exists_not_isTypeI h₁
      ⟨hG.odd, hG.simple, hG.nonabelian, hG.solvable⟩ hM hMI
  exact false_of_isTypePPair h₃ hpair

end

end CFSG.FeitThompson.Proofs
