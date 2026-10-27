module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
import CFSG.FeitThompson.Representations.ChiefActionKernelNormalQuotientLayers
import CFSG.FeitThompson.Representations.ConjugationTransportsDadeSignalizers
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open CFSG.FeitThompson CFSG.FeitThompson Subgroup
  Pointwise

universe u

variable {G : Type u} [Group G]

theorem eq_conjSubgroup_of_conj_smul_eq {M S : Subgroup G} {g : G}
    (h : MulAut.conj g • M = S) : M = conjSubgroup S g := by
  subst h
  ext x
  rw [mem_conjSubgroup]
  refine ⟨fun hx => ⟨g * x * g⁻¹, ?_, by group⟩, ?_⟩
  · rw [mem_conj_smul_iff]
    simpa [mul_assoc] using hx
  · rintro ⟨y, hy, rfl⟩
    rw [mem_conj_smul_iff] at hy
    simpa [mul_assoc] using hy

theorem isInternalSemidirectProduct_commutator_self {X W : Subgroup G}
    (hsup : ⁅X, X⁆ ⊔ W = X) (hdisj : Disjoint (⁅X, X⁆ : Subgroup G) W) :
    FreeCore.IsInternalSemidirectProduct X (⁅X, X⁆ : Subgroup G) W where
  sup_eq := hsup
  le_normalizer := le_normalizer_commutator_self Subgroup.le_normalizer
  disjoint := hdisj

theorem exists_isTypePPair_of_exists_not_isTypeI [Finite G]
    (h₁ : Statements.FBG_maximal_type_dichotomy.{u}) (hG : IsOddOrderMinimalSimple G)
    {M : Subgroup G} (hM : IsCoatom M) (hMI : ¬ IsTypeI M) :
    ∃ S T W₁ W₂ : Subgroup G, IsTypePPair S T W₁ W₂ := by
  have hamb : IsFBGAmbient G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  rcases (h₁ G hamb).2 with hall | hpair
  · exact absurd (hall M hM) hMI
  · exact hpair

theorem FBG_paired_maximal_configuration
    (h₁ : Statements.FBG_maximal_type_dichotomy.{u}) :
    Statements.FBG_paired_maximal_configuration.{u} := by
  intro G _ _ hG hex
  obtain ⟨M, hM, hMI⟩ := hex
  obtain ⟨S, T, W₁, W₂, h⟩ := exists_isTypePPair_of_exists_not_isTypeI h₁ hG hM hMI
  refine ⟨S, T, W₁, W₂, h.isCoatom_left, h.isCoatom_right, h.ne, h.ne_bot_left, h.ne_bot_right,
    h.isCyclic_left, h.isCyclic_right, h.isInternalDirectProduct, h.isCyclic_sup,
    isInternalSemidirectProduct_commutator_self h.sup_commutator_left h.disjoint_commutator_left,
    isInternalSemidirectProduct_commutator_self h.sup_commutator_right h.disjoint_commutator_right,
    h.inf_eq, h.isTIWithNormalizer, h.typeIIToV_left, h.typeIIToV_right, h.typeII,
    fun L hL hLI => ?_⟩
  rcases h.conj_of_not_isTypeI L hL hLI with ⟨g, hg⟩ | ⟨g, hg⟩
  · exact Or.inl ⟨g, eq_conjSubgroup_of_conj_smul_eq hg⟩
  · exact Or.inr ⟨g, eq_conjSubgroup_of_conj_smul_eq hg⟩

end

end CFSG.FeitThompson.Proofs
