module

public import CFSG.FeitThompson.Statements.TauThirteenTypeIStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
import CFSG.FeitThompson.Representations.TypeVMaximalExclusion
import CFSG.FeitThompson.Representations.TypeThreeFourInnerComplementCyclic
import CFSG.FeitThompson.OddOrder.NoncyclicPPowerInNormalHall

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup

variable {G : Type*} [Group G] [Finite G]

theorem centralizer_le_of_isTIWithNormalizer_fittingRawSharp {N : Subgroup G}
    (hTI : IsTIWithNormalizer (fittingRawSharp N) N) {x : G} (hx : x ∈ fittingRawSharp N) :
    centralizer ({x} : Set G) ≤ N := by
  intro g hg
  by_contra hgN
  refine Set.disjoint_left.1 (hTI.disjoint_conj_image g hgN) hx ⟨x, hx, ?_⟩
  rw [MulAut.conj_apply, mem_centralizer_singleton_iff.1 hg, mul_inv_cancel_right]

theorem coprime_natCard_index_hallCore_subgroupOf {N K : Subgroup G} (hKN : K ≤ N)
    (hHK : (hallCore N).map N.subtype ≤ K) :
    (Nat.card (((hallCore N).map N.subtype).subgroupOf K)).Coprime
      (((hallCore N).map N.subtype).subgroupOf K).index := by
  have hcop := coprime_natCard_index_hallCore (X := ↥N)
  have hcard : Nat.card (((hallCore N).map N.subtype).subgroupOf K) = Nat.card (hallCore N) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHK).toEquiv]
    exact (Nat.card_congr (Subgroup.equivMapOfInjective _ _ N.subtype_injective).toEquiv).symm
  have hidx : (hallCore N).index = ((hallCore N).map N.subtype).relIndex N := by
    rw [Subgroup.relIndex, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective N.subtype_injective]
  have hmul := Subgroup.relIndex_mul_relIndex _ _ _ hHK hKN
  rw [hcard]
  refine Nat.Coprime.coprime_dvd_right ?_ hcop
  rw [hidx, ← hmul]
  exact dvd_mul_right _ _

theorem IsWitnessedPConfiguration.le_hallCore_of_isCyclic {N E W₁ W₂ : Subgroup G}
    (hc : IsWitnessedPConfiguration N E W₁ W₂) (hE : IsCyclic E) {p a : ℕ} (hp : p.Prime)
    {P : Subgroup G} (hPK : P ≤ ⁅N, N⁆) (hPcard : Nat.card P = p ^ a) (hPnc : ¬ IsCyclic P) :
    P ≤ (hallCore N).map N.subtype := by
  set K : Subgroup G := ⁅N, N⁆
  set H : Subgroup G := (hallCore N).map N.subtype
  have := hc.normal_subgroupOf_hallCore
  have hcompl := hc.isComplement'_subgroupOf_hallCore_E
  have hEK : IsCyclic (E.subgroupOf K) :=
    isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hc.le_commutator_E).symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hc.le_commutator_E).symm.surjective
  have : IsCyclic (↥K ⧸ H.subgroupOf K) :=
    isCyclic_of_surjective hcompl.symm.QuotientMulEquiv.symm.toMonoidHom
      hcompl.symm.QuotientMulEquiv.symm.surjective
  have hPK' : Nat.card (P.subgroupOf K) = p ^ a := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPK).toEquiv, hPcard]
  have hPnc' : ¬ IsCyclic (P.subgroupOf K) := fun h => hPnc
    (isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hPK).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hPK).surjective)
  have hle := le_of_natCard_eq_prime_pow_of_not_isCyclic
    (coprime_natCard_index_hallCore_subgroupOf (Subgroup.commutator_le_self N)
      hc.hallCore_le_commutator) hp hPK' hPnc'
  intro x hx
  exact Subgroup.mem_subgroupOf.1
    (hle (Subgroup.mem_subgroupOf.2 (show ((⟨x, hPK hx⟩ : K) : G) ∈ P from hx)))

end CFSG.FeitThompson

namespace CFSG.FeitThompson.Proofs

open CFSG.FeitThompson

universe u

theorem FPF_non_type_i_supporting_maximum_exclusion
    (h₁ : Statements.FPF_non_type_i_sigma_core_identities.{u})
    (h₂ : Statements.FPF_type_iii_iv_core_elementary_chief_kernel_trivial.{u})
    (h₃ : Statements.FPF_type_iii_iv_second_derived_fitting.{u})
    (h₄ : Statements.FPF_type_iii_v_extended_dade_support.{u})
    (h₅ : Statements.FPF_type_iii_v_induced_family_noncoherence.{u})
    (h₆ : Statements.FPF_type_iii_v_second_factor_prime.{u}) :
    Statements.FPF_non_type_i_supporting_maximum_exclusion.{u} := by
  intro G _ _ hG N hN htype p a hp P hPS hPcard hPnc x hxP hx1 hC
  have : Fintype G := Fintype.ofFinite G
  have hG6 : Prep06.IsMinimalOddSimple G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hnotV := FPF_type_v_exclusion h₄ h₅ h₆ G hG6 N hN
  have hsig := h₁ G hG N hN
  obtain ⟨hPH, hTI⟩ : P ≤ (hallCore N).map N.subtype ∧
      IsTIWithNormalizer (fittingRawSharp N) N := by
    rcases htype with hII | hIII | hIV | hV
    · have h : P ≤ CFSG.FeitThompson.Prep05.hallCoreOf N := hsig.1 hII ▸ hPS
      exact ⟨h, hII.isTIWithNormalizer_fittingRawSharp⟩
    · obtain ⟨E, W₁, W₂, hc⟩ := hIII.exists_isPConfiguration
      have hcyc := (FPF_type_iii_iv_inner_complement_cyclic h₂ h₃ h₄ h₅ h₆ G hG6 N E W₁ W₂ hN
        (Or.inl hIII) hc.isWitnessedPConfiguration).1
      exact ⟨hc.isWitnessedPConfiguration.le_hallCore_of_isCyclic hcyc hp
        (hsig.2 (Or.inl hIII) ▸ hPS) hPcard hPnc, hIII.isTIWithNormalizer_fittingRawSharp⟩
    · obtain ⟨E, W₁, W₂, hc⟩ := hIV.exists_isPConfiguration
      have hcyc := (FPF_type_iii_iv_inner_complement_cyclic h₂ h₃ h₄ h₅ h₆ G hG6 N E W₁ W₂ hN
        (Or.inr hIV) hc.isWitnessedPConfiguration).1
      exact ⟨hc.isWitnessedPConfiguration.le_hallCore_of_isCyclic hcyc hp
        (hsig.2 (Or.inr (Or.inl hIV)) ▸ hPS) hPcard hPnc, hIV.isTIWithNormalizer_fittingRawSharp⟩
    · exact absurd hV hnotV
  have hx : x ∈ fittingRawSharp N := by
    apply hallCoreSharp_subset_fittingRawSharp N
    rw [hallCoreSharp_eq]
    exact ⟨hPH hxP, hx1⟩
  exact hC (centralizer_le_of_isTIWithNormalizer_fittingRawSharp hTI hx)

end CFSG.FeitThompson.Proofs

end
