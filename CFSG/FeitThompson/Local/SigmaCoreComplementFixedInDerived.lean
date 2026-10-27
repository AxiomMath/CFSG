module

public import CFSG.FeitThompson.Statements.KappaResidualCoreStatements
import CFSG.FeitThompson.Local.SigmaCoreNormalHallDerived
import CFSG.FeitThompson.Local.SolvableDerivedKernelCommutators
import CFSG.FeitThompson.Foundations.CoprimeAbelianComplementsConjugate
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open CFSG.FeitThompson CFSG.FeitThompson Subgroup FreeCore

universe u

attribute [local instance] CFSG.FeitThompson.conjMulDistribMulAction

theorem inf_centralizer_le_commutator_self_of_eq_commutator {L : Type*} [Group L] [Finite L]
    {H K : Subgroup L} [H.Normal] (hcop : (Nat.card ↥K).Coprime (Nat.card ↥H))
    (hHK : H = ⁅H, K⁆) : H ⊓ centralizer (K : Set L) ≤ ⁅H, H⁆ := by
  rintro x ⟨hxH, hxC⟩
  have hgen : smulDisplacementSubgroup ↥K ↥H = ⊤ := by
    refine Subgroup.map_injective H.subtype_injective ?_
    rw [map_subtype_smulDisplacementSubgroup_eq_commutator H K, ← hHK,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hfix : (⟨x, hxH⟩ : ↥H) ∈ FixedPoints.subgroup ↥K ↥H := by
    rw [FixedPoints.mem_subgroup]
    intro k
    refine Subtype.ext ?_
    rw [conjMulDistribMulAction_smul_coe K H k ⟨x, hxH⟩,
      (Subgroup.mem_centralizer_iff.1 hxC) (k : L) k.2]
    group
  have h2 := Subgroup.mem_map_of_mem H.subtype (fixedPoints_subgroup_le_commutator hcop hgen hfix)
  rwa [Subgroup.map_subtype_commutator] at h2

variable {G : Type*} [Group G] [Finite G] {M E : Subgroup G}

theorem inf_centralizer_sigmaCore_le_commutator [IsSimpleGroup G] (hna : ¬ IsMulCommutative G)
    (hodd : Odd (Nat.card G)) (hsolv : ∀ Y : Subgroup G, Y ≠ ⊤ → Group.IsSolvable ↥Y)
    (hM : IsCoatom M) (hEM : E ≤ M)
    (hsplit : IsInternalSemidirectProduct M (sigmaCore M) E) :
    sigmaCore M ⊓ centralizer (E : Set G) ≤ ⁅sigmaCore M, sigmaCore M⁆ := by
  have hSM : sigmaCore M ≤ M := sigmaCore_le M
  have := hsolv M hM.1
  set H : Subgroup ↥M := (sigmaCore M).subgroupOf M with hH
  set K : Subgroup ↥M := E.subgroupOf M with hK
  have hHnormal : H.Normal := sigmaCore_normal_subgroupOf M
  have hsup : H ⊔ K = ⊤ := by
    rw [hH, hK, ← subgroupOf_sup hSM hEM, hsplit.sup_eq, subgroupOf_self]
  have hinf : H ⊓ K = ⊥ := by
    rw [hH, hK, ← subgroupOf_inf, hsplit.inf_eq_bot, Subgroup.bot_subgroupOf]
  have hcompl : H.IsComplement' K :=
    (isComplement'_of_sup_eq_top_of_inf_eq_bot hsup hinf).symm
  have hcop : (Nat.card ↥K).Coprime (Nat.card ↥H) := by
    have hidx : H.index = Nat.card ↥K := hcompl.symm.index_eq_card
    have hc := (isHallSubgroup_subgroupOf_sigmaCore hna hodd hsolv hM).coprime_natCard_index
    rw [hidx] at hc
    exact hc.symm
  have hle : H ≤ _root_.commutator ↥M := by
    have h1 : sigmaCore M ≤ ⁅M, M⁆ := sigmaCore_le_commutator hna hodd hsolv hM
    have h2 : (⁅M, M⁆ : Subgroup G).subgroupOf M = _root_.commutator ↥M := by
      rw [← Subgroup.map_subtype_commutator, Subgroup.subgroupOf,
        Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
    rw [hH, ← h2]
    exact Subgroup.subgroupOf_mono M h1
  have hHK : H = ⁅H, K⁆ :=
    eq_commutator_of_isSolvable_of_le_commutator H K hsup hinf hle
  rintro x ⟨hxS, hxC⟩
  have hxM : x ∈ M := hSM hxS
  have hmem : (⟨x, hxM⟩ : ↥M) ∈ H ⊓ centralizer (K : Set ↥M) :=
    ⟨hxS, Subgroup.mem_centralizer_iff.2 fun k hk =>
      Subtype.ext ((Subgroup.mem_centralizer_iff.1 hxC) (k : G) hk)⟩
  have h3 := inf_centralizer_le_commutator_self_of_eq_commutator hcop hHK hmem
  rw [hH, commutator_subgroupOf hSM hSM] at h3
  exact h3

theorem FTS_complement_fixed_core_contained_derived :
    Statements.FTS_complement_fixed_core_contained_derived.{u} := by
  intro G _ _ hG M hM E hEM hsplit
  have := hG.isSimpleGroup
  exact inf_centralizer_sigmaCore_le_commutator hG.not_isMulCommutative hG.odd_natCard
    hG.isSolvable hM hEM hsplit

end

end CFSG.FeitThompson.Proofs
