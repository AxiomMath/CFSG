module

public import CFSG.Foundations.Basic
import CFSG.GroupTheory.CyclicSylowNormalOddComplement
import CFSG.GroupTheory.LocalCores.Components
import CFSG.Milestones.OO_odd_order_solvable

public section

namespace CFSG.GH74.E2

open Subgroup
open scoped Pointwise

theorem isCyclic_of_rank_le_one {A : Type*} [Group A] [Finite A] (h : Group.rank A ≤ 1) :
    IsCyclic A := by
  obtain ⟨s, hs, hcl⟩ := Group.rank_spec A
  obtain ⟨x, hx⟩ := Finset.card_le_one_iff_subset_singleton.mp (hs ▸ h : s.card ≤ 1)
  rw [isCyclic_iff_exists_zpowers_eq_top]
  refine ⟨x, top_unique ?_⟩
  rw [← hcl, Subgroup.zpowers_eq_closure]
  refine Subgroup.closure_mono fun y hy => ?_
  have := hx hy
  simpa using this

theorem exists_noncyclic_sylow_two_of_quasisimple {Q : Type*} [Group Q] [Finite Q]
    (hQ : IsQuasisimple Q) : ∃ T : Subgroup Q, IsPGroup 2 T ∧ 2 ≤ Group.rank T := by
  obtain ⟨S⟩ : Nonempty (Sylow 2 Q) := inferInstance
  refine ⟨S, S.isPGroup', ?_⟩
  by_contra hrk
  have hScyc : IsCyclic ↥(S : Subgroup Q) := isCyclic_of_rank_le_one (by omega)
  obtain ⟨-, hmul, -, ⟨-, hodd, -, -⟩, -⟩ := CFSG.cyclic_sylow_normal_odd_complement S hScyc
  set N := CFSG.pPrimeCore 2 Q with hN
  have hcycq : IsCyclic (Q ⧸ N) := by
    have := hScyc
    refine isCyclic_of_surjective ((QuotientGroup.mk' N).comp (S : Subgroup Q).subtype) ?_
    intro y
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective y
    have hq : q ∈ (N : Set Q) * (S : Set Q) := by
      rw [hmul]
      trivial
    obtain ⟨n, hn, s, hs, rfl⟩ := hq
    refine ⟨⟨s, hs⟩, ?_⟩
    have h1 : QuotientGroup.mk' N n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
    change QuotientGroup.mk' N s = QuotientGroup.mk' N (n * s)
    rw [map_mul, h1, one_mul]
  have hNtop : N = ⊤ := by
    have hperf : commutator Q = ⊤ := hQ.1.commutator_eq_top
    rw [eq_top_iff, ← hperf, _root_.commutator_def]
    refine Subgroup.commutator_le.2 fun g₁ _ g₂ _ => ?_
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 (IsCyclic.commGroup.mul_comm _ _)
  have hQodd : Odd (Nat.card Q) := by
    have : Nat.card N = Nat.card Q := by rw [hNtop]; exact Subgroup.card_top
    rw [← this]
    exact hodd
  have hsolv : Group.IsSolvable Q := CFSG.Milestones.odd_order_solvable hQodd
  have : Nontrivial Q := CFSG.LocalCores.isQuasisimple_nontrivial hQ
  have : Group.IsPerfect Q := hQ.1
  exact Group.IsPerfect.not_isSolvable Q hsolv

end CFSG.GH74.E2
