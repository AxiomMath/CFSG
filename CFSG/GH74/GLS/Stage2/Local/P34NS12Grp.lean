module

public import CFSG.FeitThompson.OddOrderTheorem
public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.GH74.GLS.Stage2.Local.P34NS

open Subgroup

variable {N : Type*} [Group N]

theorem perfect_le_ker {Q : Type*} [Group Q] (π : N →* Q) {P : Subgroup N} (hP : ⁅P, P⁆ = P)
    (hsol : Group.IsSolvable ↥(P.map π)) : P ≤ π.ker := by
  have hperf : ⁅P.map π, P.map π⁆ = P.map π := by
    rw [← Subgroup.map_commutator, hP]
  have hbot : P.map π = ⊥ := by
    by_contra hne
    have : Nontrivial ↥(P.map π) := (Subgroup.nontrivial_iff_ne_bot _).2 hne
    have hlt := Group.IsSolvable.commutator_lt_top_of_nontrivial ↥(P.map π)
    have htop : commutator ↥(P.map π) = ⊤ :=
      (Subgroup.isPerfect_iff.2 hperf).commutator_eq_top
    rw [htop] at hlt
    exact lt_irrefl _ hlt
  exact (Subgroup.map_eq_bot_iff _).1 hbot

theorem perfect_le_of_odd_quot [Finite N] {K : Subgroup N} [K.Normal]
    (hodd : Odd (Nat.card (N ⧸ K))) {P : Subgroup N} (hP : ⁅P, P⁆ = P) : P ≤ K := by
  have : Group.IsSolvable (N ⧸ K) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have := perfect_le_ker (QuotientGroup.mk' K) hP (by infer_instance)
  rwa [QuotientGroup.ker_mk'] at this

theorem perfect_le_of_sup {K W : Subgroup N} [K.Normal] (hW : Group.IsSolvable ↥W) {P : Subgroup N}
    (hP : ⁅P, P⁆ = P) (h : P ≤ K ⊔ W) : P ≤ K := by
  have hle : P.map (QuotientGroup.mk' K) ≤ W.map (QuotientGroup.mk' K) := by
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨k, hk, w, hw, hkw⟩ := (Subgroup.mem_sup_of_normal_left (s := K) (t := W) (x := g)).1 (h hg)
    refine ⟨w, hw, ?_⟩
    have hk1 : QuotientGroup.mk' K k = 1 := (QuotientGroup.eq_one_iff (N := K) k).2 hk
    rw [← hkw, map_mul, hk1, one_mul]
  have : Group.IsSolvable ↥(W.map (QuotientGroup.mk' K)) :=
    Group.isSolvable_of_surjective (f := (QuotientGroup.mk' K).subgroupMap W)
      (MonoidHom.subgroupMap_surjective _ W)
  have hsol : Group.IsSolvable ↥(P.map (QuotientGroup.mk' K)) :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)
  have := perfect_le_ker (QuotientGroup.mk' K) hP hsol
  rwa [QuotientGroup.ker_mk'] at this

theorem exists_perfect_lift {A B : Type*} [Group A] [Finite A] [Group B] (φ : A →* B) {Q : Subgroup B}
    (hQ : ⁅Q, Q⁆ = Q) (hQφ : Q ≤ φ.range) : ∃ P : Subgroup A, ⁅P, P⁆ = P ∧ P.map φ = Q := by
  have hne : {P : Subgroup A | P.map φ = Q}.Nonempty :=
    ⟨Q.comap φ, by
      show (Q.comap φ).map φ = Q
      rw [Subgroup.map_comap_eq, inf_of_le_right hQφ]⟩
  obtain ⟨P, hPS, hmin⟩ := (measure fun P : Subgroup A => Nat.card ↥P).wf.has_min _ hne
  refine ⟨P, ?_, hPS⟩
  have hcomm : ⁅P, P⁆ ∈ {P : Subgroup A | P.map φ = Q} := by
    show ⁅P, P⁆.map φ = Q
    rw [Subgroup.map_commutator]
    have : P.map φ = Q := hPS
    rw [this, hQ]
  by_contra hne'
  have hlt : ⁅P, P⁆ < P := lt_of_le_of_ne (Subgroup.commutator_le_self P) hne'
  exact hmin _ hcomm (Subgroup.card_lt_of_lt hlt)

end CFSG.GH74.GLS.Stage2.Local.P34NS
