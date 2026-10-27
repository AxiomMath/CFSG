module

public import CFSG.GH74.GLS.Balance.Bender.Stmts

public section

namespace CFSG.GH74.GLS.Balance

open Subgroup CFSG CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

omit [Finite G] [Fact p.Prime] in
theorem isPStar_bot : IsPStar p ↥(⊥ : Subgroup G) := by
  refine ⟨?_, ?_⟩
  · exact Subsingleton.elim _ _
  · intro N hN P
    exact Subsingleton.elim _ _

theorem isPStar_opStar (h56 : BenderL56 p) (X : Subgroup G) : IsPStar p ↥(OpStar p X) := by
  set S : Set (Subgroup G) := {N | N ≤ X ∧ (N.subgroupOf X).Normal ∧ IsPStar p ↥N} with hS
  have hbot : (⊥ : Subgroup G) ∈ S := ⟨bot_le, by rw [Subgroup.bot_subgroupOf]; infer_instance,
    isPStar_bot⟩
  have hsup : ∀ x ∈ S, ∀ y ∈ S, x ⊔ y ∈ S := by
    rintro x ⟨hx, hxn, hxp⟩ y ⟨hy, hyn, hyp⟩
    refine ⟨sup_le hx hy, ?_, h56 G X x y hx hy hxn hyn hxp hyp⟩
    rw [Subgroup.subgroupOf_sup hx hy]
    have := hxn
    have := hyn
    infer_instance
  have hfin : S.Finite := Set.toFinite S
  have hmem := Finset.sup_mem S hbot hsup hfin.toFinset id (fun i hi => by
    simpa using (hfin.mem_toFinset.mp hi))
  rw [Finset.sup_id_eq_sSup, Set.Finite.coe_toFinset] at hmem
  exact hmem.2.2

omit [Finite G] [Fact p.Prime] in
theorem opStar_eq_self {X : Subgroup G} (hp : IsPStar p ↥X) : OpStar p X = X :=
  le_antisymm (opStar_le p X) (le_opStar le_rfl (by rw [Subgroup.subgroupOf_self]; infer_instance) hp)

end CFSG.GH74.GLS.Balance
