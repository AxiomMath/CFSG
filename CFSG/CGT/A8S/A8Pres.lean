module

public import CFSG.CGT.A8S.A8Enum
public import CFSG.CGT.A8S.A8Native
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.CGT.A8S

open CFSG.CosetTable Equiv Equiv.Perm

theorem closure_range_a8Alt : Subgroup.closure (Set.range a8Alt) = ⊤ := by
  apply Subgroup.map_injective (alternatingGroup (Fin 8)).subtype_injective
  have hcomp : (alternatingGroup (Fin 8)).subtype ∘ a8Alt = a8Perm := funext coe_a8Alt
  rw [MonoidHom.map_closure, ← Set.range_comp, hcomp, closure_range_a8Perm,
    ← MonoidHom.range_eq_map, Subgroup.range_subtype]

private theorem nat_card_alternatingGroup_fin8 : Nat.card (alternatingGroup (Fin 8)) = 20160 := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  rfl

theorem lift_a8Alt_eq_one :
    ∀ r ∈ {r : FreeGroup (Fin 6) | r ∈ a8Rels.map FreeGroup.mk}, FreeGroup.lift a8Alt r = 1 := by
  intro r hr
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
  exact evalA8_a8Alt_eq_one hw

noncomputable def a8Phi : a8Presented →* alternatingGroup (Fin 8) :=
  PresentedGroup.toGroup lift_a8Alt_eq_one

theorem a8Phi_of (i : Fin 6) : a8Phi (PresentedGroup.of i) = a8Alt i :=
  PresentedGroup.toGroup.of _

theorem a8Phi_surjective : Function.Surjective a8Phi := by
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← closure_range_a8Alt, Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  exact ⟨PresentedGroup.of i, a8Phi_of i⟩

theorem a8Phi_bijective (hE : A8SubIndex) [Finite (PG 5 relsN0A8)]
    (hN0 : Nat.card (PG 5 relsN0A8) ≤ 1344) : Function.Bijective a8Phi := by
  obtain ⟨hfin, hcard⟩ := a8Presented_card_le hE hN0
  refine a8Phi_surjective.bijective_of_nat_card_le ?_
  rw [nat_card_alternatingGroup_fin8]
  exact hcard

noncomputable def a8PresentedEquiv (hE : A8SubIndex) [Finite (PG 5 relsN0A8)]
    (hN0 : Nat.card (PG 5 relsN0A8) ≤ 1344) : a8Presented ≃* alternatingGroup (Fin 8) :=
  MulEquiv.ofBijective _ (a8Phi_bijective hE hN0)

theorem a8PresentedEquiv_of (hE : A8SubIndex) [Finite (PG 5 relsN0A8)]
    (hN0 : Nat.card (PG 5 relsN0A8) ≤ 1344) (i : Fin 6) :
    a8PresentedEquiv hE hN0 (PresentedGroup.of i) = a8Alt i :=
  a8Phi_of i

theorem isSimpleGroup_a8Presented (hE : A8SubIndex) [Finite (PG 5 relsN0A8)]
    (hN0 : Nat.card (PG 5 relsN0A8) ≤ 1344) : IsSimpleGroup a8Presented :=
  haveI : IsSimpleGroup (alternatingGroup (Fin 8)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; omega)
  (a8PresentedEquiv hE hN0).isSimpleGroup

theorem lift_eq_one_of_a8Rels {H : Type*} [Group H] (e : Fin 6 → H)
    (hp : ∀ r ∈ a8Rels, evalA8 e r = 1) :
    ∀ r ∈ {r : FreeGroup (Fin 6) | r ∈ a8Rels.map FreeGroup.mk}, FreeGroup.lift e r = 1 := by
  intro r hr
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
  exact hp w hw

theorem exists_mulEquiv_A8_of_relations (hE : A8SubIndex) [Finite (PG 5 relsN0A8)]
    (hN0 : Nat.card (PG 5 relsN0A8) ≤ 1344) {H : Type*} [Group H] (e : Fin 6 → H)
    (hp : ∀ r ∈ a8Rels, evalA8 e r = 1) (hK : Subgroup.closure (Set.range e) ≠ ⊥) :
    ∃ φ : ↥(Subgroup.closure (Set.range e)) ≃* alternatingGroup (Fin 8),
      ∀ i, ((φ ⟨e i, Subgroup.subset_closure ⟨i, rfl⟩⟩ : alternatingGroup (Fin 8)) :
        Perm (Fin 8)) = a8Perm i := by
  have hsimple := isSimpleGroup_a8Presented hE hN0
  let ψ : a8Presented →* H := PresentedGroup.toGroup (lift_eq_one_of_a8Rels e hp)
  have hψ : ∀ i, ψ (PresentedGroup.of i) = e i := fun i => PresentedGroup.toGroup.of _
  have hrange : ψ.range = Subgroup.closure (Set.range e) := by
    have hcomp : (ψ ∘ PresentedGroup.of) = e := funext hψ
    rw [MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of, MonoidHom.map_closure,
      ← Set.range_comp, hcomp]
  have hker : ψ.ker = ⊥ := by
    rcases hsimple.eq_bot_or_eq_top_of_normal ψ.ker with h0 | h0
    · exact h0
    · exfalso
      apply hK
      rw [← hrange, MonoidHom.range_eq_bot_iff]
      exact MonoidHom.ker_eq_top_iff.1 h0
  have hinj : Function.Injective ψ := (MonoidHom.ker_eq_bot_iff ψ).1 hker
  let κ : a8Presented ≃* ↥(Subgroup.closure (Set.range e)) :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
  refine ⟨κ.symm.trans (a8PresentedEquiv hE hN0), fun i => ?_⟩
  have hκ : κ.symm ⟨e i, Subgroup.subset_closure ⟨i, rfl⟩⟩ = PresentedGroup.of i := by
    rw [MulEquiv.symm_apply_eq]
    exact Subtype.ext (hψ i).symm
  rw [MulEquiv.trans_apply, hκ, a8PresentedEquiv_of, coe_a8Alt]

end CFSG.CGT.A8S
