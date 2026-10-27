module

public import CFSG.CGT.L5R.L52Enum
public import CFSG.CGT.L5R.L52Native

public section

namespace CFSG.CGT.L5R

open CFSG.CosetTable CFSG.CGT.M24R CFSG.GroupTheory.GL52

theorem lift_l52Mat_eq_one :
    ∀ r ∈ {r : FreeGroup (Fin 11) | r ∈ l52Rels.map FreeGroup.mk}, FreeGroup.lift l52Mat r = 1 := by
  intro r hr
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
  exact evalW_l52Mat_eq_one hw

noncomputable def l52Phi : l52Presented →* G52 :=
  PresentedGroup.toGroup lift_l52Mat_eq_one

theorem l52Phi_of (i : Fin 11) : l52Phi (PresentedGroup.of i) = l52Mat i :=
  PresentedGroup.toGroup.of _

theorem l52Phi_surjective : Function.Surjective l52Phi := by
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← closure_range_l52Mat, Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  exact ⟨PresentedGroup.of i, l52Phi_of i⟩

theorem l52Phi_bijective (hE : l52Enum = true) [Finite (PG 10 relsN8Ten)]
    (hN8 : Nat.card (PG 10 relsN8Ten) ≤ 322560) : Function.Bijective l52Phi := by
  obtain ⟨hfin, hcard⟩ := l52Presented_card_le hE hN8
  refine l52Phi_surjective.bijective_of_nat_card_le ?_
  rw [card_G52]
  exact hcard

noncomputable def l52PresentedEquiv (hE : l52Enum = true) [Finite (PG 10 relsN8Ten)]
    (hN8 : Nat.card (PG 10 relsN8Ten) ≤ 322560) : l52Presented ≃* G52 :=
  MulEquiv.ofBijective _ (l52Phi_bijective hE hN8)

theorem l52PresentedEquiv_of (hE : l52Enum = true) [Finite (PG 10 relsN8Ten)]
    (hN8 : Nat.card (PG 10 relsN8Ten) ≤ 322560) (i : Fin 11) :
    l52PresentedEquiv hE hN8 (PresentedGroup.of i) = l52Mat i :=
  l52Phi_of i

theorem isSimpleGroup_l52Presented (hE : l52Enum = true) [Finite (PG 10 relsN8Ten)]
    (hN8 : Nat.card (PG 10 relsN8Ten) ≤ 322560) : IsSimpleGroup l52Presented :=
  haveI := isSimpleGroup_G52
  (l52PresentedEquiv hE hN8).isSimpleGroup

theorem exists_mulEquiv_G52_of_relations (hE : l52Enum = true) [Finite (PG 10 relsN8Ten)]
    (hN8 : Nat.card (PG 10 relsN8Ten) ≤ 322560) {H : Type*} [Group H] (e : Fin 11 → H)
    (hp : ∀ r ∈ l52Rels, evalW e r = 1) (hK : Subgroup.closure (Set.range e) ≠ ⊥) :
    ∃ φ : ↥(Subgroup.closure (Set.range e)) ≃* G52,
      ∀ i, ((φ ⟨e i, Subgroup.subset_closure ⟨i, rfl⟩⟩ : G52) : M5) = l52M i := by
  have hsimple := isSimpleGroup_l52Presented hE hN8
  have hrel : ∀ r ∈ {r : FreeGroup (Fin 11) | r ∈ l52Rels.map FreeGroup.mk},
      FreeGroup.lift e r = 1 := by
    intro r hr
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
    exact hp w hw
  let ψ : l52Presented →* H := PresentedGroup.toGroup hrel
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
  let κ : l52Presented ≃* ↥(Subgroup.closure (Set.range e)) :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
  refine ⟨κ.symm.trans (l52PresentedEquiv hE hN8), fun i => ?_⟩
  have hκ : κ.symm ⟨e i, Subgroup.subset_closure ⟨i, rfl⟩⟩ = PresentedGroup.of i := by
    rw [MulEquiv.symm_apply_eq]
    exact Subtype.ext (hψ i).symm
  rw [MulEquiv.trans_apply, hκ, l52PresentedEquiv_of, coe_l52Mat]

end CFSG.CGT.L5R
