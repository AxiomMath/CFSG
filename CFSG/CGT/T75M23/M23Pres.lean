module

public import CFSG.CGT.T75M23.M23PresTables

public section

namespace CFSG.CGT.T75M23

open CFSG.CosetTable CFSG.Blueprint

abbrev m23Presented : Type := PG 7 m23Rels

@[expose] abbrev M23Facts : Prop :=
  (Finite m23Presented ∧ Nat.card m23Presented ≤ 10200960) ∧ m23TabCheck = true

section Model

noncomputable def m23Phi (h : m23TabCheck = true) : m23Presented →* NativeSporadic.M23 :=
  PresentedGroup.toGroup (f := m23Gen) fun r hr => by
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
    exact lift_m23Gen_eq_one h hw

theorem m23Phi_of (h : m23TabCheck = true) (i : Fin 7) :
    m23Phi h (PresentedGroup.of i) = m23Gen i :=
  PresentedGroup.toGroup.of _

theorem m23Phi_surjective (h : m23TabCheck = true) : Function.Surjective (m23Phi h) := by
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← closure_m23Gen h, Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  exact ⟨PresentedGroup.of i, m23Phi_of h i⟩

theorem m23Phi_bijective (hcard : Nat.card NativeSporadic.M23 = 10200960)
    (h : M23Facts) : Function.Bijective (m23Phi h.2) := by
  obtain ⟨hfin, hc⟩ := h.1
  have := hfin
  refine (m23Phi_surjective _).bijective_of_nat_card_le ?_
  rw [hcard]
  exact hc

noncomputable def m23PresentedEquiv (hcard : Nat.card NativeSporadic.M23 = 10200960)
    (h : M23Facts) : m23Presented ≃* NativeSporadic.M23 :=
  MulEquiv.ofBijective _ (m23Phi_bijective hcard h)

theorem isSimpleGroup_m23Presented (hcard : Nat.card NativeSporadic.M23 = 10200960)
    (hsimp : IsSimpleGroup NativeSporadic.M23) (h : M23Facts) :
    IsSimpleGroup m23Presented :=
  @MulEquiv.isSimpleGroup m23Presented _ NativeSporadic.M23 _ hsimp (m23PresentedEquiv hcard h)

end Model

theorem lift_gen_rels7 {G : Type*} [Group G] (e : Fin 7 → G)
    (hp : ∀ r ∈ m23Rels, FreeGroup.lift e (FreeGroup.mk r) = 1) :
    ∀ r ∈ {r : FreeGroup (Fin 7) | r ∈ m23Rels.map FreeGroup.mk}, FreeGroup.lift e r = 1 := by
  intro r hr
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
  exact hp w hw

section Recognition

theorem exists_mulEquiv_m23_of_relations (hcard : Nat.card NativeSporadic.M23 = 10200960)
    (hsimp : IsSimpleGroup NativeSporadic.M23) {G : Type*} [Group G] (e : Fin 7 → G)
    (h : M23Facts) (hp : ∀ r ∈ m23Rels, FreeGroup.lift e (FreeGroup.mk r) = 1)
    (hK : Subgroup.closure (Set.range e) ≠ ⊥) :
    Nonempty (Subgroup.closure (Set.range e) ≃* NativeSporadic.M23) := by
  have hsimple := isSimpleGroup_m23Presented hcard hsimp h
  let ψ : m23Presented →* G := PresentedGroup.toGroup (lift_gen_rels7 e hp)
  have hrange : ψ.range = Subgroup.closure (Set.range e) := by
    have hcomp : (ψ ∘ PresentedGroup.of) = e := funext fun i => PresentedGroup.toGroup.of _
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
  exact ⟨((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)).symm.trans
    (m23PresentedEquiv hcard h)⟩

end Recognition

end CFSG.CGT.T75M23
