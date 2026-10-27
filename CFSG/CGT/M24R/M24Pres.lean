module

public import CFSG.CGT.M24R.M24Enum
public import CFSG.CGT.M24R.M24Native

public section

namespace CFSG.CGT.M24R

open CFSG.CosetTable CFSG.Blueprint CFSG.Sporadic.Mathieu

section Model

noncomputable def m24Phi (h : m24TabCheck = true) : m24Presented →* NativeSporadic.M24 :=
  PresentedGroup.toGroup (f := m24Gen) fun r hr => by
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
    exact lift_m24Gen_eq_one h hw

theorem m24Phi_of (h : m24TabCheck = true) (i : Fin 11) :
    m24Phi h (PresentedGroup.of i) = m24Gen i :=
  PresentedGroup.toGroup.of _

theorem m24Phi_surjective (h : m24TabCheck = true) : Function.Surjective (m24Phi h) := by
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← closure_m24Gen h, Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  exact ⟨PresentedGroup.of i, m24Phi_of h i⟩

theorem m24Phi_bijective (hE : n8Sub.FiniteIndex ∧ n8Sub.index ≤ 759) (hT : m24TabCheck = true)
    (hN8 : N8Bound) : Function.Bijective (m24Phi hT) := by
  obtain ⟨hfin, hcard⟩ := m24Presented_card_le hE hN8
  have := hfin
  refine (m24Phi_surjective hT).bijective_of_nat_card_le ?_
  rw [card_M24]
  exact hcard

noncomputable def m24PresentedEquiv (hE : n8Sub.FiniteIndex ∧ n8Sub.index ≤ 759)
    (hT : m24TabCheck = true) (hN8 : N8Bound) : m24Presented ≃* NativeSporadic.M24 :=
  MulEquiv.ofBijective _ (m24Phi_bijective hE hT hN8)

theorem isSimpleGroup_m24Presented (hE : n8Sub.FiniteIndex ∧ n8Sub.index ≤ 759)
    (hT : m24TabCheck = true) (hN8 : N8Bound) : IsSimpleGroup m24Presented :=
  @MulEquiv.isSimpleGroup m24Presented _ NativeSporadic.M24 _ fam_m24_simplicity.2.2
    (m24PresentedEquiv hE hT hN8)

end Model

theorem lift_gen_m24Rels {G : Type*} [Group G] (e : Fin 11 → G)
    (hp : ∀ r ∈ m24Rels, FreeGroup.lift e (FreeGroup.mk r) = 1) :
    ∀ r ∈ {r : FreeGroup (Fin 11) | r ∈ m24Rels.map FreeGroup.mk}, FreeGroup.lift e r = 1 := by
  intro r hr
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
  exact hp w hw

section Recognition

theorem exists_mulEquiv_m24_of_relations (hE : n8Sub.FiniteIndex ∧ n8Sub.index ≤ 759)
    (hT : m24TabCheck = true) (hN8 : N8Bound) {G : Type*} [Group G] (e : Fin 11 → G)
    (hp : ∀ r ∈ m24Rels, FreeGroup.lift e (FreeGroup.mk r) = 1)
    (hK : Subgroup.closure (Set.range e) ≠ ⊥) :
    Nonempty (Subgroup.closure (Set.range e) ≃* NativeSporadic.M24) := by
  have hsimple := isSimpleGroup_m24Presented hE hT hN8
  let ψ : m24Presented →* G := PresentedGroup.toGroup (lift_gen_m24Rels e hp)
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
    (m24PresentedEquiv hE hT hN8)⟩

end Recognition

end CFSG.CGT.M24R
