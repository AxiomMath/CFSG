module

public import CFSG.LocalAnalysis.ComponentInitial.LocalBMaximalPropagation
public import CFSG.Blueprint.Catalog

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.P51e.Comp

open CFSG Subgroup
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

variable {P P' : Type} [Group P] [Group P']

theorem centralizer_map_mulEquiv (θ : P ≃* P') (z : P) :
    centralizer {θ z} = (centralizer {z}).map θ.toMonoidHom := by
  ext y
  rw [mem_centralizer_singleton_iff, mem_map]
  constructor
  · intro h
    refine ⟨θ.symm y, ?_, θ.apply_symm_apply y⟩
    rw [mem_centralizer_singleton_iff]
    apply θ.injective
    rw [map_mul, map_mul, θ.apply_symm_apply, h]
  · rintro ⟨x, hx, rfl⟩
    rw [mem_centralizer_singleton_iff] at hx
    change θ x * θ z = θ z * θ x
    rw [← map_mul, ← map_mul, hx]

theorem comp_map_mulEquiv (θ : P ≃* P') {z : P} {L : Subgroup P} (hLH : L ≤ centralizer {z})
    (hL : IsPComponent 2 (L.subgroupOf (centralizer {z}))) :
    L.map θ.toMonoidHom ≤ centralizer {θ z} ∧
      IsPComponent 2 ((L.map θ.toMonoidHom).subgroupOf (centralizer {θ z})) := by
  rw [centralizer_map_mulEquiv θ z]
  refine ⟨map_mono hLH, ?_⟩
  have h := LocalAnalysis.ComponentInitial.isPComponent_map_of_isPComponent 2
    (θ.subgroupMap (centralizer {z})) hL
  have hmap : (L.subgroupOf (centralizer {z})).map (θ.subgroupMap (centralizer {z})).toMonoidHom =
      (L.map θ.toMonoidHom).subgroupOf ((centralizer {z}).map θ.toMonoidHom) := by
    ext ⟨y, hy⟩
    simp only [mem_subgroupOf, mem_map]
    constructor
    · rintro ⟨⟨x, hxH⟩, hx, hxy⟩
      exact ⟨x, hx, congrArg Subtype.val hxy⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hLH hx⟩, hx, rfl⟩
  rw [hmap] at h
  exact h

theorem fixedSubgroup_conj_eq (g : P) : fixedSubgroup (MulAut.conj g) = centralizer {g} := by
  ext x
  rw [mem_centralizer_singleton_iff]
  change MulAut.conj g x = x ↔ _
  rw [MulAut.conj_apply]
  constructor
  · intro h
    calc x * g = g * x * g⁻¹ * g := by rw [h]
      _ = g * x := by group
  · intro h
    rw [← h, mul_inv_cancel_right]

theorem mul_self_eq_one_of_orderOf_conj (hZ : center P = ⊥) {g : P}
    (hg : orderOf (MulAut.conj g) = 2) : g * g = 1 ∧ g ≠ 1 := by
  have h2 : MulAut.conj (g * g) = 1 := by
    rw [map_mul, ← pow_two, ← hg, pow_orderOf_eq_one]
  have hc : g * g ∈ center P := by
    rw [mem_center_iff]
    intro x
    have e := congrArg (fun α : MulAut P => α x) h2
    simp only [MulAut.conj_apply, MulAut.one_apply] at e
    calc x * (g * g) = g * g * x * (g * g)⁻¹ * (g * g) := by rw [e]
      _ = g * g * x := by group
  rw [hZ, mem_bot] at hc
  refine ⟨hc, fun h1 => ?_⟩
  rw [h1, map_one, orderOf_one] at hg
  exact absurd hg (by norm_num)

theorem center_eq_bot_of_orderOf_conj [IsSimpleGroup P] {g : P}
    (hg : orderOf (MulAut.conj g) = 2) : center P = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center P) with h | h
  · exact h
  · exfalso
    have hgc : g ∈ center P := h ▸ mem_top g
    have hg1 : MulAut.conj g = 1 := by
      ext x
      rw [MulAut.conj_apply, MulAut.one_apply, (mem_center_iff.1 hgc x).symm,
        mul_inv_cancel_right]
    rw [hg1, orderOf_one] at hg
    exact absurd hg (by norm_num)

theorem exists_comp_of_isComponent [Finite P] (θ : P ≃* P') (g : P)
    {L : Subgroup (fixedSubgroup (MulAut.conj g))} (hL : IsComponent L) :
    ∃ L' : Subgroup P', L' ≤ centralizer {θ g} ∧
      IsPComponent 2 (L'.subgroupOf (centralizer {θ g})) ∧ Nonempty (L ≃* L') := by
  set C := centralizer ({g} : Set P) with hC
  set ψ := MulEquiv.subgroupCongr (fixedSubgroup_conj_eq g) with hψ
  have hL₁ := LocalCores.isComponent_map_mulEquiv ψ hL
  set L₂ := (L.map ψ.toMonoidHom).map C.subtype with hL₂
  have hL₂C : L₂ ≤ C := map_subtype_le _
  have hL₂s : L₂.subgroupOf C = L.map ψ.toMonoidHom :=
    Subgroup.comap_map_eq_self_of_injective C.subtype_injective _
  have hp : IsPComponent 2 (L₂.subgroupOf C) := by
    rw [hL₂s]
    exact LocalAnalysis.ComponentInitial.isPComponent_two_of_isComponent hL₁
  obtain ⟨hle, hcomp⟩ := comp_map_mulEquiv θ hL₂C hp
  exact ⟨L₂.map θ.toMonoidHom, hle, hcomp, ⟨(L.equivMapOfInjective ψ.toMonoidHom ψ.injective).trans
    (((L.map ψ.toMonoidHom).equivMapOfInjective C.subtype C.subtype_injective).trans
      (L₂.equivMapOfInjective θ.toMonoidHom θ.injective))⟩⟩

theorem exists_fixed_comp_of_isComponent (θ : P ≃* P') (g : P)
    {L : Subgroup (fixedSubgroup (MulAut.conj g))} (hL : IsComponent L) :
    ∃ L' : Subgroup (fixedSubgroup (MulAut.conj (θ g))), IsComponent L' ∧ Nonempty (L ≃* L') := by
  have heq : (fixedSubgroup (MulAut.conj g)).map θ.toMonoidHom =
      fixedSubgroup (MulAut.conj (θ g)) := by
    rw [fixedSubgroup_conj_eq, fixedSubgroup_conj_eq, centralizer_map_mulEquiv θ g]
  set ψ := (θ.subgroupMap (fixedSubgroup (MulAut.conj g))).trans (MulEquiv.subgroupCongr heq)
    with hψ
  exact ⟨L.map ψ.toMonoidHom, LocalCores.isComponent_map_mulEquiv ψ hL,
    ⟨L.equivMapOfInjective ψ.toMonoidHom ψ.injective⟩⟩

theorem statedClassicalModel_of_lieModel {G : Type} [Group G]
    {t : Assembly.LowTwoRank.StatedLieTag} {n p f : ℕ} (ht : t ∈ Blueprint.classicalTags)
    (h : Blueprint.LieModel G t n p f) :
    Assembly.LowTwoRank.StatedClassicalModel G t n p f :=
  CFSG.Blueprint.LieModel.statedClassicalModel h ht

end CFSG.ComponentClassification.HarrisLit.T1.P51e.Comp
