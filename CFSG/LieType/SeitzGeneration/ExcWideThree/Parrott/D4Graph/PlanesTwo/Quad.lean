module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.Basic

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.PlanesTwo

open CFSG.RankThree.PartOne.CTP

variable {G : Type*} [Group G]

@[expose] def quadSet (x : G) (β : MulAut G) : Set G :=
  (Subgroup.centralizer ({x} : Set G) : Set G) ∪ (fixedSubgroup β : Set G) ∪
    (fixedSubgroup (MulAut.conj x * β) : Set G) ∪ (fixedSubgroup ((MulAut.conj x)⁻¹ * β) : Set G)

theorem mem_centralizer_iff_conj {x g : G} :
    g ∈ Subgroup.centralizer ({x} : Set G) ↔ MulAut.conj x g = g := by
  rw [Subgroup.mem_centralizer_singleton_iff, MulAut.conj_apply]
  constructor
  · intro h
    rw [← h, mul_inv_cancel_right]
  · intro h
    calc g * x = x * g * x⁻¹ * x := by rw [h]
      _ = x * g := by group

theorem centralizer_eq_fixedSubgroup (x : G) :
    (Subgroup.centralizer ({x} : Set G) : Set G) = (fixedSubgroup (MulAut.conj x) : Set G) := by
  ext g
  exact mem_centralizer_iff_conj

theorem quadSet_subset_fixUnion {E : Subgroup (MulAut G)} {x : G} {β : MulAut G}
    (hx : MulAut.conj x ∈ E) (hβ : β ∈ E) (hx1 : MulAut.conj x ≠ 1) (hβ1 : β ≠ 1)
    (hxβ : MulAut.conj x * β ≠ 1) (hxβ' : (MulAut.conj x)⁻¹ * β ≠ 1) :
    quadSet x β ⊆ fixUnion E := by
  rintro g (((hg | hg) | hg) | hg)
  · rw [centralizer_eq_fixedSubgroup] at hg
    exact fixedSubgroup_subset_fixUnion hx hx1 hg
  · exact fixedSubgroup_subset_fixUnion hβ hβ1 hg
  · exact fixedSubgroup_subset_fixUnion (E.mul_mem hx hβ) hxβ hg
  · exact fixedSubgroup_subset_fixUnion (E.mul_mem (E.inv_mem hx) hβ) hxβ' hg

theorem mem_fixedSubgroup_conj (ψ α : MulAut G) {g : G} (hg : α g = g) :
    (ψ * α * ψ⁻¹) (ψ g) = ψ g := by
  simp only [MulAut.mul_apply, MulAut.inv_apply_self, hg]

theorem conj_mulAut_conj (ψ : MulAut G) (x : G) :
    ψ * MulAut.conj x * ψ⁻¹ = MulAut.conj (ψ x) := by
  ext g
  simp [MulAut.mul_apply, MulAut.conj_apply]

theorem image_quadSet_subset (ψ : MulAut G) (x : G) (β : MulAut G) :
    ψ '' quadSet x β ⊆ quadSet (ψ x) (ψ * β * ψ⁻¹) := by
  have key : ∀ α : MulAut G, ∀ g, α g = g →
      (ψ * α * ψ⁻¹) (ψ g) = ψ g := fun α g hg => mem_fixedSubgroup_conj ψ α hg
  rintro _ ⟨g, (((hg | hg) | hg) | hg), rfl⟩
  · refine Or.inl (Or.inl (Or.inl ?_))
    rw [SetLike.mem_coe, mem_centralizer_iff_conj] at hg ⊢
    have := key _ g hg
    rwa [conj_mulAut_conj] at this
  · exact Or.inl (Or.inl (Or.inr (key β g hg)))
  · refine Or.inl (Or.inr ?_)
    have := key _ g hg
    rwa [show ψ * (MulAut.conj x * β) * ψ⁻¹ = (ψ * MulAut.conj x * ψ⁻¹) * (ψ * β * ψ⁻¹) by group,
      conj_mulAut_conj] at this
  · refine Or.inr ?_
    have := key _ g hg
    rwa [show ψ * ((MulAut.conj x)⁻¹ * β) * ψ⁻¹ =
        (ψ * MulAut.conj x * ψ⁻¹)⁻¹ * (ψ * β * ψ⁻¹) by group, conj_mulAut_conj] at this

theorem closure_quadSet_eq_top_of_conj (ψ : MulAut G) {x : G} {β : MulAut G}
    (h : Subgroup.closure (quadSet (ψ x) (ψ * β * ψ⁻¹)) = ⊤) :
    Subgroup.closure (quadSet x β) = ⊤ := by
  refine eq_top_of_closure_image ψ⁻¹ h ?_
  have := image_quadSet_subset ψ⁻¹ (ψ x) (ψ * β * ψ⁻¹)
  rwa [MulAut.inv_apply_self, show ψ⁻¹ * (ψ * β * ψ⁻¹) * ψ⁻¹⁻¹ = β by group] at this

theorem commute_conj_of_fixed {x : G} {β : MulAut G} (hβx : β x = x) :
    β * MulAut.conj x = MulAut.conj x * β := by
  ext g
  simp [MulAut.mul_apply, MulAut.conj_apply, hβx]

theorem coe_fixedSubgroup_inv (α : MulAut G) :
    (fixedSubgroup α⁻¹ : Set G) = fixedSubgroup α := by
  ext g
  simp only [SetLike.mem_coe, mem_fixedSubgroup]
  constructor
  · intro h
    have := congrArg (fun y => α y) h
    simp only [MulAut.apply_inv_self] at this
    exact this.symm
  · intro h
    have := congrArg (fun y => α⁻¹ y) h
    simp only [MulAut.inv_apply_self] at this
    exact this.symm

theorem quadSet_inv {x : G} {β : MulAut G} (hβx : β x = x) : quadSet x β⁻¹ = quadSet x β := by
  have hc := commute_conj_of_fixed hβx
  have e1 : (MulAut.conj x * β⁻¹)⁻¹ = (MulAut.conj x)⁻¹ * β := by
    rw [mul_inv_rev, inv_inv]
    calc β * (MulAut.conj x)⁻¹ = (MulAut.conj x)⁻¹ * (MulAut.conj x * β) * (MulAut.conj x)⁻¹ := by
          group
      _ = (MulAut.conj x)⁻¹ * (β * MulAut.conj x) * (MulAut.conj x)⁻¹ := by rw [hc]
      _ = (MulAut.conj x)⁻¹ * β := by group
  have e2 : ((MulAut.conj x)⁻¹ * β⁻¹)⁻¹ = MulAut.conj x * β := by
    rw [mul_inv_rev, inv_inv, inv_inv]
    exact hc
  unfold quadSet
  rw [coe_fixedSubgroup_inv β, ← coe_fixedSubgroup_inv (MulAut.conj x * β⁻¹), e1,
    ← coe_fixedSubgroup_inv ((MulAut.conj x)⁻¹ * β⁻¹), e2]
  ext g
  simp only [Set.mem_union]
  tauto

theorem quadSet_sq {x : G} (hx3 : x ^ 3 = 1) (β : MulAut G) : quadSet (x ^ 2) β = quadSet x β := by
  have hinv : x ^ 2 = x⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_succ]
    exact hx3
  have hcent : (Subgroup.centralizer ({x ^ 2} : Set G) : Set G) =
      Subgroup.centralizer ({x} : Set G) := by
    rw [hinv]
    ext g
    simp only [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      calc g * x = x * (x⁻¹ * g) * x := by group
        _ = x * (g * x⁻¹) * x := by rw [h]
        _ = x * g := by group
    · intro h
      calc g * x⁻¹ = x⁻¹ * (x * g) * x⁻¹ := by group
        _ = x⁻¹ * (g * x) * x⁻¹ := by rw [h]
        _ = x⁻¹ * g := by group
  unfold quadSet
  rw [hcent, hinv, map_inv, inv_inv]
  ext g
  simp only [Set.mem_union]
  tauto

theorem closure_quadSet_eq_top_of_conj_fixed {x c : G} {β : MulAut G} (hc : β c = c)
    (h : Subgroup.closure (quadSet (c * x * c⁻¹) β) = ⊤) :
    Subgroup.closure (quadSet x β) = ⊤ := by
  have hψ : MulAut.conj c * β * (MulAut.conj c)⁻¹ = β := by
    ext g
    simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_symm_apply, MulAut.inv_apply,
      map_mul, map_inv, hc]
    group
  refine closure_quadSet_eq_top_of_conj (MulAut.conj c) ?_
  rwa [hψ, MulAut.conj_apply]

end CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.PlanesTwo
