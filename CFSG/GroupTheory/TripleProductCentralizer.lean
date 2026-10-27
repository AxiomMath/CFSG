module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Tactic.Group

public section

namespace CFSG.GroupTheory

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem triple_product_mem_centralizer {K : Subgroup G} {e : G} (he3 : e ^ 3 = 1)
    (hK1 : ⁅K, K.map (MulAut.conj e).toMonoidHom⁆ = ⊥)
    (hK2 : ⁅K, K.map (MulAut.conj (e ^ 2)).toMonoidHom⁆ = ⊥)
    {c : G} (hc : c ∈ K) :
    c * (e * c * e⁻¹) * (e ^ 2 * c * e⁻¹ ^ 2) ∈ centralizer ({e} : Set G) := by
  have hc1 : e * c * e⁻¹ ∈ K.map (MulAut.conj e).toMonoidHom :=
    Subgroup.mem_map.mpr ⟨c, hc, by simp [MulAut.conj_apply]⟩
  have hc2 : e ^ 2 * c * e⁻¹ ^ 2 ∈ K.map (MulAut.conj (e ^ 2)).toMonoidHom := by
    refine Subgroup.mem_map.mpr ⟨c, hc, ?_⟩
    change (MulAut.conj (e ^ 2)) c = e ^ 2 * c * e⁻¹ ^ 2
    rw [MulAut.conj_apply, inv_pow]
  have hcent1 : K ≤ centralizer (K.map (MulAut.conj e).toMonoidHom : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hK1
  have hcent2 : K ≤ centralizer (K.map (MulAut.conj (e ^ 2)).toMonoidHom : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hK2
  have hcc1 : Commute c (e * c * e⁻¹) :=
    (Subgroup.mem_centralizer_iff.mp (hcent1 hc) _ hc1).symm
  have hcc2 : Commute c (e ^ 2 * c * e⁻¹ ^ 2) :=
    (Subgroup.mem_centralizer_iff.mp (hcent2 hc) _ hc2).symm
  have h3inv : (e⁻¹) ^ 3 = 1 := by
    rw [inv_pow, he3, inv_one]
  have e1 : e * (e * c * e⁻¹) * e⁻¹ = e ^ 2 * c * e⁻¹ ^ 2 := by
    simp only [pow_two]
    group
  have e2 : e * (e ^ 2 * c * e⁻¹ ^ 2) * e⁻¹ = c := by
    calc e * (e ^ 2 * c * e⁻¹ ^ 2) * e⁻¹ = e ^ 3 * c * (e⁻¹) ^ 3 := by group
      _ = c := by rw [he3, h3inv, mul_one, one_mul]
  have hconj : e * (c * (e * c * e⁻¹) * (e ^ 2 * c * e⁻¹ ^ 2)) * e⁻¹ =
      (e * c * e⁻¹) * (e ^ 2 * c * e⁻¹ ^ 2) * c := by
    calc e * (c * (e * c * e⁻¹) * (e ^ 2 * c * e⁻¹ ^ 2)) * e⁻¹
        = (e * c * e⁻¹) * (e * (e * c * e⁻¹) * e⁻¹) *
            (e * (e ^ 2 * c * e⁻¹ ^ 2) * e⁻¹) := by group
      _ = (e * c * e⁻¹) * (e ^ 2 * c * e⁻¹ ^ 2) * c := by rw [e1, e2]
  have hreorder : (e * c * e⁻¹) * (e ^ 2 * c * e⁻¹ ^ 2) * c =
      c * (e * c * e⁻¹) * (e ^ 2 * c * e⁻¹ ^ 2) := by
    calc (e * c * e⁻¹) * (e ^ 2 * c * e⁻¹ ^ 2) * c
        = (e * c * e⁻¹) * ((e ^ 2 * c * e⁻¹ ^ 2) * c) := by rw [mul_assoc]
      _ = (e * c * e⁻¹) * (c * (e ^ 2 * c * e⁻¹ ^ 2)) := by rw [← hcc2.eq]
      _ = ((e * c * e⁻¹) * c) * (e ^ 2 * c * e⁻¹ ^ 2) := (mul_assoc _ _ _).symm
      _ = (c * (e * c * e⁻¹)) * (e ^ 2 * c * e⁻¹ ^ 2) := by rw [← hcc1.eq]
      _ = c * (e * c * e⁻¹) * (e ^ 2 * c * e⁻¹ ^ 2) := rfl
  have hfix : e * (c * (e * c * e⁻¹) * (e ^ 2 * c * e⁻¹ ^ 2)) * e⁻¹ =
      c * (e * c * e⁻¹) * (e ^ 2 * c * e⁻¹ ^ 2) := hconj.trans hreorder
  have heq : e * (c * (e * c * e⁻¹) * (e ^ 2 * c * e⁻¹ ^ 2)) =
      c * (e * c * e⁻¹) * (e ^ 2 * c * e⁻¹ ^ 2) * e := by
    have := congrArg (· * e) hfix
    simpa [mul_assoc] using this
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst y
  exact heq

end CFSG.GroupTheory
