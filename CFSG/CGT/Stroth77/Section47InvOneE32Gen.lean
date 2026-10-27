module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.Group
import CFSG.GroupTheory.CommuteOfSqEqOne
import TauCeti.Algebra.Group.Subgroup.ZPowers
import TauCeti.GroupTheory.Index.Basic

public section

namespace CFSG.CGT.Stroth77

open scoped Pointwise

namespace Stroth47Core

section Group

variable {G : Type*} [Group G]

theorem elab_sup_zpowers {U : Subgroup G} {f : G} (hU : ∀ x ∈ U, x * x = 1)
    (hf : f * f = 1) (hUf : U ≤ Subgroup.centralizer {f}) (hfU : f ∉ U) :
    (∀ x ∈ U ⊔ Subgroup.zpowers f, x * x = 1) ∧
      Nat.card ↥(U ⊔ Subgroup.zpowers f) = 2 * Nat.card U := by
  have hf2 : orderOf f = 2 := orderOf_eq_prime (by rwa [sq]) fun h => hfU (h ▸ U.one_mem)
  have hzf : ∀ z ∈ Subgroup.zpowers f, z = 1 ∨ z = f := fun z =>
    (Subgroup.mem_zpowers_iff_of_orderOf_eq_two hf2).mp
  have hnorm : U ≤ Subgroup.normalizer (Subgroup.zpowers f : Set G) := fun x hx =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun z hz => by
      rcases hzf z hz with rfl | rfl
      · simp
      · exact (Subgroup.mem_centralizer_singleton_iff.mp (hUf hx)).symm)
  refine ⟨fun x hx => ?_, ?_⟩
  · change x ∈ ((U ⊔ Subgroup.zpowers f : Subgroup G) : Set G) at hx
    rw [Subgroup.coe_mul_of_left_le_normalizer_right U (Subgroup.zpowers f) hnorm] at hx
    obtain ⟨u, hu, z, hz, rfl⟩ := Set.mem_mul.mp hx
    rcases hzf z hz with h | h <;> rw [h]
    · rw [mul_one, hU u hu]
    · rw [show u * f * (u * f) = u * (f * u) * f by group,
        ← Subgroup.mem_centralizer_singleton_iff.mp (hUf hu), ← mul_assoc, hU u hu, one_mul, hf]
  · have h := Subgroup.relIndex_mul_card U (U ⊔ Subgroup.zpowers f)
    rw [Subgroup.relIndex_sup_eq_two _ hnorm (Subgroup.mem_zpowers f) hfU hzf,
      inf_eq_left.2 le_sup_left] at h
    exact h.symm

theorem elab_closure_insert {x₁ x₂ x₃ x₄ f : G}
    (hU : ∀ x ∈ Subgroup.closure {x₁, x₂, x₃, x₄}, x * x = 1) (hf : f * f = 1)
    (h₁ : f * x₁ = x₁ * f) (h₂ : f * x₂ = x₂ * f) (h₃ : f * x₃ = x₃ * f) (h₄ : f * x₄ = x₄ * f)
    (hfU : f ∉ Subgroup.closure {x₁, x₂, x₃, x₄}) :
    (∀ x ∈ Subgroup.closure {x₁, x₂, x₃, x₄, f}, x * x = 1) ∧
      Nat.card (Subgroup.closure {x₁, x₂, x₃, x₄, f}) =
        2 * Nat.card (Subgroup.closure {x₁, x₂, x₃, x₄}) := by
  have hcl : Subgroup.closure {x₁, x₂, x₃, x₄, f} =
      Subgroup.closure {x₁, x₂, x₃, x₄} ⊔ Subgroup.zpowers f := by
    rw [show ({x₁, x₂, x₃, x₄, f} : Set G) = {x₁, x₂, x₃, x₄} ∪ {f} from by
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union, or_assoc],
      Subgroup.closure_union, Subgroup.zpowers_eq_closure]
  have hcent : Subgroup.closure {x₁, x₂, x₃, x₄} ≤ Subgroup.centralizer {f} := by
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact Subgroup.mem_centralizer_singleton_iff.mpr h₁.symm
    · exact Subgroup.mem_centralizer_singleton_iff.mpr h₂.symm
    · exact Subgroup.mem_centralizer_singleton_iff.mpr h₃.symm
    · exact Subgroup.mem_centralizer_singleton_iff.mpr h₄.symm
  rw [hcl]
  exact elab_sup_zpowers hU hf hcent hfU

theorem le_centralizer_of_mul_self {E : Subgroup G} (hE : ∀ x ∈ E, x * x = 1) {y : G}
    (hy : y ∈ E) : E ≤ Subgroup.centralizer {y} := fun x hx =>
  Subgroup.mem_centralizer_singleton_iff.mpr <| commute_of_sq_eq_one ((sq x).trans (hE x hx))
    ((sq y).trans (hE y hy)) ((sq _).trans (hE _ (mul_mem hx hy)))

theorem exists_elab_of_conj {y y' g : G} {n : ℕ} (h : y = g⁻¹ * y' * g)
    (hE : ∃ E : Subgroup G, E ≤ Subgroup.centralizer {y'} ∧ (∀ x ∈ E, x * x = 1) ∧
      Nat.card E = n) :
    ∃ E : Subgroup G, E ≤ Subgroup.centralizer {y} ∧ (∀ x ∈ E, x * x = 1) ∧ Nat.card E = n := by
  obtain ⟨E, hEcent, hEsq, hEcard⟩ := hE
  have hconj : ∀ x : G, (MulAut.conj g⁻¹) x = g⁻¹ * x * g := by
    intro x
    rw [MulAut.conj_apply]
    group
  refine ⟨E.map (MulAut.conj g⁻¹).toMonoidHom, ?_, ?_, ?_⟩
  · intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hx
    have hey : e * y' = y' * e := Subgroup.mem_centralizer_singleton_iff.mp (hEcent he)
    change (MulAut.conj g⁻¹) e * y = y * (MulAut.conj g⁻¹) e
    calc (MulAut.conj g⁻¹) e * y
        = (g⁻¹ * e * g) * (g⁻¹ * y' * g) := by rw [hconj e, h]
      _ = g⁻¹ * (e * y') * g := by group
      _ = g⁻¹ * (y' * e) * g := by rw [hey]
      _ = (g⁻¹ * y' * g) * (g⁻¹ * e * g) := by group
      _ = y * (MulAut.conj g⁻¹) e := by rw [hconj e, h]
  · intro x hx
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hx
    change (MulAut.conj g⁻¹) e * (MulAut.conj g⁻¹) e = 1
    calc (MulAut.conj g⁻¹) e * (MulAut.conj g⁻¹) e
        = (g⁻¹ * e * g) * (g⁻¹ * e * g) := by rw [hconj e]
      _ = g⁻¹ * (e * e) * g := by group
      _ = 1 := by rw [hEsq e he]; group
  · rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hEcard]

end Group

end Stroth47Core

end CFSG.CGT.Stroth77
