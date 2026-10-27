module

public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.ComponentClassification.GrSLit.HeKN

open CFSG Subgroup
open scoped commutatorElement

variable {X : Type} [Group X]

theorem subgroupOf_map_conj (D K : Subgroup X) (g : ↥D) :
    (K.subgroupOf D).map (MulAut.conj g).toMonoidHom =
      (K.map (MulAut.conj (g : X)).toMonoidHom).subgroupOf D := by
  ext x
  simp only [mem_map, mem_subgroupOf, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨(y : X), hy, by simp⟩
  · rintro ⟨k, hk, hkx⟩
    have hkD : k ∈ D := by
      have : k = (g : X)⁻¹ * (x : X) * (g : X) := by rw [← hkx]; group
      rw [this]
      exact mul_mem (mul_mem (inv_mem g.2) x.2) g.2
    refine ⟨⟨k, hkD⟩, hk, ?_⟩
    exact Subtype.ext (by simpa using hkx)

theorem isComponent_map_conj [Finite X] {D K : Subgroup X}
    (hK : IsComponent (K.subgroupOf D)) (g : ↥D) :
    IsComponent ((K.map (MulAut.conj (g : X)).toMonoidHom).subgroupOf D) := by
  rw [← subgroupOf_map_conj]
  exact LocalCores.isComponent_map_mulEquiv (MulAut.conj g) hK

theorem commute_of_components [Finite X] {D K K' : Subgroup X} (hKD : K ≤ D) (hK'D : K' ≤ D)
    (hK : IsComponent (K.subgroupOf D)) (hK' : IsComponent (K'.subgroupOf D)) (hne : K ≠ K') :
    ∀ x ∈ K, ∀ y ∈ K', x * y = y * x := by
  rcases LocalCores.distinct_components_commute hK hK' with h | h
  · exfalso
    apply hne
    have h1 := Subgroup.subgroupOf_inj.mp h
    rwa [inf_eq_left.mpr hKD, inf_eq_left.mpr hK'D] at h1
  · intro x hx y hy
    have h1 : ⁅(⟨x, hKD hx⟩ : ↥D), (⟨y, hK'D hy⟩ : ↥D)⁆ ∈ ⁅K.subgroupOf D, K'.subgroupOf D⁆ :=
      commutator_mem_commutator (mem_subgroupOf.mpr hx) (mem_subgroupOf.mpr hy)
    rw [h, mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact congrArg Subtype.val h1

theorem map_conj_map_conj (K : Subgroup X) (a g : X) :
    (K.map (MulAut.conj g).toMonoidHom).map (MulAut.conj a).toMonoidHom =
      K.map (MulAut.conj (a * g)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [mul_assoc]

theorem card_map_conj (K : Subgroup X) (a : X) :
    Nat.card (K.map (MulAut.conj a).toMonoidHom) = Nat.card K :=
  Subgroup.card_map_of_injective (f := (MulAut.conj a).toMonoidHom) (MulAut.conj a).injective

theorem map_conj_le {D K : Subgroup X} (hKD : K ≤ D) {g : X} (hg : g ∈ D) :
    K.map (MulAut.conj g).toMonoidHom ≤ D := by
  rintro _ ⟨k, hk, rfl⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  exact mul_mem (mul_mem hg (hKD hk)) (inv_mem hg)

theorem map_conj_eq_of_commute {K : Subgroup X} {a : X} (haK : ∀ k ∈ K, a * k = k * a) :
    K.map (MulAut.conj a).toMonoidHom = K := by
  ext x
  simp only [mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨k, hk, rfl⟩
    rw [haK k hk, mul_inv_cancel_right]
    exact hk
  · intro hx
    exact ⟨x, hx, by rw [haK x hx, mul_inv_cancel_right]⟩

end CFSG.ComponentClassification.GrSLit.HeKN
