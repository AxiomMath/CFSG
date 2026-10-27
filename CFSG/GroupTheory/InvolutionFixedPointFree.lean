module

public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Tactic.Group
public import Mathlib.Algebra.Group.Subgroup.Finite

public section

namespace CFSG.GroupTheory

open Subgroup

variable {G : Type*} [Group G] [Finite G]

theorem mul_mul_inv_eq_inv_of_inf_centralizer_eq_bot {K : Subgroup G} {z : G} (hz : z * z = 1)
    (hzK : ∀ k ∈ K, z * k * z⁻¹ ∈ K) (hfix : K ⊓ centralizer ({z} : Set G) = ⊥) :
    ∀ k ∈ K, z * k * z⁻¹ = k⁻¹ := by
  have hz' : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  let φ : K → K := fun x => ⟨(x : G)⁻¹ * (z * x * z⁻¹), K.mul_mem (K.inv_mem x.2) (hzK x x.2)⟩
  have hinj : Function.Injective φ := by
    intro x y hxy
    have h1 : (x : G)⁻¹ * (z * x * z⁻¹) = (y : G)⁻¹ * (z * y * z⁻¹) := congrArg Subtype.val hxy
    have h3 : (y : G) * (x : G)⁻¹ = z * ((y : G) * (x : G)⁻¹) * z⁻¹ := by
      calc (y : G) * (x : G)⁻¹
          = (y : G) * ((x : G)⁻¹ * (z * x * z⁻¹)) * (z * x * z⁻¹)⁻¹ := by group
        _ = (y : G) * ((y : G)⁻¹ * (z * y * z⁻¹)) * (z * x * z⁻¹)⁻¹ := by rw [h1]
        _ = z * ((y : G) * (x : G)⁻¹) * z⁻¹ := by group
    have h2 : (y : G) * (x : G)⁻¹ ∈ K ⊓ centralizer ({z} : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨K.mul_mem y.2 (K.inv_mem x.2), ?_⟩
      rw [mem_centralizer_singleton_iff]
      calc (y : G) * (x : G)⁻¹ * z = z * ((y : G) * (x : G)⁻¹) * z⁻¹ * z := by rw [← h3]
        _ = z * ((y : G) * (x : G)⁻¹) := by group
    rw [hfix, Subgroup.mem_bot] at h2
    exact Subtype.ext (mul_inv_eq_one.mp h2).symm
  have hsurj : Function.Surjective φ := Finite.injective_iff_surjective.mp hinj
  intro k hk
  obtain ⟨x, hx⟩ := hsurj ⟨k, hk⟩
  have hkx : k = (x : G)⁻¹ * (z * x * z⁻¹) := (congrArg Subtype.val hx).symm
  rw [hkx, hz']
  calc z * ((x : G)⁻¹ * (z * x * z)) * z = z * (x : G)⁻¹ * z * x * (z * z) := by group
    _ = z * (x : G)⁻¹ * z * x := by rw [hz, mul_one]
    _ = z⁻¹ * (x : G)⁻¹ * z⁻¹ * x := by rw [hz']
    _ = ((x : G)⁻¹ * (z * x * z))⁻¹ := by group

theorem mul_mem_centralizer_of_isConj_of_inf_centralizer_eq_bot {K : Subgroup G} [K.Normal]
    {z t : G} (hz : z * z = 1) (ht : t * t = 1) (hconj : IsConj z t)
    (hfix : K ⊓ centralizer ({z} : Set G) = ⊥) : t * z ∈ centralizer (K : Set G) := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hconj
  have hfix' : K ⊓ centralizer ({t} : Set G) = ⊥ := by
    rw [eq_bot_iff]
    intro k hk
    rw [Subgroup.mem_bot]
    have hk1 : g⁻¹ * k * g ∈ K := by
      have := Subgroup.Normal.conj_mem inferInstance k hk.1 g⁻¹
      simpa using this
    have hk2 : g⁻¹ * k * g ∈ centralizer ({z} : Set G) := by
      have hkt : k * t = t * k := mem_centralizer_singleton_iff.mp hk.2
      rw [mem_centralizer_singleton_iff]
      rw [← hg] at hkt
      calc g⁻¹ * k * g * z = g⁻¹ * (k * (g * z * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * z * g⁻¹) * k) * g := by rw [hkt]
        _ = z * (g⁻¹ * k * g) := by group
    have hk3 : g⁻¹ * k * g ∈ K ⊓ centralizer ({z} : Set G) := Subgroup.mem_inf.mpr ⟨hk1, hk2⟩
    rw [hfix, Subgroup.mem_bot] at hk3
    calc k = g * (g⁻¹ * k * g) * g⁻¹ := by group
      _ = 1 := by rw [hk3]; group
  have hzK : ∀ k ∈ K, z * k * z⁻¹ ∈ K := fun k hk => by
    simpa using Subgroup.Normal.conj_mem inferInstance k hk z
  have htK : ∀ k ∈ K, t * k * t⁻¹ ∈ K := fun k hk => by
    simpa using Subgroup.Normal.conj_mem inferInstance k hk t
  have hzi := mul_mul_inv_eq_inv_of_inf_centralizer_eq_bot hz hzK hfix
  have hti := mul_mul_inv_eq_inv_of_inf_centralizer_eq_bot ht htK hfix'
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have h1 : t * (z * k * z⁻¹) * t⁻¹ = k := by
    rw [hzi k hk]
    calc t * k⁻¹ * t⁻¹ = (t * k * t⁻¹)⁻¹ := by group
      _ = k := by rw [hti k hk]; group
  have h2 : (t * z) * k * (t * z)⁻¹ = k := by
    calc (t * z) * k * (t * z)⁻¹ = t * (z * k * z⁻¹) * t⁻¹ := by group
      _ = k := h1
  calc k * (t * z) = (t * z) * k * (t * z)⁻¹ * (t * z) := by rw [h2]
    _ = (t * z) * k := by group

end CFSG.GroupTheory
