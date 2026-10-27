module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup
open scoped commutatorElement

section Lift

variable {H : Type*} [Group H] {Y : Type*} [Group Y]

theorem mem_normalizer_map_comap (U : Subgroup H) (θ : ↥U →* Y) (X : Subgroup Y) {u : ↥U}
    (hu : θ u ∈ normalizer (X : Set Y)) :
    (u : H) ∈ normalizer (((X.comap θ).map U.subtype : Subgroup H) : Set H) := by
  rw [Subgroup.mem_normalizer_iff] at hu ⊢
  intro a
  constructor
  · rintro ⟨g, hg, rfl⟩
    refine ⟨u * g * u⁻¹, ?_, by simp⟩
    show θ (u * g * u⁻¹) ∈ X
    rw [map_mul, map_mul, map_inv]
    exact (hu (θ g)).1 hg
  · rintro ⟨g', hg', hga⟩
    have hga'' : (g' : H) = (u : H) * a * (u : H)⁻¹ := hga
    have hga' : a = (u : H)⁻¹ * (g' : H) * u := by
      rw [hga'']
      group
    refine ⟨u⁻¹ * g' * u, ?_, by rw [hga']; simp⟩
    show θ (u⁻¹ * g' * u) ∈ X
    rw [map_mul, map_mul, map_inv]
    refine (hu _).2 ?_
    have : θ u * ((θ u)⁻¹ * θ g' * θ u) * (θ u)⁻¹ = θ g' := by group
    rw [this]
    exact hg'

theorem u3q3_isPGroup_map_comap {p : ℕ} (U : Subgroup H) (θ : ↥U →* Y) (hθ : Function.Injective θ)
    {X : Subgroup Y} (hX : IsPGroup p ↥X) : IsPGroup p ↥((X.comap θ).map U.subtype) :=
  IsPGroup.of_equiv (hX.comap_of_injective θ hθ)
    (Subgroup.equivMapOfInjective (X.comap θ) U.subtype U.subtype_injective)

theorem u3q3_map_comap_ne_bot (U : Subgroup H) (θ : ↥U →* Y) (hθ : Function.Surjective θ)
    {X : Subgroup Y} (hX : X ≠ ⊥) : (X.comap θ).map U.subtype ≠ ⊥ := by
  obtain ⟨x, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hX
  obtain ⟨g, hg⟩ := hθ (x : Y)
  intro hbot
  have hgmem : (g : H) ∈ (X.comap θ).map U.subtype := ⟨g, by simp [hg], rfl⟩
  rw [hbot, Subgroup.mem_bot] at hgmem
  have hg1 : g = 1 := Subtype.ext hgmem
  apply hx1
  apply Subtype.ext
  rw [← hg, hg1, map_one]
  rfl

end Lift

section Odd

variable {G : Type*} [Group G] {Y : Type*} [Group Y]

theorem range_closure_odd (φ : G →* Y) (hG : Subgroup.closure {g : G | Odd (orderOf g)} = ⊤) :
    Subgroup.closure {x : Y | x ∈ φ.range ∧ Odd (orderOf x)} = φ.range := by
  apply le_antisymm
  · exact (Subgroup.closure_le _).2 fun x hx => hx.1
  · rintro _ ⟨g, rfl⟩
    have hg : g ∈ Subgroup.closure {g : G | Odd (orderOf g)} := by
      rw [hG]
      exact Subgroup.mem_top g
    have h1 := Subgroup.mem_map_of_mem φ hg
    rw [MonoidHom.map_closure] at h1
    refine (Subgroup.closure_mono ?_) h1
    rintro _ ⟨g', hg', rfl⟩
    exact ⟨⟨g', rfl⟩, Odd.of_dvd_nat hg' (orderOf_map_dvd φ g')⟩

end Odd

section Cyc

variable {A : Type*} [Group A]

theorem commutator_mem_centralizer_of_cyclic_cl {X : Subgroup A} (hX : IsCyclic ↥X) {a b : A}
    (ha : a ∈ normalizer (X : Set A)) (hb : b ∈ normalizer (X : Set A)) :
    ⁅a, b⁆ ∈ centralizer (X : Set A) := by
  classical
  let _ : CommGroup (MulAut ↥X) :=
    (IsCyclic.mulAutMulEquiv ↥X).toMonoidHom.commGroupOfInjective
      (IsCyclic.mulAutMulEquiv ↥X).injective
  let a' : ↥(normalizer (X : Set A)) := ⟨a, ha⟩
  let b' : ↥(normalizer (X : Set A)) := ⟨b, hb⟩
  have h1 : ⁅a', b'⁆ ∈ X.normalizerMonoidHom.ker := by
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)
  rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf] at h1
  exact h1

end Cyc

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
