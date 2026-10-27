module

public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Fintype.Lattice

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

theorem exists_min_odd_add_two_le {ι : Type*} {I : Finset ι} (hI : I.Nonempty) (h : ι → ℤ)
    (hodd : ∀ i ∈ I, Odd (h i)) (hinj : Set.InjOn h I) :
    ∃ i₀ ∈ I, ∀ j ∈ I, j ≠ i₀ → h i₀ + 2 ≤ h j := by
  obtain ⟨i₀, hi₀, hmin⟩ := I.exists_min_image h hI
  refine ⟨i₀, hi₀, fun j hj hji => ?_⟩
  have hle : h i₀ ≤ h j := hmin j hj
  have hne : h i₀ ≠ h j := fun e => hji (hinj hj hi₀ e.symm)
  obtain ⟨a, ha⟩ := hodd i₀ hi₀
  obtain ⟨b, hb⟩ := hodd j hj
  omega

theorem exists_min_odd_add_two_le_nat {ι : Type*} {I : Finset ι} (hI : I.Nonempty) (h : ι → ℕ)
    (hodd : ∀ i ∈ I, Odd (h i)) (hinj : Set.InjOn h I) :
    ∃ i₀ ∈ I, ∀ j ∈ I, j ≠ i₀ → h i₀ + 2 ≤ h j := by
  obtain ⟨i₀, hi₀, hmin⟩ := I.exists_min_image h hI
  refine ⟨i₀, hi₀, fun j hj hji => ?_⟩
  have hle : h i₀ ≤ h j := hmin j hj
  have hne : h i₀ ≠ h j := fun e => hji (hinj hj hi₀ e.symm)
  obtain ⟨a, ha⟩ := hodd i₀ hi₀
  obtain ⟨b, hb⟩ := hodd j hj
  omega

theorem exists_min_odd_add_two_le_of_injective {ι : Type*} [Finite ι] [Nonempty ι] (h : ι → ℤ)
    (hodd : ∀ i, Odd (h i)) (hinj : Function.Injective h) :
    ∃ i₀ : ι, ∀ j, j ≠ i₀ → h i₀ + 2 ≤ h j := by
  obtain ⟨i₀, hmin⟩ := Finite.exists_min h
  refine ⟨i₀, fun j hj => ?_⟩
  have hle : h i₀ ≤ h j := hmin j
  have hne : h i₀ ≠ h j := fun e => hj (hinj e.symm)
  obtain ⟨a, ha⟩ := hodd i₀
  obtain ⟨b, hb⟩ := hodd j
  omega

end CFSG.FeitThompson
