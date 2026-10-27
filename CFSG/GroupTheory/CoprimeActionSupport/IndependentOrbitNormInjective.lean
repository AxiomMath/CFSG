module


public import Mathlib.RepresentationTheory.Basic

public section

namespace CFSG.GroupTheory.CoprimeActionSupport.IndependentOrbitNormInjective

theorem injective {F : Type*} [Field F] {A : Type*} [Group A] [Fintype A]
    {V : Type*} [AddCommGroup V] [Module F V] (ρ : Representation F A V) (E : Submodule F V)
    (hInd : iSupIndep (fun a : A => E.map (ρ a))) :
    Function.Injective ((∑ a : A, ρ a).comp E.subtype) := by
  classical
  rw [injective_iff_map_eq_zero]
  rintro ⟨e, he⟩ h
  have hN : ∑ a : A, ρ a e = 0 := by
    simpa [LinearMap.sum_apply] using h
  have key : ∀ a0 : A, ρ a0 e = 0 := by
    intro a0
    have hd := hInd.disjoint_biSup (x := a0)
      (y := ((Finset.univ.erase a0 : Finset A) : Set A)) (by simp)
    have h1 : ρ a0 e ∈ E.map (ρ a0) := Submodule.mem_map_of_mem he
    have h2 : ∑ a ∈ Finset.univ.erase a0, ρ a e ∈
        ⨆ i ∈ ((Finset.univ.erase a0 : Finset A) : Set A), E.map (ρ i) :=
      Submodule.sum_mem_biSup (fun i _ => Submodule.mem_map_of_mem he)
    have h3 : ρ a0 e = -∑ a ∈ Finset.univ.erase a0, ρ a e := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a0)] at hN
      exact eq_neg_of_add_eq_zero_left hN
    have h4 : ρ a0 e ∈ ⨆ i ∈ ((Finset.univ.erase a0 : Finset A) : Set A), E.map (ρ i) := by
      rw [h3]; exact neg_mem h2
    have h5 : ρ a0 e ∈ E.map (ρ a0) ⊓
        ⨆ i ∈ ((Finset.univ.erase a0 : Finset A) : Set A), E.map (ρ i) :=
      Submodule.mem_inf.2 ⟨h1, h4⟩
    rw [disjoint_iff.mp hd] at h5
    exact (Submodule.mem_bot F).mp h5
  apply Subtype.ext
  have h1 := key 1
  simpa using h1

theorem fixed_range {F : Type*} [Field F] {A : Type*} [Group A] [Fintype A]
    {V : Type*} [AddCommGroup V] [Module F V] (ρ : Representation F A V) (E : Submodule F V) :
    LinearMap.range ((∑ a : A, ρ a).comp E.subtype) ≤
      {v : V | ∀ a : A, ρ a v = v} := by
  rintro _ ⟨e, rfl⟩ a
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.sum_apply, Set.mem_setOf_eq]
  rw [map_sum]
  simp only [← Module.End.mul_apply, ← map_mul]
  exact Equiv.sum_comp (Equiv.mulLeft a) (fun b => ρ b (e : V))
