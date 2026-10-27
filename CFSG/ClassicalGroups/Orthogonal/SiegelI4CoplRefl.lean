module

public import CFSG.ClassicalGroups.Orthogonal.SiegelI4FamilyPi

public section

namespace CFSG.ClassicalGroups.Orthogonal.SiegelRT1

open CFSG.HardMathSupport.Kantor79 QuadraticMap Module

variable {K : Type*} [Field K] [CharP K 2] {V : Type*} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Qf : QuadraticForm K V}
  (hnd : ∀ x : V, (∀ y, polar Qf x y = 0) → x = 0)
include hnd

theorem exists_reflection_form {u : V ≃ₗ[K] V} (hu : ∀ v, Qf (u v) = Qf v)
    (h1 : finrank K (movedSpace u) = 1) :
    ∃ w : V, Qf w ≠ 0 ∧ movedSpace u = Submodule.span K {w} ∧
      ∀ x, u x = x + (polar Qf x w / Qf w) • w := by
  obtain ⟨w, hw0, hspan⟩ := exists_ne_zero_span_eq_of_finrank_eq_one h1
  have hQw : Qf w ≠ 0 := by
    intro hQ
    have hu1 : u = 1 := eq_one_of_movedSpace_le_span_singular hnd hu hQ hspan.le
    have h0 : movedSpace (1 : V ≃ₗ[K] V) = ⊥ := by
      rw [movedSpace, LinearMap.range_eq_bot]
      ext v
      simp
    rw [hu1, h0, finrank_bot] at h1
    omega
  have hex : ∀ x, ∃ c : K, u x = x + c • w := by
    intro x
    have hmem : u x - x ∈ Submodule.span K ({w} : Set V) := by
      rw [← hspan]
      exact sub_mem_movedSpace u x
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    exact ⟨c, by rw [hc]; abel⟩
  choose a ha using hex
  have hd : ∀ x, u x - x = a x • w := fun x => by rw [ha x]; abel
  have hadd : ∀ x y, a (x + y) = a x + a y := by
    intro x y
    apply smul_left_injective K hw0
    show a (x + y) • w = (a x + a y) • w
    rw [add_smul, ← hd, ← hd, ← hd, map_add]
    abel
  have key : ∀ x, a x = 0 ∨ a x = polar Qf x w / Qf w := by
    intro x
    have h : Qf (x + a x • w) = Qf x := by
      rw [← ha x]
      exact hu x
    simp only [QuadraticMap.map_add, QuadraticMap.map_smul, QuadraticMap.polar_smul_right,
      smul_eq_mul] at h
    have h2 : a x * (a x * Qf w + polar Qf x w) = 0 := by
      linear_combination h
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact Or.inl h3
    · refine Or.inr ?_
      rw [eq_div_iff hQw]
      have h4 : (2 : K) = 0 := CharTwo.two_eq_zero
      linear_combination h3 - polar Qf x w * h4
  have hwmem : w ∈ movedSpace u := by
    rw [hspan]
    exact Submodule.mem_span_singleton_self w
  obtain ⟨z, hz⟩ := mem_movedSpace_iff.mp hwmem
  have hz1 : a z = 1 := by
    apply smul_left_injective K hw0
    show a z • w = (1 : K) • w
    rw [one_smul, ← hd z]
    exact hz
  have hgz : a z = polar Qf z w / Qf w :=
    (key z).resolve_left (by rw [hz1]; exact one_ne_zero)
  have hfinal : ∀ x, a x = polar Qf x w / Qf w := by
    intro x
    by_cases hx : a x = 0
    · have hxz : a (x + z) = a z := by rw [hadd, hx, zero_add]
      have hne : a (x + z) ≠ 0 := by rw [hxz, hz1]; exact one_ne_zero
      have h3 : a (x + z) = polar Qf (x + z) w / Qf w := (key (x + z)).resolve_left hne
      rw [hxz, polar_add_left, add_div] at h3
      linear_combination hx + h3 - hgz
    · exact (key x).resolve_left hx
  refine ⟨w, hQw, hspan, fun x => ?_⟩
  rw [ha x, hfinal x]

theorem eq_of_finrank_movedSpace_mul_le_one {u₁ u₂ : V ≃ₗ[K] V}
    (hu₁ : ∀ v, Qf (u₁ v) = Qf v) (hu₂ : ∀ v, Qf (u₂ v) = Qf v)
    (h₁ : finrank K (movedSpace u₁) = 1) (h₂ : finrank K (movedSpace u₂) = 1)
    (h : finrank K (movedSpace (u₁ * u₂)) ≤ 1) : u₁ = u₂ := by
  obtain ⟨w₁, hQ₁, hspan₁, hform₁⟩ := exists_reflection_form hnd hu₁ h₁
  obtain ⟨w₂, hQ₂, hspan₂, hform₂⟩ := exists_reflection_form hnd hu₂ h₂
  have hw₁ : w₁ ≠ 0 := by
    rintro rfl
    exact hQ₁ (by simp)
  have hw₂ : w₂ ≠ 0 := by
    rintro rfl
    exact hQ₂ (by simp)
  by_cases hli : LinearIndependent K ![w₁, w₂]
  ·
    exfalso
    obtain ⟨x, hx1, hx2⟩ := exists_polar_pair hnd hli (Qf w₁) 0
    obtain ⟨y, hy1, hy2⟩ := exists_polar_pair hnd hli 0 (Qf w₂)
    have hu2x : u₂ x = x := by
      rw [hform₂ x, hx2, zero_div, zero_smul, add_zero]
    have hux : (u₁ * u₂) x = x + w₁ := by
      rw [LinearEquiv.mul_apply, hu2x, hform₁ x, hx1, div_self hQ₁, one_smul]
    have hu2y : u₂ y = y + w₂ := by
      rw [hform₂ y, hy2, div_self hQ₂, one_smul]
    have hu1yw : u₁ (y + w₂) = y + w₂ + (polar Qf w₂ w₁ / Qf w₁) • w₁ := by
      rw [hform₁ (y + w₂), polar_add_left, hy1, zero_add]
    have hyy : (u₁ * u₂) y = y + w₂ + (polar Qf w₂ w₁ / Qf w₁) • w₁ := by
      rw [LinearEquiv.mul_apply, hu2y, hu1yw]
    have hd1 : (u₁ * u₂) x - x = w₁ := by
      rw [hux]
      abel
    have hd2 : (u₁ * u₂) y - y = w₂ + (polar Qf w₂ w₁ / Qf w₁) • w₁ := by
      rw [hyy]
      abel
    have hw1M : w₁ ∈ movedSpace (u₁ * u₂) := by
      rw [← hd1]
      exact sub_mem_movedSpace _ x
    have hw2M' : w₂ + (polar Qf w₂ w₁ / Qf w₁) • w₁ ∈ movedSpace (u₁ * u₂) := by
      rw [← hd2]
      exact sub_mem_movedSpace _ y
    have hw2M : w₂ ∈ movedSpace (u₁ * u₂) := by
      have h' := Submodule.sub_mem _ hw2M' (Submodule.smul_mem _ (polar Qf w₂ w₁ / Qf w₁) hw1M)
      simpa using h'
    have hspanle : Submodule.span K (Set.range ![w₁, w₂]) ≤ movedSpace (u₁ * u₂) := by
      rw [Submodule.span_le, Set.range_subset_iff, Fin.forall_fin_two]
      exact ⟨hw1M, hw2M⟩
    have hfin := Submodule.finrank_mono hspanle
    rw [finrank_span_eq_card hli, Fintype.card_fin] at hfin
    omega
  ·
    have hdep : ∃ c : K, c • w₂ = w₁ := by
      by_contra hcon
      simp only [not_exists] at hcon
      exact hli (linearIndependent_fin2.mpr ⟨hw₂, hcon⟩)
    obtain ⟨c, hc⟩ := hdep
    have hc0 : c ≠ 0 := by
      rintro rfl
      exact hw₁ (by rw [← hc, zero_smul])
    subst hc
    refine LinearEquiv.ext fun x => ?_
    rw [hform₁ x, hform₂ x]
    congr 1
    simp only [QuadraticMap.polar_smul_right, QuadraticMap.map_smul, smul_eq_mul, smul_smul]
    congr 1
    field_simp

end CFSG.ClassicalGroups.Orthogonal.SiegelRT1
