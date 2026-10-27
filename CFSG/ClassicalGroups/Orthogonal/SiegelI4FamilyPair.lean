module

public import CFSG.ClassicalGroups.Orthogonal.SiegelRT1Pair

public section

namespace CFSG.ClassicalGroups.Orthogonal.SiegelRT1

open CFSG.HardMathSupport.Kantor79 QuadraticMap Module

variable {K : Type*} [Field K] [CharP K 2] {V : Type*} [AddCommGroup V] [Module K V]
  {Qf : QuadraticForm K V}

theorem le_orthogonal_symm {A B : Submodule K V}
    (h : A ≤ LinearMap.BilinForm.orthogonal (polarBilin Qf) B) :
    B ≤ LinearMap.BilinForm.orthogonal (polarBilin Qf) A := by
  intro y hy
  rw [mem_orthogonal_iff_polar]
  intro z hz
  rw [polar_comm]
  exact mem_orthogonal_iff_polar.mp (h hz) y hy

theorem not_isLongRootElement_mul_of_disjoint [FiniteDimensional K V]
    (hnd : ∀ x : V, (∀ y, polar Qf x y = 0) → x = 0) {s s' : V ≃ₗ[K] V}
    (hs : IsLongRootElement Qf s) (hs' : IsLongRootElement Qf s')
    (hdisj : Disjoint (movedSpace s) (movedSpace s'))
    (horth : movedSpace s ≤ LinearMap.BilinForm.orthogonal (polarBilin Qf) (movedSpace s')) :
    ¬ IsLongRootElement Qf (s * s') := by
  intro hmul
  have horth' := le_orthogonal_symm horth
  have hker : ∀ {t : V ≃ₗ[K] V}, (∀ v, Qf (t v) = Qf v) → ∀ x,
      x ∈ LinearMap.BilinForm.orthogonal (polarBilin Qf) (movedSpace t) ↔ t x - x = 0 :=
    fun {t} ht x => by
      rw [← ker_sub_one_eq_orthogonal_movedSpace hnd ht, LinearMap.mem_ker]
      simp
  have hn : ∀ x, (s * s') x - x = (s x - x) + (s' x - x) := fun x => by
    have h1 : s (s' x - x) - (s' x - x) = 0 :=
      (hker hs.isometry _).mp (horth' (sub_mem_movedSpace s' x))
    rw [map_sub] at h1
    rw [LinearEquiv.mul_apply]
    linear_combination (norm := module) h1
  have hkern : LinearMap.ker (((s * s' : V ≃ₗ[K] V) : V →ₗ[K] V) - 1) =
      LinearMap.BilinForm.orthogonal (polarBilin Qf) (movedSpace s ⊔ movedSpace s') := by
    ext x
    rw [LinearMap.mem_ker]
    simp only [LinearMap.sub_apply, LinearEquiv.coe_coe, Module.End.one_apply]
    constructor
    · intro hx
      rw [hn] at hx
      have hA : s x - x ∈ movedSpace s ⊓ movedSpace s' := by
        refine ⟨sub_mem_movedSpace s x, ?_⟩
        have : s x - x = -(s' x - x) := by linear_combination (norm := module) hx
        rw [this]
        exact Submodule.neg_mem _ (sub_mem_movedSpace s' x)
      have hA0 : s x - x = 0 := by
        have := hdisj.le_bot hA
        simpa using this
      have hA' : s' x - x = 0 := by
        rw [hA0, zero_add] at hx
        exact hx
      rw [mem_orthogonal_iff_polar]
      intro y hy
      obtain ⟨a, ha, a', ha', rfl⟩ := Submodule.mem_sup.mp hy
      rw [polar_add_left]
      have h1 := mem_orthogonal_iff_polar.mp ((hker hs.isometry x).mpr hA0) a ha
      have h2 := mem_orthogonal_iff_polar.mp ((hker hs'.isometry x).mpr hA') a' ha'
      rw [h1, h2, add_zero]
    · intro hx
      have h1 : s x - x = 0 := (hker hs.isometry x).mp
        (LinearMap.BilinForm.orthogonal_le le_sup_left hx)
      have h2 : s' x - x = 0 := (hker hs'.isometry x).mp
        (LinearMap.BilinForm.orthogonal_le le_sup_right hx)
      rw [hn, h1, h2, add_zero]
  have hA2 := hs.finrank_movedSpace hnd
  have hA'2 := hs'.finrank_movedSpace hnd
  have hmul2 := hmul.finrank_movedSpace hnd
  have : Module.Finite K (movedSpace s) := Module.finite_of_finrank_pos (by omega)
  have : Module.Finite K (movedSpace s') := Module.finite_of_finrank_pos (by omega)
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq (movedSpace s) (movedSpace s')
  rw [hdisj.eq_bot, finrank_bot, hA2, hA'2] at hsup
  have hrn := LinearMap.finrank_range_add_finrank_ker
    (((s * s' : V ≃ₗ[K] V) : V →ₗ[K] V) - 1)
  rw [hkern, finrank_orthogonal_polar hnd] at hrn
  have hle : finrank K ↥(movedSpace s ⊔ movedSpace s') ≤ finrank K V := Submodule.finrank_le _
  have hmv : finrank K (LinearMap.range (((s * s' : V ≃ₗ[K] V) : V →ₗ[K] V) - 1)) = 2 := hmul2
  omega

theorem lemma_three_one [FiniteDimensional K V]
    (hnd : ∀ x : V, (∀ y, polar Qf x y = 0) → x = 0) {s s' : V ≃ₗ[K] V}
    (hs : IsLongRootElement Qf s) (hs' : IsLongRootElement Qf s') (hcomm : s * s' = s' * s)
    (hmul : IsLongRootElement Qf (s * s')) (hne : movedSpace s ≠ movedSpace s') :
    finrank K ↥(movedSpace s ⊓ movedSpace s') = 1 ∧
      movedSpace s ≤ LinearMap.BilinForm.orthogonal (polarBilin Qf) (movedSpace s') ∧
      finrank K ↥(movedSpace s ⊔ movedSpace s') = 3 ∧
      ∀ x ∈ movedSpace s ⊔ movedSpace s', Qf x = 0 := by
  have horth := movedSpace_le_orthogonal_of_commute_of_isLongRootElement_mul hnd hs hs' hcomm hmul
  have hA2 := hs.finrank_movedSpace hnd
  have hA'2 := hs'.finrank_movedSpace hnd
  have hbot : movedSpace s ⊓ movedSpace s' ≠ ⊥ := fun h =>
    not_isLongRootElement_mul_of_disjoint hnd hs hs' (disjoint_iff.mpr h) horth hmul
  have h1 := finrank_inf_eq_one_of_finrank_two hA2 hA'2 hne hbot
  refine ⟨h1, horth, ?_, ?_⟩
  · have : Module.Finite K (movedSpace s) := Module.finite_of_finrank_pos (by omega)
    have : Module.Finite K (movedSpace s') := Module.finite_of_finrank_pos (by omega)
    have h := Submodule.finrank_sup_add_finrank_inf_eq (movedSpace s) (movedSpace s')
    rw [h1, hA2, hA'2] at h
    omega
  · intro x hx
    obtain ⟨a, ha, a', ha', rfl⟩ := Submodule.mem_sup.mp hx
    have hQa := hs.qf_eq_zero_of_mem_movedSpace ha
    have hQa' := hs'.qf_eq_zero_of_mem_movedSpace ha'
    have hpol : polar Qf a a' = 0 := by
      rw [polar_comm]
      exact mem_orthogonal_iff_polar.mp (horth ha) a' ha'
    rw [QuadraticMap.map_add Qf a a', hQa, hQa', hpol, add_zero, add_zero]

end CFSG.ClassicalGroups.Orthogonal.SiegelRT1
