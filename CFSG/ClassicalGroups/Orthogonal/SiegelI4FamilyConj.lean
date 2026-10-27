module

public import CFSG.ClassicalGroups.Orthogonal.SiegelI4FamilyDichotomy

public section

namespace CFSG.ClassicalGroups.Orthogonal.SiegelRT1

open CFSG.HardMathSupport.Kantor79 QuadraticMap Module

variable {K : Type*} [Field K] [CharP K 2] {V : Type*} [AddCommGroup V] [Module K V]
  {Qf : QuadraticForm K V}

@[expose] def conjSubgroup (h : V ≃ₗ[K] V) (E : Subgroup (V ≃ₗ[K] V)) : Subgroup (V ≃ₗ[K] V) :=
  E.map (MulAut.conj h).toMonoidHom

theorem mem_conjSubgroup_iff {h s : V ≃ₗ[K] V} {E : Subgroup (V ≃ₗ[K] V)} :
    s ∈ conjSubgroup h E ↔ h⁻¹ * s * h ∈ E := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hx
  · intro hs
    exact ⟨h⁻¹ * s * h, hs, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem mul_mem_conjSubgroup {h x : V ≃ₗ[K] V} {E : Subgroup (V ≃ₗ[K] V)} (hx : x ∈ E) :
    h * x * h⁻¹ ∈ conjSubgroup h E :=
  ⟨x, hx, by simp [MulAut.conj_apply]⟩

theorem movedSpace_conj (h s : V ≃ₗ[K] V) :
    movedSpace (h * s * h⁻¹) = (movedSpace s).map (h : V →ₗ[K] V) := by
  ext y
  simp only [movedSpace, LinearMap.mem_range, Submodule.mem_map]
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨s (h⁻¹ x) - h⁻¹ x, ⟨h⁻¹ x, by simp⟩, ?_⟩
    rw [← hx]
    simp
  · rintro ⟨z, ⟨x, rfl⟩, rfl⟩
    refine ⟨h x, ?_⟩
    simp

theorem axes_conjSubgroup (h : V ≃ₗ[K] V) (E : Subgroup (V ≃ₗ[K] V)) :
    axes (conjSubgroup h E) = Submodule.map (h : V →ₗ[K] V) '' axes E := by
  ext A
  constructor
  · rintro ⟨s', hs', hs1, rfl⟩
    have hs : h⁻¹ * s' * h ∈ E := mem_conjSubgroup_iff.mp hs'
    refine ⟨movedSpace (h⁻¹ * s' * h), ⟨_, hs, ?_, rfl⟩, ?_⟩
    · intro h1
      apply hs1
      have : s' = h * (h⁻¹ * s' * h) * h⁻¹ := by simp [mul_assoc]
      rw [this, h1]
      simp
    · rw [← movedSpace_conj]
      simp [mul_assoc]
  · rintro ⟨_, ⟨s, hs, hs1, rfl⟩, rfl⟩
    refine ⟨h * s * h⁻¹, mul_mem_conjSubgroup hs, ?_, (movedSpace_conj h s).symm⟩
    intro h1
    apply hs1
    have : s = h⁻¹ * (h * s * h⁻¹) * h := by simp [mul_assoc]
    rw [this, h1]
    simp

theorem mem_axisInf_iff {E : Subgroup (V ≃ₗ[K] V)} {x : V} :
    x ∈ axisInf E ↔ ∀ A ∈ axes E, x ∈ A := by
  simp [axisInf, Submodule.mem_iInf]

theorem axisInf_conjSubgroup (h : V ≃ₗ[K] V) (E : Subgroup (V ≃ₗ[K] V)) :
    axisInf (conjSubgroup h E) = (axisInf E).map (h : V →ₗ[K] V) := by
  ext x
  rw [mem_axisInf_iff, axes_conjSubgroup]
  simp only [Set.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  constructor
  · intro hx
    refine ⟨h.symm x, mem_axisInf_iff.mpr fun A hA => ?_, by simp⟩
    obtain ⟨a, ha, hxa⟩ := Submodule.mem_map.mp (hx A hA)
    have : h.symm x = a := by rw [← hxa]; simp
    rw [this]
    exact ha
  · rintro ⟨y, hy, rfl⟩ A hA
    exact Submodule.mem_map_of_mem (mem_axisInf_iff.mp hy A hA)

theorem commutatorSpace_conjSubgroup (h : V ≃ₗ[K] V) (E : Subgroup (V ≃ₗ[K] V)) :
    commutatorSpace (conjSubgroup h E) = (commutatorSpace E).map (h : V →ₗ[K] V) := by
  refine le_antisymm (commutatorSpace_le_of_forall_axes_le fun B hB => ?_) ?_
  · rw [axes_conjSubgroup] at hB
    obtain ⟨A, hA, rfl⟩ := hB
    exact Submodule.map_mono (le_commutatorSpace_of_mem_axes hA)
  · rw [Submodule.map_le_iff_le_comap]
    refine commutatorSpace_le_of_forall_axes_le fun A hA => ?_
    rw [← Submodule.map_le_iff_le_comap]
    exact le_commutatorSpace_of_mem_axes (by rw [axes_conjSubgroup]; exact ⟨A, hA, rfl⟩)

theorem exists_le_map_iff (h : V ≃ₗ[K] V) (n : ℕ) (𝓕 : Set (Submodule K V)) :
    (∃ P : Submodule K V, finrank K P = n ∧ ∀ A ∈ Submodule.map (h : V →ₗ[K] V) '' 𝓕, P ≤ A) ↔
      ∃ P : Submodule K V, finrank K P = n ∧ ∀ A ∈ 𝓕, P ≤ A := by
  constructor
  · rintro ⟨P, hP1, hP⟩
    refine ⟨P.map (h.symm : V →ₗ[K] V), by rw [LinearEquiv.finrank_map_eq, hP1], fun A hA => ?_⟩
    have h2 := Submodule.map_mono (f := (h.symm : V →ₗ[K] V)) (hP _ ⟨A, hA, rfl⟩)
    have e : (h.symm : V →ₗ[K] V) ∘ₗ (h : V →ₗ[K] V) = LinearMap.id := by ext x; simp
    rwa [← Submodule.map_comp, e, Submodule.map_id] at h2
  · rintro ⟨P, hP1, hP⟩
    exact ⟨P.map (h : V →ₗ[K] V), by rw [LinearEquiv.finrank_map_eq, hP1],
      fun A ⟨B, hB, hBA⟩ => hBA ▸ Submodule.map_mono (hP B hB)⟩

theorem exists_map_le_iff (h : V ≃ₗ[K] V) (n : ℕ) (𝓕 : Set (Submodule K V)) :
    (∃ U : Submodule K V, finrank K U = n ∧ ∀ A ∈ Submodule.map (h : V →ₗ[K] V) '' 𝓕, A ≤ U) ↔
      ∃ U : Submodule K V, finrank K U = n ∧ ∀ A ∈ 𝓕, A ≤ U := by
  constructor
  · rintro ⟨U, hU1, hU⟩
    refine ⟨U.map (h.symm : V →ₗ[K] V), by rw [LinearEquiv.finrank_map_eq, hU1], fun A hA => ?_⟩
    have h2 := Submodule.map_mono (f := (h.symm : V →ₗ[K] V)) (hU _ ⟨A, hA, rfl⟩)
    have e : (h.symm : V →ₗ[K] V) ∘ₗ (h : V →ₗ[K] V) = LinearMap.id := by ext x; simp
    rwa [← Submodule.map_comp, e, Submodule.map_id] at h2
  · rintro ⟨U, hU1, hU⟩
    exact ⟨U.map (h : V →ₗ[K] V), by rw [LinearEquiv.finrank_map_eq, hU1],
      fun A ⟨B, hB, hBA⟩ => hBA ▸ Submodule.map_mono (hU B hB)⟩

theorem conc_conjSubgroup_iff (h : V ≃ₗ[K] V) (E : Subgroup (V ≃ₗ[K] V)) :
    Conc (conjSubgroup h E) ↔ Conc E := by
  unfold Conc
  rw [axes_conjSubgroup, exists_le_map_iff, exists_map_le_iff]

theorem isLongRootElement_conj_iff {h : V ≃ₗ[K] V} (hh : ∀ v, Qf (h v) = Qf v)
    {s : V ≃ₗ[K] V} : IsLongRootElement Qf (h * s * h⁻¹) ↔ IsLongRootElement Qf s := by
  have hg : h ∈ TauCeti.QuadraticMap.orthogonalGroup Qf :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr hh
  refine ⟨fun hs => ?_, fun hs => hs.conj hg⟩
  have := hs.conj (inv_mem hg)
  simpa [mul_assoc] using this

end CFSG.ClassicalGroups.Orthogonal.SiegelRT1
