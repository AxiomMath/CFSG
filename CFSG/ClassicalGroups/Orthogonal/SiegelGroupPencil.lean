module

public import CFSG.ClassicalGroups.Orthogonal.SiegelI4FamilyDichotomy

public section

namespace CFSG.ClassicalGroups.Orthogonal.SiegelRT1

open CFSG.HardMathSupport.Kantor79 QuadraticMap Module

variable {K : Type*} [Field K] [CharP K 2] {V : Type*} [AddCommGroup V] [Module K V]
  {Qf : QuadraticForm K V}

structure IsSiegelGroup (Qf : QuadraticForm K V) (E : Subgroup (V ≃ₗ[K] V)) : Prop where
  comm : ∀ s ∈ E, ∀ t ∈ E, s * t = t * s
  siegel : ∀ s ∈ E, s ≠ 1 → IsLongRootElement Qf s

@[expose] def IsStar (E : Subgroup (V ≃ₗ[K] V)) : Prop :=
  ∃ P : Submodule K V, finrank K P = 1 ∧ ∀ A ∈ axes E, P ≤ A

section Group

variable [FiniteDimensional K V]
  (hnd : ∀ x : V, (∀ y, polar Qf x y = 0) → x = 0) {E : Subgroup (V ≃ₗ[K] V)}
  (hE : IsSiegelGroup Qf E)

include hnd hE

omit [FiniteDimensional K V] in
theorem IsSiegelGroup.finrank_eq_two {A : Submodule K V} (hA : A ∈ axes E) :
    finrank K A = 2 := by
  obtain ⟨s, hs, hs1, rfl⟩ := hA
  exact (hE.siegel s hs hs1).finrank_movedSpace hnd

omit [FiniteDimensional K V] hnd in
theorem IsSiegelGroup.qf_eq_zero_of_mem_axes {A : Submodule K V} (hA : A ∈ axes E) :
    ∀ w ∈ A, Qf w = 0 := by
  obtain ⟨s, hs, hs1, rfl⟩ := hA
  exact fun w hw => (hE.siegel s hs hs1).qf_eq_zero_of_mem_movedSpace hw

theorem IsSiegelGroup.pair {A A' : Submodule K V} (hA : A ∈ axes E) (hA' : A' ∈ axes E)
    (hne : A ≠ A') :
    finrank K ↥(A ⊓ A') = 1 ∧ A ≤ LinearMap.BilinForm.orthogonal (polarBilin Qf) A' ∧
      finrank K ↥(A ⊔ A') = 3 ∧ ∀ x ∈ A ⊔ A', Qf x = 0 := by
  obtain ⟨s, hs, hs1, rfl⟩ := hA
  obtain ⟨s', hs', hs1', rfl⟩ := hA'
  have hss : s ≠ s' := fun h => hne (h ▸ rfl)
  have hsq : s * s = 1 := (hE.siegel s hs hs1).mul_self
  have hmul : s * s' ≠ 1 := fun h => hss (by
    have h1 : s' = s⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [h1, inv_eq_of_mul_eq_one_right hsq])
  exact lemma_three_one hnd (hE.siegel s hs hs1) (hE.siegel s' hs' hs1')
    (hE.comm s hs s' hs') (hE.siegel _ (mul_mem hs hs') hmul) hne

theorem IsSiegelGroup.polar_eq_zero_of_mem_axes {A A' : Submodule K V} (hA : A ∈ axes E)
    (hA' : A' ∈ axes E) {u w : V} (hu : u ∈ A) (hw : w ∈ A') : polar Qf u w = 0 := by
  by_cases h : A = A'
  · subst h
    exact polar_eq_zero_of_totallySingular (hE.qf_eq_zero_of_mem_axes hA) hu hw
  · rw [polar_comm]
    exact mem_orthogonal_iff_polar.mp ((hE.pair hnd hA hA' h).2.1 hu) w hw

theorem IsSiegelGroup.qf_eq_zero_of_mem_commutatorSpace :
    ∀ w ∈ commutatorSpace E, Qf w = 0 := by
  intro w hw
  have hle : commutatorSpace E ≤ Submodule.span K (⋃ A ∈ axes E, (A : Set V)) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨s, hs, v, rfl⟩
    by_cases h1 : s = 1
    · subst h1
      simp
    · exact Submodule.subset_span (Set.mem_biUnion ⟨s, hs, h1, rfl⟩ (sub_mem_movedSpace s v))
  refine map_eq_zero_of_mem_span (S := ⋃ A ∈ axes E, (A : Set V)) ?_ ?_ (hle hw)
  · intro u hu
    obtain ⟨A, hA, hu⟩ := Set.mem_iUnion₂.mp hu
    exact hE.qf_eq_zero_of_mem_axes hA u hu
  · intro u hu w hw
    obtain ⟨A, hA, hu⟩ := Set.mem_iUnion₂.mp hu
    obtain ⟨A', hA', hw⟩ := Set.mem_iUnion₂.mp hw
    exact hE.polar_eq_zero_of_mem_axes hnd hA hA' hu hw

omit [FiniteDimensional K V] hnd in
theorem IsSiegelGroup.le_piGroup {P : Submodule K V} (hP : ∀ A ∈ axes E, P ≤ A) :
    E ≤ piGroup Qf P (commutatorSpace E) := by
  intro s hs
  by_cases h1 : s = 1
  · rw [h1]
    exact one_mem _
  · exact isLongRootElement_mem_piGroup (hE.siegel s hs h1) (hP _ ⟨s, hs, h1, rfl⟩)
      (movedSpace_le_commutatorSpace hs)

omit [FiniteDimensional K V] hnd in
theorem IsSiegelGroup.le_sigmaGroup : E ≤ sigmaGroup Qf (commutatorSpace E) := by
  intro s hs
  by_cases h1 : s = 1
  · rw [h1]
    exact one_mem _
  · exact isLongRootElement_mem_sigmaGroup (hE.siegel s hs h1) (movedSpace_le_commutatorSpace hs)

theorem IsSiegelGroup.finrank_commutatorSpace_eq_three (hne : (axes E).Nonempty)
    (hst : ¬ IsStar E) : finrank K (commutatorSpace E) = 3 := by
  obtain ⟨A₀, hA₀⟩ := hne
  rcases exists_point_le_or_exists_plane_ge ⟨A₀, hA₀⟩ (fun A hA => hE.finrank_eq_two hnd hA)
    (fun A hA A' hA' hne => (hE.pair hnd hA hA' hne).1) with hP | ⟨U, hU3, hU⟩
  · exact absurd hP hst
  obtain ⟨A₁, hA₁, A₂, hA₂, hne12⟩ : ∃ A₁ ∈ axes E, ∃ A₂ ∈ axes E, A₁ ≠ A₂ := by
    by_contra! hcon
    apply hst
    have hbot : A₀ ≠ ⊥ := fun h => by
      have := hE.finrank_eq_two hnd hA₀
      rw [h, finrank_bot] at this
      omega
    obtain ⟨p, hpA₀, hp0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
    refine ⟨Submodule.span K {p}, finrank_span_singleton hp0, fun A hA => ?_⟩
    rw [Submodule.span_singleton_le_iff_mem, hcon A hA A₀ hA₀]
    exact hpA₀
  have h3 := (hE.pair hnd hA₁ hA₂ hne12).2.2.1
  have h1 : A₁ ⊔ A₂ ≤ commutatorSpace E :=
    sup_le (le_commutatorSpace_of_mem_axes hA₁) (le_commutatorSpace_of_mem_axes hA₂)
  have h2 : commutatorSpace E ≤ U := commutatorSpace_le_of_forall_axes_le hU
  have := Submodule.finrank_mono h1
  have := Submodule.finrank_mono h2
  omega

theorem IsSiegelGroup.eq_axisInf {P : Submodule K V} (hP1 : finrank K P = 1)
    (hP : ∀ A ∈ axes E, P ≤ A) {A₁ A₂ : Submodule K V} (hA₁ : A₁ ∈ axes E) (hA₂ : A₂ ∈ axes E)
    (hne : A₁ ≠ A₂) : P = axisInf E ∧ finrank K (axisInf E) = 1 := by
  have h3 := (hE.pair hnd hA₁ hA₂ hne).1
  have h4 := Submodule.finrank_mono (le_axisInf hP)
  have h5 := Submodule.finrank_mono (le_inf (axisInf_le hA₁) (axisInf_le hA₂))
  have h1 : finrank K (axisInf E) = 1 := by omega
  exact ⟨Submodule.eq_of_le_of_finrank_eq (le_axisInf hP) (by rw [hP1, h1]), h1⟩

variable [Finite K]

theorem IsSiegelGroup.card_le_of_star {P : Submodule K V} (hP1 : finrank K P = 1)
    (hP : ∀ A ∈ axes E, P ≤ A) (hne : (axes E).Nonempty) :
    Nat.card E ≤ Nat.card K ^ (finrank K (commutatorSpace E) - 1) := by
  obtain ⟨A₀, hA₀⟩ := hne
  have hPW : P ≤ commutatorSpace E := (hP A₀ hA₀).trans (le_commutatorSpace_of_mem_axes hA₀)
  have hcard := natCard_piGroup hnd (hE.qf_eq_zero_of_mem_commutatorSpace hnd) hP1 hPW
  have hq : 1 < Nat.card K := Finite.one_lt_card
  have hfin : Finite (piGroup Qf P (commutatorSpace E)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ (by omega))
  have hle := Subgroup.card_le_of_le (hE.le_piGroup hP)
  rwa [hcard] at hle

theorem IsSiegelGroup.exists_ne_axes (hcard : Nat.card K < Nat.card E) :
    ∃ A₁ ∈ axes E, ∃ A₂ ∈ axes E, A₁ ≠ A₂ := by
  have hq : 1 < Nat.card K := Finite.one_lt_card
  obtain ⟨s₀, hs₀, hs₀1⟩ : ∃ s ∈ E, s ≠ 1 := by
    by_contra! hall
    have hbot : E = ⊥ := (Subgroup.eq_bot_iff_forall E).mpr hall
    rw [hbot, Subgroup.card_bot] at hcard
    omega
  set A₀ := movedSpace s₀ with hA₀def
  have hA₀ : A₀ ∈ axes E := ⟨s₀, hs₀, hs₀1, rfl⟩
  by_contra! hcon
  have hbot : A₀ ≠ ⊥ := fun h => by
    have := hE.finrank_eq_two hnd hA₀
    rw [h, finrank_bot] at this
    omega
  obtain ⟨p, hpA₀, hp0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  set P := Submodule.span K {p}
  have hP1 : finrank K P = 1 := finrank_span_singleton hp0
  have hPA₀ : P ≤ A₀ := (Submodule.span_singleton_le_iff_mem p A₀).mpr hpA₀
  have hle : E ≤ piGroup Qf P A₀ := by
    intro s hs
    by_cases h1 : s = 1
    · rw [h1]
      exact one_mem _
    · have hA : movedSpace s = A₀ := hcon _ ⟨s, hs, h1, rfl⟩ A₀ hA₀
      exact isLongRootElement_mem_piGroup (hE.siegel s hs h1) (hA ▸ hPA₀) hA.le
  have hpi := natCard_piGroup hnd (hE.qf_eq_zero_of_mem_axes hA₀) hP1 hPA₀
  rw [hE.finrank_eq_two hnd hA₀] at hpi
  have hfin : Finite (piGroup Qf P A₀) :=
    Nat.finite_of_card_ne_zero (by rw [hpi]; exact pow_ne_zero _ (by omega))
  have := Subgroup.card_le_of_le hle
  rw [hpi] at this
  simp at this
  omega

end Group

end CFSG.ClassicalGroups.Orthogonal.SiegelRT1
