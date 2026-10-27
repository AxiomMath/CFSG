module

public import CFSG.ClassicalGroups.Orthogonal.SiegelI4FamilyPair
public import CFSG.ClassicalGroups.Orthogonal.SiegelI4FamilyPencil
public import CFSG.ClassicalGroups.Orthogonal.SiegelI4FamilySigma

public section

namespace CFSG.ClassicalGroups.Orthogonal.SiegelRT1

open CFSG.HardMathSupport.Kantor79 QuadraticMap Module

variable {K : Type*} [Field K] [CharP K 2] {V : Type*} [AddCommGroup V] [Module K V]
  {Qf : QuadraticForm K V}

@[expose] def axes (E : Subgroup (V ≃ₗ[K] V)) : Set (Submodule K V) :=
  {A | ∃ s ∈ E, s ≠ 1 ∧ A = movedSpace s}

@[expose] noncomputable def axisInf (E : Subgroup (V ≃ₗ[K] V)) : Submodule K V :=
  ⨅ A ∈ axes E, A

@[expose] def Conc (E : Subgroup (V ≃ₗ[K] V)) : Prop :=
  (∃ P : Submodule K V, finrank K P = 1 ∧ ∀ A ∈ axes E, P ≤ A) ∧
    ¬ ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ A ∈ axes E, A ≤ U

@[expose] def Copl (E : Subgroup (V ≃ₗ[K] V)) : Prop :=
  (∃ U : Submodule K V, finrank K U = 3 ∧ ∀ A ∈ axes E, A ≤ U) ∧
    ¬ ∃ P : Submodule K V, finrank K P = 1 ∧ ∀ A ∈ axes E, P ≤ A

structure IsSiegelFamily (Qf : QuadraticForm K V) (E : Subgroup (V ≃ₗ[K] V)) : Prop where
  comm : ∀ s ∈ E, ∀ t ∈ E, s * t = t * s
  card : Nat.card E = Nat.card K ^ 3
  siegel : ∀ s ∈ E, s ≠ 1 → IsLongRootElement Qf s

theorem axisInf_le {E : Subgroup (V ≃ₗ[K] V)} {A : Submodule K V} (hA : A ∈ axes E) :
    axisInf E ≤ A :=
  iInf₂_le A hA

theorem le_axisInf {E : Subgroup (V ≃ₗ[K] V)} {P : Submodule K V} (h : ∀ A ∈ axes E, P ≤ A) :
    P ≤ axisInf E :=
  le_iInf₂ h

theorem le_commutatorSpace_of_mem_axes {E : Subgroup (V ≃ₗ[K] V)} {A : Submodule K V}
    (hA : A ∈ axes E) : A ≤ commutatorSpace E := by
  obtain ⟨s, hs, -, rfl⟩ := hA
  exact movedSpace_le_commutatorSpace hs

theorem commutatorSpace_le_of_forall_axes_le {E : Subgroup (V ≃ₗ[K] V)} {U : Submodule K V}
    (h : ∀ A ∈ axes E, A ≤ U) : commutatorSpace E ≤ U := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨s, hs, v, rfl⟩
  by_cases h1 : s = 1
  · subst h1
    simp
  · exact h _ ⟨s, hs, h1, rfl⟩ (sub_mem_movedSpace s v)

section Family

variable [Finite K] [FiniteDimensional K V]
  (hnd : ∀ x : V, (∀ y, polar Qf x y = 0) → x = 0) {E : Subgroup (V ≃ₗ[K] V)}
  (hE : IsSiegelFamily Qf E)

include hnd hE

theorem IsSiegelFamily.finrank_eq_two {A : Submodule K V} (hA : A ∈ axes E) :
    finrank K A = 2 := by
  obtain ⟨s, hs, hs1, rfl⟩ := hA
  exact (hE.siegel s hs hs1).finrank_movedSpace hnd

theorem IsSiegelFamily.qf_eq_zero_of_mem_axes {A : Submodule K V} (hA : A ∈ axes E) :
    ∀ w ∈ A, Qf w = 0 := by
  obtain ⟨s, hs, hs1, rfl⟩ := hA
  exact fun w hw => (hE.siegel s hs hs1).qf_eq_zero_of_mem_movedSpace hw

theorem IsSiegelFamily.nonempty_axes : (axes E).Nonempty := by
  by_contra hne
  have hall : ∀ s ∈ E, s = 1 := fun s hs => by
    by_contra h1
    exact hne ⟨movedSpace s, s, hs, h1, rfl⟩
  have hbot : E = ⊥ := (Subgroup.eq_bot_iff_forall E).mpr hall
  have h1 := hE.card
  rw [hbot, Subgroup.card_bot] at h1
  have hq : 1 < Nat.card K := Finite.one_lt_card
  have : 1 < Nat.card K ^ 3 := Nat.one_lt_pow (by norm_num) hq
  omega

theorem IsSiegelFamily.pair {A A' : Submodule K V} (hA : A ∈ axes E) (hA' : A' ∈ axes E)
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

theorem IsSiegelFamily.polar_eq_zero_of_mem_axes {A A' : Submodule K V} (hA : A ∈ axes E)
    (hA' : A' ∈ axes E) {u w : V} (hu : u ∈ A) (hw : w ∈ A') : polar Qf u w = 0 := by
  by_cases h : A = A'
  · subst h
    exact polar_eq_zero_of_totallySingular (hE.qf_eq_zero_of_mem_axes hnd hA) hu hw
  · rw [polar_comm]
    exact mem_orthogonal_iff_polar.mp ((hE.pair hnd hA hA' h).2.1 hu) w hw

theorem IsSiegelFamily.qf_eq_zero_of_mem_commutatorSpace :
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
    exact hE.qf_eq_zero_of_mem_axes hnd hA u hu
  · intro u hu w hw
    obtain ⟨A, hA, hu⟩ := Set.mem_iUnion₂.mp hu
    obtain ⟨A', hA', hw⟩ := Set.mem_iUnion₂.mp hw
    exact hE.polar_eq_zero_of_mem_axes hnd hA hA' hu hw

theorem IsSiegelFamily.le_piGroup {P : Submodule K V} (hP : ∀ A ∈ axes E, P ≤ A) :
    E ≤ piGroup Qf P (commutatorSpace E) := by
  intro s hs
  by_cases h1 : s = 1
  · rw [h1]
    exact one_mem _
  · exact isLongRootElement_mem_piGroup (hE.siegel s hs h1) (hP _ ⟨s, hs, h1, rfl⟩)
      (movedSpace_le_commutatorSpace hs)

theorem IsSiegelFamily.four_le_finrank_commutatorSpace {P : Submodule K V}
    (hP1 : finrank K P = 1) (hP : ∀ A ∈ axes E, P ≤ A) : 4 ≤ finrank K (commutatorSpace E) := by
  obtain ⟨A₀, hA₀⟩ := hE.nonempty_axes hnd
  have hPW : P ≤ commutatorSpace E := (hP A₀ hA₀).trans (le_commutatorSpace_of_mem_axes hA₀)
  have hcard := natCard_piGroup hnd (hE.qf_eq_zero_of_mem_commutatorSpace hnd) hP1 hPW
  have hq : 1 < Nat.card K := Finite.one_lt_card
  have hfin : Finite (piGroup Qf P (commutatorSpace E)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ (by omega))
  have hle := Subgroup.card_le_of_le (hE.le_piGroup hnd hP)
  rw [hE.card, hcard] at hle
  have := (pow_le_pow_iff_right₀ hq).mp hle
  omega

theorem IsSiegelFamily.conc_or_copl : Conc E ∨ Copl E := by
  obtain ⟨A₀, hA₀⟩ := hE.nonempty_axes hnd
  rcases exists_point_le_or_exists_plane_ge ⟨A₀, hA₀⟩ (fun A hA => hE.finrank_eq_two hnd hA)
    (fun A hA A' hA' hne => (hE.pair hnd hA hA' hne).1) with ⟨P, hP1, hP⟩ | ⟨U, hU3, hU⟩
  · refine Or.inl ⟨⟨P, hP1, hP⟩, ?_⟩
    rintro ⟨U, hU3, hU⟩
    have h4 := hE.four_le_finrank_commutatorSpace hnd hP1 hP
    have := Submodule.finrank_mono (commutatorSpace_le_of_forall_axes_le hU)
    omega
  · refine Or.inr ⟨⟨U, hU3, hU⟩, ?_⟩
    rintro ⟨P, hP1, hP⟩
    have h4 := hE.four_le_finrank_commutatorSpace hnd hP1 hP
    have := Submodule.finrank_mono (commutatorSpace_le_of_forall_axes_le hU)
    omega

theorem IsSiegelFamily.exists_ne_axes_of_conc (hc : Conc E) :
    ∃ A₁ ∈ axes E, ∃ A₂ ∈ axes E, A₁ ≠ A₂ := by
  obtain ⟨⟨P, hP1, hP⟩, -⟩ := hc
  obtain ⟨A₀, hA₀⟩ := hE.nonempty_axes hnd
  by_contra! hcon
  have hle : commutatorSpace E ≤ A₀ :=
    commutatorSpace_le_of_forall_axes_le fun A hA => (hcon A hA A₀ hA₀).le
  have h4 := hE.four_le_finrank_commutatorSpace hnd hP1 hP
  have := Submodule.finrank_mono hle
  rw [hE.finrank_eq_two hnd hA₀] at this
  omega

theorem IsSiegelFamily.finrank_axisInf_of_conc (hc : Conc E) : finrank K (axisInf E) = 1 := by
  obtain ⟨A₁, hA₁, A₂, hA₂, hne⟩ := hE.exists_ne_axes_of_conc hnd hc
  obtain ⟨⟨P, hP1, hP⟩, -⟩ := hc
  have h3 := (hE.pair hnd hA₁ hA₂ hne).1
  have h4 := Submodule.finrank_mono (le_axisInf hP)
  have h5 := Submodule.finrank_mono (le_inf (axisInf_le hA₁) (axisInf_le hA₂))
  omega

theorem IsSiegelFamily.le_piGroup_axisInf : E ≤ piGroup Qf (axisInf E) (commutatorSpace E) :=
  hE.le_piGroup hnd fun _ hA => axisInf_le hA

theorem IsSiegelFamily.exists_ne_axes_of_copl (hc : Copl E) :
    ∃ A₁ ∈ axes E, ∃ A₂ ∈ axes E, A₁ ≠ A₂ := by
  obtain ⟨-, hnP⟩ := hc
  obtain ⟨A₀, hA₀⟩ := hE.nonempty_axes hnd
  by_contra! hcon
  apply hnP
  have hbot : A₀ ≠ ⊥ := fun h => by
    have := hE.finrank_eq_two hnd hA₀
    rw [h, finrank_bot] at this
    omega
  obtain ⟨p, hpA₀, hp0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  refine ⟨Submodule.span K {p}, finrank_span_singleton hp0, fun A hA => ?_⟩
  rw [Submodule.span_singleton_le_iff_mem, hcon A hA A₀ hA₀]
  exact hpA₀

theorem IsSiegelFamily.finrank_commutatorSpace_of_copl (hc : Copl E) :
    finrank K (commutatorSpace E) = 3 := by
  obtain ⟨A₁, hA₁, A₂, hA₂, hne⟩ := hE.exists_ne_axes_of_copl hnd hc
  obtain ⟨⟨U, hU3, hU⟩, -⟩ := hc
  have h3 := (hE.pair hnd hA₁ hA₂ hne).2.2.1
  have h1 : A₁ ⊔ A₂ ≤ commutatorSpace E :=
    sup_le (le_commutatorSpace_of_mem_axes hA₁) (le_commutatorSpace_of_mem_axes hA₂)
  have h2 : commutatorSpace E ≤ U := commutatorSpace_le_of_forall_axes_le hU
  have := Submodule.finrank_mono h1
  have := Submodule.finrank_mono h2
  omega

theorem IsSiegelFamily.eq_sigmaGroup_of_copl (hc : Copl E) :
    E = sigmaGroup Qf (commutatorSpace E) := by
  have hW3 := hE.finrank_commutatorSpace_of_copl hnd hc
  have hWs := hE.qf_eq_zero_of_mem_commutatorSpace hnd
  have hle : E ≤ sigmaGroup Qf (commutatorSpace E) := by
    intro s hs
    by_cases h1 : s = 1
    · rw [h1]
      exact one_mem _
    · exact isLongRootElement_mem_sigmaGroup (hE.siegel s hs h1) (movedSpace_le_commutatorSpace hs)
  have hcard := natCard_sigmaGroup hnd hWs hW3
  have hq : 1 < Nat.card K := Finite.one_lt_card
  have hfin : Finite (sigmaGroup Qf (commutatorSpace E)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ (by omega))
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hE.card])

end Family

end CFSG.ClassicalGroups.Orthogonal.SiegelRT1
