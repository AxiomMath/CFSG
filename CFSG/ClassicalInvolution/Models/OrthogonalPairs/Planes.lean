module

public import CFSG.ClassicalGroups.Orthogonal.Hyperbolic
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.Fundamental

public section

namespace CFSG.ClassicalInvolution.Models.OrthogonalPairs

open QuadraticMap Matrix CFSG.ClassicalGroups.Orthogonal

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

variable (Q) in
@[expose] def HasSingularVector (U : Submodule K V) : Prop :=
  ∃ v ∈ U, v ≠ 0 ∧ Q v = 0

theorem Frame.polarNondegOn_span (F : Frame Q) : PolarNondegOn Q F.span := by
  intro x hx h
  have h' : x ∈ F.perp := (Frame.mem_perp_iff_forall_incl F).mpr fun Y => h _ ⟨Y, rfl⟩
  exact Submodule.disjoint_def.mp (Frame.isCompl_span_perp F).disjoint x hx h'

theorem polarNondegOn_of_orth {F : Frame Q} {U U' : Submodule K V} (hspan : F.span = U ⊔ U')
    (horth : ∀ x ∈ U, ∀ y ∈ U', polar Q x y = 0) : PolarNondegOn Q U := by
  intro x hx h
  refine F.polarNondegOn_span x (hspan ▸ Submodule.mem_sup_left hx) fun w hw => ?_
  rw [hspan] at hw
  obtain ⟨u, hu, u', hu', rfl⟩ := Submodule.mem_sup.mp hw
  rw [polar_add_right, h u hu, horth x hx u' hu', add_zero]

theorem exists_hypPair_of_hasSingularVector {U : Submodule K V} (hU : PolarNondegOn Q U)
    (hfin : Module.finrank K U = 2) (hs : HasSingularVector Q U) :
    ∃ P : HypPair Q, P.e ∈ U ∧ P.f ∈ U ∧ U = Submodule.span K {P.e, P.f} := by
  obtain ⟨e, he, he0, hQe⟩ := hs
  obtain ⟨y, hy, hey⟩ := hU.exists_polar_ne_zero he he0
  have h1 : polar Q e ((polar Q e y)⁻¹ • y) = 1 := by
    rw [polar_smul_right_eq, inv_mul_cancel₀ hey]
  let P : HypPair Q := HypPair.ofPolarEqOne hQe h1
  have hPf : P.f ∈ U := by
    refine U.sub_mem (U.smul_mem _ hy) (U.smul_mem _ he)
  refine ⟨P, he, hPf, ?_⟩
  have hind : LinearIndependent K ![P.e, P.f] := by
    rw [LinearIndependent.pair_iff]
    intro a b hab
    have h3 := congrArg (fun z => polar Q z P.f) hab
    have h4 := congrArg (fun z => polar Q z P.e) hab
    simp only [polar_add_left, polar_smul_left_eq, polar_zero_left, P.polar_ef, HypPair.polar_ff,
      P.polar_fe, HypPair.polar_ee] at h3 h4
    exact ⟨by simpa using h3, by simpa using h4⟩
  have hle : Submodule.span K {P.e, P.f} ≤ U := by
    rw [Submodule.span_le]
    rintro _ (rfl | rfl)
    · exact he
    · exact hPf
  have : FiniteDimensional K U := Module.finite_of_finrank_pos (by omega)
  refine (Submodule.eq_of_le_of_finrank_eq hle ?_).symm
  have h5 := finrank_span_eq_card hind
  have hr : Set.range ![P.e, P.f] = {P.e, P.f} := by
    ext x
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff, Fin.exists_fin_two]
    simp [eq_comm]
  rw [hr] at h5
  rw [hfin, h5]
  simp

section Types

namespace Frame

variable (F : Frame Q)

theorem e₁_mem_span : F.e₁ ∈ F.span := ⟨!![1, 0; 0, 0], by simp [incl_apply]⟩

theorem f₁_mem_span : F.f₁ ∈ F.span := ⟨!![0, 0; 0, 1], by simp [incl_apply]⟩

theorem e₂_mem_span : F.e₂ ∈ F.span := ⟨!![0, -1; 0, 0], by simp [incl_apply]⟩

theorem f₂_mem_span : F.f₂ ∈ F.span := ⟨!![0, 0; 1, 0], by simp [incl_apply]⟩

theorem span_e₁_e₂_le : Submodule.span K {F.e₁, F.e₂} ≤ F.span := by
  rw [Submodule.span_le]
  rintro _ (rfl | rfl)
  · exact F.e₁_mem_span
  · exact F.e₂_mem_span

theorem polar_eq_zero_of_mem_span_e₁_e₂ {x y : V} (hx : x ∈ Submodule.span K {F.e₁, F.e₂})
    (hy : y ∈ Submodule.span K {F.e₁, F.e₂}) : polar Q x y = 0 := by
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hx
  obtain ⟨c, d, rfl⟩ := Submodule.mem_span_pair.mp hy
  simp only [polar_add_left, polar_add_right, polar_smul_left_eq, polar_smul_right_eq,
    polar_e₁_e₁, polar_e₂_e₂, polar_e₁_e₂, polar_e₂_e₁]
  ring

theorem Q_eq_zero_of_mem_span_e₁_e₂ {x : V} (hx : x ∈ Submodule.span K {F.e₁, F.e₂}) :
    Q x = 0 := by
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hx
  rw [QuadraticMap.map_add Q, map_smul_eq_sq, map_smul_eq_sq, F.Q_e₁, F.Q_e₂,
    polar_smul_left_eq, polar_smul_right_eq, F.polar_e₁_e₂]
  simp

theorem exists_mem_span_e₁_e₂_orth (w : V) :
    ∃ p ∈ Submodule.span K {F.e₁, F.e₂}, p ≠ 0 ∧ polar Q p w = 0 := by
  by_cases h : polar Q F.e₁ w = 0 ∧ polar Q F.e₂ w = 0
  · refine ⟨F.e₁, Submodule.subset_span (by simp), F.P.e_ne_zero, h.1⟩
  · refine ⟨polar Q F.e₂ w • F.e₁ - polar Q F.e₁ w • F.e₂, ?_, ?_, ?_⟩
    · exact Submodule.sub_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    · intro h0
      apply h
      have h1 := congrArg (fun z => polar Q z F.f₁) h0
      have h2 := congrArg (fun z => polar Q z F.f₂) h0
      simp only [polar_sub_left, polar_smul_left_eq, polar_zero_left, polar_e₁_f₁, polar_e₂_f₁,
        polar_e₁_f₂, polar_e₂_f₂] at h1 h2
      exact ⟨by simpa using h2, by simpa using h1⟩
    · rw [polar_sub_left, polar_smul_left_eq, polar_smul_left_eq]
      ring

end Frame

variable {F : Frame Q} {U U' : Submodule K V}

theorem hasSingularVector_of_complement (hspan : F.span = U ⊔ U')
    (horth : ∀ x ∈ U, ∀ y ∈ U', polar Q x y = 0) (hnd : PolarNondegOn Q U')
    (hfin : Module.finrank K U' = 2) (hs : HasSingularVector Q U') : HasSingularVector Q U := by
  obtain ⟨P, he, hf, hU'⟩ := exists_hypPair_of_hasSingularVector hnd hfin hs
  have aux : ∀ P' : HypPair Q, U' = Submodule.span K {P'.e, P'.f} →
      HasSingularVector Q U ∨ P'.e ∈ Submodule.span K {F.e₁, F.e₂} := by
    intro P' hU''
    have he' : P'.e ∈ U' := hU'' ▸ Submodule.subset_span (by simp)
    obtain ⟨p, hpT, hp0, hpe⟩ := F.exists_mem_span_e₁_e₂_orth P'.e
    have hQp := F.Q_eq_zero_of_mem_span_e₁_e₂ hpT
    obtain ⟨u, hu, u', hu', hsum⟩ := Submodule.mem_sup.mp (hspan ▸ F.span_e₁_e₂_le hpT)
    obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp (hU'' ▸ hu')
    have hue : polar Q u P'.e = 0 := horth u hu _ he'
    have hb : b = 0 := by
      have h1 := hpe
      rw [← hsum, ← hab, polar_add_left, polar_add_left, polar_smul_left_eq, polar_smul_left_eq,
        hue, P'.polar_ee, P'.polar_fe] at h1
      simpa using h1
    subst hb
    rw [zero_smul, add_zero] at hab
    subst hab
    have hQu : Q u = 0 := by
      rw [← hsum, QuadraticMap.map_add Q, map_smul_eq_sq, P'.Q_e, polar_smul_right_eq, hue] at hQp
      simpa using hQp
    by_cases hu0 : u = 0
    · right
      subst hu0
      have ha : a ≠ 0 := by
        intro ha
        apply hp0
        rw [← hsum, ha, zero_smul, zero_add]
      have : P'.e = a⁻¹ • p := by
        rw [← hsum, zero_add, smul_smul, inv_mul_cancel₀ ha, one_smul]
      rw [this]
      exact Submodule.smul_mem _ _ hpT
    · left
      exact ⟨u, hu, hu0, hQu⟩
  by_contra hno
  have h1 := (aux P hU').resolve_left hno
  have h2 := (aux ⟨P.f, P.e, P.Q_f, P.Q_e, HypPair.polar_fe P⟩ (by
    show U' = Submodule.span K {P.f, P.e}
    rw [hU', Set.pair_comm])).resolve_left hno
  have h3 : polar Q P.e P.f = 0 := F.polar_eq_zero_of_mem_span_e₁_e₂ h1 h2
  rw [P.polar_ef] at h3
  exact one_ne_zero h3

end Types

end CFSG.ClassicalInvolution.Models.OrthogonalPairs
