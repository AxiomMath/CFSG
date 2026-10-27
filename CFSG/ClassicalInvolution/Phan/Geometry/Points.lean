module

public import CFSG.ClassicalInvolution.Phan.Geometry.Basic

public section

namespace CFSG.ClassicalInvolution.Phan

open CFSG.ClassicalGroups.Unitary Module

variable {K : Type*} [Field K] {σ : K ≃+* K} {m : ℕ}

section Points

@[expose] def pts (W : Submodule K (Fin m → K)) : Set (Submodule K (Fin m → K)) :=
  {L | L ≤ W ∧ finrank K L = 1}

@[expose] def nsPts (σ : K ≃+* K) (W : Submodule K (Fin m → K)) : Set (Submodule K (Fin m → K)) :=
  {L | L ≤ W ∧ finrank K L = 1 ∧ Nondeg σ L}

@[expose] def isoPts (σ : K ≃+* K) (W : Submodule K (Fin m → K)) : Set (Submodule K (Fin m → K)) :=
  {L | L ≤ W ∧ finrank K L = 1 ∧ ¬ Nondeg σ L}

variable {W : Submodule K (Fin m → K)}

theorem exists_eq_span_of_finrank_eq_one {L : Submodule K (Fin m → K)} (h : finrank K L = 1) :
    ∃ v : Fin m → K, v ≠ 0 ∧ L = K ∙ v := by
  obtain ⟨v, rfl⟩ := ((Submodule.finrank_le_one_iff_isPrincipal L).mp h.le).principal
  refine ⟨v, ?_, rfl⟩
  rintro rfl
  rw [Submodule.span_zero_singleton, finrank_bot] at h
  exact absurd h (by norm_num)

theorem span_singleton_mem_pts {v : Fin m → K} (hv : v ≠ 0) (hvW : v ∈ W) : K ∙ v ∈ pts W :=
  ⟨(Submodule.span_singleton_le_iff_mem _ _).mpr hvW, finrank_span_singleton hv⟩

theorem mem_pts_iff {L : Submodule K (Fin m → K)} :
    L ∈ pts W ↔ ∃ v : Fin m → K, v ≠ 0 ∧ v ∈ W ∧ L = K ∙ v := by
  constructor
  · rintro ⟨hLW, hL⟩
    obtain ⟨v, hv, rfl⟩ := exists_eq_span_of_finrank_eq_one hL
    exact ⟨v, hv, (Submodule.span_singleton_le_iff_mem _ _).mp hLW, rfl⟩
  · rintro ⟨v, hv, hvW, rfl⟩
    exact span_singleton_mem_pts hv hvW

theorem span_singleton_mem_nsPts {v : Fin m → K} (hv : herm σ v v ≠ 0) (hvW : v ∈ W) :
    K ∙ v ∈ nsPts σ W := by
  have hv0 : v ≠ 0 := fun h => hv (by rw [h]; simp)
  exact ⟨(span_singleton_mem_pts hv0 hvW).1, (span_singleton_mem_pts hv0 hvW).2,
    nondeg_span_singleton hv⟩

theorem span_singleton_mem_isoPts {v : Fin m → K} (hv0 : v ≠ 0) (hv : herm σ v v = 0)
    (hvW : v ∈ W) : K ∙ v ∈ isoPts σ W := by
  refine ⟨(span_singleton_mem_pts hv0 hvW).1, (span_singleton_mem_pts hv0 hvW).2, fun h => hv0 ?_⟩
  refine h v (Submodule.mem_span_singleton_self v) fun t ht => ?_
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp ht
  rw [herm_smul_right, hv, mul_zero]

theorem mem_nsPts_iff {L : Submodule K (Fin m → K)} :
    L ∈ nsPts σ W ↔ ∃ v : Fin m → K, herm σ v v ≠ 0 ∧ v ∈ W ∧ L = K ∙ v := by
  constructor
  · rintro ⟨hLW, hL, hnd⟩
    obtain ⟨v, hv, rfl⟩ := exists_eq_span_of_finrank_eq_one hL
    exact ⟨v, herm_self_ne_zero_of_nondeg_span hv hnd,
      (Submodule.span_singleton_le_iff_mem _ _).mp hLW, rfl⟩
  · rintro ⟨v, hv, hvW, rfl⟩
    exact span_singleton_mem_nsPts hv hvW

theorem mem_isoPts_iff {L : Submodule K (Fin m → K)} :
    L ∈ isoPts σ W ↔ ∃ v : Fin m → K, v ≠ 0 ∧ herm σ v v = 0 ∧ v ∈ W ∧ L = K ∙ v := by
  constructor
  · rintro ⟨hLW, hL, hnd⟩
    obtain ⟨v, hv, rfl⟩ := exists_eq_span_of_finrank_eq_one hL
    refine ⟨v, hv, ?_, (Submodule.span_singleton_le_iff_mem _ _).mp hLW, rfl⟩
    by_contra h
    exact hnd (nondeg_span_singleton h)
  · rintro ⟨v, hv, hvv, hvW, rfl⟩
    exact span_singleton_mem_isoPts hv hvv hvW

theorem pts_eq_union : pts W = nsPts σ W ∪ isoPts σ W := by
  ext L
  constructor
  · rintro ⟨h1, h2⟩
    by_cases h : Nondeg σ L
    · exact Or.inl ⟨h1, h2, h⟩
    · exact Or.inr ⟨h1, h2, h⟩
  · rintro (⟨h1, h2, -⟩ | ⟨h1, h2, -⟩) <;> exact ⟨h1, h2⟩

theorem disjoint_nsPts_isoPts : Disjoint (nsPts σ W) (isoPts σ W) := by
  rw [Set.disjoint_left]
  rintro L ⟨-, -, h⟩ ⟨-, -, h'⟩
  exact h' h

end Points

@[expose] def InProperNondeg (σ : K ≃+* K) (W : Submodule K (Fin m → K))
    (S : Set (Submodule K (Fin m → K))) : Prop :=
  ∃ Y : Submodule K (Fin m → K), Y ≤ W ∧ Nondeg σ Y ∧ finrank K ↥Y < finrank K ↥W ∧ ∀ x ∈ S, x ≤ Y

section NonSingular

variable (hσ : IsUnitaryInvolution σ)
include hσ

theorem exists_aniso_of_rad_le_one {S : Submodule K (Fin m → K)} (h2 : 2 ≤ finrank K S)
    (hrad : finrank K ↥(rad σ S) ≤ 1) : ∃ v ∈ S, herm σ v v ≠ 0 := by
  by_contra! hcon
  have htot : S ≤ perp σ S := fun s hs t ht =>
    herm_eq_zero_of_forall_isotropic hσ (fun v hv => hcon v hv) hs ht
  have : rad σ S = S := inf_eq_left.mpr htot
  rw [this] at hrad
  omega

theorem nsPts_nonempty_of_rad_le_one {S : Submodule K (Fin m → K)} (h2 : 2 ≤ finrank K S)
    (hrad : finrank K ↥(rad σ S) ≤ 1) : (nsPts σ S).Nonempty := by
  obtain ⟨v, hvS, hv⟩ := exists_aniso_of_rad_le_one hσ h2 hrad
  exact ⟨K ∙ v, span_singleton_mem_nsPts hv hvS⟩

theorem nsPts_nonempty_of_nondeg {S : Submodule K (Fin m → K)} (hS : Nondeg σ S) (hne : S ≠ ⊥) :
    (nsPts σ S).Nonempty := by
  obtain ⟨v, hvS, hv⟩ := exists_aniso_of_nondeg hσ hS hne
  exact ⟨K ∙ v, span_singleton_mem_nsPts hv hvS⟩

end NonSingular

end CFSG.ClassicalInvolution.Phan
