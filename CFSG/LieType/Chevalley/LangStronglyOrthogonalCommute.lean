module

public import CFSG.LieType.Chevalley.LangRootRankOneTorus

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint

variable {τ : Tag}

theorem iform_neg_left (x y : Fin τ.rank → ℤ) : iform (-x) y = -iform x y := by
  simp [iform, Finset.sum_neg_distrib]

theorem iform_neg_right
    (x y : Fin τ.rank → ℤ) : iform x (-y) = -iform x y := by
  rw [iform_comm, iform_neg_left, iform_comm]

theorem symmetrizer_le_three (τ : Tag) (j : Fin τ.rank) : τ.symmetrizer j j ≤ 3 := by
  cases τ <;> fin_cases j <;> decide

theorem iform_self_bounds_of_isRoot
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    2 ≤ iform α α ∧ iform α α ≤ 6 := by
  obtain ⟨j, hj⟩ := iform_self_of_isRoot hα
  have h1 := symmetrizer_pos τ j
  have h2 := symmetrizer_le_three τ j
  omega

theorem not_isRoot_nsmul_add_nsmul
    {α β : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hβ : IsRoot τ β)
    (h0 : iform α β = 0) (hp : ¬ IsRoot τ (α + β)) {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    ¬ IsRoot τ (a • α + b • β) := by
  intro h
  have hn := iform_nsmul_add_nsmul a b α β
  rw [h0, mul_zero, add_zero] at hn
  obtain ⟨hα2, -⟩ := iform_self_bounds_of_isRoot hα
  obtain ⟨hβ2, -⟩ := iform_self_bounds_of_isRoot hβ
  obtain ⟨-, h6⟩ := iform_self_bounds_of_isRoot h
  by_cases h11 : a = 1 ∧ b = 1
  · obtain ⟨rfl, rfl⟩ := h11
    exact hp (by simpa using h)
  have hA : (1 : ℤ) ≤ a := by exact_mod_cast ha
  have hB : (1 : ℤ) ≤ b := by exact_mod_cast hb
  have h1A : (1 : ℤ) ≤ (a : ℤ) ^ 2 := by nlinarith
  have h1B : (1 : ℤ) ≤ (b : ℤ) ^ 2 := by nlinarith
  rcases (show (2 : ℤ) ≤ a ∨ (2 : ℤ) ≤ b by omega) with h2 | h2
  · have h4 : (4 : ℤ) ≤ (a : ℤ) ^ 2 := by nlinarith
    nlinarith [mul_le_mul h4 hα2 (by norm_num) (by positivity),
      mul_le_mul h1B hβ2 (by norm_num) (by positivity)]
  · have h4 : (4 : ℤ) ≤ (b : ℤ) ^ 2 := by nlinarith
    nlinarith [mul_le_mul h4 hβ2 (by norm_num) (by positivity),
      mul_le_mul h1A hα2 (by norm_num) (by positivity)]

theorem pinnedX_commute_of_iform_eq_zero
    (K : Type) [Field K] {α β : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) (hβ : IsRoot τ β) (h0 : iform α β = 0) (hp : ¬ IsRoot τ (α + β))
    (c d : K) : pinnedX τ K α c * pinnedX τ K β d = pinnedX τ K β d * pinnedX τ K α c := by
  have hne : α ≠ β := by
    rintro rfl
    have := iform_self_pos_of_isRoot hα
    omega
  have hne' : α ≠ -β := by
    rintro rfl
    rw [iform_neg_left] at h0
    have := iform_self_pos_of_isRoot hβ
    omega
  obtain ⟨-, hmem, -, -, hF⟩ := root_commutator_formula τ hα hβ hne hne'
  have hnil : commPairs τ α β = [] := by
    rw [List.eq_nil_iff_forall_not_mem]
    intro p hp'
    obtain ⟨h1, h2, h3⟩ := (hmem p).1 hp'
    exact not_isRoot_nsmul_add_nsmul hα hβ h0 hp h1 h2 h3
  have h := hF K c d
  rw [hnil, List.map_nil, List.prod_nil, ← pinnedX_neg, ← pinnedX_neg] at h
  calc pinnedX τ K α c * pinnedX τ K β d =
        (pinnedX τ K α c * pinnedX τ K β d * (pinnedX τ K α c)⁻¹ * (pinnedX τ K β d)⁻¹) *
          pinnedX τ K β d * pinnedX τ K α c := by group
    _ = pinnedX τ K β d * pinnedX τ K α c := by rw [h, one_mul]

theorem closure_commute {G : Type*} [Group G] {S T : Set G}
    (h : ∀ x ∈ S, ∀ y ∈ T, x * y = y * x) :
    ∀ x ∈ Subgroup.closure S, ∀ y ∈ Subgroup.closure T, x * y = y * x := by
  have hle : Subgroup.closure S ≤ Subgroup.centralizer (Subgroup.closure T : Set G) := by
    rw [Subgroup.closure_le]
    intro x hx
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro y hy
    have hT : Subgroup.closure T ≤ Subgroup.centralizer {x} := by
      rw [Subgroup.closure_le]
      intro z hz
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      exact (h x hx z hz).symm
    exact Subgroup.mem_centralizer_singleton_iff.1 (hT hy)
  intro x hx y hy
  exact (Subgroup.mem_centralizer_iff.1 (hle hx) y hy).symm

theorem exceptional_Lang_strongly_orthogonal_root_rank_one_commutation
    (τ : Tag) (K : Type)
    [Field K] {β γ : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (hγ : IsRoot τ γ) (h0 : iform β γ = 0)
    (hp : ¬ IsRoot τ (β + γ)) (hm : ¬ IsRoot τ (β - γ)) :
    ∀ g ∈ rootRankOneGroup τ K β, ∀ h ∈ rootRankOneGroup τ K γ, g * h = h * g := by
  have hL : ∀ {δ : Fin τ.rank → ℤ}, IsRoot τ δ → rootRankOneGroup τ K δ =
      Subgroup.closure (Set.range (pinnedX τ K δ) ∪ Set.range (pinnedX τ K (-δ))) := fun hδ => by
    rw [(exceptional_Lang_root_rank_one_torus_transport τ K hδ).1, rootSubgroup, rootSubgroup,
      Subgroup.closure_union]
  have hneg : ∀ {δ : Fin τ.rank → ℤ}, ¬ IsRoot τ δ → ¬ IsRoot τ (-δ) := fun hδ h =>
    hδ (by simpa using IsRoot.neg h)
  rw [hL hβ, hL hγ]
  refine closure_commute ?_
  rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩) _ (⟨d, rfl⟩ | ⟨d, rfl⟩)
  · exact pinnedX_commute_of_iform_eq_zero K hβ hγ h0 hp c d
  · refine pinnedX_commute_of_iform_eq_zero K hβ (IsRoot.neg hγ) ?_ ?_ c d
    · rw [iform_neg_right, h0, neg_zero]
    · rwa [← sub_eq_add_neg]
  · refine pinnedX_commute_of_iform_eq_zero K (IsRoot.neg hβ) hγ ?_ ?_ c d
    · rw [iform_neg_left, h0, neg_zero]
    · rw [show -β + γ = -(β - γ) by abel]
      exact hneg hm
  · refine pinnedX_commute_of_iform_eq_zero K (IsRoot.neg hβ) (IsRoot.neg hγ) ?_ ?_ c d
    · rw [iform_neg_left, iform_neg_right, h0, neg_zero, neg_zero]
    · rw [show -β + -γ = -(β + γ) by abel]
      exact hneg hp

end CFSG.LieType.Chevalley
