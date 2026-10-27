module

public import CFSG.LieType.Chevalley.ParabolicRadicalLeviRoots
public import CFSG.LieType.Chevalley.RootPairCommonField

public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley

variable {τ : Tag}

@[expose] def heightLinear (τ : Tag) : (Fin τ.rank → ℤ) →ₗ[ℤ] ℤ where
  toFun := height
  map_add' u v := by simp [height, Finset.sum_add_distrib]
  map_smul' c v := by simp [height, Finset.mul_sum]

theorem heightLinear_apply (v : Fin τ.rank → ℤ) : heightLinear τ v = height v :=
  rfl

@[expose] def cartanFunctional (τ : Tag) (j : Fin τ.rank) : (Fin τ.rank → ℤ) →ₗ[ℤ] ℤ :=
  (LinearMap.proj j).comp (Matrix.mulVecLin τ.cartan)

theorem cartanFunctional_apply (j : Fin τ.rank) (v : Fin τ.rank → ℤ) :
    cartanFunctional τ j v = ∑ k, τ.cartan j k * v k :=
  rfl

theorem cartanFunctional_single (j i : Fin τ.rank) :
    cartanFunctional τ j (Pi.single i 1) = τ.cartan j i := by
  rw [cartanFunctional_apply, Finset.sum_eq_single i (fun k _ hk => by simp [hk])
    (fun h => absurd (Finset.mem_univ i) h)]
  simp

theorem cartan_eq_zero_of_symm : ∀ (τ : Tag) (i j : Fin τ.rank),
    (τ.cartan i j).natAbs = 0 → (τ.cartan j i).natAbs = 0 := by
  intro τ
  cases τ <;> decide

theorem cartan_eq_zero_iff_symm (τ : Tag) (i j : Fin τ.rank) :
    τ.cartan i j = 0 ↔ τ.cartan j i = 0 := by
  rw [← Int.natAbs_eq_zero, ← Int.natAbs_eq_zero]
  exact ⟨cartan_eq_zero_of_symm τ i j, cartan_eq_zero_of_symm τ j i⟩

theorem single_mem_parabolicRadicalRoots
    {J : Set (Fin τ.rank)} {i : Fin τ.rank} (hi : i ∉ J) :
    (Pi.single i 1 : Fin τ.rank → ℤ) ∈ parabolicRadicalRoots τ J :=
  mem_parabolicRadicalRoots_iff.2 ⟨isRoot_single τ i, by rw [height_single]; exact one_pos,
    i, hi, by simp⟩

theorem add_smul_single_mem_parabolicRadicalRoots
    {J : Set (Fin τ.rank)} {j : Fin τ.rank}
    (hj : j ∈ J) {α : Fin τ.rank → ℤ} (hα : α ∈ parabolicRadicalRoots τ J) (k : ℤ)
    (hβ : IsRoot τ (α + k • Pi.single j 1)) :
    α + k • Pi.single j 1 ∈ parabolicRadicalRoots τ J := by
  obtain ⟨hαr, hαp, i, hi, hαi⟩ := mem_parabolicRadicalRoots_iff.1 hα
  have hij : i ≠ j := fun h => hi (h ▸ hj)
  have hcoord : (α + k • Pi.single j 1 : Fin τ.rank → ℤ) i = α i := by
    simp [Pi.single_eq_of_ne hij]
  have hpos : 0 < α i := lt_of_le_of_ne ((IsRoot.height_pos_iff hαr).1 hαp i) (Ne.symm hαi)
  have hβp : 0 < height (α + k • Pi.single j 1) := by
    rcases IsRoot.height_pos_or_neg hβ with h | h
    · exact h
    · have := (IsRoot.height_neg_iff hβ).1 h i
      rw [hcoord] at this
      omega
  exact mem_parabolicRadicalRoots_iff.2 ⟨hβ, hβp, i, hi, by rw [hcoord]; exact hαi⟩

theorem single_mem_span_of_adjacent
    {J : Set (Fin τ.rank)} {i j : Fin τ.rank} (hj : j ∈ J)
    (hi : (Pi.single i 1 : Fin τ.rank → ℤ) ∈ Submodule.span ℤ (parabolicRadicalRoots τ J))
    (hji : τ.cartan j i ≠ 0) :
    (Pi.single j 1 : Fin τ.rank → ℤ) ∈ Submodule.span ℤ (parabolicRadicalRoots τ J) := by
  obtain ⟨α, hα, hmα⟩ : ∃ α ∈ parabolicRadicalRoots τ J, cartanFunctional τ j α ≠ 0 := by
    by_contra h
    push Not at h
    have hle : Submodule.span ℤ (parabolicRadicalRoots τ J) ≤
        LinearMap.ker (cartanFunctional τ j) :=
      Submodule.span_le.2 fun α hα => h α hα
    have := hle hi
    rw [LinearMap.mem_ker, cartanFunctional_single] at this
    exact hji this
  obtain ⟨hαr, -, i', hi', hαi'⟩ := mem_parabolicRadicalRoots_iff.1 hα
  have hi'j : i' ≠ j := fun h => hi' (h ▸ hj)
  have hne : α ≠ Pi.single j 1 := fun h => hαi' (by rw [h, Pi.single_eq_of_ne hi'j])
  have hne' : α ≠ -Pi.single j 1 := fun h => hαi' (by
    rw [h, Pi.neg_apply, Pi.single_eq_of_ne hi'j, neg_zero])
  obtain ⟨-, hint⟩ := isRoot_add_smul_single_iff hαr j hne hne'
  have hm := (root_string_reflection hαr j).1
  rw [← cartanFunctional_apply] at hm
  have hspan : ∀ k : ℤ, IsRoot τ (α + k • Pi.single j 1) →
      k • (Pi.single j 1 : Fin τ.rank → ℤ) ∈ Submodule.span ℤ (parabolicRadicalRoots τ J) := by
    intro k hk
    have h1 := Submodule.subset_span (R := ℤ)
      (add_smul_single_mem_parabolicRadicalRoots hj hα k hk)
    have h2 := Submodule.subset_span (R := ℤ) hα
    have := Submodule.sub_mem _ h1 h2
    rwa [add_sub_cancel_left] at this
  by_cases hp : 1 ≤ (stringUp τ j α : ℤ)
  · simpa using hspan 1 ((hint 1).2 ⟨by omega, hp⟩)
  · have hq : 1 ≤ (stringDown τ j α : ℤ) := by
      by_contra hq
      exact hmα (by rw [hm]; omega)
    have := hspan (-1) ((hint (-1)).2 ⟨by omega, by omega⟩)
    rw [neg_smul, one_smul] at this
    simpa using Submodule.neg_mem _ this

theorem span_parabolicRadicalRoots
    {J : Set (Fin τ.rank)} (hJ : J ≠ Set.univ) :
    Submodule.span ℤ (parabolicRadicalRoots τ J) = ⊤ := by
  classical
  set Λ := Submodule.span ℤ (parabolicRadicalRoots τ J) with hΛ
  obtain ⟨i₀, hi₀⟩ : ∃ i₀, i₀ ∉ J := by
    by_contra h
    push Not at h
    exact hJ (Set.eq_univ_of_forall h)
  have hout : ∀ i ∉ J, (Pi.single i 1 : Fin τ.rank → ℤ) ∈ Λ := fun i hi =>
    Submodule.subset_span (single_mem_parabolicRadicalRoots hi)
  have hstep : ∀ i j, τ.cartan j i ≠ 0 → (Pi.single i 1 : Fin τ.rank → ℤ) ∈ Λ →
      (Pi.single j 1 : Fin τ.rank → ℤ) ∈ Λ := fun i j hji hi => by
    by_cases hj : j ∈ J
    · exact single_mem_span_of_adjacent hj hi hji
    · exact hout j hj
  have hall : ∀ j, (Pi.single j 1 : Fin τ.rank → ℤ) ∈ Λ := by
    have hconst := eq_of_cartan_edges (τ := τ)
      (fun i => decide ((Pi.single i 1 : Fin τ.rank → ℤ) ∈ Λ)) fun i j hij => by
        have hij' : τ.cartan i j ≠ 0 := by rw [hij]; decide
        have hji : τ.cartan j i ≠ 0 := fun h => hij' ((cartan_eq_zero_iff_symm τ i j).2 h)
        simp only [decide_eq_decide]
        exact ⟨hstep i j hji, hstep j i hij'⟩
    intro j
    have := hconst j i₀
    simp only [decide_eq_decide] at this
    exact this.2 (hout i₀ hi₀)
  rw [eq_top_iff]
  intro v _
  rw [← Finset.univ_sum_single v]
  refine Submodule.sum_mem _ fun j _ => ?_
  have h := Submodule.smul_mem Λ (v j) (hall j)
  have e : v j • (Pi.single j 1 : Fin τ.rank → ℤ) = Pi.single j (v j) := by
    ext k
    simp [Pi.single_apply]
  rwa [e] at h

theorem mem_parabolicRadicalRoots_smul_iff
    {J : Set (Fin τ.rank)} {w : WeylGroup τ}
    (hw : w ∈ parabolicWeylGroup τ J) (α : Fin τ.rank → ℤ) :
    w • α ∈ parabolicRadicalRoots τ J ↔ α ∈ parabolicRadicalRoots τ J := by
  induction hw using Subgroup.closure_induction generalizing α with
  | mem x hx =>
    obtain ⟨j, hj, rfl⟩ := hx
    rw [simple_smul]
    refine ⟨fun h => ?_, reflect_mem_parabolicRadicalRoots hj⟩
    have := reflect_mem_parabolicRadicalRoots hj h
    rwa [reflect_reflect] at this
  | one => rw [one_smul]
  | mul x y _ _ hx hy => rw [mul_smul, hx, hy]
  | inv x _ hx =>
    rw [← hx, smul_inv_smul]

theorem parabolic_radical_roots_span_lattice
    (τ : Tag) {J : Set (Fin τ.rank)}
    (hJ : J ≠ Set.univ) :
    (∀ α : Fin τ.rank → ℤ, α ∈ parabolicRadicalRoots τ J ↔
      (IsRoot τ α ∧ 0 < height α) ∧ ∃ i ∉ J, 0 < α i) ∧
    Submodule.span ℤ (parabolicRadicalRoots τ J) = ⊤ ∧
    (∀ w ∈ parabolicWeylGroup τ J,
      Set.BijOn (fun α => w • α) (parabolicRadicalRoots τ J) (parabolicRadicalRoots τ J)) ∧
    ∀ w ∈ parabolicWeylGroup τ J,
      (∀ α ∈ parabolicRadicalRoots τ J, height (w • α) = height α) → w = 1 := by
  refine ⟨fun α => ?_, span_parabolicRadicalRoots hJ, fun w hw => ?_, fun w hw hht => ?_⟩
  · rw [mem_parabolicRadicalRoots_iff]
    constructor
    · rintro ⟨hα, hpos, i, hi, hαi⟩
      exact ⟨⟨hα, hpos⟩, i, hi,
        lt_of_le_of_ne ((IsRoot.height_pos_iff hα).1 hpos i) (Ne.symm hαi)⟩
    · rintro ⟨⟨hα, hpos⟩, i, hi, hαi⟩
      exact ⟨hα, hpos, i, hi, hαi.ne'⟩
  · refine ⟨fun α hα => (mem_parabolicRadicalRoots_smul_iff hw α).2 hα,
      fun α _ β _ h => smul_left_cancel w h, fun β hβ => ⟨w⁻¹ • β, ?_, smul_inv_smul w β⟩⟩
    rw [← mem_parabolicRadicalRoots_smul_iff hw, smul_inv_smul]
    exact hβ
  · have hlin : (heightLinear τ).comp (CFSG.LieType.RootSystem.weylAction
        (isFiniteType_cartan τ) w) = heightLinear τ :=
      LinearMap.ext_on (span_parabolicRadicalRoots hJ) fun α hα => hht α hα
    refine eq_one_of_forall_height_pos fun i => ?_
    have := LinearMap.congr_fun hlin (Pi.single i 1)
    rw [LinearMap.comp_apply, heightLinear_apply, heightLinear_apply, height_single] at this
    rw [smul_def, this]
    exact one_pos

end CFSG.LieType.Chevalley
