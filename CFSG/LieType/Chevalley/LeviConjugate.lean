module

public import CFSG.LieType.Chevalley.ParabolicRootFactorData
public import CFSG.LieType.Chevalley.WeylSpace

public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley RootSpace

private theorem mem_of_forall_orthogonal_inner_eq_zero
    {τ : Tag}
    (V : Submodule ℝ (RootSpace τ)) {x : RootSpace τ}
    (h : ∀ v ∈ Submodule.orthogonal V, inner ℝ x v = 0) : x ∈ V := by
  have : FiniteDimensional ℝ V := FiniteDimensional.finiteDimensional_submodule V
  have : CompleteSpace V := FiniteDimensional.complete ℝ V
  rw [← Submodule.orthogonal_orthogonal (K := V)]
  exact (Submodule.mem_orthogonal' (Submodule.orthogonal V) x).2 h

private lemma exists_forall_inner_ne_zero
    {τ : Tag}
    (V : Submodule ℝ (RootSpace τ)) :
    ∃ v₀ ∈ Submodule.orthogonal V,
      ∀ α, IsRoot τ α → ofLattice α ∉ V → inner ℝ (ofLattice α) v₀ ≠ 0 := by
  classical
  have h : ∀ α : {α : {v : Fin τ.rank → ℤ // IsRoot τ v} // ofLattice α.1 ∉ V},
      ∃ x ∈ Submodule.orthogonal V, (innerₗ (RootSpace τ) (ofLattice α.1.1)) x ≠ 0 := by
    intro α
    by_contra h
    push Not at h
    exact α.2 (mem_of_forall_orthogonal_inner_eq_zero V fun x hx => h x hx)
  obtain ⟨v₀, hv₀, hv₀'⟩ := Module.Dual.exists_forall_mem_ne_zero_of_forall_exists
    (p := Submodule.orthogonal V)
    (f := fun α : {α : {v : Fin τ.rank → ℤ // IsRoot τ v} // ofLattice α.1 ∉ V} =>
      innerₗ (RootSpace τ) (ofLattice α.1.1)) h
  exact ⟨v₀, hv₀, fun α hα hαV => hv₀' ⟨⟨α, hα⟩, hαV⟩⟩

private theorem mem_smul_image_iff_inner_eq_zero
    {τ : Tag}
    (V : Submodule ℝ (RootSpace τ)) {v₀ : RootSpace τ}
    (hv₀ : v₀ ∈ Submodule.orthogonal V)
    (hv₀' : ∀ α, IsRoot τ α → ofLattice α ∉ V → inner ℝ (ofLattice α) v₀ ≠ 0)
    {w : WeylGroup τ} {y : RootSpace τ} (hwy : v₀ = weylAct τ w y)
    {β : Fin τ.rank → ℤ} :
    β ∈ (fun α => w⁻¹ • α) '' {α | IsRoot τ α ∧ ofLattice α ∈ V} ↔
      IsRoot τ β ∧ inner ℝ (ofLattice β) y = 0 := by
  have hchar : ∀ γ, IsRoot τ γ → (ofLattice γ ∈ V ↔ inner ℝ (ofLattice γ) v₀ = 0) := by
    intro γ hγ
    constructor
    · intro hγV
      exact (Submodule.mem_orthogonal V v₀).1 hv₀ (ofLattice γ) hγV
    · intro hinner
      by_contra hγV
      exact hv₀' γ hγ hγV hinner
  constructor
  · rintro ⟨α, ⟨hα, hαV⟩, rfl⟩
    refine ⟨IsRoot.smul hα w⁻¹, ?_⟩
    have hαinner : inner ℝ (ofLattice α) v₀ = 0 := (hchar α hα).1 hαV
    rw [hwy] at hαinner
    have hmul : w • (w⁻¹ • α) = α := by
      rw [← mul_smul, mul_inv_cancel, one_smul]
    rwa [← hmul, ← weylAct_ofLattice, LinearIsometryEquiv.inner_map_map] at hαinner
  · rintro ⟨hβ, hinner⟩
    refine ⟨w • β, ⟨IsRoot.smul hβ w, ?_⟩, ?_⟩
    · apply (hchar (w • β) (IsRoot.smul hβ w)).2
      rw [hwy, ← weylAct_ofLattice, LinearIsometryEquiv.inner_map_map]
      exact hinner
    · change w⁻¹ • (w • β) = β
      rw [← mul_smul, inv_mul_cancel, one_smul]

private theorem inner_eq_zero_iff_coord_eq_zero
    {τ : Tag}
    {y : RootSpace τ} (hy : y ∈ dominantCone τ) {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) :
    inner ℝ (ofLattice β) y = 0 ↔
      ∀ i, inner ℝ (ofLattice (Pi.single i 1)) y ≠ 0 → β i = 0 := by
  rw [inner_ofLattice_eq_sum]
  constructor
  · intro hsum i hi
    rcases hβ.nonneg_or_nonpos with hnn | hnp
    · have hterm : ∀ j, 0 ≤ (β j : ℝ) * inner ℝ (ofLattice (Pi.single j 1)) y :=
        fun j => mul_nonneg (by exact_mod_cast hnn j) (hy j)
      have hzero := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hterm j)).1 hsum i
        (Finset.mem_univ i)
      exact_mod_cast (mul_eq_zero.1 hzero).resolve_right hi
    · have hterm : ∀ j, (β j : ℝ) * inner ℝ (ofLattice (Pi.single j 1)) y ≤ 0 :=
        fun j => mul_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hnp j) (hy j)
      have hzero := (Finset.sum_eq_zero_iff_of_nonpos (fun j _ => hterm j)).1 hsum i
        (Finset.mem_univ i)
      exact_mod_cast (mul_eq_zero.1 hzero).resolve_right hi
  · intro hzero
    exact Finset.sum_eq_zero fun j _ => by
      by_cases hj : inner ℝ (ofLattice (Pi.single j 1)) y = 0
      · rw [hj, mul_zero]
      · simp [hzero j hj]

theorem exists_smul_rootsIn_eq_parabolicRoots
    {τ : Tag} (V : Submodule ℝ (RootSpace τ)) :
    ∃ u : WeylGroup τ, ∃ J : Set (Fin τ.rank),
      (u • ·) '' {α | IsRoot τ α ∧ ofLattice α ∈ V} = parabolicRoots τ J := by
  classical
  obtain ⟨v₀, hv₀, hv₀'⟩ := exists_forall_inner_ne_zero V
  obtain ⟨w, y, hyD, hwy⟩ := exists_weylAct_mem_dominantCone v₀
  refine ⟨w⁻¹, {i | inner ℝ (ofLattice (Pi.single i 1)) y = 0}, ?_⟩
  ext β
  rw [mem_smul_image_iff_inner_eq_zero V hv₀ hv₀' hwy, parabolicRoots]
  constructor
  · rintro ⟨hβ, hinner⟩
    exact ⟨hβ, fun i hi => (inner_eq_zero_iff_coord_eq_zero hyD hβ).1 hinner i hi⟩
  · rintro ⟨hβ, hcoord⟩
    exact ⟨hβ, (inner_eq_zero_iff_coord_eq_zero hyD hβ).2 hcoord⟩

end CFSG.LieType.Chevalley
