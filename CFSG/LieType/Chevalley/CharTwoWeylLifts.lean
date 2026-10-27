module

public import CFSG.LieType.Chevalley.OrthogonalUnionBruhat
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6ReeContainment

public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint

theorem canonicalRep_rootReflection_eq_charTwo
    {τ : Tag} {K : Type} [Field K]
    [CharP K 2] {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) :
    canonicalRep (coxeterSystem τ) K (rootReflection β) =
      pinnedX τ K β 1 * pinnedX τ K (-β) 1 * pinnedX τ K β 1 := by
  obtain ⟨w, j, hwj⟩ := isRoot_iff_exists_smul_single.1 hβ
  have hmul (x y : WeylGroup τ) :
      canonicalRep (coxeterSystem τ) K (x * y) =
        canonicalRep (coxeterSystem τ) K x * canonicalRep (coxeterSystem τ) K y :=
    CFSG.QuasithinUnique.Setup.X6.canonicalRep_mul_charTwo x y
  have hinv : canonicalRep (coxeterSystem τ) K w⁻¹ =
      (canonicalRep (coxeterSystem τ) K w)⁻¹ := by
    rw [eq_inv_iff_mul_eq_one]
    rw [← hmul w⁻¹ w, inv_mul_cancel, canonicalRep_one]
  have hconj : ∀ {γ : Fin τ.rank → ℤ}, IsRoot τ γ → ∀ {δ : Fin τ.rank → ℤ},
      w • γ = δ → canonicalRep (coxeterSystem τ) K w * pinnedX τ K γ 1 *
        (canonicalRep (coxeterSystem τ) K w)⁻¹ = pinnedX τ K δ 1 := by
    intro γ hγ δ hδ
    obtain ⟨ε, hε, hεc⟩ := exists_canonicalRep_mul_pinnedX_mul_inv K w hγ
    have hε1 : ε = 1 := by
      have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
      have h : (ε - 1) * (ε - 1) = 0 := by linear_combination hε + (1 - ε) * h2
      exact sub_eq_zero.1 (mul_self_eq_zero.1 h)
    rw [hεc, hε1, one_mul, hδ]
  have hj : IsRoot τ (Pi.single j 1) := isRoot_single τ j
  have hsimple : weylElt τ K j 1 = pinnedX τ K (Pi.single j 1) 1 *
      pinnedX τ K (-(Pi.single j 1)) 1 * pinnedX τ K (Pi.single j 1) 1 := by
    rw [weylElt_eq_xUnit_mul]
    simp only [inv_one, Units.val_one, CharTwo.neg_eq, ← pinnedX_single, ← pinnedX_neg_single]
  rw [rootReflection_eq_conj hwj, hmul, hmul, hinv, canonicalRep_simple, hsimple]
  have h₁ := hconj hj hwj
  have h₂ := hconj (IsRoot.neg hj) (by rw [smul_neg, hwj])
  calc
    canonicalRep (coxeterSystem τ) K w *
        (pinnedX τ K (Pi.single j 1) 1 * pinnedX τ K (-(Pi.single j 1)) 1 *
          pinnedX τ K (Pi.single j 1) 1) * (canonicalRep (coxeterSystem τ) K w)⁻¹ =
      (canonicalRep (coxeterSystem τ) K w * pinnedX τ K (Pi.single j 1) 1 *
          (canonicalRep (coxeterSystem τ) K w)⁻¹) *
        (canonicalRep (coxeterSystem τ) K w * pinnedX τ K (-(Pi.single j 1)) 1 *
          (canonicalRep (coxeterSystem τ) K w)⁻¹) *
        (canonicalRep (coxeterSystem τ) K w * pinnedX τ K (Pi.single j 1) 1 *
          (canonicalRep (coxeterSystem τ) K w)⁻¹) := by group
    _ = pinnedX τ K β 1 * pinnedX τ K (-β) 1 * pinnedX τ K β 1 := by rw [h₁, h₂]

theorem map_canonicalRep_rootReflection_charTwo
    {τ : Tag} {K : Type} [Field K]
    [CharP K 2] (F : ModGL τ K →* ModGL τ K) {β γ : Fin τ.rank → ℤ} (hβ : IsRoot τ β)
    (hγ : IsRoot τ γ) (h₁ : F (pinnedX τ K β 1) = pinnedX τ K γ 1)
    (h₂ : F (pinnedX τ K (-β) 1) = pinnedX τ K (-γ) 1) :
    F (canonicalRep (coxeterSystem τ) K (rootReflection β)) =
      canonicalRep (coxeterSystem τ) K (rootReflection γ) := by
  rw [canonicalRep_rootReflection_eq_charTwo hβ,
    canonicalRep_rootReflection_eq_charTwo hγ, map_mul, map_mul, h₁, h₂]

theorem canonicalRep_mem_rootSpan_unionRoots
    {τ : Tag} {K : Type} [Field K]
    [CharP K 2] {M : Type*} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    {J : Set (KernelComponent χ)} {w : WeylGroup τ} (hw : w ∈ unionWeylGroup χ J) :
    canonicalRep (coxeterSystem τ) K w ∈ rootSpan τ K (unionRoots χ J) := by
  have hinv (u : WeylGroup τ) :
      canonicalRep (coxeterSystem τ) K u⁻¹ =
        (canonicalRep (coxeterSystem τ) K u)⁻¹ := by
    rw [eq_inv_iff_mul_eq_one]
    rw [← CFSG.QuasithinUnique.Setup.X6.canonicalRep_mul_charTwo, inv_mul_cancel,
      canonicalRep_one]
  have hgen : ∀ α ∈ unionRoots χ J, pinnedX τ K α 1 ∈ rootSpan τ K (unionRoots χ J) := by
    intro α hα
    rw [rootSpan_eq_closure K (unionRoots χ J)]
    exact Subgroup.subset_closure ⟨α, hα, 1, rfl⟩
  refine Subgroup.closure_induction (p := fun u _ =>
    canonicalRep (coxeterSystem τ) K u ∈ rootSpan τ K (unionRoots χ J)) ?_ ?_ ?_ ?_ hw
  · rintro x ⟨β, hβ, rfl⟩
    have hβΨ : β ∈ unionRoots χ J := mem_unionRoots_of_mem_unionSimpleRoots hβ
    have hX : pinnedX τ K β 1 ∈ rootSpan τ K (unionRoots χ J) := hgen β hβΨ
    have hY : pinnedX τ K (-β) 1 ∈ rootSpan τ K (unionRoots χ J) :=
      hgen (-β) (neg_mem_unionRoots hβΨ)
    rw [canonicalRep_rootReflection_eq_charTwo (isRoot_of_mem_unionSimpleRoots hβ)]
    exact mul_mem (mul_mem hX hY) hX
  · rw [canonicalRep_one]
    exact one_mem _
  · intro x y _ _ hx hy
    rw [CFSG.QuasithinUnique.Setup.X6.canonicalRep_mul_charTwo]
    exact mul_mem hx hy
  · intro x _ hx
    rw [hinv x]
    exact inv_mem hx

theorem map_canonicalRep_eq_self_of_commute
    {τ : Tag} {K : Type} [Field K]
    [CharP K 2] {M : Type*} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    {J : Set (KernelComponent χ)} (F : ModGL τ K →* ModGL τ K)
    (θ : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ)
    (hθ : Set.BijOn θ (unionRoots χ J) (unionRoots χ J))
    (hθref : ∀ γ ∈ unionRoots χ J, ∀ α ∈ unionRoots χ J,
      θ (rootReflection γ • α) = rootReflection (θ γ) • θ α)
    (hF : ∀ α ∈ unionRoots χ J, F (pinnedX τ K α 1) = pinnedX τ K (θ α) 1)
    {w : WeylGroup τ} (hw : w ∈ unionWeylGroup χ J)
    (hwθ : ∀ α ∈ unionRoots χ J, θ (w • α) = w • θ α) :
    F (canonicalRep (coxeterSystem τ) K w) = canonicalRep (coxeterSystem τ) K w := by
  classical
  have hinv (u : WeylGroup τ) :
      canonicalRep (coxeterSystem τ) K u⁻¹ =
        (canonicalRep (coxeterSystem τ) K u)⁻¹ := by
    rw [eq_inv_iff_mul_eq_one]
    rw [← CFSG.QuasithinUnique.Setup.X6.canonicalRep_mul_charTwo, inv_mul_cancel,
      canonicalRep_one]
  have hθneg : ∀ α ∈ unionRoots χ J, θ (-α) = -θ α := by
    intro α hα
    have h := hθref α hα α hα
    rwa [rootReflection_smul_self (isRoot_of_mem_unionRoots hα),
      rootReflection_smul_self (isRoot_of_mem_unionRoots (hθ.mapsTo hα))] at h
  have key : ∀ u ∈ unionWeylGroup χ J, ∃ u' ∈ unionWeylGroup χ J,
      F (canonicalRep (coxeterSystem τ) K u) = canonicalRep (coxeterSystem τ) K u' ∧
      ∀ α ∈ unionRoots χ J, u' • θ α = θ (u • α) := by
    intro u hu
    induction hu using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨β, hβ, rfl⟩ := hx
      have hβΨ : β ∈ unionRoots χ J := mem_unionRoots_of_mem_unionSimpleRoots hβ
      have hβr : IsRoot τ β := isRoot_of_mem_unionSimpleRoots hβ
      have hθβΨ : θ β ∈ unionRoots χ J := hθ.mapsTo hβΨ
      have hθβr : IsRoot τ (θ β) := isRoot_of_mem_unionRoots hθβΨ
      have hmem : rootReflection (θ β) ∈ unionWeylGroup χ J := by
        obtain ⟨v, hv, δ, hδ, hδβ⟩ := exists_smul_unionSimpleRoot hθβΨ
        rw [hδβ, rootReflection_smul_root v (isRoot_of_mem_unionSimpleRoots hδ)]
        exact mul_mem (mul_mem hv (rootReflection_mem_unionWeylGroup hδ)) (inv_mem hv)
      refine ⟨rootReflection (θ β), hmem, ?_, ?_⟩
      · exact map_canonicalRep_rootReflection_charTwo F hβr hθβr (hF β hβΨ)
          (by rw [← hθneg β hβΨ]; exact hF (-β) (neg_mem_unionRoots hβΨ))
      · intro α hα
        exact (hθref β hβΨ α hα).symm
    | one =>
      refine ⟨1, one_mem _, ?_, ?_⟩
      · rw [canonicalRep_one, map_one]
      · intro α _
        rw [one_smul, one_smul]
    | mul x y hx hy ihx ihy =>
      obtain ⟨x', hx', hFx', hx'θ⟩ := ihx
      obtain ⟨y', hy', hFy', hy'θ⟩ := ihy
      refine ⟨x' * y', mul_mem hx' hy', ?_, ?_⟩
      · rw [CFSG.QuasithinUnique.Setup.X6.canonicalRep_mul_charTwo, map_mul, hFx', hFy',
          CFSG.QuasithinUnique.Setup.X6.canonicalRep_mul_charTwo]
      · intro α hα
        rw [mul_smul, hy'θ α hα, hx'θ (y • α) (smul_mem_unionRoots hy hα)]
        congr 1
        exact (mul_smul x y α).symm
    | inv x hx ihx =>
      obtain ⟨x', hx', hFx', hx'θ⟩ := ihx
      refine ⟨x'⁻¹, inv_mem hx', ?_, ?_⟩
      · rw [hinv x, map_inv, hFx', hinv x']
      · intro α hα
        have h := hx'θ (x⁻¹ • α) (smul_mem_unionRoots (inv_mem hx) hα)
        rw [smul_inv_smul] at h
        rw [← h, inv_smul_smul]
  obtain ⟨w', hw', hFw', hw'θ⟩ := key w hw
  have hfix : ∀ α ∈ unionRoots χ J, (w'⁻¹ * w) • α = α := by
    intro α hα
    obtain ⟨β, hβ, hβθ⟩ := hθ.surjOn hα
    rw [← hβθ, mul_smul, ← (hw'θ β hβ).trans (hwθ β hβ), inv_smul_smul]
  have hw'w : w'⁻¹ * w = 1 :=
    eq_one_of_forall_smul_eq (mul_mem (inv_mem hw') hw) hfix
  have hw_eq : w' = w := by
    calc w' = w' * (w'⁻¹ * w) := by rw [hw'w, mul_one]
      _ = w := by group
  rw [hFw', hw_eq]

end CFSG.LieType.Chevalley
