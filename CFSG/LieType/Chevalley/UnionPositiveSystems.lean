module

public import CFSG.LieType.Chevalley.OrthogonalUnionBruhat

public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint

private noncomputable def twistedInvCount {τ : Tag} {M : Type*} [CommGroup M]
    (χ : Multiplicative (Fin τ.rank → ℤ) →* M) (J : Set (KernelComponent χ))
    (θ : (Fin τ.rank → ℤ) ≃+ (Fin τ.rank → ℤ)) (u : WeylGroup τ) : ℕ :=
  {α | α ∈ posRoots (unionRoots χ J) ∧ u • θ α ∈ negRoots (unionRoots χ J)}.ncard

private theorem twistedInvCount_rootReflection_mul
    {τ : Tag} {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {J : Set (KernelComponent χ)}
    (θ : (Fin τ.rank → ℤ) ≃+ (Fin τ.rank → ℤ))
    (hθ : Set.BijOn θ (unionRoots χ J) (unionRoots χ J))
    {u : WeylGroup τ} (hu : u ∈ unionWeylGroup χ J)
    {β α₀ : Fin τ.rank → ℤ} (hβ : β ∈ unionSimpleRoots χ J)
    (hα₀ : α₀ ∈ posRoots (unionRoots χ J)) (hα₀β : u • θ α₀ = -β) :
    twistedInvCount χ J θ (rootReflection β * u) + 1 = twistedInvCount χ J θ u := by
  classical
  have hβr := isRoot_of_mem_unionSimpleRoots hβ
  have hβpos := mem_posRoots_of_mem_unionSimpleRoots hβ
  have hφinj : Function.Injective (fun x : Fin τ.rank → ℤ => u • θ x) :=
    (MulAction.injective u).comp θ.injective
  let S : Set (Fin τ.rank → ℤ) :=
    {α | α ∈ posRoots (unionRoots χ J) ∧ u • θ α ∈ negRoots (unionRoots χ J)}
  let S' : Set (Fin τ.rank → ℤ) :=
    {α | α ∈ posRoots (unionRoots χ J) ∧
      (rootReflection β * u) • θ α ∈ negRoots (unionRoots χ J)}
  have hEq : S' = S \ {α₀} := by
    ext α
    constructor
    · rintro ⟨hαpos, hαneg⟩
      have hαne : α ≠ α₀ := by
        intro hαeq
        have h1 : rootReflection β • (u • θ α) ∈ negRoots (unionRoots χ J) := by
          simpa only [mul_smul] using hαneg
        rw [hαeq, hα₀β, smul_neg, rootReflection_smul_self hβr, neg_neg] at h1
        have h2 : 0 < -height β := by simpa [height_neg] using h1.2
        have h3 : 0 < height β := hβpos.2
        omega
      refine ⟨⟨hαpos, ?_⟩, hαne⟩
      by_contra hαnot
      have hmem : u • θ α ∈ unionRoots χ J :=
        smul_mem_unionRoots hu (hθ.mapsTo hαpos.1)
      have hαpos' : u • θ α ∈ posRoots (unionRoots χ J) :=
        (mem_posRoots_or_mem_negRoots_unionRoots hmem).resolve_right hαnot
      have hαβ : u • θ α ≠ β := by
        intro hβeq
        have hx : α = -α₀ := by
          apply hφinj
          change u • θ α = u • θ (-α₀)
          rw [hβeq]
          simp only [map_neg, smul_neg, hα₀β, neg_neg]
        rw [hx] at hαpos
        have h2 : 0 < -height α₀ := by
          simpa [height_neg] using hαpos.2
        have h3 : 0 < height α₀ := hα₀.2
        omega
      have hpos' := rootReflection_smul_mem_posRoots_unionRoots hβ hαpos' hαβ
      have hαneg' : rootReflection β • (u • θ α) ∈ negRoots (unionRoots χ J) := by
        simpa only [mul_smul] using hαneg
      have h2 : 0 < height (rootReflection β • (u • θ α)) := hpos'.2
      have h3 : 0 < height (-(rootReflection β • (u • θ α))) := hαneg'.2
      rw [height_neg] at h3
      omega
    · rintro ⟨⟨hαpos, hαneg⟩, hαne⟩
      have hδpos : -(u • θ α) ∈ posRoots (unionRoots χ J) := hαneg
      have hδne : -(u • θ α) ≠ β := by
        intro h
        apply hαne
        apply hφinj
        calc u • θ α = -β := by rw [← h, neg_neg]
          _ = u • θ α₀ := hα₀β.symm
      refine ⟨hαpos, ?_⟩
      change -((rootReflection β * u) • θ α) ∈ posRoots (unionRoots χ J)
      rw [mul_smul, show u • θ α = -(-(u • θ α)) by abel, smul_neg, neg_neg]
      exact rootReflection_smul_mem_posRoots_unionRoots hβ hδpos hδne
  have hmemS : α₀ ∈ S := by
    refine ⟨hα₀, ?_⟩
    rw [hα₀β]
    exact (show -β ∈ negRoots (unionRoots χ J) from by
      simpa [negRoots] using hβpos)
  have hfin : S.Finite :=
    (finite_setOf_isRoot τ).subset fun _ hα => isRoot_of_mem_unionRoots hα.1.1
  change twistedInvCount χ J θ (rootReflection β * u) + 1 = twistedInvCount χ J θ u
  unfold twistedInvCount
  change S'.ncard + 1 = S.ncard
  rw [hEq, Set.ncard_sdiff_singleton_of_mem hmemS]
  have hpos : 0 < S.ncard := (Set.ncard_pos hfin).2 ⟨α₀, hmemS⟩
  omega

private theorem exists_simpleRoot_neg_mem_smul
    {τ : Tag} {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {J : Set (KernelComponent χ)}
    (θ : (Fin τ.rank → ℤ) ≃+ (Fin τ.rank → ℤ))
    (hθ : Set.BijOn θ (unionRoots χ J) (unionRoots χ J))
    {u : WeylGroup τ} (hu : u ∈ unionWeylGroup χ J)
    {α : Fin τ.rank → ℤ} (hα : α ∈ posRoots (unionRoots χ J))
    (hαneg : u • θ α ∈ negRoots (unionRoots χ J)) :
    ∃ β ∈ unionSimpleRoots χ J,
      ∃ α₀ ∈ posRoots (unionRoots χ J), u • θ α₀ = -β := by
  classical
  by_contra hno
  push Not at hno
  have hsurj : Set.SurjOn (fun x => u • θ x) (unionRoots χ J) (unionRoots χ J) := by
    intro γ hγ
    obtain ⟨δ, hδ, hδθ⟩ := hθ.surjOn (smul_mem_unionRoots (inv_mem hu) hγ)
    exact ⟨δ, hδ, by
      show u • θ δ = γ
      rw [hδθ, smul_inv_smul]⟩
  have hex : ∀ β ∈ unionSimpleRoots χ J,
      ∃ γ ∈ posRoots (unionRoots χ J), u • θ γ = β := by
    intro β hβ
    obtain ⟨γ, hγ, hγβ⟩ := hsurj (mem_unionRoots_of_mem_unionSimpleRoots hβ)
    have hγβ' : u • θ γ = β := hγβ
    refine ⟨γ, ?_, hγβ⟩
    rcases mem_posRoots_or_mem_negRoots_unionRoots hγ with hp | hn
    · exact hp
    · exact absurd (by
        have h1 : u • θ (-γ) = -β := by rw [map_neg, smul_neg, hγβ']
        exact h1) (hno β hβ (-γ) hn)
  choose! g hgpos hgβ using hex
  have hη : -(u • θ α) ∈ posRoots (unionRoots χ J) := hαneg
  obtain ⟨i, hi, hηi⟩ := mem_unionRoots_iff.1 hη.1
  obtain ⟨c, hc, hce⟩ := exists_nonneg_coords (isRootComponent_componentRoots i)
    ⟨hηi, hη.2⟩
  have hβΔ : ∀ β ∈ simpleRoots (componentRoots χ i), β ∈ unionSimpleRoots χ J :=
    fun β hβ => ⟨i, hi, hβ⟩
  let δ : Fin τ.rank → ℤ :=
    α + ∑ β ∈ simpleRoots (componentRoots χ i), c β • g β
  have hφδ : u • θ δ = 0 := by
    have hsum : ∑ β ∈ simpleRoots (componentRoots χ i), c β • (u • θ (g β)) =
        ∑ β ∈ simpleRoots (componentRoots χ i), c β • β := by
      refine Finset.sum_congr rfl fun β hβ => ?_
      rw [hgβ β (hβΔ β hβ)]
    have hshift : u • θ (∑ β ∈ simpleRoots (componentRoots χ i), c β • g β) =
        ∑ β ∈ simpleRoots (componentRoots χ i), c β • (u • θ (g β)) := by
      rw [map_sum, Finset.smul_sum]
      exact Finset.sum_congr rfl fun β _ => by
        rw [map_zsmul, smul_comm u (c β)]
    show u • θ (α + ∑ β ∈ simpleRoots (componentRoots χ i), c β • g β) = 0
    rw [map_add, smul_add, hshift, hsum, ← hce]
    abel
  have hφinj : Function.Injective (fun x : Fin τ.rank → ℤ => u • θ x) :=
    (MulAction.injective u).comp θ.injective
  have hδ0 : δ = 0 := by
    apply hφinj
    show u • θ δ = u • θ 0
    rw [hφδ]
    simp
  have hheight : 0 < height δ := by
    show 0 < height (α + ∑ β ∈ simpleRoots (componentRoots χ i), c β • g β)
    rw [height_add, height_finset_sum]
    have hposα : 0 < height α := hα.2
    have hsum : 0 ≤ ∑ β ∈ simpleRoots (componentRoots χ i), height (c β • g β) :=
      Finset.sum_nonneg fun β hβ => by
        rw [height_zsmul]
        exact mul_nonneg (hc β hβ) (hgpos β (hβΔ β hβ)).2.le
    omega
  rw [hδ0, show height (0 : Fin τ.rank → ℤ) = 0 by simp [height]] at hheight
  exact absurd hheight (lt_irrefl 0)

theorem exists_smul_bijOn_posRoots
    {τ : Tag} {M : Type*} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    {J : Set (KernelComponent χ)} (θ : (Fin τ.rank → ℤ) ≃+ (Fin τ.rank → ℤ))
    (hθ : Set.BijOn θ (unionRoots χ J) (unionRoots χ J)) :
    ∃ u ∈ unionWeylGroup χ J,
      Set.BijOn (fun α => u • θ α) (posRoots (unionRoots χ J)) (posRoots (unionRoots χ J)) := by
  classical
  have hfin : (unionRoots χ J).Finite :=
    (finite_setOf_isRoot τ).subset fun _ hα => isRoot_of_mem_unionRoots hα
  have hposfin : (posRoots (unionRoots χ J)).Finite :=
    hfin.subset fun _ hα => hα.1
  obtain ⟨u, hu, hmin⟩ := Set.exists_min_image (unionWeylGroup χ J)
    (twistedInvCount χ J θ) (Set.toFinite _) ⟨1, one_mem _⟩
  by_cases hN : twistedInvCount χ J θ u = 0
  · refine ⟨u, hu, ?_⟩
    have hempty : ∀ α ∈ posRoots (unionRoots χ J),
        u • θ α ∉ negRoots (unionRoots χ J) := by
      intro α hα hαneg
      have hpos : 0 < twistedInvCount χ J θ u := by
        unfold twistedInvCount
        exact (Set.ncard_pos (hfin.subset fun _ h => h.1.1)).2 ⟨α, hα, hαneg⟩
      omega
    have hmaps : Set.MapsTo (fun α => u • θ α)
        (posRoots (unionRoots χ J)) (posRoots (unionRoots χ J)) := by
      intro α hα
      have hmem : u • θ α ∈ unionRoots χ J :=
        smul_mem_unionRoots hu (hθ.mapsTo hα.1)
      rcases mem_posRoots_or_mem_negRoots_unionRoots hmem with hp | hn
      · exact hp
      · exact absurd hn (hempty α hα)
    exact (Set.Finite.injOn_iff_bijOn_of_mapsTo hposfin hmaps).1
      ((MulAction.injective u).comp θ.injective).injOn
  · have hpos : 0 < twistedInvCount χ J θ u := Nat.pos_of_ne_zero hN
    unfold twistedInvCount at hpos
    obtain ⟨α, hαpos, hαneg⟩ :=
      (Set.ncard_pos (hfin.subset fun _ h => h.1.1)).1 hpos
    obtain ⟨β, hβ, α₀, hα₀, hα₀β⟩ :=
      exists_simpleRoot_neg_mem_smul θ hθ hu hαpos hαneg
    have hdec := twistedInvCount_rootReflection_mul θ hθ hu hβ hα₀ hα₀β
    have hu' : rootReflection β * u ∈ unionWeylGroup χ J :=
      mul_mem (rootReflection_mem_unionWeylGroup hβ) hu
    have hle := hmin _ hu'
    omega

end CFSG.LieType.Chevalley
