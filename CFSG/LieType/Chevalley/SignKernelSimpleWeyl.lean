module

public import CFSG.LieType.Chevalley.KernelComponentLength

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint Matrix

variable {τ : Tag} {M : Type*} [CommGroup M]

@[expose] def componentRoots (χ : Multiplicative (Fin τ.rank → ℤ) →* M)
    (i : KernelComponent χ) : Set (Fin τ.rank → ℤ) :=
  {α | ∃ h : α ∈ kernelRoots χ, (⟦⟨α, h⟩⟧ : KernelComponent χ) = i}

variable {χ : Multiplicative (Fin τ.rank → ℤ) →* M}

theorem chi_neg {α : Fin τ.rank → ℤ} (h : χ (Multiplicative.ofAdd α) = 1) :
    χ (Multiplicative.ofAdd (-α)) = 1 := by
  rw [ofAdd_neg, map_inv, h, inv_one]

theorem chi_zsmul {α : Fin τ.rank → ℤ} (h : χ (Multiplicative.ofAdd α) = 1) (n : ℤ) :
    χ (Multiplicative.ofAdd (n • α)) = 1 := by
  rw [ofAdd_zsmul, map_zpow, h, _root_.one_zpow]

theorem isRootComponent_componentRoots
    (i : KernelComponent χ) :
    IsRootComponent (componentRoots χ i) := by
  have hmk : ∀ {α β : Fin τ.rank → ℤ} (hα : α ∈ kernelRoots χ) (hβ : β ∈ kernelRoots χ),
      iform α β ≠ 0 → (⟦⟨α, hα⟩⟧ : KernelComponent χ) = ⟦⟨β, hβ⟩⟧ :=
    fun hα hβ h => mk_eq_of_iform_ne_zero (α := ⟨_, hα⟩) (β := ⟨_, hβ⟩) h
  refine ⟨fun α ⟨h, _⟩ => h.1, fun α ⟨h, hi⟩ => ?_, fun α ⟨hα, hαi⟩ β ⟨hβ, hβi⟩ hr => ?_,
    fun α ⟨hα, hαi⟩ β ⟨hβ, hβi⟩ => ?_, fun S hS horth => ?_⟩
  ·
    have hn : -α ∈ kernelRoots χ := ⟨IsRoot.neg h.1, chi_neg h.2⟩
    refine ⟨hn, (hmk hn h ?_).trans hi⟩
    rw [← neg_one_smul ℤ α, iform_smul_left]
    have := iform_self_pos_of_isRoot h.1
    omega
  ·
    have hs : α + β ∈ kernelRoots χ := ⟨hr, by
      rw [ofAdd_add, map_mul, hα.2, hβ.2, one_mul]⟩
    have hpos := iform_self_pos_of_isRoot hr
    rw [iform_add_right] at hpos
    by_cases h1 : iform (α + β) α = 0
    · rw [h1, zero_add] at hpos
      exact ⟨hs, (hmk hs hβ hpos.ne').trans hβi⟩
    · exact ⟨hs, (hmk hs hα h1).trans hαi⟩
  ·
    have hβr := hβ.1
    have hr : rootReflection β • α ∈ kernelRoots χ := ⟨IsRoot.smul hα.1 _, by
      rw [rootReflection_smul hβr, sub_eq_add_neg, ofAdd_add, map_mul, hα.2, one_mul,
        ← neg_smul, chi_zsmul hβ.2]⟩
    by_cases h0 : iform β α = 0
    · rw [rootReflection_smul_of_iform_eq_zero hβr h0]
      exact ⟨hα, hαi⟩
    · refine ⟨hr, (hmk hr hβ ?_).trans hβi⟩
      have h1 := iform_smul (rootReflection β) α β
      rw [rootReflection_smul_self hβr, ← neg_one_smul ℤ β, iform_smul_right] at h1
      intro h2
      rw [h2, mul_zero] at h1
      exact h0 (by rw [iform_comm]; exact h1.symm)
  ·
    by_cases hne : S = ∅
    · exact Or.inl hne
    right
    obtain ⟨α, hαS⟩ := Set.nonempty_iff_ne_empty.2 hne
    obtain ⟨hα, hαi⟩ := hS hαS
    refine Set.Subset.antisymm hS fun γ hγ => ?_
    obtain ⟨hγk, hγi⟩ := hγ
    have key : ∀ x y : kernelRoots χ, Relation.EqvGen (fun α β : kernelRoots χ =>
        (α : Fin τ.rank → ℤ) ⬝ᵥ (τ.symmetrizedCartan *ᵥ (β : Fin τ.rank → ℤ)) ≠ 0) x y →
        (⟦x⟧ : KernelComponent χ) = i → ((x : Fin τ.rank → ℤ) ∈ S ↔ (y : Fin τ.rank → ℤ) ∈ S) := by
      intro x y hxy
      induction hxy with
      | rel x y hrel =>
        intro hxi
        have hyi : (⟦y⟧ : KernelComponent χ) = i :=
          (Quotient.sound (Relation.EqvGen.rel x y hrel)).symm.trans hxi
        rw [dotProduct_mulVec_eq_iform] at hrel
        constructor
        · intro hx
          by_contra hy
          exact hrel (horth _ hx _ ⟨y.2, hyi⟩ hy)
        · intro hy
          by_contra hx
          exact hrel (by rw [iform_comm]; exact horth _ hy _ ⟨x.2, hxi⟩ hx)
      | refl x => exact fun _ => Iff.rfl
      | symm x y hxy ih =>
        intro hyi
        exact (ih ((Quotient.sound hxy).trans hyi)).symm
      | trans x y z hxy hyz ih1 ih2 =>
        intro hxi
        exact (ih1 hxi).trans (ih2 ((Quotient.sound hxy).symm.trans hxi))
    have hrel := Quotient.exact (hαi.trans hγi.symm)
    exact (key ⟨α, hα⟩ ⟨γ, hγk⟩ hrel hαi).1 hαS

theorem sign_kernel_root_component_simple_Weyl_structure
    (τ : Tag) {M : Type*} [CommGroup M]
    (χ : Multiplicative (Fin τ.rank → ℤ) →* M) (i : KernelComponent χ) :
    (LinearIndependent ℝ fun β : ↥(simpleRoots (componentRoots χ i)) =>
        toReal (β : Fin τ.rank → ℤ)) ∧
    Submodule.span ℝ (toReal '' (simpleRoots (componentRoots χ i) : Set (Fin τ.rank → ℤ))) =
      Submodule.span ℝ (toReal '' componentRoots χ i) ∧
    (∀ α ∈ componentRoots χ i, ∃ c : (Fin τ.rank → ℤ) → ℤ,
      α = ∑ β ∈ simpleRoots (componentRoots χ i), c β • β) ∧
    (∀ α ∈ componentRoots χ i, ∀ c : (Fin τ.rank → ℤ) → ℤ,
      α = ∑ β ∈ simpleRoots (componentRoots χ i), c β • β →
        ((∀ β ∈ simpleRoots (componentRoots χ i), 0 ≤ c β) ↔
          α ∈ posRoots (componentRoots χ i)) ∧
        ((∀ β ∈ simpleRoots (componentRoots χ i), c β ≤ 0) ↔
          α ∈ negRoots (componentRoots χ i))) ∧
    (∀ β ∈ simpleRoots (componentRoots χ i), ∀ γ ∈ simpleRoots (componentRoots χ i), β ≠ γ →
      β ⬝ᵥ (τ.symmetrizedCartan *ᵥ γ) ≤ 0) ∧
    (∀ β ∈ simpleRoots (componentRoots χ i), ∀ γ ∈ simpleRoots (componentRoots χ i),
      Relation.ReflTransGen (fun x y => x ∈ simpleRoots (componentRoots χ i) ∧
        y ∈ simpleRoots (componentRoots χ i) ∧ x ⬝ᵥ (τ.symmetrizedCartan *ᵥ y) ≠ 0) β γ) ∧
    (∀ β ∈ simpleRoots (componentRoots χ i),
      (∀ v : Fin τ.rank → ℤ, (β ⬝ᵥ (τ.symmetrizedCartan *ᵥ β)) • (rootReflection β • v) =
        (β ⬝ᵥ (τ.symmetrizedCartan *ᵥ β)) • v -
          (2 * β ⬝ᵥ (τ.symmetrizedCartan *ᵥ v)) • β) ∧
      (∃ (w : WeylGroup τ) (j : Fin τ.rank), w • (Pi.single j 1 : Fin τ.rank → ℤ) = β ∧
        rootReflection β = w * simple τ j * w⁻¹) ∧
      (∀ α ∈ componentRoots χ i, rootReflection β • α ∈ componentRoots χ i) ∧
      rootReflection β • β = -β ∧
      Set.BijOn (rootReflection β • ·) (posRoots (componentRoots χ i) \ {β})
        (posRoots (componentRoots χ i) \ {β})) ∧
    Finite (componentWeylGroup (componentRoots χ i)) ∧
    componentRoots χ i = {α | ∃ w ∈ componentWeylGroup (componentRoots χ i),
      ∃ β ∈ simpleRoots (componentRoots χ i), α = w • β} ∧
    (∀ w ∈ componentWeylGroup (componentRoots χ i), ∀ β ∈ simpleRoots (componentRoots χ i),
      (componentLength (componentRoots χ i) (rootReflection β * w) =
          componentLength (componentRoots χ i) w - 1 ↔ w⁻¹ • β ∈ negRoots (componentRoots χ i)) ∧
      (w⁻¹ • β ∉ negRoots (componentRoots χ i) →
        componentLength (componentRoots χ i) (rootReflection β * w) =
          componentLength (componentRoots χ i) w + 1) ∧
      (componentLength (componentRoots χ i) (w * rootReflection β) =
          componentLength (componentRoots χ i) w - 1 ↔ w • β ∈ negRoots (componentRoots χ i)) ∧
      (w • β ∉ negRoots (componentRoots χ i) →
        componentLength (componentRoots χ i) (w * rootReflection β) =
          componentLength (componentRoots χ i) w + 1)) ∧
    (∀ w ∈ componentWeylGroup (componentRoots χ i), w ≠ 1 →
      ∃ β ∈ simpleRoots (componentRoots χ i), w • β ∈ negRoots (componentRoots χ i)) ∧
    (∃ w₀ ∈ componentWeylGroup (componentRoots χ i),
      (fun α => w₀ • α) '' posRoots (componentRoots χ i) = negRoots (componentRoots χ i)) ∧
    (∀ β ∈ simpleRoots (componentRoots χ i), ∀ γ ∈ simpleRoots (componentRoots χ i), β ≠ γ →
      β ⬝ᵥ (τ.symmetrizedCartan *ᵥ γ) ≠ 0 →
        componentLength (componentRoots χ i)
          (rootReflection γ * rootReflection β * rootReflection γ) = 3) ∧
    (∀ w ∈ componentWeylGroup (componentRoots χ i), ∀ β ∈ simpleRoots (componentRoots χ i),
      w⁻¹ • β ∈ negRoots (componentRoots χ i) → ∀ l : List (Fin τ.rank → ℤ),
        IsComponentWord (componentRoots χ i) l →
        l.length = componentLength (componentRoots χ i) w → reflectionWordProd l = w →
        ∃ j < l.length, rootReflection β * w = reflectionWordProd (l.eraseIdx j)) := by
  classical
  have hΨ := isRootComponent_componentRoots (χ := χ) i
  set Ψ := componentRoots χ i with hΨdef
  refine ⟨?_, ?_, fun α hα => exists_coords hΨ hα,
    fun α hα c hc => ⟨coords_nonneg_iff hΨ hα hc, coords_nonpos_iff hΨ hα hc⟩,
    fun β hβ γ hγ hne => by
      rw [dotProduct_mulVec_eq_iform]
      exact iform_simpleRoots_nonpos hΨ hβ hγ hne,
    fun β hβ γ hγ => ?_, fun β hβ => ?_, inferInstance, ?_,
    fun w hw β hβ => ⟨(componentLength_rootReflection_mul hΨ hβ hw).1,
      (componentLength_rootReflection_mul hΨ hβ hw).2,
      (componentLength_mul_rootReflection hΨ hβ hw).1,
      (componentLength_mul_rootReflection hΨ hβ hw).2⟩,
    fun w hw hne => exists_smul_mem_negRoots hΨ hw hne, exists_longest hΨ,
    fun β hβ γ hγ hne h => componentLength_braid hΨ hβ hγ hne (by
      rwa [dotProduct_mulVec_eq_iform] at h),
    fun w hw β hβ hneg l hl _ e => by
      rw [← e] at hneg ⊢
      exact exists_eraseIdx_of_mem_negRoots hΨ hl hβ hneg⟩
  ·
    rw [Fintype.linearIndependent_iff]
    intro g hg ⟨β, hβ⟩
    set c : (Fin τ.rank → ℤ) → ℝ := fun γ => if h : γ ∈ simpleRoots Ψ then g ⟨γ, h⟩ else 0
    have hc : ∑ γ ∈ simpleRoots Ψ, c γ • toReal γ = 0 := by
      rw [← Finset.sum_coe_sort (simpleRoots Ψ)]
      convert hg using 2 with x
      simp [c, x.2]
    have := eq_zero_of_sum_smul_simpleRoots hΨ hc β hβ
    simpa [c, hβ] using this
  ·
    refine le_antisymm (Submodule.span_mono (Set.image_mono fun β hβ => simpleRoots_subset hβ))
      (Submodule.span_le.2 ?_)
    rintro _ ⟨α, hα, rfl⟩
    obtain ⟨c, e⟩ := exists_coords hΨ hα
    rw [e, toReal_sum_smul]
    exact Submodule.sum_mem _ fun β hβ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨β, hβ, rfl⟩)
  ·
    have h := simpleRoots_connected hΨ hβ hγ
    refine Relation.ReflTransGen.mono (fun x y hxy => ?_) _ _ h
    obtain ⟨hx, hy, hxy⟩ := hxy
    exact ⟨hx, hy, by rwa [dotProduct_mulVec_eq_iform]⟩
  ·
    have hβr := simpleRoots_isRoot hβ
    obtain ⟨w, j, hwj⟩ := isRoot_iff_exists_smul_single.1 hβr
    refine ⟨fun v => ?_, ⟨w, j, hwj, rootReflection_eq_conj hwj⟩,
      fun α hα => hΨ.reflection_mem α hα β (simpleRoots_subset hβ),
      rootReflection_smul_self hβr, bijOn_rootReflection hΨ hβ⟩
    rw [dotProduct_mulVec_eq_iform, dotProduct_mulVec_eq_iform]
    exact iform_smul_rootReflection_smul hβr v
  ·
    ext α
    constructor
    · intro hα
      exact exists_smul_simpleRoot hΨ hα
    · rintro ⟨w, hw, β, hβ, rfl⟩
      exact smul_mem_of_mem_componentWeylGroup hΨ hw β (simpleRoots_subset hβ)

end CFSG.LieType.Chevalley
