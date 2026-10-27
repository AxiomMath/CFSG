module

public import CFSG.LieType.Chevalley.OrthogonalFoldedWeyl

public section

namespace CFSG.LieType.Chevalley
open CFSG.Blueprint.Chevalley RootSpace

private noncomputable def orbitRoots {τ : Tag} {M : Type*} [CommGroup M]
    (χ : Multiplicative (Fin τ.rank → ℤ) →* M) (J : Set (KernelComponent χ))
    (O : Set (Fin τ.rank → ℤ)) : Set (Fin τ.rank → ℤ) :=
  {α | ∃ i ∈ J, α ∈ componentRoots χ i ∧
    ∃ c : (Fin τ.rank → ℤ) → ℤ,
      (∀ β ∈ simpleRoots (componentRoots χ i), β ∉ O → c β = 0) ∧
      α = ∑ β ∈ simpleRoots (componentRoots χ i), c β • β}

private noncomputable def orbitWeyl {τ : Tag} (O : Set (Fin τ.rank → ℤ)) :
    Subgroup (WeylGroup τ) :=
  Subgroup.closure (rootReflection '' O)

private noncomputable def IsOrbitTop {τ : Tag} {M : Type*} [CommGroup M]
    (χ : Multiplicative (Fin τ.rank → ℤ) →* M) (J : Set (KernelComponent χ))
    (O : Set (Fin τ.rank → ℤ)) (f : WeylGroup τ) : Prop :=
  (∀ α ∈ posRoots (orbitRoots χ J O), f • α ∈ negRoots (orbitRoots χ J O)) ∧
    ∀ α ∈ posRoots (unionRoots χ J), α ∉ posRoots (orbitRoots χ J O) →
      f • α ∈ posRoots (unionRoots χ J) ∧ f • α ∉ posRoots (orbitRoots χ J O)

private theorem orbitRoots_subset_unionRoots {τ : Tag} {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {J : Set (KernelComponent χ)}
    {O : Set (Fin τ.rank → ℤ)} : orbitRoots χ J O ⊆ unionRoots χ J := by
  rintro _ ⟨i, hi, hα, -⟩
  exact componentRoots_subset_unionRoots hi hα

private theorem orbitWeyl_le_unionWeylGroup {τ : Tag} {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {J : Set (KernelComponent χ)}
    {O : Set (Fin τ.rank → ℤ)} (hO : O ⊆ unionSimpleRoots χ J) :
    orbitWeyl O ≤ unionWeylGroup χ J :=
  Subgroup.closure_mono (Set.image_mono hO)

private theorem pi_mem_negRoots
    {τ : Tag} {M : Type*} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    {J : Set (KernelComponent χ)} (π : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ)
    (hπ : Set.BijOn π (unionRoots χ J) (unionRoots χ J))
    (hπpos : ∀ α ∈ unionRoots χ J, 0 < height α → 0 < height (π α))
    (hπref : ∀ γ ∈ unionRoots χ J, ∀ α ∈ unionRoots χ J,
      π (rootReflection γ • α) = rootReflection (π γ) • π α)
    {α : Fin τ.rank → ℤ} (hα : α ∈ negRoots (unionRoots χ J)) :
    π α ∈ negRoots (unionRoots χ J) := by
  have hneg : -α ∈ posRoots (unionRoots χ J) := hα
  have hαΨ : α ∈ unionRoots χ J := by simpa using neg_mem_unionRoots hneg.1
  refine (mem_negRoots_iff_height_neg (hπ.1 hαΨ)).2 ?_
  have hnegα : π (-α) = -π α := by
    have h := hπref α hαΨ α hαΨ
    rwa [rootReflection_smul_self (isRoot_of_mem_unionRoots hαΨ),
      rootReflection_smul_self (isRoot_of_mem_unionRoots (hπ.1 hαΨ))] at h
  have h := hπpos (-α) hneg.1 hneg.2
  rw [hnegα, height_neg] at h
  omega

private theorem rootReflection_smul_mem_orbitRoots
    {τ : Tag} {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {J : Set (KernelComponent χ)}
    {O : Set (Fin τ.rank → ℤ)} (hO : O ⊆ unionSimpleRoots χ J)
    {γ : Fin τ.rank → ℤ} (hγ : γ ∈ O) {α : Fin τ.rank → ℤ}
    (hα : α ∈ orbitRoots χ J O) : rootReflection γ • α ∈ orbitRoots χ J O := by
  obtain ⟨i, hi, hαi, c, hc, e⟩ := hα
  obtain ⟨j, hj, hγj⟩ := hO hγ
  by_cases hji : j = i
  · have hγi : γ ∈ simpleRoots (componentRoots χ i) := hji ▸ hγj
    refine ⟨i, hi, (isRootComponent_componentRoots i).reflection_mem α hαi γ
      (simpleRoots_subset hγi), c - corootPair γ α • unitCoords γ, ?_, ?_⟩
    · intro β hβ hβO
      have hβγ : β ≠ γ := fun h => hβO (h ▸ hγ)
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, unitCoords_of_ne hβγ, mul_zero,
        sub_zero]
      exact hc β hβ hβO
    · rw [rootReflection_smul_coords (simpleRoots_isRoot hγi) hγi e]
  · rw [rootReflection_smul_eq_of_ne hji (simpleRoots_subset hγj) hαi]
    exact ⟨i, hi, hαi, c, hc, e⟩

private theorem rootReflection_smul_pos_of_not_mem
    {τ : Tag} {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {J : Set (KernelComponent χ)}
    {O : Set (Fin τ.rank → ℤ)} (hO : O ⊆ unionSimpleRoots χ J)
    {γ : Fin τ.rank → ℤ} (hγ : γ ∈ O) {α : Fin τ.rank → ℤ}
    (hα : α ∈ posRoots (unionRoots χ J))
    (hαO : α ∉ posRoots (orbitRoots χ J O)) :
    rootReflection γ • α ∈ posRoots (unionRoots χ J) ∧
      rootReflection γ • α ∉ posRoots (orbitRoots χ J O) := by
  obtain ⟨i, hi, hαi⟩ := mem_unionRoots_iff.1 hα.1
  obtain ⟨c, e⟩ := exists_coords (isRootComponent_componentRoots i) hαi
  have hci := isRootComponent_componentRoots (χ := χ) i
  have hc : ∀ β ∈ simpleRoots (componentRoots χ i), 0 ≤ c β :=
    (coords_nonneg_iff hci hαi e).2 ⟨hαi, hα.2⟩
  have hex : ∃ β ∈ simpleRoots (componentRoots χ i), β ∉ O ∧ c β ≠ 0 := by
    by_contra h; push Not at h
    exact hαO ⟨⟨i, hi, hαi, c, fun β hβ hβO => (h β hβ) hβO, e⟩, hα.2⟩
  obtain ⟨β₀, hβ₀, hβ₀O, hc₀⟩ := hex
  have hc₀pos : 0 < c β₀ := lt_of_le_of_ne (hc β₀ hβ₀) (Ne.symm hc₀)
  obtain ⟨j, hj, hγj⟩ := hO hγ
  by_cases hji : j = i
  · have hγi : γ ∈ simpleRoots (componentRoots χ i) := hji ▸ hγj
    let c' : (Fin τ.rank → ℤ) → ℤ := c - corootPair γ α • unitCoords γ
    have e' : rootReflection γ • α =
        ∑ β ∈ simpleRoots (componentRoots χ i), c' β • β :=
      rootReflection_smul_coords (simpleRoots_isRoot hγi) hγi e
    have hc' : c' β₀ = c β₀ := by
      have hβ₀γ : β₀ ≠ γ := fun h => hβ₀O (h ▸ hγ)
      simp only [c', Pi.sub_apply, Pi.smul_apply, smul_eq_mul, unitCoords_of_ne hβ₀γ,
        mul_zero, sub_zero]
    have hβ₀' : 0 < c' β₀ := by rw [hc']; exact hc₀pos
    have hmem : rootReflection γ • α ∈ componentRoots χ i :=
      (isRootComponent_componentRoots i).reflection_mem α hαi γ (simpleRoots_subset hγi)
    have hmemΨ : rootReflection γ • α ∈ unionRoots χ J :=
      componentRoots_subset_unionRoots hi hmem
    constructor
    · rcases mem_posRoots_or_mem_negRoots_unionRoots hmemΨ with hp | hn
      · exact hp
      · exfalso
        have hnon : ∀ β ∈ simpleRoots (componentRoots χ i), c' β ≤ 0 :=
          (coords_nonpos_iff hci hmem e').2
            ((mem_negRoots_iff hci).2 ⟨hmem, (mem_negRoots_iff_height_neg hmemΨ).1 hn⟩)
        have := hnon β₀ hβ₀
        omega
    · intro hmemO
      obtain ⟨i', hi', hβi', c'', hc'', e''⟩ := hmemO.1
      obtain rfl : i' = i := eq_of_mem_componentRoots hβi' hmem
      have hcoords : c'' β₀ = c' β₀ := coords_unique hci (e''.symm.trans e') β₀ hβ₀
      rw [hc'' β₀ hβ₀ hβ₀O] at hcoords
      omega
  · rw [rootReflection_smul_eq_of_ne hji (simpleRoots_subset hγj) hαi]
    exact ⟨hα, hαO⟩

private theorem orbitWeyl_mem_and_complement
    {τ : Tag} {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {J : Set (KernelComponent χ)}
    {O : Set (Fin τ.rank → ℤ)} (hO : O ⊆ unionSimpleRoots χ J) {f : WeylGroup τ}
    (hf : f ∈ orbitWeyl O) :
    (∀ α ∈ orbitRoots χ J O, f • α ∈ orbitRoots χ J O) ∧
      (∀ α ∈ posRoots (unionRoots χ J), α ∉ posRoots (orbitRoots χ J O) →
        f • α ∈ posRoots (unionRoots χ J) ∧ f • α ∉ posRoots (orbitRoots χ J O)) := by
  induction hf using Subgroup.closure_induction'' with
  | mem x hx =>
    obtain ⟨γ, hγ, rfl⟩ := hx
    exact ⟨fun α hα => rootReflection_smul_mem_orbitRoots hO hγ hα,
      fun α hα hαO => rootReflection_smul_pos_of_not_mem hO hγ hα hαO⟩
  | inv_mem x hx =>
    obtain ⟨γ, hγ, rfl⟩ := hx
    rw [rootReflection_inv (isRoot_of_mem_unionSimpleRoots (hO hγ))]
    exact ⟨fun α hα => rootReflection_smul_mem_orbitRoots hO hγ hα,
      fun α hα hαO => rootReflection_smul_pos_of_not_mem hO hγ hα hαO⟩
  | one => exact ⟨fun α hα => by simpa using hα, fun α hα hαO => ⟨hα, hαO⟩⟩
  | mul x y hxmem hymem ihx ihy =>
    refine ⟨fun α hα => ?_, fun α hα hαO => ?_⟩
    · rw [mul_smul]; exact ihx.1 _ (ihy.1 α hα)
    · obtain ⟨h1, h2⟩ := ihy.2 α hα hαO
      simpa only [mul_smul] using ihx.2 _ h1 h2

private theorem smul_posRoots_orbitRoots_subset_negRoots
    {τ : Tag} {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {J : Set (KernelComponent χ)}
    {O : Set (Fin τ.rank → ℤ)} {w : WeylGroup τ} (hw : w ∈ unionWeylGroup χ J)
    (hwO : ∀ γ ∈ O, w • γ ∈ negRoots (unionRoots χ J))
    {α : Fin τ.rank → ℤ} (hα : α ∈ posRoots (orbitRoots χ J O)) :
    w • α ∈ negRoots (unionRoots χ J) := by
  obtain ⟨i, hi, hαi, c, hc, e⟩ := hα.1
  have hci := isRootComponent_componentRoots (χ := χ) i
  have hcnonneg : ∀ β ∈ simpleRoots (componentRoots χ i), 0 ≤ c β :=
    (coords_nonneg_iff hci hαi e).2 ⟨hαi, hα.2⟩
  have hex : ∀ β ∈ simpleRoots (componentRoots χ i), ∃ d : (Fin τ.rank → ℤ) → ℤ,
      w • β = ∑ δ ∈ simpleRoots (componentRoots χ i), d δ • δ := fun β hβ =>
    exists_coords hci (smul_mem_componentRoots hw (simpleRoots_subset hβ))
  choose! d hd using hex
  have hdneg : ∀ β ∈ simpleRoots (componentRoots χ i), β ∈ O →
      ∀ δ ∈ simpleRoots (componentRoots χ i), d β δ ≤ 0 := by
    intro β hβ hβO δ hδ
    have hβi := smul_mem_componentRoots hw (simpleRoots_subset hβ)
    have hrel : w • β ∈ negRoots (componentRoots χ i) :=
      (mem_negRoots_iff hci).2 ⟨hβi, (mem_negRoots_iff_height_neg
        (componentRoots_subset_unionRoots hi hβi)).1 (hwO β hβO)⟩
    exact (coords_nonpos_iff hci hβi (hd β hβ)).2 hrel δ hδ
  have hwα : w • α = ∑ δ ∈ simpleRoots (componentRoots χ i),
      (∑ β ∈ simpleRoots (componentRoots χ i), c β * d β δ) • δ := by
    rw [e, Finset.smul_sum]
    simp only [smul_comm w (c _)]
    rw [Finset.sum_congr rfl fun β hβ => by rw [hd β hβ]]
    simp only [Finset.smul_sum, smul_smul, Finset.sum_smul]
    exact Finset.sum_comm
  have hC : ∀ δ ∈ simpleRoots (componentRoots χ i),
      (∑ β ∈ simpleRoots (componentRoots χ i), c β * d β δ) ≤ 0 := by
    intro δ hδ
    refine Finset.sum_nonpos fun β hβ => ?_
    by_cases hβO : β ∈ O
    · exact mul_nonpos_of_nonneg_of_nonpos (hcnonneg β hβ) (hdneg β hβ hβO δ hδ)
    · rw [hc β hβ hβO, zero_mul]
  have hwαi := smul_mem_componentRoots hw hαi
  exact (mem_negRoots_iff_height_neg (componentRoots_subset_unionRoots hi hwαi)).2
    ((mem_negRoots_iff hci).1 ((coords_nonpos_iff hci hwαi hwα).1 hC)).2

private theorem exists_conj_orbitWeyl
    {τ : Tag} {M : Type*} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    {J : Set (KernelComponent χ)} {O : Set (Fin τ.rank → ℤ)}
    (π : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ) (hO : O ⊆ unionSimpleRoots χ J)
    (hOπ : Set.MapsTo π O O)
    (hπref : ∀ γ ∈ unionRoots χ J, ∀ α ∈ unionRoots χ J,
      π (rootReflection γ • α) = rootReflection (π γ) • π α)
    {f : WeylGroup τ} (hf : f ∈ orbitWeyl O) :
    ∃ f' ∈ orbitWeyl O, ∀ x ∈ unionRoots χ J, f' • π x = π (f • x) := by
  induction hf using Subgroup.closure_induction'' with
  | mem x hx =>
    obtain ⟨γ, hγ, rfl⟩ := hx
    exact ⟨rootReflection (π γ), Subgroup.subset_closure ⟨π γ, hOπ hγ, rfl⟩,
      fun x hx => (hπref γ (mem_unionRoots_of_mem_unionSimpleRoots (hO hγ)) x hx).symm⟩
  | inv_mem x hx =>
    obtain ⟨γ, hγ, rfl⟩ := hx
    refine ⟨rootReflection (π γ), Subgroup.subset_closure ⟨π γ, hOπ hγ, rfl⟩, ?_⟩
    intro x hx
    rw [rootReflection_inv (isRoot_of_mem_unionSimpleRoots (hO hγ))]
    exact (hπref γ (mem_unionRoots_of_mem_unionSimpleRoots (hO hγ)) x hx).symm
  | one =>
    refine ⟨1, one_mem _, ?_⟩
    intro x _
    rw [one_smul, one_smul]
  | mul x y hxmem hymem ihx ihy =>
    obtain ⟨x', hx', hxrel⟩ := ihx
    obtain ⟨y', hy', hyrel⟩ := ihy
    have hyW : y ∈ unionWeylGroup χ J := orbitWeyl_le_unionWeylGroup hO hymem
    refine ⟨x' * y', mul_mem hx' hy', ?_⟩
    intro z hz
    have hmem : y • z ∈ unionRoots χ J := smul_mem_unionRoots hyW hz
    rw [mul_smul, mul_smul, hyrel z hz, hxrel _ hmem]

private theorem isOrbitTop_of_mem
    {τ : Tag} {M : Type*} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    {J : Set (KernelComponent χ)} {O : Set (Fin τ.rank → ℤ)}
    (hO : O ⊆ unionSimpleRoots χ J) {f : WeylGroup τ}
    (hfW : f ∈ unionWeylGroup χ J) (hf : f ∈ orbitWeyl O)
    (hfO : ∀ γ ∈ O, f • γ ∈ negRoots (unionRoots χ J)) : IsOrbitTop χ J O f := by
  have hpos : ∀ α ∈ posRoots (orbitRoots χ J O), f • α ∈ negRoots (unionRoots χ J) :=
    fun α hα => smul_posRoots_orbitRoots_subset_negRoots hfW hfO hα
  constructor
  · intro α hα
    have hneg := hpos α hα
    have hlt : height (f • α) < 0 :=
      (mem_negRoots_iff_height_neg (smul_mem_unionRoots hfW
        (orbitRoots_subset_unionRoots hα.1))).1 hneg
    have hmem := (orbitWeyl_mem_and_complement hO hf).1 α hα.1
    refine ⟨?_, by rw [height_neg]; omega⟩
    obtain ⟨i, hi, hαi, c, hc, e⟩ := hmem
    exact ⟨i, hi, (isRootComponent_componentRoots i).neg_mem (f • α) hαi, -c,
      fun β hβ hβO => by simp only [Pi.neg_apply, hc β hβ hβO, neg_zero],
      by rw [e, ← Finset.sum_neg_distrib]
         exact Finset.sum_congr rfl fun β _ => by rw [Pi.neg_apply, neg_smul]⟩
  · exact (orbitWeyl_mem_and_complement hO hf).2

private theorem orbit_involution
    {τ : Tag} {M : Type*} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    {J : Set (KernelComponent χ)} {O : Set (Fin τ.rank → ℤ)}
    (π : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ)
    (hπ : Set.BijOn π (unionRoots χ J) (unionRoots χ J))
    (hπpos : ∀ α ∈ unionRoots χ J, 0 < height α → 0 < height (π α))
    (hπref : ∀ γ ∈ unionRoots χ J, ∀ α ∈ unionRoots χ J,
      π (rootReflection γ • α) = rootReflection (π γ) • π α)
    (hO : O ⊆ unionSimpleRoots χ J) (hOπ : Set.BijOn π O O) :
    ∃ f : WeylGroup τ, f ∈ unionWeylGroup χ J ∧ IsOrbitTop χ J O f ∧ f * f = 1 ∧
      ∀ α ∈ unionRoots χ J, π (f • α) = f • π α := by
  classical
  obtain ⟨f, hfW, hfmax⟩ := (Set.toFinite (orbitWeyl O : Set (WeylGroup τ))).exists_maximalFor
    (fun v => (unionInversionRoots χ J v).ncard) _ ⟨1, one_mem _⟩
  have hfWeyl : f ∈ unionWeylGroup χ J := orbitWeyl_le_unionWeylGroup hO hfW
  have hfO : ∀ γ ∈ O, f • γ ∈ negRoots (unionRoots χ J) := by
    intro γ hγ
    have hγΔ : γ ∈ unionSimpleRoots χ J := hO hγ
    have hγr := isRoot_of_mem_unionSimpleRoots hγΔ
    have hmemΨ : f • γ ∈ unionRoots χ J := smul_mem_unionRoots hfWeyl
      (mem_unionRoots_of_mem_unionSimpleRoots hγΔ)
    by_contra hneg
    have hpos : 0 < height (f • γ) := by
      rcases IsRoot.height_pos_or_neg (isRoot_of_mem_unionRoots hmemΨ) with h | h
      · exact h
      · exact absurd ((mem_negRoots_iff_height_neg hmemΨ).2 h) hneg
    have hkey := ncard_unionInversionRoots_mul_rootReflection (χ := χ) (J := J)
      (w := f * rootReflection γ) hγΔ (by
        rw [mul_smul, rootReflection_smul_self hγr, smul_neg, height_neg]; omega)
    rw [mul_assoc, rootReflection_mul_self hγr, mul_one] at hkey
    have hlt : (unionInversionRoots χ J f).ncard <
        (unionInversionRoots χ J (f * rootReflection γ)).ncard := Nat.lt_of_succ_le hkey.le
    exact (not_le.2 hlt) (hfmax (mul_mem hfW (Subgroup.subset_closure ⟨γ, hγ, rfl⟩))
      (le_of_lt hlt))
  have hf := isOrbitTop_of_mem hO hfWeyl hfW hfO
  have hf2 : f * f = 1 := by
    have hpos : ∀ α ∈ posRoots (unionRoots χ J), 0 < height ((f * f) • α) := by
      intro α hα
      by_cases hαO : α ∈ posRoots (orbitRoots χ J O)
      · have h2 := hf.1 (-(f • α)) (hf.1 α hαO)
        rw [smul_neg] at h2
        simpa only [neg_neg, mul_smul] using h2.2
      · obtain ⟨h1, h2⟩ := hf.2 α hα hαO
        simpa only [mul_smul] using (hf.2 (f • α) h1 h2).1.2
    by_contra hne
    obtain ⟨β, hβΔ, hβneg⟩ := exists_unionSimpleRoots_smul_mem_negRoots
      (mul_mem hfWeyl hfWeyl) hne
    have hlt := hβneg.2
    rw [height_neg] at hlt
    have := hpos β (mem_posRoots_of_mem_unionSimpleRoots hβΔ)
    omega
  obtain ⟨f', hf'W, hpow⟩ := exists_conj_orbitWeyl π hO hOπ.1 hπref hfW
  have hf'Weyl : f' ∈ unionWeylGroup χ J := orbitWeyl_le_unionWeylGroup hO hf'W
  have hf'O : ∀ γ ∈ O, f' • γ ∈ negRoots (unionRoots χ J) := by
    intro γ hγ
    obtain ⟨δ, hδ, hδeq⟩ := hOπ.2.2 hγ
    rw [← hδeq, hpow δ (mem_unionRoots_of_mem_unionSimpleRoots (hO hδ))]
    exact pi_mem_negRoots π hπ hπpos hπref (hfO δ hδ)
  have hf' := isOrbitTop_of_mem hO hf'Weyl hf'W hf'O
  have hEq : f' = f := by
    let C : Set (Fin τ.rank → ℤ) := {α | α ∈ posRoots (unionRoots χ J) ∧
      α ∉ posRoots (orbitRoots χ J O)}
    have hfinC : C.Finite := (finite_unionRoots (χ := χ) (J := J)).subset fun _ h => h.1.1
    have hfinN : (negRoots (orbitRoots χ J O)).Finite :=
      (finite_unionRoots (χ := χ) (J := J)).subset fun _ hx =>
        by simpa using neg_mem_unionRoots (orbitRoots_subset_unionRoots hx.1)
    have hposEq : (fun x => f' • x) '' posRoots (orbitRoots χ J O) =
        negRoots (orbitRoots χ J O) := by
      have hneg : negRoots (orbitRoots χ J O) =
          (fun x => -x) '' posRoots (orbitRoots χ J O) := by
        ext x; constructor
        · intro h; exact ⟨-x, h, by simp⟩
        · rintro ⟨y, hy, rfl⟩; simpa [negRoots] using hy
      refine Set.eq_of_subset_of_ncard_le ?_ ?_ hfinN
      · rintro _ ⟨α, hα, rfl⟩
        exact hf'.1 α hα
      rw [Set.InjOn.ncard_image (MulAction.injective f').injOn, hneg,
        Set.ncard_image_of_injective _ neg_injective]
    have hCEq : (fun x => f' • x) '' C = C := by
      refine Set.eq_of_subset_of_ncard_le ?_ ?_ hfinC
      · rintro _ ⟨α, hα, rfl⟩
        exact hf'.2 α hα.1 hα.2
      rw [Set.InjOn.ncard_image (MulAction.injective f').injOn]
    have hpres : ∀ α ∈ posRoots (unionRoots χ J), 0 < height ((f'⁻¹ * f) • α) := by
      intro α hα
      by_cases hαO : α ∈ posRoots (orbitRoots χ J O)
      · obtain ⟨β, hβ, hβeq⟩ :
            f • α ∈ (fun x => f' • x) '' posRoots (orbitRoots χ J O) := by
          rw [hposEq]; exact hf.1 α hαO
        have he : (f'⁻¹ * f) • α = β := by rw [mul_smul, ← hβeq, inv_smul_smul]
        rw [he]; exact hβ.2
      · obtain ⟨β, hβ, hβeq⟩ : f • α ∈ (fun x => f' • x) '' C := by
          rw [hCEq]; exact hf.2 α hα hαO
        have he : (f'⁻¹ * f) • α = β := by rw [mul_smul, ← hβeq, inv_smul_smul]
        rw [he]; exact hβ.1.2
    by_contra hne
    have hne1 : f'⁻¹ * f ≠ 1 := fun h => hne (by
      have := congrArg (f' * ·) h
      simpa [mul_assoc] using this.symm)
    obtain ⟨β, hβΔ, hβneg⟩ := exists_unionSimpleRoots_smul_mem_negRoots
      (mul_mem (inv_mem hf'Weyl) hfWeyl) hne1
    have hlt := hβneg.2
    rw [height_neg] at hlt
    have := hpres β (mem_posRoots_of_mem_unionSimpleRoots hβΔ)
    omega
  refine ⟨f, hfWeyl, hf, hf2, fun α hα => ?_⟩
  have h := hpow α hα
  rw [hEq] at h
  exact h.symm

private theorem ncard_inversion_mul_orbit_lt
    {τ : Tag} {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {J : Set (KernelComponent χ)}
    {O : Set (Fin τ.rank → ℤ)} {w f : WeylGroup τ} {β : Fin τ.rank → ℤ}
    (hw : w ∈ unionWeylGroup χ J) (hwO : ∀ γ ∈ O, w • γ ∈ negRoots (unionRoots χ J))
    (hf : IsOrbitTop χ J O f) (hf2 : f * f = 1) (hO : O ⊆ unionSimpleRoots χ J)
    (hβO : β ∈ O) (hβΔ : β ∈ unionSimpleRoots χ J) :
    (unionInversionRoots χ J (w * f)).ncard < (unionInversionRoots χ J w).ncard := by
  classical
  have hwpos : ∀ α ∈ posRoots (orbitRoots χ J O),
      w • α ∈ negRoots (unionRoots χ J) :=
    fun α hα => smul_posRoots_orbitRoots_subset_negRoots hw hwO hα
  have hfin : (posRoots (orbitRoots χ J O)).Finite :=
    (finite_unionRoots (χ := χ) (J := J)).subset fun _ h => orbitRoots_subset_unionRoots h.1
  have hsub : posRoots (orbitRoots χ J O) ⊆ unionInversionRoots χ J w := by
    intro α hα
    exact ⟨⟨orbitRoots_subset_unionRoots hα.1, hα.2⟩, (mem_negRoots_iff_height_neg
      (smul_mem_unionRoots hw (orbitRoots_subset_unionRoots hα.1))).1 (hwpos α hα)⟩
  have hff : ∀ x : Fin τ.rank → ℤ, f • (f • x) = x := fun x => by
    rw [← mul_smul, hf2, one_smul]
  have hN : unionInversionRoots χ J (w * f) = (fun x => f • x) ''
      (unionInversionRoots χ J w \ posRoots (orbitRoots χ J O)) := by
    ext x; constructor
    · intro hx
      have hx2 := hx.2
      rw [mul_smul] at hx2
      have hxO : x ∉ posRoots (orbitRoots χ J O) := by
        intro hxP
        have hneg := hwpos (-(f • x)) (hf.1 x hxP)
        rw [smul_neg] at hneg
        change -(-(w • (f • x))) ∈ posRoots (unionRoots χ J) at hneg
        have hposw : 0 < height (w • (f • x)) := by simpa using hneg.2
        omega
      have hfx := hf.2 x hx.1 hxO
      exact ⟨f • x, ⟨⟨hfx.1, hx2⟩, hfx.2⟩, hff x⟩
    · rintro ⟨y, ⟨hypos, hyneg⟩, rfl⟩
      refine ⟨(hf.2 y hypos.1 hyneg).1, ?_⟩
      rw [mul_smul, hff]
      exact hypos.2
  rw [hN, Set.InjOn.ncard_image (MulAction.injective f).injOn, Set.ncard_sdiff hsub hfin]
  have hle : (posRoots (orbitRoots χ J O)).ncard ≤ (unionInversionRoots χ J w).ncard :=
    Set.ncard_le_ncard hsub ((finite_unionRoots (χ := χ) (J := J)).subset fun _ h => h.1.1)
  have hpos : 0 < (posRoots (orbitRoots χ J O)).ncard :=
    (Set.ncard_pos hfin).2 ⟨β, (by
      obtain ⟨i, hi, hβi⟩ := hO hβO
      exact ⟨i, hi, simpleRoots_subset hβi, unitCoords β,
        fun γ hγ hγO => unitCoords_of_ne fun h => hγO (h ▸ hβO),
        (sum_unitCoords hβi).symm⟩), (mem_posRoots_of_mem_unionSimpleRoots hβΔ).2⟩
  omega

theorem mem_closure_fixed_involutions
    {τ : Tag} {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {J : Set (KernelComponent χ)}
    (π : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ)
    (hπ : Set.BijOn π (unionRoots χ J) (unionRoots χ J))
    (hπΔ : Set.MapsTo π (unionSimpleRoots χ J) (unionSimpleRoots χ J))
    (hπpos : ∀ α ∈ unionRoots χ J, 0 < height α → 0 < height (π α))
    (hπref : ∀ γ ∈ unionRoots χ J, ∀ α ∈ unionRoots χ J,
      π (rootReflection γ • α) = rootReflection (π γ) • π α)
    {w : WeylGroup τ} (hw : w ∈ unionWeylGroup χ J)
    (hwπ : ∀ α ∈ unionRoots χ J, π (w • α) = w • π α) :
    w ∈ Subgroup.closure {v : WeylGroup τ | v ∈ unionWeylGroup χ J ∧
      (∀ α ∈ unionRoots χ J, π (v • α) = v • π α) ∧ v * v = 1} := by
  classical
  let C : Subgroup (WeylGroup τ) := Subgroup.closure {v : WeylGroup τ |
    v ∈ unionWeylGroup χ J ∧ (∀ α ∈ unionRoots χ J, π (v • α) = v • π α) ∧ v * v = 1}
  change w ∈ C
  suffices h : ∀ n, ∀ w : WeylGroup τ, w ∈ unionWeylGroup χ J →
      (∀ α ∈ unionRoots χ J, π (w • α) = w • π α) →
      (unionInversionRoots χ J w).ncard = n → w ∈ C from h _ w hw hwπ rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro w hw hwπ hn
    by_cases h1 : w = 1
    · rw [h1]; exact one_mem _
    obtain ⟨β, hβΔ, hβneg⟩ := exists_unionSimpleRoots_smul_mem_negRoots hw h1
    let O : Set (Fin τ.rank → ℤ) := {γ | ∃ k : ℕ, (π^[k]) β = γ}
    have hOΔ : O ⊆ unionSimpleRoots χ J := by
      rintro γ ⟨k, rfl⟩
      induction k with
      | zero => simpa using hβΔ
      | succ k ihk => simpa only [Function.iterate_succ_apply'] using hπΔ ihk
    have hβO : β ∈ O := ⟨0, rfl⟩
    have hOΨ : O ⊆ unionRoots χ J := hOΔ.trans fun _ h =>
      mem_unionRoots_of_mem_unionSimpleRoots h
    have hfinO : O.Finite := (finite_unionRoots (χ := χ) (J := J)).subset hOΨ
    have hOπ : Set.BijOn π O O :=
      (hfinO.injOn_iff_bijOn_of_mapsTo (by
        rintro γ ⟨k, rfl⟩
        exact ⟨k + 1, by rw [Function.iterate_succ_apply']⟩)).1 fun a ha b hb h =>
        hπ.2.1 (hOΨ ha) (hOΨ hb) h
    have hwO : ∀ γ ∈ O, w • γ ∈ negRoots (unionRoots χ J) := by
      rintro γ ⟨k, rfl⟩
      have hiter : ∀ k, w • ((π^[k]) β) = (π^[k]) (w • β) := by
        intro k; induction k with
        | zero => simp
        | succ k ihk =>
          rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ihk,
            hwπ _ (mem_unionRoots_of_mem_unionSimpleRoots (hOΔ ⟨k, rfl⟩))]
      rw [hiter k]
      induction k with
      | zero => exact hβneg
      | succ k ihk =>
        rw [Function.iterate_succ_apply']
        exact pi_mem_negRoots π hπ hπpos hπref ihk
    obtain ⟨f, hfW, hf, hf2, hfcomm⟩ := orbit_involution π hπ hπpos hπref hOΔ hOπ
    have hlt := ncard_inversion_mul_orbit_lt hw hwO hf hf2 hOΔ hβO hβΔ
    have hwfπ : ∀ α ∈ unionRoots χ J, π ((w * f) • α) = (w * f) • π α := by
      intro α hα
      have h1 : π ((w * f) • α) = w • π (f • α) := by
        rw [mul_smul, hwπ (f • α) (smul_mem_unionRoots hfW hα)]
      calc π ((w * f) • α) = w • π (f • α) := h1
        _ = w • (f • π α) := by rw [hfcomm α hα]
        _ = (w * f) • π α := (mul_smul w f (π α)).symm
    have hmem : w * f ∈ C :=
      ih (unionInversionRoots χ J (w * f)).ncard (hn ▸ hlt) (w * f)
        (mul_mem hw hfW) hwfπ rfl
    rw [show w = w * f * f by rw [mul_assoc, hf2, mul_one]]
    exact mul_mem hmem (show f ∈ C from
      Subgroup.subset_closure ⟨hfW, hfcomm, hf2⟩)
