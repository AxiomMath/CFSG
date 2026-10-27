module

public import CFSG.LieType.Chevalley.RootCharacterKernelProduct

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint Matrix

variable {τ : Tag}

theorem iform_smul
    (w : WeylGroup τ) (x y : Fin τ.rank → ℤ) :
    iform (w • x) (w • y) = iform x y := by
  rw [← dotProduct_mulVec_eq_iform, ← dotProduct_mulVec_eq_iform, rootForm_smul]

theorem symmetrizer_pos (τ : Tag) (j : Fin τ.rank) : 0 < τ.symmetrizer j j := by
  cases τ <;> fin_cases j <;> decide

theorem height_add (u v : Fin τ.rank → ℤ) : height (u + v) = height u + height v := by
  simp only [height, Pi.add_apply, Finset.sum_add_distrib]

theorem height_zsmul (c : ℤ) (v : Fin τ.rank → ℤ) : height (c • v) = c * height v := by
  simp only [height, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]

theorem height_sub (u v : Fin τ.rank → ℤ) : height (u - v) = height u - height v := by
  simp only [height, Pi.sub_apply, Finset.sum_sub_distrib]

theorem height_finset_sum {ι : Type*} (s : Finset ι) (f : ι → Fin τ.rank → ℤ) :
    height (∑ i ∈ s, f i) = ∑ i ∈ s, height (f i) := by
  simp only [height, Finset.sum_apply]
  exact Finset.sum_comm

theorem iform_finset_sum_left
    {ι : Type*} (s : Finset ι) (f : ι → Fin τ.rank → ℤ)
    (y : Fin τ.rank → ℤ) : iform (∑ i ∈ s, f i) y = ∑ i ∈ s, iform (f i) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [iform]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, iform_add_left, ih]

theorem iform_finset_sum_right
    {ι : Type*} (s : Finset ι) (x : Fin τ.rank → ℤ)
    (f : ι → Fin τ.rank → ℤ) : iform x (∑ i ∈ s, f i) = ∑ i ∈ s, iform x (f i) := by
  rw [iform_comm, iform_finset_sum_left]
  exact Finset.sum_congr rfl fun i _ => iform_comm _ _

@[expose] def corootPair (β v : Fin τ.rank → ℤ) : ℤ :=
  2 * iform β v / iform β β

theorem corootPair_mul
    {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (v : Fin τ.rank → ℤ) :
    corootPair β v * iform β β = 2 * iform β v :=
  Int.ediv_mul_cancel (iform_dvd_of_isRoot hβ v)

theorem iform_self_pos_of_isRoot
    {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) : 0 < iform β β :=
  iform_self_pos hβ.ne_zero

theorem smul_conj_simple
    (w : WeylGroup τ) (j : Fin τ.rank) (v : Fin τ.rank → ℤ) :
    (w * simple τ j * w⁻¹) • v =
      v - (∑ k, τ.cartan j k * (w⁻¹ • v) k) • (w • (Pi.single j 1 : Fin τ.rank → ℤ)) := by
  rw [mul_smul, mul_smul, simple_smul]
  change w • (w⁻¹ • v - (∑ k, τ.cartan j k * (w⁻¹ • v) k) • Pi.single j 1) = _
  rw [smul_sub, smul_inv_smul, smul_comm]

theorem corootPair_smul_single
    (w : WeylGroup τ) (j : Fin τ.rank) (v : Fin τ.rank → ℤ) :
    corootPair (w • (Pi.single j 1 : Fin τ.rank → ℤ)) v = ∑ k, τ.cartan j k * (w⁻¹ • v) k := by
  have hβ : IsRoot τ (w • (Pi.single j 1 : Fin τ.rank → ℤ)) := IsRoot.smul (isRoot_single τ j) w
  have h := corootPair_mul hβ v
  have e1 : iform (w • (Pi.single j 1 : Fin τ.rank → ℤ)) (w • (Pi.single j 1 : Fin τ.rank → ℤ)) =
      2 * τ.symmetrizer j j := by rw [iform_smul, iform_single_single]
  have e2 : iform (w • (Pi.single j 1 : Fin τ.rank → ℤ)) v =
      τ.symmetrizer j j * ∑ k, τ.cartan j k * (w⁻¹ • v) k := by
    rw [← smul_inv_smul w v, iform_smul, iform_single_left, inv_smul_smul]
  rw [e1, e2] at h
  have hd := symmetrizer_pos τ j
  have : corootPair (w • (Pi.single j 1 : Fin τ.rank → ℤ)) v * (2 * τ.symmetrizer j j) =
      (∑ k, τ.cartan j k * (w⁻¹ • v) k) * (2 * τ.symmetrizer j j) := by rw [h]; ring
  exact mul_right_cancel₀ (by positivity) this

open _root_.Classical in
@[expose] def rootReflection
    (β : Fin τ.rank → ℤ) : WeylGroup τ :=
  if h : IsRoot τ β then
    Classical.choose (isRoot_iff_exists_smul_single.1 h) *
      simple τ (Classical.choose (Classical.choose_spec (isRoot_iff_exists_smul_single.1 h))) *
        (Classical.choose (isRoot_iff_exists_smul_single.1 h))⁻¹
  else 1

theorem rootReflection_smul
    {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (v : Fin τ.rank → ℤ) :
    rootReflection β • v = v - corootPair β v • β := by
  have hspec := Classical.choose_spec (Classical.choose_spec (isRoot_iff_exists_smul_single.1 hβ))
  simp only [rootReflection, hβ, ↓reduceDIte]
  rw [smul_conj_simple, ← corootPair_smul_single, hspec]

theorem rootReflection_eq_conj
    {β : Fin τ.rank → ℤ} {w : WeylGroup τ} {j : Fin τ.rank}
    (h : w • (Pi.single j 1 : Fin τ.rank → ℤ) = β) :
    rootReflection β = w * simple τ j * w⁻¹ := by
  have hβ : IsRoot τ β := h ▸ IsRoot.smul (isRoot_single τ j) w
  refine ext_single fun i => ?_
  rw [rootReflection_smul hβ, smul_conj_simple, ← corootPair_smul_single, h]

theorem iform_smul_rootReflection_smul
    {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β)
    (v : Fin τ.rank → ℤ) :
    iform β β • (rootReflection β • v) = iform β β • v - (2 * iform β v) • β := by
  rw [rootReflection_smul hβ, smul_sub, smul_smul, ← corootPair_mul hβ v, mul_comm]

theorem rootReflection_smul_self
    {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) :
    rootReflection β • β = -β := by
  have h := corootPair_mul hβ β
  have hp := iform_self_pos_of_isRoot hβ
  have h2 : corootPair β β = 2 := mul_right_cancel₀ hp.ne' (by rw [h])
  rw [rootReflection_smul hβ, h2]
  abel

theorem rootReflection_mul_self
    {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) :
    rootReflection β * rootReflection β = 1 := by
  obtain ⟨w, j, h⟩ := isRoot_iff_exists_smul_single.1 hβ
  rw [rootReflection_eq_conj h]
  have : simple τ j * simple τ j = 1 := (coxeterSystem τ).simple_mul_simple_self j
  calc w * simple τ j * w⁻¹ * (w * simple τ j * w⁻¹) = w * (simple τ j * simple τ j) * w⁻¹ := by
        group
    _ = 1 := by rw [this, mul_one, mul_inv_cancel]

theorem rootReflection_inv
    {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) :
    (rootReflection β)⁻¹ = rootReflection β :=
  inv_eq_of_mul_eq_one_right (rootReflection_mul_self hβ)

theorem rootReflection_smul_root
    (u : WeylGroup τ) {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) :
    rootReflection (u • β) = u * rootReflection β * u⁻¹ := by
  obtain ⟨w, j, h⟩ := isRoot_iff_exists_smul_single.1 hβ
  have h' : (u * w) • (Pi.single j 1 : Fin τ.rank → ℤ) = u • β := by rw [mul_smul, h]
  rw [rootReflection_eq_conj h', rootReflection_eq_conj h]
  group

theorem rootReflection_neg
    {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) :
    rootReflection (-β) = rootReflection β := by
  have h : rootReflection β • β = -β := rootReflection_smul_self hβ
  rw [← h, rootReflection_smul_root _ hβ, rootReflection_inv hβ, mul_assoc,
    rootReflection_mul_self hβ, mul_one]

theorem rootReflection_smul_of_iform_eq_zero
    {β v : Fin τ.rank → ℤ} (hβ : IsRoot τ β)
    (h : iform β v = 0) : rootReflection β • v = v := by
  rw [rootReflection_smul hβ, corootPair, h, mul_zero, Int.zero_ediv, zero_smul, sub_zero]

theorem isRoot_sub_of_iform_pos
    {β γ : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (hγ : IsRoot τ γ)
    (hne : β ≠ γ) (h : 0 < iform β γ) : IsRoot τ (β - γ) := by
  obtain ⟨w, j, rfl⟩ := isRoot_iff_exists_smul_single.1 hγ
  set δ := w⁻¹ • β with hδdef
  have hδ : IsRoot τ δ := IsRoot.smul hβ w⁻¹
  have hβδ : β = w • δ := (smul_inv_smul w β).symm
  have h1 : 0 < iform δ (Pi.single j 1) := by
    rw [← iform_smul w, ← hβδ]
    exact h
  rw [iform_single_right] at h1
  have h2 : 0 < ∑ k, τ.cartan j k * δ k := pos_of_mul_pos_right h1 (symmetrizer_pos τ j).le
  have hne1 : δ ≠ Pi.single j 1 := fun e => hne (by rw [hβδ, e])
  have hne2 : δ ≠ -Pi.single j 1 := fun e => by
    rw [e] at h2
    simp only [Pi.neg_apply, mul_neg, Finset.sum_neg_distrib, sum_cartan_mul_single] at h2
    omega
  obtain ⟨hm, -⟩ := root_string_reflection hδ j
  rw [hm] at h2
  have hq : 1 ≤ (stringDown τ j δ : ℤ) := by omega
  have hr := ((isRoot_add_smul_single_iff hδ j hne1 hne2).2 (-1)).2 ⟨by omega, by omega⟩
  have e : β - w • (Pi.single j 1 : Fin τ.rank → ℤ) = w • (δ + (-1 : ℤ) • Pi.single j 1) := by
    rw [smul_add, smul_comm w (-1 : ℤ), ← hβδ, neg_one_smul, sub_eq_add_neg]
  rw [e]
  exact IsRoot.smul hr w

theorem isRoot_add_of_iform_neg
    {β γ : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (hγ : IsRoot τ γ)
    (hne : β ≠ -γ) (h : iform β γ < 0) : IsRoot τ (β + γ) := by
  have h' : 0 < iform β (-γ) := by
    rw [← neg_one_smul ℤ γ, iform_smul_right]
    omega
  have := isRoot_sub_of_iform_pos hβ (IsRoot.neg hγ) hne h'
  rwa [sub_neg_eq_add] at this

structure IsRootComponent (Ψ : Set (Fin τ.rank → ℤ)) : Prop where
  isRoot : ∀ α ∈ Ψ, IsRoot τ α
  neg_mem : ∀ α ∈ Ψ, -α ∈ Ψ
  add_mem : ∀ α ∈ Ψ, ∀ β ∈ Ψ, IsRoot τ (α + β) → α + β ∈ Ψ
  reflection_mem : ∀ α ∈ Ψ, ∀ β ∈ Ψ, rootReflection β • α ∈ Ψ
  irreducible : ∀ S ⊆ Ψ, (∀ α ∈ S, ∀ β ∈ Ψ, β ∉ S → iform α β = 0) → S = ∅ ∨ S = Ψ

@[expose] def posRoots (Ψ : Set (Fin τ.rank → ℤ)) : Set (Fin τ.rank → ℤ) :=
  {α | α ∈ Ψ ∧ 0 < height α}

@[expose] def negRoots (Ψ : Set (Fin τ.rank → ℤ)) : Set (Fin τ.rank → ℤ) :=
  {α | -α ∈ posRoots Ψ}

open _root_.Classical in
@[expose] def simpleRoots (Ψ : Set (Fin τ.rank → ℤ)) : Finset (Fin τ.rank → ℤ) :=
  (rootFinset τ).filter fun β => β ∈ posRoots Ψ ∧
    ∀ γ ∈ posRoots Ψ, ∀ δ ∈ posRoots Ψ, β ≠ γ + δ

variable {Ψ : Set (Fin τ.rank → ℤ)}

theorem mem_simpleRoots {β : Fin τ.rank → ℤ} :
    β ∈ simpleRoots Ψ ↔ IsRoot τ β ∧ β ∈ posRoots Ψ ∧
      ∀ γ ∈ posRoots Ψ, ∀ δ ∈ posRoots Ψ, β ≠ γ + δ := by
  classical
  rw [simpleRoots, Finset.mem_filter, mem_rootFinset]

theorem mem_negRoots_iff
    (hΨ : IsRootComponent Ψ) {α : Fin τ.rank → ℤ} :
    α ∈ negRoots Ψ ↔ α ∈ Ψ ∧ height α < 0 := by
  refine ⟨fun ⟨h1, h2⟩ => ⟨by simpa using hΨ.neg_mem _ h1, by rwa [height_neg, neg_pos] at h2⟩,
    fun ⟨h1, h2⟩ => ⟨hΨ.neg_mem _ h1, by rwa [height_neg, neg_pos]⟩⟩

theorem mem_posRoots_or_mem_negRoots
    (hΨ : IsRootComponent Ψ) {α : Fin τ.rank → ℤ}
    (hα : α ∈ Ψ) : α ∈ posRoots Ψ ∨ α ∈ negRoots Ψ := by
  rcases IsRoot.height_pos_or_neg (hΨ.isRoot α hα) with h | h
  · exact Or.inl ⟨hα, h⟩
  · exact Or.inr ((mem_negRoots_iff hΨ).2 ⟨hα, h⟩)

theorem not_mem_negRoots_of_mem_posRoots
    {α : Fin τ.rank → ℤ} (h : α ∈ posRoots Ψ) :
    α ∉ negRoots Ψ := fun h' => by
  have := h'.2
  rw [height_neg] at this
  have := h.2
  omega

theorem simpleRoots_subset
    {β : Fin τ.rank → ℤ} (hβ : β ∈ simpleRoots Ψ) : β ∈ Ψ :=
  (mem_simpleRoots.1 hβ).2.1.1

theorem simpleRoots_isRoot
    {β : Fin τ.rank → ℤ} (hβ : β ∈ simpleRoots Ψ) : IsRoot τ β :=
  (mem_simpleRoots.1 hβ).1

theorem simpleRoots_height_pos
    {β : Fin τ.rank → ℤ} (hβ : β ∈ simpleRoots Ψ) : 0 < height β :=
  (mem_simpleRoots.1 hβ).2.1.2

@[expose] def unitCoords (β : Fin τ.rank → ℤ) : (Fin τ.rank → ℤ) → ℤ :=
  fun γ => if γ = β then 1 else 0

theorem unitCoords_self (β : Fin τ.rank → ℤ) : unitCoords β β = 1 := by
  simp [unitCoords]

theorem unitCoords_of_ne {β γ : Fin τ.rank → ℤ} (h : γ ≠ β) : unitCoords β γ = 0 := by
  simp [unitCoords, h]

theorem unitCoords_nonneg (β γ : Fin τ.rank → ℤ) : 0 ≤ unitCoords β γ := by
  unfold unitCoords
  split_ifs <;> omega

theorem sum_unitCoords {Δ : Finset (Fin τ.rank → ℤ)} {β : Fin τ.rank → ℤ} (hβ : β ∈ Δ) :
    ∑ γ ∈ Δ, unitCoords β γ • γ = β := by
  rw [Finset.sum_eq_single β (fun γ _ hγ => by rw [unitCoords_of_ne hγ, zero_smul])
    (fun h => absurd hβ h), unitCoords_self, one_smul]

theorem rootReflection_smul_coords
    {Δ : Finset (Fin τ.rank → ℤ)} {β α : Fin τ.rank → ℤ}
    (hβ : IsRoot τ β) (hβΔ : β ∈ Δ) {c : (Fin τ.rank → ℤ) → ℤ}
    (e : α = ∑ γ ∈ Δ, c γ • γ) :
    rootReflection β • α = ∑ γ ∈ Δ, (c - corootPair β α • unitCoords β) γ • γ := by
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_smul, Finset.sum_sub_distrib,
    mul_smul]
  rw [← Finset.smul_sum, sum_unitCoords hβΔ, ← e, rootReflection_smul hβ]

theorem exists_nonneg_coords
    (hΨ : IsRootComponent Ψ) {α : Fin τ.rank → ℤ}
    (hα : α ∈ posRoots Ψ) :
    ∃ c : (Fin τ.rank → ℤ) → ℤ, (∀ β ∈ simpleRoots Ψ, 0 ≤ c β) ∧
      α = ∑ β ∈ simpleRoots Ψ, c β • β := by
  classical
  suffices h : ∀ n : ℕ, ∀ α, α ∈ posRoots Ψ → height α = n →
      ∃ c : (Fin τ.rank → ℤ) → ℤ, (∀ β ∈ simpleRoots Ψ, 0 ≤ c β) ∧
        α = ∑ β ∈ simpleRoots Ψ, c β • β from
    h _ α hα (Int.toNat_of_nonneg hα.2.le).symm
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro α hα hn
    by_cases hs : α ∈ simpleRoots Ψ
    · refine ⟨unitCoords α, fun β _ => unitCoords_nonneg α β, (sum_unitCoords hs).symm⟩
    · have hα' := hα
      rw [mem_simpleRoots] at hs
      push Not at hs
      obtain ⟨γ, hγ, δ, hδ, rfl⟩ := hs (hΨ.isRoot α hα.1) hα'
      have hsum := hn
      rw [height_add] at hsum
      have h1 := hγ.2
      have h2 := hδ.2
      have hγn : (height γ).toNat < n := by omega
      have hδn : (height δ).toNat < n := by omega
      obtain ⟨c₁, h₁, e₁⟩ := ih _ hγn γ hγ (Int.toNat_of_nonneg hγ.2.le).symm
      obtain ⟨c₂, h₂, e₂⟩ := ih _ hδn δ hδ (Int.toNat_of_nonneg hδ.2.le).symm
      refine ⟨c₁ + c₂, fun β hβ => add_nonneg (h₁ β hβ) (h₂ β hβ), ?_⟩
      rw [e₁, e₂, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun β _ => by rw [Pi.add_apply, add_smul]

theorem iform_simpleRoots_nonpos
    (hΨ : IsRootComponent Ψ) {β γ : Fin τ.rank → ℤ}
    (hβ : β ∈ simpleRoots Ψ) (hγ : γ ∈ simpleRoots Ψ) (hne : β ≠ γ) : iform β γ ≤ 0 := by
  by_contra hpos
  push Not at hpos
  have hβr := simpleRoots_isRoot hβ
  have hγr := simpleRoots_isRoot hγ
  have hd := isRoot_sub_of_iform_pos hβr hγr hne hpos
  have hdΨ : β - γ ∈ Ψ := by
    rw [sub_eq_add_neg]
    exact hΨ.add_mem _ (simpleRoots_subset hβ) _ (hΨ.neg_mem _ (simpleRoots_subset hγ))
      (by rw [← sub_eq_add_neg]; exact hd)
  rcases mem_posRoots_or_mem_negRoots hΨ hdΨ with h | h
  · exact (mem_simpleRoots.1 hβ).2.2 _ h γ (mem_simpleRoots.1 hγ).2.1 (by abel)
  · rw [mem_negRoots_iff hΨ] at h
    have hd' : γ - β ∈ posRoots Ψ := ⟨by simpa using hΨ.neg_mem _ hdΨ, by
      rw [height_sub]
      rw [height_sub] at h
      exact by omega⟩
    exact (mem_simpleRoots.1 hγ).2.2 _ hd' β (mem_simpleRoots.1 hβ).2.1 (by abel)

@[expose] def toReal (v : Fin τ.rank → ℤ) : Fin τ.rank → ℝ :=
  fun j => (v j : ℝ)

@[expose] def rform (x y : Fin τ.rank → ℝ) : ℝ :=
  x ⬝ᵥ ((τ.symmetrizedCartan.map (Int.cast : ℤ → ℝ)) *ᵥ y)

theorem rform_toReal (x y : Fin τ.rank → ℤ) : rform (toReal x) (toReal y) = (iform x y : ℝ) := by
  simp only [rform, toReal, dotProduct, mulVec, Matrix.map_apply, iform, Finset.mul_sum]
  push_cast
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem rform_self_pos
    {x : Fin τ.rank → ℝ} (hx : x ≠ 0) : 0 < rform x x := by
  have h := (posDef_symmetrizedCartan τ).dotProduct_mulVec_pos hx
  simpa [rform] using h

theorem rform_sum_left {ι : Type*} (s : Finset ι) (f : ι → Fin τ.rank → ℝ)
    (y : Fin τ.rank → ℝ) : rform (∑ i ∈ s, f i) y = ∑ i ∈ s, rform (f i) y := by
  simp only [rform, sum_dotProduct]

theorem rform_sum_right {ι : Type*} (s : Finset ι) (x : Fin τ.rank → ℝ)
    (f : ι → Fin τ.rank → ℝ) : rform x (∑ i ∈ s, f i) = ∑ i ∈ s, rform x (f i) := by
  simp only [rform, Matrix.mulVec_sum, dotProduct_sum]

theorem rform_smul_left (a : ℝ) (x y : Fin τ.rank → ℝ) : rform (a • x) y = a * rform x y := by
  simp only [rform, smul_dotProduct, smul_eq_mul]

theorem rform_smul_right (a : ℝ) (x y : Fin τ.rank → ℝ) : rform x (a • y) = a * rform x y := by
  simp only [rform, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem rform_sum_sum {ι κ : Type*} (s : Finset ι) (t : Finset κ) (a : ι → ℝ) (b : κ → ℝ)
    (f : ι → Fin τ.rank → ℝ) (g : κ → Fin τ.rank → ℝ) :
    rform (∑ i ∈ s, a i • f i) (∑ k ∈ t, b k • g k) =
      ∑ i ∈ s, ∑ k ∈ t, a i * b k * rform (f i) (g k) := by
  rw [rform_sum_left]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [rform_smul_left, rform_sum_right, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [rform_smul_right]
  ring

theorem sum_toReal_smul {ι : Type*} (s : Finset ι) (a : ι → ℝ) (f : ι → Fin τ.rank → ℤ) :
    ∑ j, (∑ i ∈ s, a i • toReal (f i)) j = ∑ i ∈ s, a i * (height (f i) : ℝ) := by
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, toReal, height]
  rw [Finset.sum_comm]
  push_cast
  exact Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]

theorem nonpos_of_sum_smul_toReal_eq_zero
    {Δ : Finset (Fin τ.rank → ℤ)}
    (hht : ∀ β ∈ Δ, 0 < height β) (hle : ∀ β ∈ Δ, ∀ γ ∈ Δ, β ≠ γ → iform β γ ≤ 0)
    {c : (Fin τ.rank → ℤ) → ℝ} (hc : ∑ β ∈ Δ, c β • toReal β = 0) : ∀ β ∈ Δ, c β ≤ 0 := by
  classical
  set P := Δ.filter fun β => 0 < c β with hPdef
  set Q := Δ.filter fun β => ¬0 < c β with hQdef
  have hPQ : ∑ β ∈ P, c β • toReal β + ∑ β ∈ Q, c β • toReal β = 0 := by
    rw [Finset.sum_filter_add_sum_filter_not]
    exact hc
  set v := ∑ β ∈ P, c β • toReal β with hvdef
  have hv : v = ∑ β ∈ Q, (-c β) • toReal β := by
    simp only [neg_smul, Finset.sum_neg_distrib]
    exact eq_neg_of_add_eq_zero_left hPQ
  have hvv : rform v v ≤ 0 := by
    have e : rform v v = rform (∑ β ∈ P, c β • toReal β) (∑ β ∈ Q, (-c β) • toReal β) := by
      rw [← hv]
    rw [e, rform_sum_sum]
    refine Finset.sum_nonpos fun β hβ => Finset.sum_nonpos fun γ hγ => ?_
    have hβP := Finset.mem_filter.1 hβ
    have hγQ := Finset.mem_filter.1 hγ
    have hne : β ≠ γ := fun e => hγQ.2 (e ▸ hβP.2)
    rw [rform_toReal]
    have h3 : (iform β γ : ℝ) ≤ 0 := by exact_mod_cast hle β hβP.1 γ hγQ.1 hne
    have h4 : 0 ≤ c β * -c γ := mul_nonneg hβP.2.le (by linarith [not_lt.1 hγQ.2])
    exact mul_nonpos_of_nonneg_of_nonpos h4 h3
  have hv0 : v = 0 := by
    by_contra h
    exact absurd hvv (not_le.2 (rform_self_pos h))
  have hsum : ∑ β ∈ P, c β * (height β : ℝ) = 0 := by
    have := congrArg (fun x : Fin τ.rank → ℝ => ∑ j, x j) hv0
    simpa only [hvdef, sum_toReal_smul, Pi.zero_apply, Finset.sum_const_zero] using this
  intro β hβ
  by_contra h
  push Not at h
  have hβP : β ∈ P := Finset.mem_filter.2 ⟨hβ, h⟩
  have hpos : 0 < ∑ β ∈ P, c β * (height β : ℝ) := Finset.sum_pos (fun γ hγ => by
    have h1 := Finset.mem_filter.1 hγ
    have h2 : (0 : ℝ) < height γ := by exact_mod_cast hht γ h1.1
    exact mul_pos h1.2 h2) ⟨β, hβP⟩
  linarith

theorem eq_zero_of_sum_smul_toReal_eq_zero
    {Δ : Finset (Fin τ.rank → ℤ)}
    (hht : ∀ β ∈ Δ, 0 < height β) (hle : ∀ β ∈ Δ, ∀ γ ∈ Δ, β ≠ γ → iform β γ ≤ 0)
    {c : (Fin τ.rank → ℤ) → ℝ} (hc : ∑ β ∈ Δ, c β • toReal β = 0) : ∀ β ∈ Δ, c β = 0 := by
  have h1 := nonpos_of_sum_smul_toReal_eq_zero hht hle hc
  have hc' : ∑ β ∈ Δ, (-c) β • toReal β = 0 := by
    simp only [Pi.neg_apply, neg_smul, Finset.sum_neg_distrib, hc, neg_zero]
  have h2 := nonpos_of_sum_smul_toReal_eq_zero hht hle hc'
  intro β hβ
  have := h2 β hβ
  simp only [Pi.neg_apply, Left.neg_nonpos_iff] at this
  exact le_antisymm (h1 β hβ) this

theorem eq_zero_of_sum_smul_simpleRoots
    (hΨ : IsRootComponent Ψ)
    {c : (Fin τ.rank → ℤ) → ℝ} (hc : ∑ β ∈ simpleRoots Ψ, c β • toReal β = 0) :
    ∀ β ∈ simpleRoots Ψ, c β = 0 :=
  eq_zero_of_sum_smul_toReal_eq_zero (fun _ hβ => simpleRoots_height_pos hβ)
    (fun _ hβ _ hγ hne => iform_simpleRoots_nonpos hΨ hβ hγ hne) hc

theorem toReal_sum_smul {ι : Type*} (s : Finset ι) (c : ι → ℤ) (f : ι → Fin τ.rank → ℤ) :
    toReal (∑ i ∈ s, c i • f i) = ∑ i ∈ s, (c i : ℝ) • toReal (f i) := by
  ext j
  simp [toReal, Finset.sum_apply]

theorem coords_unique
    (hΨ : IsRootComponent Ψ) {c c' : (Fin τ.rank → ℤ) → ℤ}
    (h : ∑ β ∈ simpleRoots Ψ, c β • β = ∑ β ∈ simpleRoots Ψ, c' β • β) :
    ∀ β ∈ simpleRoots Ψ, c β = c' β := by
  have h1 := congrArg toReal h
  rw [toReal_sum_smul, toReal_sum_smul] at h1
  have h2 : ∑ β ∈ simpleRoots Ψ, ((c β : ℝ) - c' β) • toReal β = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, h1, sub_self]
  intro β hβ
  have := eq_zero_of_sum_smul_simpleRoots hΨ h2 β hβ
  exact_mod_cast sub_eq_zero.1 this

theorem exists_coords
    (hΨ : IsRootComponent Ψ) {α : Fin τ.rank → ℤ} (hα : α ∈ Ψ) :
    ∃ c : (Fin τ.rank → ℤ) → ℤ, α = ∑ β ∈ simpleRoots Ψ, c β • β := by
  rcases mem_posRoots_or_mem_negRoots hΨ hα with h | h
  · obtain ⟨c, -, e⟩ := exists_nonneg_coords hΨ h
    exact ⟨c, e⟩
  · obtain ⟨c, -, e⟩ := exists_nonneg_coords hΨ h
    refine ⟨-c, ?_⟩
    rw [← neg_neg α, e, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun β _ => by rw [Pi.neg_apply, neg_smul]

theorem coords_nonneg_iff
    (hΨ : IsRootComponent Ψ) {α : Fin τ.rank → ℤ} (hα : α ∈ Ψ)
    {c : (Fin τ.rank → ℤ) → ℤ} (hc : α = ∑ β ∈ simpleRoots Ψ, c β • β) :
    (∀ β ∈ simpleRoots Ψ, 0 ≤ c β) ↔ α ∈ posRoots Ψ := by
  constructor
  · intro hnn
    rcases mem_posRoots_or_mem_negRoots hΨ hα with h | h
    · exact h
    · exfalso
      obtain ⟨d, hd, e⟩ := exists_nonneg_coords hΨ h
      have he : ∑ β ∈ simpleRoots Ψ, c β • β = ∑ β ∈ simpleRoots Ψ, (-d) β • β := by
        rw [← hc, ← neg_neg α, e, ← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun β _ => by rw [Pi.neg_apply, neg_smul]
      have hu := coords_unique hΨ he
      have h0 : α = 0 := by
        rw [hc]
        refine Finset.sum_eq_zero fun β hβ => ?_
        have h1 := hu β hβ
        have h2 := hnn β hβ
        have h3 := hd β hβ
        simp only [Pi.neg_apply] at h1
        rw [show c β = 0 by omega, zero_smul]
      exact (hΨ.isRoot α hα).ne_zero h0
  · intro h
    obtain ⟨d, hd, e⟩ := exists_nonneg_coords hΨ h
    have hu := coords_unique hΨ (hc.symm.trans e)
    exact fun β hβ => (hu β hβ).symm ▸ hd β hβ

theorem coords_nonpos_iff
    (hΨ : IsRootComponent Ψ) {α : Fin τ.rank → ℤ} (hα : α ∈ Ψ)
    {c : (Fin τ.rank → ℤ) → ℤ} (hc : α = ∑ β ∈ simpleRoots Ψ, c β • β) :
    (∀ β ∈ simpleRoots Ψ, c β ≤ 0) ↔ α ∈ negRoots Ψ := by
  have hc' : -α = ∑ β ∈ simpleRoots Ψ, (-c) β • β := by
    rw [hc, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun β _ => by rw [Pi.neg_apply, neg_smul]
  have := coords_nonneg_iff hΨ (hΨ.neg_mem α hα) hc'
  simp only [Pi.neg_apply, Left.nonneg_neg_iff] at this
  exact this

theorem simpleRoot_mem_posRoots
    {β : Fin τ.rank → ℤ} (hβ : β ∈ simpleRoots Ψ) :
    β ∈ posRoots Ψ :=
  (mem_simpleRoots.1 hβ).2.1

theorem mem_posRoots_of_coord_pos
    (hΨ : IsRootComponent Ψ) {α : Fin τ.rank → ℤ} (hα : α ∈ Ψ)
    {c : (Fin τ.rank → ℤ) → ℤ} (hc : α = ∑ β ∈ simpleRoots Ψ, c β • β) {γ : Fin τ.rank → ℤ}
    (hγ : γ ∈ simpleRoots Ψ) (hpos : 0 < c γ) : α ∈ posRoots Ψ := by
  rcases mem_posRoots_or_mem_negRoots hΨ hα with h | h
  · exact h
  · have := (coords_nonpos_iff hΨ hα hc).2 h γ hγ
    omega

theorem rootReflection_mem_posRoots
    (hΨ : IsRootComponent Ψ) {β : Fin τ.rank → ℤ}
    (hβ : β ∈ simpleRoots Ψ) {α : Fin τ.rank → ℤ} (hα : α ∈ posRoots Ψ) (hne : α ≠ β) :
    rootReflection β • α ∈ posRoots Ψ ∧ rootReflection β • α ≠ β := by
  classical
  have hβr := simpleRoots_isRoot hβ
  obtain ⟨c, hc, e⟩ := exists_nonneg_coords hΨ hα
  obtain ⟨γ, hγ, hγβ, hγpos⟩ : ∃ γ ∈ simpleRoots Ψ, γ ≠ β ∧ 0 < c γ := by
    by_contra! h
    have hα' : α = c β • β := by
      rw [e, Finset.sum_eq_single β (fun γ hγ hγβ => by
        rw [show c γ = 0 from le_antisymm (h γ hγ hγβ) (hc γ hγ), zero_smul])
        (fun h' => absurd hβ h')]
    rcases (hΨ.isRoot α hα.1).eq_one_or_neg_one_of_eq_smul hα' with h1 | h1
    · exact hne (by rw [hα', h1, one_smul])
    · have := hc β hβ
      omega
  have hr : rootReflection β • α ∈ Ψ := hΨ.reflection_mem α hα.1 β (simpleRoots_subset hβ)
  have he := rootReflection_smul_coords hβr hβ e
  have hpos := mem_posRoots_of_coord_pos hΨ hr he hγ (by
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, unitCoords_of_ne hγβ, mul_zero,
      sub_zero]
    exact hγpos)
  refine ⟨hpos, fun h => ?_⟩
  have : α = -β := by
    have h2 := congrArg (rootReflection β • ·) h
    simp only [smul_smul, rootReflection_mul_self hβr, one_smul] at h2
    rw [h2, rootReflection_smul_self hβr]
  rw [this] at hα
  have := hα.2
  rw [height_neg] at this
  have := simpleRoots_height_pos hβ
  omega

theorem bijOn_rootReflection
    (hΨ : IsRootComponent Ψ) {β : Fin τ.rank → ℤ}
    (hβ : β ∈ simpleRoots Ψ) :
    Set.BijOn (rootReflection β • ·) (posRoots Ψ \ {β}) (posRoots Ψ \ {β}) := by
  have hβr := simpleRoots_isRoot hβ
  have hmaps : Set.MapsTo (rootReflection β • ·) (posRoots Ψ \ {β}) (posRoots Ψ \ {β}) :=
    fun α ⟨hα, hne⟩ => ⟨(rootReflection_mem_posRoots hΨ hβ hα hne).1,
      (rootReflection_mem_posRoots hΨ hβ hα hne).2⟩
  refine Set.InvOn.bijOn ⟨fun α _ => ?_, fun α _ => ?_⟩ hmaps hmaps <;>
    simp only [smul_smul, rootReflection_mul_self hβr, one_smul]

@[expose] def componentWeylGroup
    (Ψ : Set (Fin τ.rank → ℤ)) : Subgroup (WeylGroup τ) :=
  Subgroup.closure (rootReflection '' (simpleRoots Ψ : Set (Fin τ.rank → ℤ)))

theorem rootReflection_mem_componentWeylGroup
    {β : Fin τ.rank → ℤ} (hβ : β ∈ simpleRoots Ψ) :
    rootReflection β ∈ componentWeylGroup Ψ :=
  Subgroup.subset_closure ⟨β, hβ, rfl⟩

theorem smul_mem_of_mem_componentWeylGroup
    (hΨ : IsRootComponent Ψ) {w : WeylGroup τ}
    (hw : w ∈ componentWeylGroup Ψ) : ∀ α ∈ Ψ, w • α ∈ Ψ := by
  induction hw using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨β, hβ, rfl⟩ := hx
    exact fun α hα => hΨ.reflection_mem α hα β (simpleRoots_subset hβ)
  | one => exact fun α hα => by rwa [one_smul]
  | mul x y _ _ hx hy => exact fun α hα => by rw [mul_smul]; exact hx _ (hy α hα)
  | inv x hx' hx =>
    intro α hα
    have hfin : Ψ.Finite := (finite_setOf_isRoot τ).subset fun γ hγ => hΨ.isRoot γ hγ
    have hinj : Set.InjOn (x • ·) Ψ := fun a _ b _ h => smul_left_cancel x h
    have hsurj := (Set.Finite.injOn_iff_bijOn_of_mapsTo hfin (f := (x • ·)) hx).1 hinj
    obtain ⟨γ, hγ, hxγ⟩ := hsurj.2.2 hα
    rw [← hxγ, inv_smul_smul]
    exact hγ

theorem smul_mem_posRoots_or_negRoots
    (hΨ : IsRootComponent Ψ) {w : WeylGroup τ}
    (hw : w ∈ componentWeylGroup Ψ) {α : Fin τ.rank → ℤ} (hα : α ∈ Ψ) :
    w • α ∈ posRoots Ψ ∨ w • α ∈ negRoots Ψ :=
  mem_posRoots_or_mem_negRoots hΨ (smul_mem_of_mem_componentWeylGroup hΨ hw α hα)

theorem exists_smul_simpleRoot_of_pos
    (hΨ : IsRootComponent Ψ) {α : Fin τ.rank → ℤ}
    (hα : α ∈ posRoots Ψ) :
    ∃ w ∈ componentWeylGroup Ψ, ∃ β ∈ simpleRoots Ψ, α = w • β := by
  classical
  suffices h : ∀ n : ℕ, ∀ α, α ∈ posRoots Ψ → height α = n →
      ∃ w ∈ componentWeylGroup Ψ, ∃ β ∈ simpleRoots Ψ, α = w • β from
    h _ α hα (Int.toNat_of_nonneg hα.2.le).symm
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro α hα hn
    by_cases hs : α ∈ simpleRoots Ψ
    · exact ⟨1, one_mem _, α, hs, (one_smul _ _).symm⟩
    ·
      obtain ⟨c, hc, e⟩ := exists_nonneg_coords hΨ hα
      have hαα := iform_self_pos_of_isRoot (hΨ.isRoot α hα.1)
      obtain ⟨β, hβ, hαβ⟩ : ∃ β ∈ simpleRoots Ψ, 0 < iform β α := by
        by_contra! h
        have : iform α α ≤ 0 := by
          conv_lhs => arg 1; rw [e]
          rw [iform_finset_sum_left]
          refine Finset.sum_nonpos fun β hβ => ?_
          rw [iform_smul_left]
          exact mul_nonpos_of_nonneg_of_nonpos (hc β hβ) (h β hβ)
        omega
      have hβr := simpleRoots_isRoot hβ
      have hne : α ≠ β := fun h => hs (h ▸ hβ)
      obtain ⟨hpos, -⟩ := rootReflection_mem_posRoots hΨ hβ hα hne
      have hk : 0 < corootPair β α := by
        have h1 := corootPair_mul hβr α
        have h2 := iform_self_pos_of_isRoot hβr
        by_contra! h3
        have : corootPair β α * iform β β ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h3 h2.le
        omega
      have hlt : (height (rootReflection β • α)).toNat < n := by
        rw [rootReflection_smul hβr, height_sub, height_zsmul]
        have := simpleRoots_height_pos hβ
        have := hpos.2
        rw [rootReflection_smul hβr, height_sub, height_zsmul] at this
        have : 0 < corootPair β α * height β := mul_pos hk (simpleRoots_height_pos hβ)
        omega
      obtain ⟨w, hw, γ, hγ, e'⟩ := ih _ hlt _ hpos (Int.toNat_of_nonneg hpos.2.le).symm
      refine ⟨rootReflection β * w, mul_mem (rootReflection_mem_componentWeylGroup hβ) hw, γ, hγ,
        ?_⟩
      rw [mul_smul, ← e', smul_smul, rootReflection_mul_self hβr, one_smul]

theorem exists_smul_simpleRoot
    (hΨ : IsRootComponent Ψ) {α : Fin τ.rank → ℤ} (hα : α ∈ Ψ) :
    ∃ w ∈ componentWeylGroup Ψ, ∃ β ∈ simpleRoots Ψ, α = w • β := by
  rcases mem_posRoots_or_mem_negRoots hΨ hα with h | h
  · exact exists_smul_simpleRoot_of_pos hΨ h
  · obtain ⟨w, hw, β, hβ, e⟩ := exists_smul_simpleRoot_of_pos hΨ h
    refine ⟨w * rootReflection β, mul_mem hw (rootReflection_mem_componentWeylGroup hβ), β, hβ,
      ?_⟩
    rw [mul_smul, rootReflection_smul_self (simpleRoots_isRoot hβ), smul_neg, ← e, neg_neg]

@[expose] def SimpleAdj (Ψ : Set (Fin τ.rank → ℤ)) (β γ : Fin τ.rank → ℤ) : Prop :=
  β ∈ simpleRoots Ψ ∧ γ ∈ simpleRoots Ψ ∧ iform β γ ≠ 0

theorem iform_eq_zero_of_supports
    {Δ : Finset (Fin τ.rank → ℤ)} {C : Set (Fin τ.rank → ℤ)}
    (horth : ∀ δ ∈ Δ, δ ∈ C → ∀ ε ∈ Δ, ε ∉ C → iform δ ε = 0)
    {c c' : (Fin τ.rank → ℤ) → ℤ} (hc : ∀ δ ∈ Δ, δ ∉ C → c δ = 0)
    (hc' : ∀ δ ∈ Δ, δ ∈ C → c' δ = 0) :
    iform (∑ δ ∈ Δ, c δ • δ) (∑ δ ∈ Δ, c' δ • δ) = 0 := by
  rw [iform_finset_sum_left]
  refine Finset.sum_eq_zero fun δ hδ => ?_
  rw [iform_finset_sum_right]
  refine Finset.sum_eq_zero fun ε hε => ?_
  rw [iform_smul_left, iform_smul_right]
  by_cases hδC : δ ∈ C
  · by_cases hεC : ε ∈ C
    · rw [hc' ε hε hεC, zero_mul, mul_zero]
    · rw [horth δ hδ hδC ε hε hεC, mul_zero, mul_zero]
  · rw [hc δ hδ hδC, zero_mul]

@[expose] def supportedRoots (Ψ : Set (Fin τ.rank → ℤ)) (C : Set (Fin τ.rank → ℤ)) :
    Set (Fin τ.rank → ℤ) :=
  {α | α ∈ Ψ ∧ ∃ c : (Fin τ.rank → ℤ) → ℤ, (∀ δ ∈ simpleRoots Ψ, δ ∉ C → c δ = 0) ∧
    α = ∑ δ ∈ simpleRoots Ψ, c δ • δ}

theorem rootReflection_smul_mem_supportedRoots
    (hΨ : IsRootComponent Ψ)
    {C : Set (Fin τ.rank → ℤ)}
    (horth : ∀ δ ∈ simpleRoots Ψ, δ ∈ C → ∀ ε ∈ simpleRoots Ψ, ε ∉ C → iform δ ε = 0)
    {δ : Fin τ.rank → ℤ} (hδ : δ ∈ simpleRoots Ψ) {α : Fin τ.rank → ℤ}
    (hα : α ∈ supportedRoots Ψ C) : rootReflection δ • α ∈ supportedRoots Ψ C := by
  obtain ⟨hαΨ, c, hc, e⟩ := hα
  have hδr := simpleRoots_isRoot hδ
  refine ⟨hΨ.reflection_mem α hαΨ δ (simpleRoots_subset hδ), ?_⟩
  by_cases hδC : δ ∈ C
  · refine ⟨c - corootPair δ α • unitCoords δ, fun ε hε hεC => ?_,
      rootReflection_smul_coords hδr hδ e⟩
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hc ε hε hεC,
      unitCoords_of_ne (fun h : ε = δ => hεC (h ▸ hδC)), mul_zero, sub_zero]
  ·
    have h0 : iform δ α = 0 := by
      have h := iform_eq_zero_of_supports (Δ := simpleRoots Ψ) (C := C) horth hc
        (c' := unitCoords δ) (fun ε _ hεC => unitCoords_of_ne (fun h : ε = δ => hδC (h ▸ hεC)))
      rw [sum_unitCoords hδ, ← e] at h
      rw [iform_comm]
      exact h
    rw [rootReflection_smul_of_iform_eq_zero hδr h0]
    exact ⟨c, hc, e⟩

theorem smul_mem_of_forall_rootReflection
    (hΨ : IsRootComponent Ψ) {S : Set (Fin τ.rank → ℤ)}
    (hSΨ : S ⊆ Ψ) (hS : ∀ δ ∈ simpleRoots Ψ, ∀ α ∈ S, rootReflection δ • α ∈ S)
    {w : WeylGroup τ} (hw : w ∈ componentWeylGroup Ψ) : ∀ α ∈ S, w • α ∈ S := by
  induction hw using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨δ, hδ, rfl⟩ := hx
    exact hS δ hδ
  | one => exact fun α hα => by rwa [one_smul]
  | mul x y _ _ hx hy => exact fun α hα => by rw [mul_smul]; exact hx _ (hy α hα)
  | inv x _ hx =>
    intro α hα
    have hfin : S.Finite :=
      (finite_setOf_isRoot τ).subset fun γ hγ => hΨ.isRoot γ (hSΨ hγ)
    have hinj : Set.InjOn (x • ·) S := fun a _ b _ h => smul_left_cancel x h
    have hsurj := (Set.Finite.injOn_iff_bijOn_of_mapsTo hfin (f := (x • ·)) hx).1 hinj
    obtain ⟨γ, hγ, hxγ⟩ := hsurj.2.2 hα
    rw [← hxγ, inv_smul_smul]
    exact hγ

theorem simpleRoots_connected
    (hΨ : IsRootComponent Ψ) {β γ : Fin τ.rank → ℤ}
    (hβ : β ∈ simpleRoots Ψ) (hγ : γ ∈ simpleRoots Ψ) :
    Relation.ReflTransGen (SimpleAdj Ψ) β γ := by
  classical
  set C := {δ | Relation.ReflTransGen (SimpleAdj Ψ) β δ} with hC
  set C' := {δ | ¬Relation.ReflTransGen (SimpleAdj Ψ) β δ} with hC'
  have horth : ∀ δ ∈ simpleRoots Ψ, δ ∈ C → ∀ ε ∈ simpleRoots Ψ, ε ∉ C → iform δ ε = 0 := by
    intro δ hδ hδC ε hε hεC
    by_contra h
    exact hεC (Relation.ReflTransGen.tail hδC ⟨hδ, hε, h⟩)
  have horth' : ∀ δ ∈ simpleRoots Ψ, δ ∈ C' → ∀ ε ∈ simpleRoots Ψ, ε ∉ C' → iform δ ε = 0 :=
    fun δ hδ hδC ε hε hεC => by
      rw [iform_comm]
      exact horth ε hε (not_not.1 hεC) δ hδ hδC
  have hsupp : ∀ δ ∈ simpleRoots Ψ, δ ∈ supportedRoots Ψ C ∨ δ ∈ supportedRoots Ψ C' := by
    intro δ hδ
    by_cases hδC : δ ∈ C
    · exact Or.inl ⟨simpleRoots_subset hδ, unitCoords δ,
        fun ε _ hεC => unitCoords_of_ne (fun h : ε = δ => hεC (h ▸ hδC)),
        (sum_unitCoords hδ).symm⟩
    · exact Or.inr ⟨simpleRoots_subset hδ, unitCoords δ,
        fun ε _ hεC => unitCoords_of_ne (fun h : ε = δ => hεC (h ▸ hδC)),
        (sum_unitCoords hδ).symm⟩
  have hall : ∀ α ∈ Ψ, α ∈ supportedRoots Ψ C ∨ α ∈ supportedRoots Ψ C' := by
    intro α hα
    obtain ⟨w, hw, δ, hδ, rfl⟩ := exists_smul_simpleRoot hΨ hα
    rcases hsupp δ hδ with h | h
    · exact Or.inl (smul_mem_of_forall_rootReflection hΨ (fun _ h => h.1)
        (fun ε hε α hα => rootReflection_smul_mem_supportedRoots hΨ horth hε hα) hw δ h)
    · exact Or.inr (smul_mem_of_forall_rootReflection hΨ (fun _ h => h.1)
        (fun ε hε α hα => rootReflection_smul_mem_supportedRoots hΨ horth' hε hα) hw δ h)
  have hSorth : ∀ α ∈ supportedRoots Ψ C, ∀ α' ∈ Ψ, α' ∉ supportedRoots Ψ C →
      iform α α' = 0 := by
    intro α ⟨_, c, hc, e⟩ α' hα' hα'S
    rcases hall α' hα' with h | ⟨_, c', hc', e'⟩
    · exact absurd h hα'S
    · rw [e, e']
      exact iform_eq_zero_of_supports horth hc fun δ hδ hδC => hc' δ hδ (not_not.2 hδC)
  have hβS : β ∈ supportedRoots Ψ C := ⟨simpleRoots_subset hβ, unitCoords β,
    fun ε _ hεC => unitCoords_of_ne (fun h : ε = β => hεC (h ▸ Relation.ReflTransGen.refl)),
    (sum_unitCoords hβ).symm⟩
  rcases hΨ.irreducible _ (fun α h => h.1) hSorth with h | h
  · rw [h] at hβS
    exact absurd hβS (Set.notMem_empty _)
  · have hγS : γ ∈ supportedRoots Ψ C := by
      rw [h]
      exact simpleRoots_subset hγ
    obtain ⟨_, c, hc, e⟩ := hγS
    by_contra hγC
    have hcoord := coords_unique hΨ (c := unitCoords γ) (c' := c)
      ((sum_unitCoords hγ).trans e) γ hγ
    rw [unitCoords_self, hc γ hγ hγC] at hcoord
    exact one_ne_zero hcoord

end CFSG.LieType.Chevalley
