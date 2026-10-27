module

public import CFSG.LieType.Chevalley.SignKernelSimpleWeyl

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint Matrix

variable {τ : Tag} {M : Type*} [CommGroup M] (χ : Multiplicative (Fin τ.rank → ℤ) →* M)

@[expose] def charStabilizer
    : Subgroup (WeylGroup τ) where
  carrier := {w | ∀ v : Fin τ.rank → ℤ, χ (Multiplicative.ofAdd (w • v)) =
    χ (Multiplicative.ofAdd v)}
  one_mem' v := by rw [one_smul]
  mul_mem' {w w'} hw hw' v := by rw [mul_smul, hw, hw']
  inv_mem' {w} hw v := by rw [← hw (w⁻¹ • v), smul_inv_smul]

@[expose] def kernelWeylGroup
    : Subgroup (WeylGroup τ) :=
  Subgroup.closure {r | ∃ (w : WeylGroup τ) (i : Fin τ.rank),
    w • (Pi.single i 1 : Fin τ.rank → ℤ) ∈ kernelRoots χ ∧ r = w * simple τ i * w⁻¹}

@[expose] def kernelPosStabilizer
    : Subgroup (WeylGroup τ) where
  carrier := {w | w ∈ charStabilizer χ ∧
    (w • ·) '' posRoots (kernelRoots χ) = posRoots (kernelRoots χ)}
  one_mem' := ⟨one_mem _, by simp⟩
  mul_mem' {w w'} hw hw' := ⟨mul_mem hw.1 hw'.1, by
    have e : ((w * w') • ·) '' posRoots (kernelRoots χ) =
        (w • ·) '' ((w' • ·) '' posRoots (kernelRoots χ)) := by
      rw [Set.image_image]
      simp only [mul_smul]
    rw [e, hw'.2, hw.2]⟩
  inv_mem' {w} hw := ⟨inv_mem hw.1, by
    conv_lhs => rw [← hw.2]
    rw [Set.image_image]
    simp⟩

variable {χ}

theorem mem_charStabilizer
    {w : WeylGroup τ} :
    w ∈ charStabilizer χ ↔ ∀ v : Fin τ.rank → ℤ, χ (Multiplicative.ofAdd (w • v)) =
      χ (Multiplicative.ofAdd v) :=
  Iff.rfl

theorem smul_mem_kernelRoots
    {w : WeylGroup τ} (hw : w ∈ charStabilizer χ)
    {α : Fin τ.rank → ℤ} (hα : α ∈ kernelRoots χ) : w • α ∈ kernelRoots χ :=
  ⟨IsRoot.smul hα.1 w, (hw α).trans hα.2⟩

theorem rootReflection_mem_charStabilizer
    {α : Fin τ.rank → ℤ} (hα : α ∈ kernelRoots χ) :
    rootReflection α ∈ charStabilizer χ := fun v => by
  rw [rootReflection_smul hα.1, sub_eq_add_neg, ofAdd_add, map_mul, ← neg_smul,
    chi_zsmul hα.2, mul_one]

theorem conj_simple_eq_rootReflection
    (w : WeylGroup τ) (i : Fin τ.rank) :
    w * simple τ i * w⁻¹ = rootReflection (w • (Pi.single i 1 : Fin τ.rank → ℤ)) :=
  (rootReflection_eq_conj rfl).symm

theorem kernelWeylGroup_le
    : kernelWeylGroup χ ≤ charStabilizer χ := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨w, i, hα, rfl⟩
  rw [conj_simple_eq_rootReflection]
  exact rootReflection_mem_charStabilizer hα

theorem rootReflection_mem_kernelWeylGroup
    {α : Fin τ.rank → ℤ} (hα : α ∈ kernelRoots χ) :
    rootReflection α ∈ kernelWeylGroup χ := by
  obtain ⟨w, j, rfl⟩ := isRoot_iff_exists_smul_single.1 hα.1
  rw [← conj_simple_eq_rootReflection]
  exact Subgroup.subset_closure ⟨w, j, hα, rfl⟩

theorem conj_mem_kernelWeylGroup
    {v : WeylGroup τ} (hv : v ∈ charStabilizer χ)
    {x : WeylGroup τ} (hx : x ∈ kernelWeylGroup χ) : v * x * v⁻¹ ∈ kernelWeylGroup χ := by
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨w, i, hα, rfl⟩ := hx
    rw [conj_simple_eq_rootReflection, ← rootReflection_smul_root _ hα.1]
    exact rootReflection_mem_kernelWeylGroup (smul_mem_kernelRoots hv hα)
  | one => simp
  | mul x y _ _ hx hy =>
    have e : v * (x * y) * v⁻¹ = (v * x * v⁻¹) * (v * y * v⁻¹) := by group
    rw [e]
    exact mul_mem hx hy
  | inv x _ hx =>
    have e : v * x⁻¹ * v⁻¹ = (v * x * v⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem hx

instance kernelWeylGroup_normal :
    ((kernelWeylGroup χ).subgroupOf (charStabilizer χ)).Normal := by
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer kernelWeylGroup_le).2 fun v hv => ?_
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨conj_mem_kernelWeylGroup hv, fun h => ?_⟩
  have := conj_mem_kernelWeylGroup (inv_mem hv) h
  rwa [show v⁻¹ * (v * x * v⁻¹) * v⁻¹⁻¹ = x by group] at this

theorem mem_simpleRoots_kernelRoots_iff
    {β : Fin τ.rank → ℤ} (hβ : β ∈ kernelRoots χ) :
    β ∈ simpleRoots (kernelRoots χ) ↔
      β ∈ simpleRoots (componentRoots χ (⟦⟨β, hβ⟩⟧ : KernelComponent χ)) := by
  set i : KernelComponent χ := ⟦⟨β, hβ⟩⟧
  have hβi : β ∈ componentRoots χ i := ⟨hβ, rfl⟩
  rw [mem_simpleRoots, mem_simpleRoots]
  constructor
  · rintro ⟨hr, ⟨_, hpos⟩, hns⟩
    exact ⟨hr, ⟨hβi, hpos⟩, fun γ hγ δ hδ => hns γ ⟨hγ.1.1, hγ.2⟩ δ ⟨hδ.1.1, hδ.2⟩⟩
  · rintro ⟨hr, ⟨_, hpos⟩, hns⟩
    refine ⟨hr, ⟨hβ, hpos⟩, fun γ hγ δ hδ e => ?_⟩
    have hγr := hγ.1.1
    have hδr := hδ.1.1
    have hmem : ∀ x (hx : x ∈ kernelRoots χ) y (hy : y ∈ componentRoots χ i), iform x y ≠ 0 →
        x ∈ componentRoots χ i := fun x hx y hy h =>
      ⟨hx, (mk_eq_of_iform_ne_zero (α := ⟨x, hx⟩) (β := ⟨y, hy.1⟩) h).trans hy.2⟩
    have hββ := iform_self_pos_of_isRoot hr
    have hγγ := iform_self_pos_of_isRoot hγr
    have hδδ := iform_self_pos_of_isRoot hδr
    have h1 : iform γ β = iform γ γ + iform γ δ := by rw [e, iform_add_right]
    have h2 : iform δ β = iform δ γ + iform δ δ := by rw [e, iform_add_right]
    have h3 : iform β β = iform γ β + iform δ β := by rw [e, iform_add_left]
    have hγi : γ ∈ componentRoots χ i := by
      by_cases hγβ : iform γ β = 0
      · have hδi := hmem δ hδ.1 β hβi (by omega)
        exact hmem γ hγ.1 δ hδi (by omega)
      · exact hmem γ hγ.1 β hβi hγβ
    have hδi : δ ∈ componentRoots χ i := by
      by_cases hδβ : iform δ β = 0
      · exact hmem δ hδ.1 γ hγi (by omega)
      · exact hmem δ hδ.1 β hβi hδβ
    exact hns γ ⟨hγi, hγ.2⟩ δ ⟨hδi, hδ.2⟩ e

theorem simpleRoots_kernelRoots_mem {β : Fin τ.rank → ℤ}
    (hβ : β ∈ simpleRoots (kernelRoots χ)) : β ∈ kernelRoots χ :=
  (mem_simpleRoots.1 hβ).2.1.1

theorem rootReflection_mem_posRoots_kernel
    {β : Fin τ.rank → ℤ}
    (hβ : β ∈ simpleRoots (kernelRoots χ)) {α : Fin τ.rank → ℤ}
    (hα : α ∈ posRoots (kernelRoots χ)) (hne : α ≠ β) :
    rootReflection β • α ∈ posRoots (kernelRoots χ) ∧ rootReflection β • α ≠ β := by
  have hβk := simpleRoots_kernelRoots_mem hβ
  have hβr := hβk.1
  set i : KernelComponent χ := ⟦⟨β, hβk⟩⟧
  have hβi := (mem_simpleRoots_kernelRoots_iff hβk).1 hβ
  by_cases hαi : (⟦⟨α, hα.1⟩⟧ : KernelComponent χ) = i
  · have hαc : α ∈ posRoots (componentRoots χ i) := ⟨⟨hα.1, hαi⟩, hα.2⟩
    obtain ⟨h1, h2⟩ := rootReflection_mem_posRoots (isRootComponent_componentRoots i) hβi hαc hne
    exact ⟨⟨h1.1.1, h1.2⟩, h2⟩
  · have h0 : iform β α = 0 := by
      rw [iform_comm]
      exact iform_eq_zero_of_mk_ne (α := ⟨α, hα.1⟩) (β := ⟨β, hβk⟩) hαi
    rw [rootReflection_smul_of_iform_eq_zero hβr h0]
    exact ⟨hα, hne⟩

theorem exists_nonneg_coords_kernel
    {α : Fin τ.rank → ℤ} (hα : α ∈ posRoots (kernelRoots χ)) :
    ∃ c : (Fin τ.rank → ℤ) → ℤ, (∀ β ∈ simpleRoots (kernelRoots χ), 0 ≤ c β) ∧
      α = ∑ β ∈ simpleRoots (kernelRoots χ), c β • β := by
  classical
  set i : KernelComponent χ := ⟦⟨α, hα.1⟩⟧
  obtain ⟨c, hc, e⟩ := exists_nonneg_coords (isRootComponent_componentRoots i)
    (α := α) ⟨⟨hα.1, rfl⟩, hα.2⟩
  have hsub : simpleRoots (componentRoots χ i) ⊆ simpleRoots (kernelRoots χ) := fun β hβ => by
    have hβk : β ∈ kernelRoots χ := (mem_simpleRoots.1 hβ).2.1.1.1
    have hcls : (⟦⟨β, hβk⟩⟧ : KernelComponent χ) = i := (mem_simpleRoots.1 hβ).2.1.1.2
    rw [mem_simpleRoots_kernelRoots_iff hβk, hcls]
    exact hβ
  refine ⟨fun β => if β ∈ simpleRoots (componentRoots χ i) then c β else 0, fun β _ => ?_, ?_⟩
  · dsimp only
    split_ifs with h
    · exact hc β h
    · exact le_rfl
  · rw [e, ← Finset.sum_subset hsub (fun β _ hβ => by simp [hβ])]
    exact Finset.sum_congr rfl fun β hβ => by simp [hβ]

theorem height_smul_pos_of_simpleRoots
    {w : WeylGroup τ}
    (hw : ∀ β ∈ simpleRoots (kernelRoots χ), 0 < height (w • β)) {α : Fin τ.rank → ℤ}
    (hα : α ∈ posRoots (kernelRoots χ)) : 0 < height (w • α) := by
  obtain ⟨c, hc, e⟩ := exists_nonneg_coords_kernel hα
  have hr : IsRoot τ (w • α) := IsRoot.smul hα.1.1 w
  have hnn : ∀ j, 0 ≤ (w • α) j := by
    intro j
    rw [e, Finset.smul_sum]
    simp only [smul_comm w (c _)]
    rw [Finset.sum_apply]
    refine Finset.sum_nonneg fun β hβ => ?_
    rw [Pi.smul_apply, smul_eq_mul]
    exact mul_nonneg (hc β hβ)
      ((IsRoot.height_pos_iff (IsRoot.smul (simpleRoots_isRoot hβ) w)).1 (hw β hβ) j)
  exact (IsRoot.height_pos_iff hr).2 hnn

open _root_.Classical in
variable (χ) in
@[expose] def negKernelRoots
    (w : WeylGroup τ) : Finset (Fin τ.rank → ℤ) :=
  (rootFinset τ).filter fun α => α ∈ posRoots (kernelRoots χ) ∧ height (w • α) < 0

theorem mem_negKernelRoots
    {w : WeylGroup τ} {α : Fin τ.rank → ℤ} :
    α ∈ negKernelRoots χ w ↔ α ∈ posRoots (kernelRoots χ) ∧ height (w • α) < 0 := by
  classical
  rw [negKernelRoots, Finset.mem_filter, mem_rootFinset]
  exact ⟨fun h => h.2, fun h => ⟨h.1.1.1, h⟩⟩

variable (χ) in
theorem exists_mul_forall_height_pos
    (w : WeylGroup τ) :
    ∃ u ∈ kernelWeylGroup χ, ∀ β ∈ simpleRoots (kernelRoots χ), 0 < height ((w * u) • β) := by
  classical
  suffices h : ∀ n : ℕ, ∀ w : WeylGroup τ, (negKernelRoots χ w).card = n →
      ∃ u ∈ kernelWeylGroup χ, ∀ β ∈ simpleRoots (kernelRoots χ), 0 < height ((w * u) • β) from
    h _ w rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro w hn
    by_cases hall : ∀ β ∈ simpleRoots (kernelRoots χ), 0 < height (w • β)
    · exact ⟨1, one_mem _, by simpa using hall⟩
    push Not at hall
    obtain ⟨β, hβ, hneg⟩ := hall
    have hβk := simpleRoots_kernelRoots_mem hβ
    have hβr := hβk.1
    have hβpos : β ∈ posRoots (kernelRoots χ) := (mem_simpleRoots.1 hβ).2.1
    have hneg' : height (w • β) < 0 := lt_of_le_of_ne hneg (IsRoot.smul hβr w).height_ne_zero
    set w' := w * rootReflection β with hw'
    have hsub : negKernelRoots χ w' ⊆ ((negKernelRoots χ w).erase β).image
        (rootReflection β • ·) := by
      intro α hα
      obtain ⟨hαpos, hαneg⟩ := mem_negKernelRoots.1 hα
      have hne : α ≠ β := by
        rintro rfl
        rw [hw', mul_smul, rootReflection_smul_self hβr, smul_neg, height_neg] at hαneg
        omega
      obtain ⟨h1, h2⟩ := rootReflection_mem_posRoots_kernel hβ hαpos hne
      refine Finset.mem_image.2 ⟨rootReflection β • α, Finset.mem_erase.2 ⟨h2,
        mem_negKernelRoots.2 ⟨h1, by rwa [hw', mul_smul] at hαneg⟩⟩, ?_⟩
      simp only [smul_smul, rootReflection_mul_self hβr, one_smul]
    have hβmem : β ∈ negKernelRoots χ w := mem_negKernelRoots.2 ⟨hβpos, hneg'⟩
    have hlt : (negKernelRoots χ w').card < n := by
      calc (negKernelRoots χ w').card ≤ (((negKernelRoots χ w).erase β).image
            (rootReflection β • ·)).card := Finset.card_le_card hsub
        _ ≤ ((negKernelRoots χ w).erase β).card := Finset.card_image_le
        _ < (negKernelRoots χ w).card := Finset.card_erase_lt_of_mem hβmem
        _ = n := hn
    obtain ⟨u, hu, hpos⟩ := ih _ hlt w' rfl
    refine ⟨rootReflection β * u, mul_mem (rootReflection_mem_kernelWeylGroup hβk) hu, ?_⟩
    simpa [hw', mul_assoc] using hpos

theorem kernelPosStabilizer_le
    : kernelPosStabilizer χ ≤ charStabilizer χ := fun _ h => h.1

theorem exists_mul_mem_kernelPosStabilizer
    {w : WeylGroup τ} (hw : w ∈ charStabilizer χ) :
    ∃ u ∈ kernelWeylGroup χ, w * u ∈ kernelPosStabilizer χ := by
  obtain ⟨u, hu, hpos⟩ := exists_mul_forall_height_pos χ w
  have hwu : w * u ∈ charStabilizer χ := mul_mem hw (kernelWeylGroup_le hu)
  refine ⟨u, hu, hwu, ?_⟩
  have hmaps : Set.MapsTo ((w * u) • ·) (posRoots (kernelRoots χ)) (posRoots (kernelRoots χ)) :=
    fun α hα => ⟨smul_mem_kernelRoots hwu hα.1, height_smul_pos_of_simpleRoots hpos hα⟩
  have hfin : (posRoots (kernelRoots χ)).Finite :=
    (finite_setOf_isRoot τ).subset fun α (hα : α ∈ posRoots (kernelRoots χ)) => hα.1.1
  have hinj : Set.InjOn ((w * u) • ·) (posRoots (kernelRoots χ)) :=
    fun a _ b _ h => smul_left_cancel _ h
  exact ((Set.Finite.injOn_iff_bijOn_of_mapsTo hfin hmaps).1 hinj).image_eq

theorem surjective_kernelPosStabilizer :
    Function.Surjective fun ω : kernelPosStabilizer χ =>
      (QuotientGroup.mk (⟨ω, kernelPosStabilizer_le ω.2⟩ : charStabilizer χ) :
        charStabilizer χ ⧸ (kernelWeylGroup χ).subgroupOf (charStabilizer χ)) := by
  intro q
  obtain ⟨⟨w, hw⟩, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨u, hu, hwu⟩ := exists_mul_mem_kernelPosStabilizer hw
  refine ⟨⟨w * u, hwu⟩, ?_⟩
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
  simpa using hu

theorem card_quotient_le_card_kernelPosStabilizer :
    Nat.card (charStabilizer χ ⧸ (kernelWeylGroup χ).subgroupOf (charStabilizer χ)) ≤
      Nat.card (kernelPosStabilizer χ) :=
  Nat.card_le_card_of_surjective _ surjective_kernelPosStabilizer

end CFSG.LieType.Chevalley
