module

public import CFSG.LieType.Chevalley.WeylInversion

public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley

variable {τ : Tag}

theorem height_smul_neg_of_forall_single
    {w : WeylGroup τ}
    (h : ∀ i, height (w • (Pi.single i 1 : Fin τ.rank → ℤ)) < 0) {α : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) (hpos : 0 < height α) : height (w • α) < 0 := by
  have hnn := (IsRoot.height_pos_iff hα).1 hpos
  have hw : ∀ i k, (w • (Pi.single i 1 : Fin τ.rank → ℤ)) k ≤ 0 := fun i =>
    (IsRoot.height_neg_iff (IsRoot.smul (isRoot_single τ i) w)).1 (h i)
  have hsum : α = ∑ j, α j • (Pi.single j 1 : Fin τ.rank → ℤ) := by
    ext k
    simp [Pi.single_apply]
  have hz : ∀ (c : ℤ) (x : Fin τ.rank → ℤ), w • (c • x) = c • (w • x) := fun c x => by
    rw [smul_def, smul_def, map_zsmul]
  refine (IsRoot.height_neg_iff (IsRoot.smul hα w)).2 fun k => ?_
  rw [hsum, Finset.smul_sum, Finset.sum_apply]
  refine Finset.sum_nonpos fun j _ => ?_
  rw [hz, Pi.smul_apply, smul_eq_mul]
  exact mul_nonpos_of_nonneg_of_nonpos (hnn j) (hw j k)

@[expose] def ReversesSigns
    (w : WeylGroup τ) : Prop :=
  ∀ α : Fin τ.rank → ℤ, IsRoot τ α → 0 < height α → height (w • α) < 0

theorem ReversesSigns.inv
    {w : WeylGroup τ} (hw : ReversesSigns w) : ReversesSigns w⁻¹ := by
  intro α hα hpos
  have hβ := IsRoot.smul hα w⁻¹
  rcases IsRoot.height_pos_or_neg hβ with h | h
  · have := hw _ hβ h
    rw [smul_inv_smul] at this
    omega
  · exact h

theorem ReversesSigns.height_smul_pos
    {w : WeylGroup τ} (hw : ReversesSigns w)
    {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (hneg : height β < 0) : 0 < height (w • β) := by
  have := hw (-β) (IsRoot.neg hβ) (by rw [height_neg]; omega)
  rw [smul_neg, height_neg] at this
  omega

theorem ReversesSigns.eq
    {u v : WeylGroup τ} (hu : ReversesSigns u) (hv : ReversesSigns v) :
    u = v := by
  have h1 : v⁻¹ * u = 1 := eq_one_of_forall_height_pos fun i => by
    rw [mul_smul]
    exact hv.inv.height_smul_pos (IsRoot.smul (isRoot_single τ i) u)
      (hu _ (isRoot_single τ i) (by rw [height_single]; exact one_pos))
  rw [← mul_left_cancel_iff (a := v⁻¹), h1, inv_mul_cancel]

theorem reversesSigns_of_forall_length_le
    {w : WeylGroup τ}
    (hw : ∀ u, (coxeterSystem τ).length u ≤ (coxeterSystem τ).length w) : ReversesSigns w := by
  refine fun α hα hpos => height_smul_neg_of_forall_single (fun i => ?_) hα hpos
  have hd : (coxeterSystem τ).IsRightDescent w i := by
    rw [isRightDescent_iff_length]
    rcases length_mul_simple_cases w i with h | h
    · have := hw (w * simple τ i)
      omega
    · exact h
  exact ((smul_single_mem_negRoots_iff w i).2 hd).2

theorem ReversesSigns.inversionSet_eq
    {w : WeylGroup τ} (hw : ReversesSigns w) :
    inversionSet w = {α | IsRoot τ α ∧ 0 < height α} := by
  ext α
  simp only [inversionSet, Set.mem_ofPred_eq]
  exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, IsRoot.smul h.1 w, hw α h.1 h.2⟩⟩

theorem ReversesSigns.inversionSet_mul
    {w₀ : WeylGroup τ} (h₀ : ReversesSigns w₀)
    (w : WeylGroup τ) :
    inversionSet (w * w₀) =
      (fun β => -(w₀⁻¹ • β)) '' ({α | IsRoot τ α ∧ 0 < height α} \ inversionSet w) := by
  ext α
  simp only [inversionSet, Set.mem_image, Set.mem_sdiff, Set.mem_ofPred_eq, mul_smul]
  constructor
  · rintro ⟨hα, hpos, -, hneg⟩
    have hβ : IsRoot τ (-(w₀ • α)) := IsRoot.neg (IsRoot.smul hα w₀)
    refine ⟨-(w₀ • α), ⟨⟨hβ, ?_⟩, fun ⟨_, _, _, h⟩ => ?_⟩, by rw [smul_neg, inv_smul_smul, neg_neg]⟩
    · rw [height_neg]
      have := h₀ α hα hpos
      omega
    · rw [smul_neg, height_neg] at h
      omega
  · rintro ⟨β, ⟨⟨hβ, hβpos⟩, hβI⟩, rfl⟩
    have hr : IsRoot τ (w₀⁻¹ • β) := IsRoot.smul hβ w₀⁻¹
    have hwβ : 0 < height (w • β) := by
      rcases IsRoot.height_pos_or_neg (IsRoot.smul hβ w) with h | h
      · exact h
      · exact absurd ⟨hβ, hβpos, IsRoot.smul hβ w, h⟩ hβI
    refine ⟨IsRoot.neg hr, ?_, ?_, ?_⟩
    · rw [height_neg]
      have := h₀.inv β hβ hβpos
      omega
    · rw [smul_neg, smul_inv_smul, smul_neg]
      exact IsRoot.neg (IsRoot.smul hβ w)
    · rw [smul_neg, smul_inv_smul, smul_neg, height_neg]
      omega

theorem weyl_longest_element (τ : Tag) :
    ∃ w₀ : WeylGroup τ,
      (∀ w, (coxeterSystem τ).length w ≤ (coxeterSystem τ).length w₀) ∧
      (∀ w, (∀ u, (coxeterSystem τ).length u ≤ (coxeterSystem τ).length w) → w = w₀) ∧
      (fun α => w₀ • α) '' {α | IsRoot τ α ∧ 0 < height α} =
        {α | IsRoot τ α ∧ height α < 0} ∧
      w₀ ^ 2 = 1 ∧
      (coxeterSystem τ).length w₀ = {α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α}.ncard ∧
      ∀ w, (coxeterSystem τ).length (w * w₀) =
        {α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α}.ncard - (coxeterSystem τ).length w := by
  obtain ⟨w₀, hmax⟩ := Finite.exists_max (coxeterSystem τ).length
  have h₀ := reversesSigns_of_forall_length_le hmax
  have hlen := (weyl_inversion_length τ).1
  refine ⟨w₀, hmax, fun w hw => (reversesSigns_of_forall_length_le hw).eq h₀, ?_, ?_, ?_, ?_⟩
  · ext β
    simp only [Set.mem_image, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨α, ⟨hα, hpos⟩, rfl⟩
      exact ⟨IsRoot.smul hα w₀, h₀ α hα hpos⟩
    · rintro ⟨hβ, hneg⟩
      exact ⟨w₀⁻¹ • β, ⟨IsRoot.smul hβ w₀⁻¹, h₀.inv.height_smul_pos hβ hneg⟩, smul_inv_smul w₀ β⟩
  · rw [pow_two]
    exact mul_eq_one_iff_eq_inv.2 (h₀.eq h₀.inv)
  · rw [hlen, h₀.inversionSet_eq]
  · intro w
    rw [hlen, hlen, h₀.inversionSet_mul, Set.ncard_image_of_injective _ (fun a b hab => by
      simpa using hab), Set.ncard_sdiff (show inversionSet w ⊆ {α | IsRoot τ α ∧ 0 < height α} from
        fun α hα => ⟨hα.1, hα.2.1⟩) (inversionSet_finite w)]

end CFSG.LieType.Chevalley
