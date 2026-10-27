module

public import CFSG.Blueprint.ChevalleyRootArtifact

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors

open CFSG.Blueprint.Chevalley


structure AdjHyp (τ : Tag) (θ : Fin τ.rank → ℤ) : Prop where
  two : ∀ i : Fin τ.rank, ¬ IsRoot τ (Pi.single i 1 + Pi.single i 1)
  string : ∀ {α : Fin τ.rank → ℤ}, IsRoot τ α → ∀ i : Fin τ.rank, α ≠ Pi.single i 1 →
    α ≠ -Pi.single i 1 → stringUp τ i α + stringDown τ i α ≤ 1
  succ : ∀ {α : Fin τ.rank → ℤ}, IsRoot τ α → α ≠ θ → (∀ j : Fin τ.rank, α ≠ -Pi.single j 1) →
    ∃ i : Fin τ.rank, α ≠ Pi.single i 1 ∧ α ≠ -Pi.single i 1 ∧ IsRoot τ (α + Pi.single i 1)

section Formulas

variable {τ : Tag} {R : Type*} [CommRing R]

theorem rootVec_eq_single {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) :
    rootVec τ R β = Finsupp.single (Sum.inr ⟨β, hβ⟩) 1 :=
  dite_eq_left hβ

theorem rootVec_eq_zero {β : Fin τ.rank → ℤ} (hβ : ¬IsRoot τ β) : rootVec τ R β = 0 :=
  dite_eq_right hβ

theorem xOp_hVec_eq (i j : Fin τ.rank) (c : R) :
    xOp τ R i c (hVec τ R j) =
      hVec τ R j + (((τ.cartan j i).natAbs : R) * c) • rootVec τ R (Pi.single i 1) := by
  change xOp τ R i c (Finsupp.single (Sum.inl j) 1) = _
  rw [xOp, Finsupp.linearCombination_single, one_smul]

theorem yOp_hVec_eq (i j : Fin τ.rank) (c : R) :
    yOp τ R i c (hVec τ R j) =
      hVec τ R j + (((τ.cartan j i).natAbs : R) * c) • rootVec τ R (-Pi.single i 1) := by
  change yOp τ R i c (Finsupp.single (Sum.inl j) 1) = _
  rw [yOp, Finsupp.linearCombination_single, one_smul]

theorem xOp_rootVec_single_eq (i : Fin τ.rank) (c : R) :
    xOp τ R i c (rootVec τ R (Pi.single i 1)) = rootVec τ R (Pi.single i 1) := by
  rw [rootVec_eq_single (isRoot_single τ i), xOp, Finsupp.linearCombination_single, one_smul]
  exact ite_eq_left rfl

theorem xOp_rootVec_neg_single_eq (i : Fin τ.rank) (c : R) :
    xOp τ R i c (rootVec τ R (-Pi.single i 1)) =
      rootVec τ R (-Pi.single i 1) + c • hVec τ R i + c ^ 2 • rootVec τ R (Pi.single i 1) := by
  rw [rootVec_eq_single (isRoot_neg_single τ i), xOp, Finsupp.linearCombination_single,
    one_smul]
  exact (ite_eq_right (single_ne_neg_single i).symm).trans (ite_eq_left rfl)

theorem xOp_rootVec_of_ne_eq (i : Fin τ.rank) (c : R) {α : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) (h₁ : α ≠ Pi.single i 1) (h₂ : α ≠ -Pi.single i 1) :
    xOp τ R i c (rootVec τ R α) =
      ∑ k ∈ Finset.range (stringUp τ i α + 1),
        (((stringDown τ i α + k).choose k : R) * c ^ k) •
          rootVec τ R (α + (k : ℤ) • Pi.single i 1) := by
  rw [rootVec_eq_single hα, xOp, Finsupp.linearCombination_single, one_smul]
  exact (ite_eq_right h₁).trans (ite_eq_right h₂)

theorem yOp_rootVec_single_eq (i : Fin τ.rank) (c : R) :
    yOp τ R i c (rootVec τ R (Pi.single i 1)) =
      rootVec τ R (Pi.single i 1) + c • hVec τ R i + c ^ 2 • rootVec τ R (-Pi.single i 1) := by
  rw [rootVec_eq_single (isRoot_single τ i), yOp, Finsupp.linearCombination_single, one_smul]
  exact (ite_eq_right (single_ne_neg_single i)).trans (ite_eq_left rfl)

end Formulas

variable {τ : Tag} {F : Type} [Field F] {θ : Fin τ.rank → ℤ}


theorem xOp_one_rootVec_of_ne (H : AdjHyp τ θ) (i : Fin τ.rank) {α : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) (h₁ : α ≠ Pi.single i 1) (h₂ : α ≠ -Pi.single i 1) :
    xOp τ F i 1 (rootVec τ F α) =
      rootVec τ F α + rootVec τ F (α + Pi.single i 1) := by
  rw [xOp_rootVec_of_ne_eq i 1 hα h₁ h₂]
  have hle := H.string hα i h₁ h₂
  have hint := (isRoot_add_smul_single_iff hα i h₁ h₂).2
  generalize stringUp τ i α = p at hle hint ⊢
  generalize stringDown τ i α = q at hle hint ⊢
  have h1 := hint 1
  rcases (by omega : p = 0 ∨ p = 1) with rfl | rfl
  · have : ¬ IsRoot τ (α + (1 : ℤ) • Pi.single i 1) := by
      rw [h1]; omega
    rw [one_smul] at this
    simp [rootVec_eq_zero this]
  · have hq : q = 0 := by omega
    subst hq
    simp [Finset.sum_range_succ]

theorem xOp_rootVec_of_up_zero (H : AdjHyp τ θ) (i : Fin τ.rank) (c : F)
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) (h₁ : α ≠ Pi.single i 1) (h₂ : α ≠ -Pi.single i 1)
    (hr : ¬ IsRoot τ (α + Pi.single i 1)) : xOp τ F i c (rootVec τ F α) = rootVec τ F α := by
  rw [xOp_rootVec_of_ne_eq i c hα h₁ h₂]
  have hint := (isRoot_add_smul_single_iff hα i h₁ h₂).2
  have h1 := hint 1
  rw [one_smul] at h1
  have hup : stringUp τ i α = 0 := by
    by_contra hne
    exact hr (h1.2 ⟨by omega, by omega⟩)
  rw [hup]
  simp

theorem xOp_rootVec_of_up_one (H : AdjHyp τ θ) (i : Fin τ.rank) (c : F)
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) (h₁ : α ≠ Pi.single i 1) (h₂ : α ≠ -Pi.single i 1)
    (hr : IsRoot τ (α + Pi.single i 1)) :
    xOp τ F i c (rootVec τ F α) = rootVec τ F α + c • rootVec τ F (α + Pi.single i 1) := by
  rw [xOp_rootVec_of_ne_eq i c hα h₁ h₂]
  have hle := H.string hα i h₁ h₂
  have hint := (isRoot_add_smul_single_iff hα i h₁ h₂).2
  have h1 := hint 1
  rw [one_smul] at h1
  have hup : 1 ≤ stringUp τ i α := by
    have := (h1.1 hr).2
    exact_mod_cast this
  have hup1 : stringUp τ i α = 1 := by omega
  have hdn : stringDown τ i α = 0 := by omega
  rw [hup1, hdn]
  simp [Finset.sum_range_succ]

@[expose] def Dop (τ : Tag) (F : Type) [Field F] (i : Fin τ.rank) : RootModule τ F →ₗ[F] RootModule τ F :=
  xOp τ F i 1 - 1

theorem Dop_apply (i : Fin τ.rank) (v : RootModule τ F) : Dop τ F i v = xOp τ F i 1 v - v := rfl

theorem Dop_hVec (i j : Fin τ.rank) :
    Dop τ F i (hVec τ F j) = ((τ.cartan j i).natAbs : F) •
      rootVec τ F (Pi.single i 1) := by
  rw [Dop_apply, xOp_hVec_eq, mul_one]; abel

theorem Dop_rootVec_single (i : Fin τ.rank) :
    Dop τ F i (rootVec τ F (Pi.single i 1)) = 0 := by
  rw [Dop_apply, xOp_rootVec_single_eq, sub_self]

theorem Dop_rootVec_neg_single (i : Fin τ.rank) :
    Dop τ F i (rootVec τ F (-Pi.single i 1)) =
      hVec τ F i + rootVec τ F (Pi.single i 1) := by
  rw [Dop_apply, xOp_rootVec_neg_single_eq]
  simp only [one_smul, one_pow]
  abel

theorem Dop_rootVec_of_ne (H : AdjHyp τ θ) (i : Fin τ.rank) {α : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (h₁ : α ≠ Pi.single i 1) (h₂ : α ≠ -Pi.single i 1) :
    Dop τ F i (rootVec τ F α) = rootVec τ F (α + Pi.single i 1) := by
  rw [Dop_apply, xOp_one_rootVec_of_ne H i hα h₁ h₂]; abel


open Classical in
@[expose] def coordR (v : RootModule τ F) (β : Fin τ.rank → ℤ) : F :=
  if h : IsRoot τ β then v (Sum.inr ⟨β, h⟩) else 0

theorem coordR_add (v w : RootModule τ F) (β : Fin τ.rank → ℤ) :
    coordR (v + w) β = coordR v β + coordR w β := by
  unfold coordR
  split_ifs <;> simp

theorem coordR_smul (c : F) (v : RootModule τ F) (β : Fin τ.rank → ℤ) :
    coordR (c • v) β = c * coordR v β := by
  unfold coordR
  split_ifs <;> simp

theorem coordR_zero (β : Fin τ.rank → ℤ) : coordR (0 : RootModule τ F) β = 0 := by
  unfold coordR
  split_ifs <;> simp

theorem coordR_hVec (j : Fin τ.rank) (β : Fin τ.rank → ℤ) :
    coordR (hVec τ F j) β = 0 := by
  unfold coordR hVec
  split_ifs <;> simp

theorem coordR_rootVec {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) (β : Fin τ.rank → ℤ) :
    coordR (rootVec τ F α) β = if α = β then 1 else 0 := by
  classical
  unfold coordR
  rw [rootVec_eq_single hα]
  by_cases hβ : IsRoot τ β
  · rw [dif_pos hβ, Finsupp.single_apply]
    by_cases h : α = β
    · subst h; simp
    · rw [if_neg h, if_neg]
      intro h'
      exact h (congrArg Subtype.val (Sum.inr.inj h'))
  · rw [dif_neg hβ, if_neg]
    rintro rfl
    exact hβ hα

theorem coordR_rootVec_of_not {α : Fin τ.rank → ℤ} (hα : ¬ IsRoot τ α)
    (β : Fin τ.rank → ℤ) : coordR (rootVec τ F α) β = 0 := by
  rw [rootVec_eq_zero hα, coordR_zero]

theorem coordR_Dop (H : AdjHyp τ θ) (i : Fin τ.rank) (v : RootModule τ F) {β : Fin τ.rank → ℤ}
    (hβ : IsRoot τ β) (hβe : β ≠ Pi.single i 1) :
    coordR (Dop τ F i v) β = coordR v (β - Pi.single i 1) := by
  induction v using Finsupp.induction_linear with
  | zero => simp [coordR_zero]
  | add v w hv hw => rw [map_add, coordR_add, coordR_add, hv, hw]
  | single b a =>
    rw [← Finsupp.smul_single_one b a, map_smul, coordR_smul, coordR_smul]
    congr 1
    rcases b with j | ⟨α, hα⟩
    · change coordR (Dop τ F i (hVec τ F j)) β = coordR (hVec τ F j) _
      rw [Dop_hVec, coordR_smul, coordR_rootVec (isRoot_single _ i), coordR_hVec, if_neg (Ne.symm hβe),
        mul_zero]
    · change coordR (Dop τ F i (Finsupp.single (Sum.inr ⟨α, hα⟩) 1)) β =
        coordR (Finsupp.single (Sum.inr ⟨α, hα⟩) 1) _
      rw [← rootVec_eq_single hα]
      by_cases h1 : α = Pi.single i 1
      · subst h1
        rw [Dop_rootVec_single, coordR_zero, coordR_rootVec (isRoot_single _ i), if_neg]
        intro h
        apply H.two i
        have : β = Pi.single i 1 + Pi.single i 1 := eq_add_of_sub_eq h.symm
        exact this ▸ hβ
      by_cases h2 : α = -Pi.single i 1
      · subst h2
        rw [Dop_rootVec_neg_single, coordR_add, coordR_hVec, coordR_rootVec (isRoot_single _ i),
          coordR_rootVec (isRoot_neg_single _ i), if_neg (Ne.symm hβe), if_neg]
        · simp
        · intro h
          apply hβ.ne_zero
          have : β = 0 := by
            have h' : -(Pi.single i 1 : Fin τ.rank → ℤ) + Pi.single i 1 = β - Pi.single i 1 + Pi.single i 1 := by
              rw [h]
            simpa using h'.symm
          exact this
      · rw [Dop_rootVec_of_ne H i hα h1 h2, coordR_rootVec hα]
        by_cases hr : IsRoot τ (α + Pi.single i 1)
        · rw [coordR_rootVec hr]
          by_cases h : α + Pi.single i 1 = β
          · rw [if_pos h, if_pos]
            rw [← h]; abel
          · rw [if_neg h, if_neg]
            intro h'
            apply h
            rw [h']; abel
        · rw [coordR_rootVec_of_not hr]
          by_cases h : α = β - Pi.single i 1
          · exfalso; apply hr
            have : α + Pi.single i 1 = β := by rw [h]; abel
            rw [this]; exact hβ
          · rw [if_neg h]


theorem adj_induction {P : RootModule τ F → Prop} (h0 : P 0) (hadd : ∀ v w, P v → P w → P (v + w))
    (hsmul : ∀ (c : F) v, P v → P (c • v)) (hH : ∀ j, P (hVec τ F j))
    (hR : ∀ α, P (rootVec τ F α)) (v : RootModule τ F) : P v := by
  induction v using Finsupp.induction_linear with
  | zero => exact h0
  | add v w hv hw => exact hadd v w hv hw
  | single b a =>
    rw [← Finsupp.smul_single_one b a]
    refine hsmul a _ ?_
    rcases b with j | ⟨α, hα⟩
    · exact hH j
    · rw [← rootVec_eq_single hα]; exact hR α

theorem rootVec_inl (α : Fin τ.rank → ℤ) (k : Fin τ.rank) :
    (rootVec τ F α : RootModule τ F) (Sum.inl k) = 0 := by
  unfold rootVec
  split_ifs <;> simp

theorem hVec_inl (j k : Fin τ.rank) :
    (hVec τ F j : RootModule τ F) (Sum.inl k) = if j = k then 1 else 0 := by
  unfold hVec
  simp [Finsupp.single_apply]

theorem Dop_inl (H : AdjHyp τ θ) (i : Fin τ.rank) (v : RootModule τ F) (k : Fin τ.rank) :
    (Dop τ F i v) (Sum.inl k) = if k = i then coordR v (-Pi.single i 1) else 0 := by
  refine adj_induction (P := fun v => (Dop τ F i v) (Sum.inl k) =
    if k = i then coordR v (-Pi.single i 1) else 0) ?_ ?_ ?_ ?_ ?_ v
  · simp [coordR_zero]
  · intro v w hv hw
    simp only [map_add, Finsupp.add_apply, hv, hw, coordR_add]
    split_ifs <;> simp
  · intro c v hv
    simp only [map_smul, Finsupp.smul_apply, hv, coordR_smul, smul_eq_mul]
    split_ifs <;> simp
  · intro j
    rw [Dop_hVec, Finsupp.smul_apply, rootVec_inl, coordR_hVec]
    split_ifs <;> simp
  · intro α
    by_cases hα : IsRoot τ α
    swap
    · rw [rootVec_eq_zero hα]; simp [coordR_zero]
    by_cases h1 : α = Pi.single i 1
    · subst h1
      rw [Dop_rootVec_single, coordR_rootVec (isRoot_single _ i),
        if_neg (single_ne_neg_single i)]
      split_ifs <;> simp
    by_cases h2 : α = -Pi.single i 1
    · subst h2
      rw [Dop_rootVec_neg_single, Finsupp.add_apply, rootVec_inl, hVec_inl,
        coordR_rootVec (isRoot_neg_single _ i), if_pos rfl]
      by_cases hk : k = i
      · subst hk; simp
      · simp [Ne.symm hk, hk]
    · rw [Dop_rootVec_of_ne H i hα h1 h2, rootVec_inl, coordR_rootVec hα, if_neg h2]
      split_ifs <;> simp

theorem coordR_Dop_single (H : AdjHyp τ θ) (i : Fin τ.rank) (v : RootModule τ F) :
    coordR (Dop τ F i v) (Pi.single i 1) =
      coordR v (-Pi.single i 1) +
        ∑ j, ((τ.cartan j i).natAbs : F) * v (Sum.inl j) := by
  refine adj_induction (P := fun v => coordR (Dop τ F i v) (Pi.single i 1) =
    coordR v (-Pi.single i 1) +
        ∑ j, ((τ.cartan j i).natAbs : F) * v (Sum.inl j)) ?_ ?_ ?_ ?_ ?_ v
  · simp [coordR_zero]
  · intro v w hv hw
    simp only [map_add, coordR_add, hv, hw, Finsupp.add_apply, mul_add, Finset.sum_add_distrib]
    abel
  · intro c v hv
    simp only [map_smul, coordR_smul, hv, Finsupp.smul_apply, smul_eq_mul, mul_add,
      Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => by ring
  · intro j
    rw [Dop_hVec, coordR_smul, coordR_rootVec (isRoot_single _ i), if_pos rfl, coordR_hVec]
    simp only [hVec_inl, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
      if_true, zero_add]
  · intro α
    by_cases hα : IsRoot τ α
    swap
    · rw [rootVec_eq_zero hα]; simp [coordR_zero]
    simp only [rootVec_inl, mul_zero, Finset.sum_const_zero, add_zero]
    by_cases h1 : α = Pi.single i 1
    · subst h1
      rw [Dop_rootVec_single, coordR_zero, coordR_rootVec (isRoot_single _ i),
        if_neg (single_ne_neg_single i)]
    by_cases h2 : α = -Pi.single i 1
    · subst h2
      rw [Dop_rootVec_neg_single, coordR_add, coordR_hVec, coordR_rootVec (isRoot_single _ i),
        coordR_rootVec (isRoot_neg_single _ i), if_pos rfl, if_pos rfl, zero_add]
    · rw [Dop_rootVec_of_ne H i hα h1 h2, coordR_rootVec hα, if_neg h2]
      by_cases hr : IsRoot τ (α + Pi.single i 1)
      · rw [coordR_rootVec hr, if_neg]
        intro h
        apply hα.ne_zero
        have : α + Pi.single i 1 = 0 + Pi.single i 1 := by rw [zero_add]; exact h
        exact add_right_cancel this
      · rw [coordR_rootVec_of_not hr]


section Kernel

variable (H : AdjHyp τ θ)

include H in
theorem coordR_eq_zero_of_Dop {v : RootModule τ F} (hv : ∀ i, Dop τ F i v = 0)
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hαθ : α ≠ θ) : coordR v α = 0 := by
  by_cases hneg : ∃ j : Fin τ.rank, α = -Pi.single j 1
  · obtain ⟨j, rfl⟩ := hneg
    have := Dop_inl H j v j
    rw [hv j, if_pos rfl] at this
    exact this.symm
  · push Not at hneg
    obtain ⟨i, h1, h2, hr⟩ := H.succ hα hαθ hneg
    have hne : α + Pi.single i 1 ≠ Pi.single i 1 := fun h => hα.ne_zero (by
      have : α + Pi.single i 1 = 0 + Pi.single i 1 := by rw [zero_add]; exact h
      exact add_right_cancel this)
    have := coordR_Dop H i v hr hne
    rw [hv i, coordR_zero, add_sub_cancel_right] at this
    exact this.symm

include H in
theorem cartan_cond_of_Dop {v : RootModule τ F} (hv : ∀ i, Dop τ F i v = 0) (i : Fin τ.rank) :
    ∑ j, ((τ.cartan j i).natAbs : F) * v (Sum.inl j) = 0 := by
  have h2 : coordR v (-Pi.single i 1) = 0 := by
    have := Dop_inl H i v i
    rw [hv i, if_pos rfl] at this
    exact this.symm
  have h1 := coordR_Dop_single H i v
  rw [hv i, coordR_zero, h2, zero_add] at h1
  exact h1.symm

include H in
theorem eq_decomp_of_Dop (hθ : IsRoot τ θ) {v : RootModule τ F} (hv : ∀ i, Dop τ F i v = 0) :
    v = coordR v θ • rootVec τ F θ + ∑ j, v (Sum.inl j) • hVec τ F j := by
  ext b
  rcases b with k | ⟨α, hα⟩
  · simp only [Finsupp.add_apply, Finsupp.smul_apply, rootVec_inl, smul_zero, zero_add,
      smul_eq_mul]
    rw [Finsupp.coe_finsetSum, Finset.sum_apply]
    simp [hVec_inl]
  · simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
    rw [Finsupp.coe_finsetSum, Finset.sum_apply]
    have hh : ∀ j, (hVec τ F j : RootModule τ F) (Sum.inr ⟨α, hα⟩) = 0 := fun j => by
      unfold hVec
      simp [Finsupp.single_apply]
    simp only [Finsupp.smul_apply, hh, smul_zero, Finset.sum_const_zero, add_zero]
    rw [rootVec_eq_single hθ, Finsupp.single_apply]
    by_cases h : α = θ
    · subst h
      simp [coordR, hα]
    · have : coordR v α = 0 := coordR_eq_zero_of_Dop H hv hα h
      have h' : ¬ (Sum.inr ⟨θ, hθ⟩ : Label τ) = Sum.inr ⟨α, hα⟩ := fun e =>
        h (congrArg Subtype.val (Sum.inr.inj e)).symm
      rw [if_neg h', mul_zero]
      simpa [coordR, hα] using this

end Kernel

theorem AdjHyp.of_checks {τ : Tag} {θ : Fin τ.rank → ℤ}
    (htwo : ∀ i : Fin τ.rank,
      List.ofFn (Pi.single i 1 + Pi.single i 1 : Fin τ.rank → ℤ) ∉ τ.artifactRoots)
    (hstr : ∀ k < τ.rootCount, ∀ i : Fin τ.rank,
      (Tag.rootCertificate τ).root k = Pi.single i 1 ∨
        (Tag.rootCertificate τ).root k = -Pi.single i 1 ∨
          (Tag.stringData τ).up k i + (Tag.stringData τ).down k i ≤ 1)
    (hsucc : ∀ k < τ.rootCount, (Tag.rootCertificate τ).root k = θ ∨
      (∃ j : Fin τ.rank, (Tag.rootCertificate τ).root k = -Pi.single j 1) ∨
        ∃ i : Fin τ.rank, (Tag.rootCertificate τ).root k ≠ Pi.single i 1 ∧
          (Tag.rootCertificate τ).root k ≠ -Pi.single i 1 ∧ 1 ≤ (Tag.stringData τ).up k i) :
    AdjHyp τ θ where
  two i h := htwo i (isRoot_iff_mem_artifactRoots.1 h)
  string := by
    intro α hα i hne hne'
    obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check τ) hα
    have hk' : k < τ.rootCount := by
      have := Tag.rootCertificate_length τ
      omega
    rcases hstr k hk' i with h | h | h
    · exact absurd h hne
    · exact absurd h hne'
    obtain ⟨-, h1⟩ := StringData.isRoot_root_add_iff (Tag.rootCertificate_check τ)
      (Tag.stringData_check τ) hk i hne hne'
    obtain ⟨-, h2⟩ := isRoot_add_smul_single_iff hα i hne hne'
    have key : ∀ m : ℤ, (-((Tag.stringData τ).down k i : ℤ) ≤ m ∧
        m ≤ (Tag.stringData τ).up k i) ↔
        (-(stringDown τ i ((Tag.rootCertificate τ).root k) : ℤ) ≤ m ∧
          m ≤ stringUp τ i ((Tag.rootCertificate τ).root k)) := fun m => (h1 m).symm.trans (h2 m)
    have a1 := (key ((Tag.stringData τ).up k i : ℤ)).1 ⟨by omega, le_rfl⟩
    have a2 := (key (stringUp τ i ((Tag.rootCertificate τ).root k) : ℤ)).2 ⟨by omega, le_rfl⟩
    have b1 := (key (-((Tag.stringData τ).down k i : ℤ))).1 ⟨le_rfl, by omega⟩
    have b2 := (key (-(stringDown τ i ((Tag.rootCertificate τ).root k) : ℤ))).2
      ⟨le_rfl, by omega⟩
    omega
  succ := by
    intro α hα hθ hneg
    obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check τ) hα
    have hk' : k < τ.rootCount := by
      have := Tag.rootCertificate_length τ
      omega
    rcases hsucc k hk' with h | ⟨j, h⟩ | ⟨i, hne, hne', hup⟩
    · exact absurd h hθ
    · exact absurd h (hneg j)
    refine ⟨i, hne, hne', ?_⟩
    obtain ⟨-, h1⟩ := StringData.isRoot_root_add_iff (Tag.rootCertificate_check τ)
      (Tag.stringData_check τ) hk i hne hne'
    have := (h1 1).2 ⟨by omega, by omega⟩
    simpa using this

end CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors
