module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.E8Roots
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.E8Weyl

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc

open CFSG.Blueprint.Chevalley


abbrev AdjMod (F : Type) [Field F] : Type := RootModule .E8 F

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

variable {F : Type} [Field F]


theorem xOp_one_rootVec_of_ne (i : Fin Tag.E8.rank) {α : Fin Tag.E8.rank → ℤ}
    (hα : IsRoot .E8 α) (h₁ : α ≠ Pi.single i 1) (h₂ : α ≠ -Pi.single i 1) :
    xOp .E8 F i 1 (rootVec .E8 F α) =
      rootVec .E8 F α + rootVec .E8 F (α + Pi.single i 1) := by
  rw [xOp_rootVec_of_ne_eq i 1 hα h₁ h₂]
  have hle := stringUp_add_stringDown_le_one hα i h₁ h₂
  have hint := (isRoot_add_smul_single_iff hα i h₁ h₂).2
  generalize stringUp .E8 i α = p at hle hint ⊢
  generalize stringDown .E8 i α = q at hle hint ⊢
  have h1 := hint 1
  rcases (by omega : p = 0 ∨ p = 1) with rfl | rfl
  · have : ¬ IsRoot .E8 (α + (1 : ℤ) • Pi.single i 1) := by
      rw [h1]; omega
    rw [one_smul] at this
    simp [rootVec_eq_zero this]
  · have hq : q = 0 := by omega
    subst hq
    simp [Finset.sum_range_succ]

@[expose] def Dop (F : Type) [Field F] (i : Fin Tag.E8.rank) : AdjMod F →ₗ[F] AdjMod F :=
  xOp .E8 F i 1 - 1

theorem Dop_apply (i : Fin Tag.E8.rank) (v : AdjMod F) : Dop F i v = xOp .E8 F i 1 v - v := rfl

theorem Dop_hVec (i j : Fin Tag.E8.rank) :
    Dop F i (hVec .E8 F j) = ((Tag.E8.cartan j i).natAbs : F) •
      rootVec .E8 F (Pi.single i 1) := by
  rw [Dop_apply, xOp_hVec_eq, mul_one]; abel

theorem Dop_rootVec_single (i : Fin Tag.E8.rank) :
    Dop F i (rootVec .E8 F (Pi.single i 1)) = 0 := by
  rw [Dop_apply, xOp_rootVec_single_eq, sub_self]

theorem Dop_rootVec_neg_single (i : Fin Tag.E8.rank) :
    Dop F i (rootVec .E8 F (-Pi.single i 1)) =
      hVec .E8 F i + rootVec .E8 F (Pi.single i 1) := by
  rw [Dop_apply, xOp_rootVec_neg_single_eq]
  simp only [one_smul, one_pow]
  abel

theorem Dop_rootVec_of_ne (i : Fin Tag.E8.rank) {α : Fin Tag.E8.rank → ℤ} (hα : IsRoot .E8 α)
    (h₁ : α ≠ Pi.single i 1) (h₂ : α ≠ -Pi.single i 1) :
    Dop F i (rootVec .E8 F α) = rootVec .E8 F (α + Pi.single i 1) := by
  rw [Dop_apply, xOp_one_rootVec_of_ne i hα h₁ h₂]; abel


open Classical in
@[expose] def coordR (v : AdjMod F) (β : Fin Tag.E8.rank → ℤ) : F :=
  if h : IsRoot .E8 β then v (Sum.inr ⟨β, h⟩) else 0

theorem coordR_add (v w : AdjMod F) (β : Fin Tag.E8.rank → ℤ) :
    coordR (v + w) β = coordR v β + coordR w β := by
  unfold coordR
  split_ifs <;> simp

theorem coordR_smul (c : F) (v : AdjMod F) (β : Fin Tag.E8.rank → ℤ) :
    coordR (c • v) β = c * coordR v β := by
  unfold coordR
  split_ifs <;> simp

theorem coordR_zero (β : Fin Tag.E8.rank → ℤ) : coordR (0 : AdjMod F) β = 0 := by
  unfold coordR
  split_ifs <;> simp

theorem coordR_hVec (j : Fin Tag.E8.rank) (β : Fin Tag.E8.rank → ℤ) :
    coordR (hVec .E8 F j) β = 0 := by
  unfold coordR hVec
  split_ifs <;> simp

theorem coordR_rootVec {α : Fin Tag.E8.rank → ℤ} (hα : IsRoot .E8 α) (β : Fin Tag.E8.rank → ℤ) :
    coordR (rootVec .E8 F α) β = if α = β then 1 else 0 := by
  classical
  unfold coordR
  rw [rootVec_eq_single hα]
  by_cases hβ : IsRoot .E8 β
  · rw [dif_pos hβ, Finsupp.single_apply]
    by_cases h : α = β
    · subst h; simp
    · rw [if_neg h, if_neg]
      intro h'
      exact h (congrArg Subtype.val (Sum.inr.inj h'))
  · rw [dif_neg hβ, if_neg]
    rintro rfl
    exact hβ hα

theorem coordR_rootVec_of_not {α : Fin Tag.E8.rank → ℤ} (hα : ¬ IsRoot .E8 α)
    (β : Fin Tag.E8.rank → ℤ) : coordR (rootVec .E8 F α) β = 0 := by
  rw [rootVec_eq_zero hα, coordR_zero]

theorem coordR_Dop (i : Fin Tag.E8.rank) (v : AdjMod F) {β : Fin Tag.E8.rank → ℤ}
    (hβ : IsRoot .E8 β) (hβe : β ≠ Pi.single i 1) :
    coordR (Dop F i v) β = coordR v (β - Pi.single i 1) := by
  induction v using Finsupp.induction_linear with
  | zero => simp [coordR_zero]
  | add v w hv hw => rw [map_add, coordR_add, coordR_add, hv, hw]
  | single b a =>
    rw [← Finsupp.smul_single_one b a, map_smul, coordR_smul, coordR_smul]
    congr 1
    rcases b with j | ⟨α, hα⟩
    · change coordR (Dop F i (hVec .E8 F j)) β = coordR (hVec .E8 F j) _
      rw [Dop_hVec, coordR_smul, coordR_rootVec (isRoot_single _ i), coordR_hVec, if_neg (Ne.symm hβe),
        mul_zero]
    · change coordR (Dop F i (Finsupp.single (Sum.inr ⟨α, hα⟩) 1)) β =
        coordR (Finsupp.single (Sum.inr ⟨α, hα⟩) 1) _
      rw [← rootVec_eq_single hα]
      by_cases h1 : α = Pi.single i 1
      · subst h1
        rw [Dop_rootVec_single, coordR_zero, coordR_rootVec (isRoot_single _ i), if_neg]
        intro h
        apply not_isRoot_two_single i
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
            have h' : -(Pi.single i 1 : Fin Tag.E8.rank → ℤ) + Pi.single i 1 = β - Pi.single i 1 + Pi.single i 1 := by
              rw [h]
            simpa using h'.symm
          exact this
      · rw [Dop_rootVec_of_ne i hα h1 h2, coordR_rootVec hα]
        by_cases hr : IsRoot .E8 (α + Pi.single i 1)
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


theorem adj_induction {P : AdjMod F → Prop} (h0 : P 0) (hadd : ∀ v w, P v → P w → P (v + w))
    (hsmul : ∀ (c : F) v, P v → P (c • v)) (hH : ∀ j, P (hVec .E8 F j))
    (hR : ∀ α, P (rootVec .E8 F α)) (v : AdjMod F) : P v := by
  induction v using Finsupp.induction_linear with
  | zero => exact h0
  | add v w hv hw => exact hadd v w hv hw
  | single b a =>
    rw [← Finsupp.smul_single_one b a]
    refine hsmul a _ ?_
    rcases b with j | ⟨α, hα⟩
    · exact hH j
    · rw [← rootVec_eq_single hα]; exact hR α

theorem rootVec_inl (α : Fin Tag.E8.rank → ℤ) (k : Fin Tag.E8.rank) :
    (rootVec .E8 F α : AdjMod F) (Sum.inl k) = 0 := by
  unfold rootVec
  split_ifs <;> simp

theorem hVec_inl (j k : Fin Tag.E8.rank) :
    (hVec .E8 F j : AdjMod F) (Sum.inl k) = if j = k then 1 else 0 := by
  unfold hVec
  simp [Finsupp.single_apply]

theorem Dop_inl (i : Fin Tag.E8.rank) (v : AdjMod F) (k : Fin Tag.E8.rank) :
    (Dop F i v) (Sum.inl k) = if k = i then coordR v (-Pi.single i 1) else 0 := by
  refine adj_induction (P := fun v => (Dop F i v) (Sum.inl k) =
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
    by_cases hα : IsRoot .E8 α
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
    · rw [Dop_rootVec_of_ne i hα h1 h2, rootVec_inl, coordR_rootVec hα, if_neg h2]
      split_ifs <;> simp

theorem coordR_Dop_single (i : Fin Tag.E8.rank) (v : AdjMod F) :
    coordR (Dop F i v) (Pi.single i 1) =
      coordR v (-Pi.single i 1) +
        ∑ j, ((Tag.E8.cartan j i).natAbs : F) * v (Sum.inl j) := by
  refine adj_induction (P := fun v => coordR (Dop F i v) (Pi.single i 1) =
    coordR v (-Pi.single i 1) +
        ∑ j, ((Tag.E8.cartan j i).natAbs : F) * v (Sum.inl j)) ?_ ?_ ?_ ?_ ?_ v
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
    by_cases hα : IsRoot .E8 α
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
    · rw [Dop_rootVec_of_ne i hα h1 h2, coordR_rootVec hα, if_neg h2]
      by_cases hr : IsRoot .E8 (α + Pi.single i 1)
      · rw [coordR_rootVec hr, if_neg]
        intro h
        apply hα.ne_zero
        have : α + Pi.single i 1 = 0 + Pi.single i 1 := by rw [zero_add]; exact h
        exact add_right_cancel this
      · rw [coordR_rootVec_of_not hr]


theorem cartan_symm (i j : Fin Tag.E8.rank) : Tag.E8.cartan i j = Tag.E8.cartan j i := by
  have h : ∀ i j : Fin Tag.E8.rank, Tag.E8.cartan i j - Tag.E8.cartan j i = 0 := by decide +kernel
  exact sub_eq_zero.1 (h i j)

theorem natAbs_cartan_cast [CharP F 2] (i j : Fin Tag.E8.rank) :
    (((Tag.E8.cartan i j).natAbs : ℕ) : F) = ((Tag.E8.cartan i j : ℤ) : F) := by
  have h : Tag.E8.cartan i j = 2 ∨ Tag.E8.cartan i j = -1 ∨ Tag.E8.cartan i j = 0 := by
    have h' : ∀ i j : Fin Tag.E8.rank,
        (Tag.E8.cartan i j - 2) * (Tag.E8.cartan i j + 1) * Tag.E8.cartan i j = 0 := by
      decide +kernel
    have := h' i j
    rcases mul_eq_zero.1 this with h1 | h1
    · rcases mul_eq_zero.1 h1 with h2 | h2
      · left; linarith
      · right; left; linarith
    · right; right; exact h1
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  rcases h with h | h | h <;> rw [h]
  · simp [h2]
  · simp [CharTwo.neg_eq]
  · simp

theorem omega_mul_cartan : ∀ l j : Fin Tag.E8.rank,
    ∑ c, e8Omega c l * Tag.E8.cartan c j = if l = j then 1 else 0 := by
  decide +kernel

theorem cartan_mod_two_inj [CharP F 2] : ∀ x : Fin Tag.E8.rank → F,
    (∀ i, ∑ j, ((Tag.E8.cartan j i).natAbs : F) * x j = 0) → x = 0 := by
  intro x hx
  funext l
  have h1 : ∀ c, ∑ j, ((Tag.E8.cartan c j : ℤ) : F) * x j = 0 := by
    intro c
    have := hx c
    rw [← this]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [natAbs_cartan_cast, cartan_symm]
  have hΩ : ∀ l j : Fin Tag.E8.rank,
      ∑ c, ((e8Omega c l : ℤ) : F) * ((Tag.E8.cartan c j : ℤ) : F) = if l = j then 1 else 0 := by
    intro l j
    have := congrArg (fun z : ℤ => (z : F)) (omega_mul_cartan l j)
    simp only [Int.cast_sum, Int.cast_mul] at this
    rw [this]
    split_ifs <;> simp
  calc x l = ∑ j, (if l = j then (1 : F) else 0) * x j := by simp
    _ = ∑ j, ∑ c, ((e8Omega c l : ℤ) : F) * ((Tag.E8.cartan c j : ℤ) : F) * x j := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← hΩ l j, Finset.sum_mul]
    _ = ∑ c, ((e8Omega c l : ℤ) : F) * ∑ j, ((Tag.E8.cartan c j : ℤ) : F) * x j := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
    _ = 0 := by simp [h1]
    _ = (0 : Fin Tag.E8.rank → F) l := rfl

theorem eq_smul_rootVec_theta_of_fixed [CharP F 2] (v : AdjMod F) (h : ∀ i, Dop F i v = 0) :
    v = coordR v e8Theta • rootVec .E8 F e8Theta := by
  have hneg : ∀ i, coordR v (-Pi.single i 1) = 0 := by
    intro i
    have := Dop_inl i v i
    rw [h i, if_pos rfl] at this
    exact this.symm
  have hcart : ∀ i, ∑ j, ((Tag.E8.cartan j i).natAbs : F) * v (Sum.inl j) = 0 := by
    intro i
    have := coordR_Dop_single i v
    rw [h i, coordR_zero, hneg i, zero_add] at this
    exact this.symm
  have hH : ∀ j, v (Sum.inl j) = 0 := fun j =>
    congrFun (cartan_mod_two_inj (fun j => v (Sum.inl j)) hcart) j
  ext b
  rcases b with j | ⟨α, hα⟩
  · rw [Finsupp.smul_apply, rootVec_inl, hH, smul_zero]
  · rw [Finsupp.smul_apply]
    by_cases hθ : α = e8Theta
    · subst hθ
      rw [rootVec_eq_single isRoot_theta, Finsupp.single_eq_same, smul_eq_mul, mul_one]
      simp [coordR, isRoot_theta]
    · rw [rootVec_eq_single isRoot_theta, Finsupp.single_apply, if_neg, smul_zero]
      · by_cases hj : ∃ j : Fin Tag.E8.rank, α = -Pi.single j 1
        · obtain ⟨j, rfl⟩ := hj
          have := hneg j
          simpa [coordR, hα] using this
        · push Not at hj
          obtain ⟨i, hne, hne', hr⟩ := exists_succ_of_ne_theta hα hθ hj
          have hβ : α + Pi.single i 1 ≠ Pi.single i 1 := by
            intro h0
            apply hα.ne_zero
            have : α + Pi.single i 1 = 0 + Pi.single i 1 := by rw [zero_add]; exact h0
            exact add_right_cancel this
          have := coordR_Dop i v hr hβ
          rw [h i, coordR_zero, add_sub_cancel_right] at this
          simpa [coordR, hα] using this.symm
      · intro h'
        exact hθ (congrArg Subtype.val (Sum.inr.inj h')).symm

end CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc
