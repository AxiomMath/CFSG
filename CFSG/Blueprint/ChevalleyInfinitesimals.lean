module

public import CFSG.Blueprint.ChevalleyStrings
public import Certificates.Certificate113
public import Certificates.Certificate114

public noncomputable section

namespace CFSG.Blueprint.Chevalley

open scoped Nat

variable (τ : Tag) (R : Type*) [CommRing R]

open Classical in
@[expose] def infE (i : Fin τ.rank) : Module.End R (RootModule τ R) :=
  Finsupp.linearCombination R fun b =>
    match b with
    | .inl j => ((τ.cartan j i).natAbs : R) • rootVec τ R (Pi.single i 1)
    | .inr α =>
      if α.1 = Pi.single i 1 then 0
      else if α.1 = -Pi.single i 1 then hVec τ R i
      else ((stringDown τ i α.1 + 1 : ℕ) : R) • rootVec τ R (α.1 + Pi.single i 1)

open Classical in
@[expose] def infF (i : Fin τ.rank) : Module.End R (RootModule τ R) :=
  Finsupp.linearCombination R fun b =>
    match b with
    | .inl j => ((τ.cartan j i).natAbs : R) • rootVec τ R (-Pi.single i 1)
    | .inr α =>
      if α.1 = -Pi.single i 1 then 0
      else if α.1 = Pi.single i 1 then hVec τ R i
      else ((stringUp τ i α.1 + 1 : ℕ) : R) • rootVec τ R (α.1 - Pi.single i 1)

open Classical in
@[expose] def xCoeff (i : Fin τ.rank) (k : ℕ) : Module.End R (RootModule τ R) :=
  Finsupp.linearCombination R fun b =>
    match b with
    | .inl j =>
      if k = 0 then hVec τ R j
      else if k = 1 then ((τ.cartan j i).natAbs : R) • rootVec τ R (Pi.single i 1) else 0
    | .inr α =>
      if α.1 = Pi.single i 1 then (if k = 0 then Finsupp.single (Sum.inr α) 1 else 0)
      else if α.1 = -Pi.single i 1 then
        (if k = 0 then Finsupp.single (Sum.inr α) 1
        else if k = 1 then hVec τ R i
        else if k = 2 then rootVec τ R (Pi.single i 1) else 0)
      else ((stringDown τ i α.1 + k).choose k : R) • rootVec τ R (α.1 + (k : ℤ) • Pi.single i 1)

open Classical in
@[expose] def yCoeff (i : Fin τ.rank) (k : ℕ) : Module.End R (RootModule τ R) :=
  Finsupp.linearCombination R fun b =>
    match b with
    | .inl j =>
      if k = 0 then hVec τ R j
      else if k = 1 then ((τ.cartan j i).natAbs : R) • rootVec τ R (-Pi.single i 1) else 0
    | .inr α =>
      if α.1 = -Pi.single i 1 then (if k = 0 then Finsupp.single (Sum.inr α) 1 else 0)
      else if α.1 = Pi.single i 1 then
        (if k = 0 then Finsupp.single (Sum.inr α) 1
        else if k = 1 then hVec τ R i
        else if k = 2 then rootVec τ R (-Pi.single i 1) else 0)
      else ((stringUp τ i α.1 + k).choose k : R) • rootVec τ R (α.1 - (k : ℤ) • Pi.single i 1)

variable {τ R}

private theorem rootVec_of_isRoot {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) :
    rootVec τ R β = Finsupp.single (Sum.inr ⟨β, hβ⟩) 1 :=
  dite_eq_left hβ

private theorem rootVec_of_not_isRoot {β : Fin τ.rank → ℤ} (hβ : ¬IsRoot τ β) :
    rootVec τ R β = 0 :=
  dite_eq_right hβ

private theorem rootVec_add_eq_zero {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) {i : Fin τ.rank}
    (h₁ : α ≠ Pi.single i 1) (h₂ : α ≠ -Pi.single i 1) {k : ℕ} (hk : stringUp τ i α < k) :
    rootVec τ R (α + (k : ℤ) • Pi.single i 1) = 0 := by
  obtain ⟨h, -, -⟩ := root_string_transport hα i h₁ h₂
  exact rootVec_of_not_isRoot fun hr => by have := (h k).1 hr; omega

private theorem rootVec_sub_eq_zero {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) {i : Fin τ.rank}
    (h₁ : α ≠ Pi.single i 1) (h₂ : α ≠ -Pi.single i 1) {k : ℕ} (hk : stringDown τ i α < k) :
    rootVec τ R (α - (k : ℤ) • Pi.single i 1) = 0 := by
  obtain ⟨h, -, -⟩ := root_string_transport hα i h₁ h₂
  refine rootVec_of_not_isRoot fun hr => ?_
  have := (h (-(k : ℤ))).1 (by rwa [neg_smul, ← sub_eq_add_neg])
  omega

private theorem stringUp_le_three {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) {i : Fin τ.rank}
    (h₁ : α ≠ Pi.single i 1) (h₂ : α ≠ -Pi.single i 1) :
    stringUp τ i α ≤ 3 ∧ stringDown τ i α ≤ 3 := by
  obtain ⟨-, h, -⟩ := root_string_transport hα i h₁ h₂
  omega

private theorem up_transport {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) {i : Fin τ.rank}
    (h₁ : α ≠ Pi.single i 1) (h₂ : α ≠ -Pi.single i 1) {k : ℕ} (hk : k ≤ stringUp τ i α) :
    IsRoot τ (α + (k : ℤ) • Pi.single i 1) ∧ α + (k : ℤ) • Pi.single i 1 ≠ Pi.single i 1 ∧
      α + (k : ℤ) • Pi.single i 1 ≠ -Pi.single i 1 ∧
      stringDown τ i (α + (k : ℤ) • Pi.single i 1) = stringDown τ i α + k := by
  obtain ⟨-, -, htr⟩ := root_string_transport hα i h₁ h₂
  obtain ⟨hr, hr₁, hr₂, -, hd⟩ := htr k (by omega) (by exact_mod_cast hk)
  exact ⟨hr, hr₁, hr₂, by omega⟩

private theorem down_transport {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) {i : Fin τ.rank}
    (h₁ : α ≠ Pi.single i 1) (h₂ : α ≠ -Pi.single i 1) {k : ℕ} (hk : k ≤ stringDown τ i α) :
    IsRoot τ (α - (k : ℤ) • Pi.single i 1) ∧ α - (k : ℤ) • Pi.single i 1 ≠ Pi.single i 1 ∧
      α - (k : ℤ) • Pi.single i 1 ≠ -Pi.single i 1 ∧
      stringUp τ i (α - (k : ℤ) • Pi.single i 1) = stringUp τ i α + k := by
  obtain ⟨-, -, htr⟩ := root_string_transport hα i h₁ h₂
  obtain ⟨hr, hr₁, hr₂, hu, -⟩ := htr (-(k : ℤ)) (by omega) (by omega)
  rw [neg_smul, ← sub_eq_add_neg] at hr hr₁ hr₂ hu
  exact ⟨hr, hr₁, hr₂, by omega⟩

theorem infE_hVec (i j : Fin τ.rank) :
    infE τ R i (hVec τ R j) = ((τ.cartan j i).natAbs : R) • rootVec τ R (Pi.single i 1) := by
  change infE τ R i (Finsupp.single (Sum.inl j) 1) = _
  rw [infE, Finsupp.linearCombination_single, one_smul]

theorem infE_rootVec_single (i : Fin τ.rank) : infE τ R i (rootVec τ R (Pi.single i 1)) = 0 := by
  rw [rootVec_of_isRoot (isRoot_single τ i), infE, Finsupp.linearCombination_single, one_smul]
  exact ite_eq_left rfl

theorem infE_rootVec_neg_single (i : Fin τ.rank) :
    infE τ R i (rootVec τ R (-Pi.single i 1)) = hVec τ R i := by
  rw [rootVec_of_isRoot (isRoot_neg_single τ i), infE, Finsupp.linearCombination_single,
    one_smul]
  exact (ite_eq_right (single_ne_neg_single i).symm).trans (ite_eq_left rfl)

theorem infE_rootVec_of_ne (i : Fin τ.rank) {α : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (h₁ : α ≠ Pi.single i 1) (h₂ : α ≠ -Pi.single i 1) :
    infE τ R i (rootVec τ R α) =
      ((stringDown τ i α + 1 : ℕ) : R) • rootVec τ R (α + Pi.single i 1) := by
  rw [rootVec_of_isRoot hα, infE, Finsupp.linearCombination_single, one_smul]
  exact (ite_eq_right h₁).trans (ite_eq_right h₂)

theorem infF_hVec (i j : Fin τ.rank) :
    infF τ R i (hVec τ R j) = ((τ.cartan j i).natAbs : R) • rootVec τ R (-Pi.single i 1) := by
  change infF τ R i (Finsupp.single (Sum.inl j) 1) = _
  rw [infF, Finsupp.linearCombination_single, one_smul]

theorem infF_rootVec_neg_single (i : Fin τ.rank) :
    infF τ R i (rootVec τ R (-Pi.single i 1)) = 0 := by
  rw [rootVec_of_isRoot (isRoot_neg_single τ i), infF, Finsupp.linearCombination_single,
    one_smul]
  exact ite_eq_left rfl

theorem infF_rootVec_single (i : Fin τ.rank) :
    infF τ R i (rootVec τ R (Pi.single i 1)) = hVec τ R i := by
  rw [rootVec_of_isRoot (isRoot_single τ i), infF, Finsupp.linearCombination_single, one_smul]
  exact (ite_eq_right (single_ne_neg_single i)).trans (ite_eq_left rfl)

theorem infF_rootVec_of_ne (i : Fin τ.rank) {α : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (h₁ : α ≠ Pi.single i 1) (h₂ : α ≠ -Pi.single i 1) :
    infF τ R i (rootVec τ R α) =
      ((stringUp τ i α + 1 : ℕ) : R) • rootVec τ R (α - Pi.single i 1) := by
  rw [rootVec_of_isRoot hα, infF, Finsupp.linearCombination_single, one_smul]
  exact (ite_eq_right h₂).trans (ite_eq_right h₁)

theorem xCoeff_hVec (i j : Fin τ.rank) (k : ℕ) :
    xCoeff τ R i k (hVec τ R j) =
      if k = 0 then hVec τ R j
      else if k = 1 then ((τ.cartan j i).natAbs : R) • rootVec τ R (Pi.single i 1) else 0 := by
  change xCoeff τ R i k (Finsupp.single (Sum.inl j) 1) = _
  rw [xCoeff, Finsupp.linearCombination_single, one_smul]

theorem xCoeff_rootVec_single (i : Fin τ.rank) (k : ℕ) :
    xCoeff τ R i k (rootVec τ R (Pi.single i 1)) =
      if k = 0 then rootVec τ R (Pi.single i 1) else 0 := by
  rw [rootVec_of_isRoot (isRoot_single τ i), xCoeff, Finsupp.linearCombination_single, one_smul]
  exact ite_eq_left rfl

theorem xCoeff_rootVec_neg_single (i : Fin τ.rank) (k : ℕ) :
    xCoeff τ R i k (rootVec τ R (-Pi.single i 1)) =
      if k = 0 then rootVec τ R (-Pi.single i 1)
      else if k = 1 then hVec τ R i
      else if k = 2 then rootVec τ R (Pi.single i 1) else 0 := by
  rw [rootVec_of_isRoot (isRoot_neg_single τ i), xCoeff, Finsupp.linearCombination_single,
    one_smul]
  exact (ite_eq_right (single_ne_neg_single i).symm).trans (ite_eq_left rfl)

theorem xCoeff_rootVec_of_ne (i : Fin τ.rank) (k : ℕ) {α : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (h₁ : α ≠ Pi.single i 1) (h₂ : α ≠ -Pi.single i 1) :
    xCoeff τ R i k (rootVec τ R α) =
      ((stringDown τ i α + k).choose k : R) • rootVec τ R (α + (k : ℤ) • Pi.single i 1) := by
  rw [rootVec_of_isRoot hα, xCoeff, Finsupp.linearCombination_single, one_smul]
  exact (ite_eq_right h₁).trans (ite_eq_right h₂)

theorem yCoeff_hVec (i j : Fin τ.rank) (k : ℕ) :
    yCoeff τ R i k (hVec τ R j) =
      if k = 0 then hVec τ R j
      else if k = 1 then ((τ.cartan j i).natAbs : R) • rootVec τ R (-Pi.single i 1) else 0 := by
  change yCoeff τ R i k (Finsupp.single (Sum.inl j) 1) = _
  rw [yCoeff, Finsupp.linearCombination_single, one_smul]

theorem yCoeff_rootVec_neg_single (i : Fin τ.rank) (k : ℕ) :
    yCoeff τ R i k (rootVec τ R (-Pi.single i 1)) =
      if k = 0 then rootVec τ R (-Pi.single i 1) else 0 := by
  rw [rootVec_of_isRoot (isRoot_neg_single τ i), yCoeff, Finsupp.linearCombination_single,
    one_smul]
  exact ite_eq_left rfl

theorem yCoeff_rootVec_single (i : Fin τ.rank) (k : ℕ) :
    yCoeff τ R i k (rootVec τ R (Pi.single i 1)) =
      if k = 0 then rootVec τ R (Pi.single i 1)
      else if k = 1 then hVec τ R i
      else if k = 2 then rootVec τ R (-Pi.single i 1) else 0 := by
  rw [rootVec_of_isRoot (isRoot_single τ i), yCoeff, Finsupp.linearCombination_single, one_smul]
  exact (ite_eq_right (single_ne_neg_single i)).trans (ite_eq_left rfl)

theorem yCoeff_rootVec_of_ne (i : Fin τ.rank) (k : ℕ) {α : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (h₁ : α ≠ Pi.single i 1) (h₂ : α ≠ -Pi.single i 1) :
    yCoeff τ R i k (rootVec τ R α) =
      ((stringUp τ i α + k).choose k : R) • rootVec τ R (α - (k : ℤ) • Pi.single i 1) := by
  rw [rootVec_of_isRoot hα, yCoeff, Finsupp.linearCombination_single, one_smul]
  exact (ite_eq_right h₂).trans (ite_eq_right h₁)

private theorem xOp_hVec (i j : Fin τ.rank) (c : R) :
    xOp τ R i c (hVec τ R j) =
      hVec τ R j + (((τ.cartan j i).natAbs : R) * c) • rootVec τ R (Pi.single i 1) := by
  change xOp τ R i c (Finsupp.single (Sum.inl j) 1) = _
  rw [xOp, Finsupp.linearCombination_single, one_smul]

private theorem xOp_rootVec_single (i : Fin τ.rank) (c : R) :
    xOp τ R i c (rootVec τ R (Pi.single i 1)) = rootVec τ R (Pi.single i 1) := by
  rw [rootVec_of_isRoot (isRoot_single τ i), xOp, Finsupp.linearCombination_single, one_smul]
  exact ite_eq_left rfl

private theorem xOp_rootVec_neg_single (i : Fin τ.rank) (c : R) :
    xOp τ R i c (rootVec τ R (-Pi.single i 1)) =
      rootVec τ R (-Pi.single i 1) + c • hVec τ R i + c ^ 2 • rootVec τ R (Pi.single i 1) := by
  rw [rootVec_of_isRoot (isRoot_neg_single τ i), xOp, Finsupp.linearCombination_single,
    one_smul]
  exact (ite_eq_right (single_ne_neg_single i).symm).trans (ite_eq_left rfl)

private theorem xOp_rootVec_of_ne (i : Fin τ.rank) (c : R) {α : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) (h₁ : α ≠ Pi.single i 1) (h₂ : α ≠ -Pi.single i 1) :
    xOp τ R i c (rootVec τ R α) =
      ∑ k ∈ Finset.range (stringUp τ i α + 1),
        (((stringDown τ i α + k).choose k : R) * c ^ k) •
          rootVec τ R (α + (k : ℤ) • Pi.single i 1) := by
  rw [rootVec_of_isRoot hα, xOp, Finsupp.linearCombination_single, one_smul]
  exact (ite_eq_right h₁).trans (ite_eq_right h₂)

private theorem yOp_hVec (i j : Fin τ.rank) (c : R) :
    yOp τ R i c (hVec τ R j) =
      hVec τ R j + (((τ.cartan j i).natAbs : R) * c) • rootVec τ R (-Pi.single i 1) := by
  change yOp τ R i c (Finsupp.single (Sum.inl j) 1) = _
  rw [yOp, Finsupp.linearCombination_single, one_smul]

private theorem yOp_rootVec_neg_single (i : Fin τ.rank) (c : R) :
    yOp τ R i c (rootVec τ R (-Pi.single i 1)) = rootVec τ R (-Pi.single i 1) := by
  rw [rootVec_of_isRoot (isRoot_neg_single τ i), yOp, Finsupp.linearCombination_single,
    one_smul]
  exact ite_eq_left rfl

private theorem yOp_rootVec_single (i : Fin τ.rank) (c : R) :
    yOp τ R i c (rootVec τ R (Pi.single i 1)) =
      rootVec τ R (Pi.single i 1) + c • hVec τ R i + c ^ 2 • rootVec τ R (-Pi.single i 1) := by
  rw [rootVec_of_isRoot (isRoot_single τ i), yOp, Finsupp.linearCombination_single, one_smul]
  exact (ite_eq_right (single_ne_neg_single i)).trans (ite_eq_left rfl)

private theorem yOp_rootVec_of_ne (i : Fin τ.rank) (c : R) {α : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) (h₁ : α ≠ Pi.single i 1) (h₂ : α ≠ -Pi.single i 1) :
    yOp τ R i c (rootVec τ R α) =
      ∑ k ∈ Finset.range (stringDown τ i α + 1),
        (((stringUp τ i α + k).choose k : R) * c ^ k) •
          rootVec τ R (α - (k : ℤ) • Pi.single i 1) := by
  rw [rootVec_of_isRoot hα, yOp, Finsupp.linearCombination_single, one_smul]
  exact (ite_eq_right h₂).trans (ite_eq_right h₁)

theorem xOp_eq_sum_xCoeff (i : Fin τ.rank) (c : R) :
    xOp τ R i c = ∑ k ∈ Finset.range 4, c ^ k • xCoeff τ R i k := by
  refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, LinearMap.sum_apply,
    LinearMap.smul_apply]
  rcases b with j | ⟨α, hα⟩
  · change xOp τ R i c (hVec τ R j) = ∑ k ∈ Finset.range 4, c ^ k • xCoeff τ R i k (hVec τ R j)
    simp only [xOp_hVec, xCoeff_hVec, Finset.sum_range_succ, Finset.sum_range_zero]
    simp only [OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one, one_ne_zero, ite_true, ite_false]
    module
  · rw [← rootVec_of_isRoot hα]
    by_cases h₁ : α = Pi.single i 1
    · subst h₁
      simp [xOp_rootVec_single, xCoeff_rootVec_single]
    by_cases h₂ : α = -Pi.single i 1
    · subst h₂
      simp [xOp_rootVec_neg_single, xCoeff_rootVec_neg_single, Finset.sum_range_succ, add_assoc]
    rw [xOp_rootVec_of_ne i c hα h₁ h₂]
    refine (Finset.sum_subset (Finset.range_subset_range.2
      (by have := (stringUp_le_three hα h₁ h₂).1; omega)) fun k hk hk' => ?_).trans
      (Finset.sum_congr rfl fun k _ => ?_)
    · simp only [Finset.mem_range, not_lt] at hk hk'
      rw [rootVec_add_eq_zero hα h₁ h₂ (by omega), smul_zero]
    · rw [xCoeff_rootVec_of_ne i k hα h₁ h₂, smul_smul, mul_comm]

theorem yOp_eq_sum_yCoeff (i : Fin τ.rank) (c : R) :
    yOp τ R i c = ∑ k ∈ Finset.range 4, c ^ k • yCoeff τ R i k := by
  refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, LinearMap.sum_apply,
    LinearMap.smul_apply]
  rcases b with j | ⟨α, hα⟩
  · change yOp τ R i c (hVec τ R j) = ∑ k ∈ Finset.range 4, c ^ k • yCoeff τ R i k (hVec τ R j)
    simp only [yOp_hVec, yCoeff_hVec, Finset.sum_range_succ, Finset.sum_range_zero]
    simp only [OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one, one_ne_zero, ite_true, ite_false]
    module
  · rw [← rootVec_of_isRoot hα]
    by_cases h₂ : α = -Pi.single i 1
    · subst h₂
      simp [yOp_rootVec_neg_single, yCoeff_rootVec_neg_single]
    by_cases h₁ : α = Pi.single i 1
    · subst h₁
      simp [yOp_rootVec_single, yCoeff_rootVec_single, Finset.sum_range_succ, add_assoc]
    rw [yOp_rootVec_of_ne i c hα h₁ h₂]
    refine (Finset.sum_subset (Finset.range_subset_range.2
      (by have := (stringUp_le_three hα h₁ h₂).2; omega)) fun k hk hk' => ?_).trans
      (Finset.sum_congr rfl fun k _ => ?_)
    · simp only [Finset.mem_range, not_lt] at hk hk'
      rw [rootVec_sub_eq_zero hα h₁ h₂ (by omega), smul_zero]
    · rw [yCoeff_rootVec_of_ne i k hα h₁ h₂, smul_smul, mul_comm]

private theorem choose_mul_add_one (q k : ℕ) :
    (q + k).choose k * (q + k + 1) = (k + 1) * (q + (k + 1)).choose (k + 1) := by
  rw [Nat.mul_comm ((q + k).choose k), Nat.add_one_mul_choose_eq, Nat.mul_comm _ (k + 1),
    add_assoc]

theorem infE_mul_xCoeff (i : Fin τ.rank) (k : ℕ) :
    infE τ R i * xCoeff τ R i k = ((k + 1 : ℕ) : R) • xCoeff τ R i (k + 1) := by
  refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, Module.End.mul_apply,
    LinearMap.smul_apply]
  rcases b with j | ⟨α, hα⟩
  · change infE τ R i (xCoeff τ R i k (hVec τ R j)) =
      ((k + 1 : ℕ) : R) • xCoeff τ R i (k + 1) (hVec τ R j)
    rw [xCoeff_hVec, xCoeff_hVec]
    rcases k with _ | _ | k
    · simp [infE_hVec]
    · simp [infE_rootVec_single]
    · simp
  · rw [← rootVec_of_isRoot hα]
    by_cases h₁ : α = Pi.single i 1
    · subst h₁
      rw [xCoeff_rootVec_single, xCoeff_rootVec_single]
      rcases k with _ | k
      · simp [infE_rootVec_single]
      · simp
    by_cases h₂ : α = -Pi.single i 1
    · subst h₂
      rw [xCoeff_rootVec_neg_single, xCoeff_rootVec_neg_single]
      rcases k with _ | _ | _ | k
      · simp [infE_rootVec_neg_single]
      · simp [infE_hVec, τ.cartan_self]
      · simp [infE_rootVec_single]
      · simp
    rw [xCoeff_rootVec_of_ne i k hα h₁ h₂, xCoeff_rootVec_of_ne i (k + 1) hα h₁ h₂, map_smul]
    by_cases hk : k ≤ stringUp τ i α
    · obtain ⟨hr, hr₁, hr₂, hd⟩ := up_transport hα h₁ h₂ hk
      have hv : α + (k : ℤ) • Pi.single i 1 + Pi.single i 1 =
          α + ((k + 1 : ℕ) : ℤ) • Pi.single i 1 := by
        rw [Nat.cast_succ, add_smul, one_smul, add_assoc]
      rw [infE_rootVec_of_ne i hr hr₁ hr₂, hd, hv, smul_smul, smul_smul, ← Nat.cast_mul,
        ← Nat.cast_mul, choose_mul_add_one]
    · rw [rootVec_add_eq_zero hα h₁ h₂ (by omega), rootVec_add_eq_zero hα h₁ h₂ (by omega)]
      simp only [map_zero, smul_zero]

theorem infF_mul_yCoeff (i : Fin τ.rank) (k : ℕ) :
    infF τ R i * yCoeff τ R i k = ((k + 1 : ℕ) : R) • yCoeff τ R i (k + 1) := by
  refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, Module.End.mul_apply,
    LinearMap.smul_apply]
  rcases b with j | ⟨α, hα⟩
  · change infF τ R i (yCoeff τ R i k (hVec τ R j)) =
      ((k + 1 : ℕ) : R) • yCoeff τ R i (k + 1) (hVec τ R j)
    rw [yCoeff_hVec, yCoeff_hVec]
    rcases k with _ | _ | k
    · simp [infF_hVec]
    · simp [infF_rootVec_neg_single]
    · simp
  · rw [← rootVec_of_isRoot hα]
    by_cases h₂ : α = -Pi.single i 1
    · subst h₂
      rw [yCoeff_rootVec_neg_single, yCoeff_rootVec_neg_single]
      rcases k with _ | k
      · simp [infF_rootVec_neg_single]
      · simp
    by_cases h₁ : α = Pi.single i 1
    · subst h₁
      rw [yCoeff_rootVec_single, yCoeff_rootVec_single]
      rcases k with _ | _ | _ | k
      · simp [infF_rootVec_single]
      · simp [infF_hVec, τ.cartan_self]
      · simp [infF_rootVec_neg_single]
      · simp
    rw [yCoeff_rootVec_of_ne i k hα h₁ h₂, yCoeff_rootVec_of_ne i (k + 1) hα h₁ h₂, map_smul]
    by_cases hk : k ≤ stringDown τ i α
    · obtain ⟨hr, hr₁, hr₂, hu⟩ := down_transport hα h₁ h₂ hk
      have hv : α - (k : ℤ) • Pi.single i 1 - Pi.single i 1 =
          α - ((k + 1 : ℕ) : ℤ) • Pi.single i 1 := by
        rw [Nat.cast_succ, add_smul, one_smul, sub_add_eq_sub_sub]
      rw [infF_rootVec_of_ne i hr hr₁ hr₂, hu, hv, smul_smul, smul_smul, ← Nat.cast_mul,
        ← Nat.cast_mul, choose_mul_add_one]
    · rw [rootVec_sub_eq_zero hα h₁ h₂ (by omega), rootVec_sub_eq_zero hα h₁ h₂ (by omega)]
      simp only [map_zero, smul_zero]

theorem xCoeff_zero (i : Fin τ.rank) : xCoeff τ R i 0 = 1 := by
  refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, Module.End.one_apply]
  rcases b with j | ⟨α, hα⟩
  · change xCoeff τ R i 0 (hVec τ R j) = hVec τ R j
    rw [xCoeff_hVec, ite_eq_left rfl]
  · rw [← rootVec_of_isRoot hα]
    by_cases h₁ : α = Pi.single i 1
    · subst h₁
      rw [xCoeff_rootVec_single, ite_eq_left rfl]
    by_cases h₂ : α = -Pi.single i 1
    · subst h₂
      rw [xCoeff_rootVec_neg_single, ite_eq_left rfl]
    rw [xCoeff_rootVec_of_ne i 0 hα h₁ h₂, Nat.choose_zero_right, Nat.cast_one, one_smul,
      Nat.cast_zero, zero_smul, add_zero]

theorem yCoeff_zero (i : Fin τ.rank) : yCoeff τ R i 0 = 1 := by
  refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, Module.End.one_apply]
  rcases b with j | ⟨α, hα⟩
  · change yCoeff τ R i 0 (hVec τ R j) = hVec τ R j
    rw [yCoeff_hVec, ite_eq_left rfl]
  · rw [← rootVec_of_isRoot hα]
    by_cases h₂ : α = -Pi.single i 1
    · subst h₂
      rw [yCoeff_rootVec_neg_single, ite_eq_left rfl]
    by_cases h₁ : α = Pi.single i 1
    · subst h₁
      rw [yCoeff_rootVec_single, ite_eq_left rfl]
    rw [yCoeff_rootVec_of_ne i 0 hα h₁ h₂, Nat.choose_zero_right, Nat.cast_one, one_smul,
      Nat.cast_zero, zero_smul, sub_zero]

theorem xCoeff_eq_zero (i : Fin τ.rank) {k : ℕ} (hk : 4 ≤ k) : xCoeff τ R i k = 0 := by
  refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, LinearMap.zero_apply]
  rcases b with j | ⟨α, hα⟩
  · change xCoeff τ R i k (hVec τ R j) = 0
    rw [xCoeff_hVec, ite_eq_right (show k ≠ 0 by omega), ite_eq_right (show k ≠ 1 by omega)]
  · rw [← rootVec_of_isRoot hα]
    by_cases h₁ : α = Pi.single i 1
    · subst h₁
      rw [xCoeff_rootVec_single, ite_eq_right (show k ≠ 0 by omega)]
    by_cases h₂ : α = -Pi.single i 1
    · subst h₂
      rw [xCoeff_rootVec_neg_single, ite_eq_right (show k ≠ 0 by omega),
        ite_eq_right (show k ≠ 1 by omega), ite_eq_right (show k ≠ 2 by omega)]
    rw [xCoeff_rootVec_of_ne i k hα h₁ h₂,
      rootVec_add_eq_zero hα h₁ h₂ (by have := (stringUp_le_three hα h₁ h₂).1; omega),
      smul_zero]

theorem yCoeff_eq_zero (i : Fin τ.rank) {k : ℕ} (hk : 4 ≤ k) : yCoeff τ R i k = 0 := by
  refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, LinearMap.zero_apply]
  rcases b with j | ⟨α, hα⟩
  · change yCoeff τ R i k (hVec τ R j) = 0
    rw [yCoeff_hVec, ite_eq_right (show k ≠ 0 by omega), ite_eq_right (show k ≠ 1 by omega)]
  · rw [← rootVec_of_isRoot hα]
    by_cases h₂ : α = -Pi.single i 1
    · subst h₂
      rw [yCoeff_rootVec_neg_single, ite_eq_right (show k ≠ 0 by omega)]
    by_cases h₁ : α = Pi.single i 1
    · subst h₁
      rw [yCoeff_rootVec_single, ite_eq_right (show k ≠ 0 by omega),
        ite_eq_right (show k ≠ 1 by omega), ite_eq_right (show k ≠ 2 by omega)]
    rw [yCoeff_rootVec_of_ne i k hα h₁ h₂,
      rootVec_sub_eq_zero hα h₁ h₂ (by have := (stringUp_le_three hα h₁ h₂).2; omega),
      smul_zero]

theorem infE_pow (i : Fin τ.rank) (k : ℕ) : infE τ R i ^ k = (k ! : R) • xCoeff τ R i k := by
  induction k with
  | zero => rw [pow_zero, Nat.factorial_zero, Nat.cast_one, one_smul, xCoeff_zero]
  | succ k ih =>
    rw [pow_succ', ih, mul_smul_comm, infE_mul_xCoeff, smul_smul, Nat.factorial_succ,
      Nat.cast_mul, mul_comm]

theorem infF_pow (i : Fin τ.rank) (k : ℕ) : infF τ R i ^ k = (k ! : R) • yCoeff τ R i k := by
  induction k with
  | zero => rw [pow_zero, Nat.factorial_zero, Nat.cast_one, one_smul, yCoeff_zero]
  | succ k ih =>
    rw [pow_succ', ih, mul_smul_comm, infF_mul_yCoeff, smul_smul, Nat.factorial_succ,
      Nat.cast_mul, mul_comm]

theorem xCoeff_one (i : Fin τ.rank) : xCoeff τ R i 1 = infE τ R i := by
  simpa using (infE_pow (R := R) i 1).symm

theorem yCoeff_one (i : Fin τ.rank) : yCoeff τ R i 1 = infF τ R i := by
  simpa using (infF_pow (R := R) i 1).symm

theorem infE_pow_eq_zero (i : Fin τ.rank) {k : ℕ} (hk : 4 ≤ k) : infE τ R i ^ k = 0 := by
  rw [infE_pow, xCoeff_eq_zero i hk, smul_zero]

theorem infF_pow_eq_zero (i : Fin τ.rank) {k : ℕ} (hk : 4 ≤ k) : infF τ R i ^ k = 0 := by
  rw [infF_pow, yCoeff_eq_zero i hk, smul_zero]

private theorem inv_factorial_smul_mul [Algebra ℚ R] (c : R) (k : ℕ) :
    ((k ! : ℚ)⁻¹ • c ^ k) * (k ! : R) = c ^ k := by
  rw [smul_mul_assoc, mul_comm, ← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul,
    inv_mul_cancel₀ (by positivity), one_smul]

theorem xOp_eq_sum_infE_pow [Algebra ℚ R] (i : Fin τ.rank) (c : R) :
    xOp τ R i c = ∑ k ∈ Finset.range 4, ((k ! : ℚ)⁻¹ • c ^ k) • infE τ R i ^ k := by
  rw [xOp_eq_sum_xCoeff]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [infE_pow, smul_smul, inv_factorial_smul_mul]

theorem yOp_eq_sum_infF_pow [Algebra ℚ R] (i : Fin τ.rank) (c : R) :
    yOp τ R i c = ∑ k ∈ Finset.range 4, ((k ! : ℚ)⁻¹ • c ^ k) • infF τ R i ^ k := by
  rw [yOp_eq_sum_yCoeff]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [infF_pow, smul_smul, inv_factorial_smul_mul]

section ChangeOfRing

variable {S : Type*} [CommRing S] (f : R →+* S)

private theorem mapRange_rootVec (β : Fin τ.rank → ℤ) :
    Finsupp.mapRange f f.map_zero (rootVec τ R β) = rootVec τ S β := by
  unfold rootVec
  split_ifs <;> simp

private theorem mapRange_hVec (j : Fin τ.rank) :
    Finsupp.mapRange f f.map_zero (hVec τ R j) = hVec τ S j := by
  simp [hVec]

private theorem mapRange_natCast_smul (n : ℕ) (x : RootModule τ R) :
    Finsupp.mapRange f f.map_zero ((n : R) • x) = (n : S) • Finsupp.mapRange f f.map_zero x := by
  ext a
  simp

theorem mapRange_xCoeff_single (i : Fin τ.rank) (k : ℕ) (b : Label τ) :
    Finsupp.mapRange f f.map_zero (xCoeff τ R i k (Finsupp.single b 1)) =
      xCoeff τ S i k (Finsupp.single b 1) := by
  rcases b with j | ⟨α, hα⟩
  · change Finsupp.mapRange f f.map_zero (xCoeff τ R i k (hVec τ R j)) =
      xCoeff τ S i k (hVec τ S j)
    rw [xCoeff_hVec, xCoeff_hVec]
    split_ifs
    · exact mapRange_hVec f j
    · rw [mapRange_natCast_smul, mapRange_rootVec]
    · exact Finsupp.mapRange_zero
  · rw [← rootVec_of_isRoot (R := R) hα, ← rootVec_of_isRoot (R := S) hα]
    by_cases h₁ : α = Pi.single i 1
    · subst h₁
      rw [xCoeff_rootVec_single, xCoeff_rootVec_single]
      split_ifs <;> simp [mapRange_rootVec]
    by_cases h₂ : α = -Pi.single i 1
    · subst h₂
      rw [xCoeff_rootVec_neg_single, xCoeff_rootVec_neg_single]
      split_ifs <;> simp [mapRange_hVec, mapRange_rootVec]
    rw [xCoeff_rootVec_of_ne i k hα h₁ h₂, xCoeff_rootVec_of_ne i k hα h₁ h₂,
      mapRange_natCast_smul, mapRange_rootVec]

theorem mapRange_yCoeff_single (i : Fin τ.rank) (k : ℕ) (b : Label τ) :
    Finsupp.mapRange f f.map_zero (yCoeff τ R i k (Finsupp.single b 1)) =
      yCoeff τ S i k (Finsupp.single b 1) := by
  rcases b with j | ⟨α, hα⟩
  · change Finsupp.mapRange f f.map_zero (yCoeff τ R i k (hVec τ R j)) =
      yCoeff τ S i k (hVec τ S j)
    rw [yCoeff_hVec, yCoeff_hVec]
    split_ifs
    · exact mapRange_hVec f j
    · rw [mapRange_natCast_smul, mapRange_rootVec]
    · exact Finsupp.mapRange_zero
  · rw [← rootVec_of_isRoot (R := R) hα, ← rootVec_of_isRoot (R := S) hα]
    by_cases h₂ : α = -Pi.single i 1
    · subst h₂
      rw [yCoeff_rootVec_neg_single, yCoeff_rootVec_neg_single]
      split_ifs <;> simp [mapRange_rootVec]
    by_cases h₁ : α = Pi.single i 1
    · subst h₁
      rw [yCoeff_rootVec_single, yCoeff_rootVec_single]
      split_ifs <;> simp [mapRange_hVec, mapRange_rootVec]
    rw [yCoeff_rootVec_of_ne i k hα h₁ h₂, yCoeff_rootVec_of_ne i k hα h₁ h₂,
      mapRange_natCast_smul, mapRange_rootVec]

end ChangeOfRing

section IntegralMatrices

open Polynomial

theorem xOp_X_single_apply (i : Fin τ.rank) (a b : Label τ) :
    xOp τ ℤ[X] i X (Finsupp.single b 1) a =
      ∑ k ∈ Finset.range 4, C (xCoeff τ ℤ i k (Finsupp.single b 1) a) * X ^ k := by
  rw [xOp_eq_sum_xCoeff, LinearMap.sum_apply, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [LinearMap.smul_apply, Finsupp.smul_apply, smul_eq_mul, mul_comm,
    ← mapRange_xCoeff_single C, Finsupp.mapRange_apply]

theorem yOp_X_single_apply (i : Fin τ.rank) (a b : Label τ) :
    yOp τ ℤ[X] i X (Finsupp.single b 1) a =
      ∑ k ∈ Finset.range 4, C (yCoeff τ ℤ i k (Finsupp.single b 1) a) * X ^ k := by
  rw [yOp_eq_sum_yCoeff, LinearMap.sum_apply, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [LinearMap.smul_apply, Finsupp.smul_apply, smul_eq_mul, mul_comm,
    ← mapRange_yCoeff_single C, Finsupp.mapRange_apply]

private theorem coeff_sum_range_four (n : ℕ → ℤ) (m : ℕ) :
    (∑ k ∈ Finset.range 4, C (n k) * X ^ k).coeff m = if m < 4 then n m else 0 := by
  rw [finsetSum_coeff]
  simp only [coeff_C_mul_X_pow, Finset.sum_ite_eq, Finset.mem_range]

private theorem natDegree_sum_range_four_le (n : ℕ → ℤ) :
    (∑ k ∈ Finset.range 4, C (n k) * X ^ k).natDegree ≤ 3 :=
  natDegree_sum_le_of_forall_le _ _ fun _ hk =>
    (natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))

theorem natDegree_xOp_X_single_apply_le (i : Fin τ.rank) (a b : Label τ) :
    (xOp τ ℤ[X] i X (Finsupp.single b 1) a).natDegree ≤ 3 := by
  rw [xOp_X_single_apply]
  exact natDegree_sum_range_four_le _

theorem natDegree_yOp_X_single_apply_le (i : Fin τ.rank) (a b : Label τ) :
    (yOp τ ℤ[X] i X (Finsupp.single b 1) a).natDegree ≤ 3 := by
  rw [yOp_X_single_apply]
  exact natDegree_sum_range_four_le _

theorem coeff_xOp_X_single_apply (i : Fin τ.rank) (a b : Label τ) (k : ℕ) :
    (xOp τ ℤ[X] i X (Finsupp.single b 1) a).coeff k = xCoeff τ ℤ i k (Finsupp.single b 1) a := by
  rw [xOp_X_single_apply, coeff_sum_range_four]
  split_ifs with hk
  · rfl
  · rw [xCoeff_eq_zero i (by omega)]
    simp

theorem coeff_yOp_X_single_apply (i : Fin τ.rank) (a b : Label τ) (k : ℕ) :
    (yOp τ ℤ[X] i X (Finsupp.single b 1) a).coeff k = yCoeff τ ℤ i k (Finsupp.single b 1) a := by
  rw [yOp_X_single_apply, coeff_sum_range_four]
  split_ifs with hk
  · rfl
  · rw [yCoeff_eq_zero i (by omega)]
    simp

end IntegralMatrices

variable (τ R) in
theorem simple_root_finite_exponential (i : Fin τ.rank) :
    (∀ c : R, xOp τ R i c = ∑ k ∈ Finset.range 4, c ^ k • xCoeff τ R i k) ∧
      (∀ c : R, yOp τ R i c = ∑ k ∈ Finset.range 4, c ^ k • yCoeff τ R i k) ∧
      (∀ k : ℕ, infE τ R i ^ k = (k ! : R) • xCoeff τ R i k) ∧
      (∀ k : ℕ, infF τ R i ^ k = (k ! : R) • yCoeff τ R i k) ∧
      xCoeff τ R i 0 = 1 ∧ yCoeff τ R i 0 = 1 ∧ infE τ R i ^ 4 = 0 ∧ infF τ R i ^ 4 = 0 :=
  ⟨xOp_eq_sum_xCoeff i, yOp_eq_sum_yCoeff i, infE_pow i, infF_pow i, xCoeff_zero i,
    yCoeff_zero i, infE_pow_eq_zero i le_rfl, infF_pow_eq_zero i le_rfl⟩

variable (τ R) in
theorem simple_root_finite_exponential_rat [Algebra ℚ R] (i : Fin τ.rank) (c : R) :
    xOp τ R i c = ∑ k ∈ Finset.range 4, ((k ! : ℚ)⁻¹ • c ^ k) • infE τ R i ^ k ∧
      yOp τ R i c = ∑ k ∈ Finset.range 4, ((k ! : ℚ)⁻¹ • c ^ k) • infF τ R i ^ k :=
  ⟨xOp_eq_sum_infE_pow i c, yOp_eq_sum_infF_pow i c⟩

variable (τ) in
open Polynomial in
theorem simple_root_finite_exponential_int (i : Fin τ.rank) :
    infE τ ℤ i ^ 4 = 0 ∧ infF τ ℤ i ^ 4 = 0 ∧
      ∀ a b : Label τ, (xOp τ ℤ[X] i X (Finsupp.single b 1) a).natDegree ≤ 3 ∧
        (yOp τ ℤ[X] i X (Finsupp.single b 1) a).natDegree ≤ 3 ∧
        ∀ k : ℕ, (infE τ ℤ i ^ k) (Finsupp.single b 1) a =
            (k ! : ℤ) * (xOp τ ℤ[X] i X (Finsupp.single b 1) a).coeff k ∧
          (infF τ ℤ i ^ k) (Finsupp.single b 1) a =
            (k ! : ℤ) * (yOp τ ℤ[X] i X (Finsupp.single b 1) a).coeff k := by
  refine ⟨infE_pow_eq_zero i le_rfl, infF_pow_eq_zero i le_rfl, fun a b =>
    ⟨natDegree_xOp_X_single_apply_le i a b, natDegree_yOp_X_single_apply_le i a b, fun k => ?_⟩⟩
  rw [coeff_xOp_X_single_apply, coeff_yOp_X_single_apply, infE_pow, infF_pow]
  exact ⟨rfl, rfl⟩

end CFSG.Blueprint.Chevalley
