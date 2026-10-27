module

public import CFSG.Blueprint.ChevalleyRoots
public import Certificates.Certificate113

public noncomputable section

namespace CFSG.Blueprint.Chevalley

@[expose] def UpTransport (τ : Tag) : Prop :=
  ∀ (i : Fin τ.rank) (α : Fin τ.rank → ℤ), IsRoot τ α → α ≠ Pi.single i 1 →
    α ≠ -Pi.single i 1 → ∀ k : ℕ, k ≤ stringUp τ i α →
      IsRoot τ (α + (k : ℤ) • Pi.single i 1) ∧ α + (k : ℤ) • Pi.single i 1 ≠ Pi.single i 1 ∧
        α + (k : ℤ) • Pi.single i 1 ≠ -Pi.single i 1 ∧
        stringUp τ i (α + (k : ℤ) • Pi.single i 1) = stringUp τ i α - k ∧
        stringDown τ i (α + (k : ℤ) • Pi.single i 1) = stringDown τ i α + k

@[expose] def DownTransport (τ : Tag) : Prop :=
  ∀ (i : Fin τ.rank) (α : Fin τ.rank → ℤ), IsRoot τ α → α ≠ Pi.single i 1 →
    α ≠ -Pi.single i 1 → ∀ k : ℕ, k ≤ stringDown τ i α →
      IsRoot τ (α - (k : ℤ) • Pi.single i 1) ∧ α - (k : ℤ) • Pi.single i 1 ≠ Pi.single i 1 ∧
        α - (k : ℤ) • Pi.single i 1 ≠ -Pi.single i 1 ∧
        stringDown τ i (α - (k : ℤ) • Pi.single i 1) = stringDown τ i α - k ∧
        stringUp τ i (α - (k : ℤ) • Pi.single i 1) = stringUp τ i α + k

variable {τ : Tag} {R : Type*} [CommRing R]

private theorem choose_add_mul_choose_add_sub {q k l : ℕ} (hkl : k ≤ l) :
    (q + k).choose k * (q + l).choose (l - k) = (q + l).choose l * l.choose k := by
  rw [Nat.choose_symm_of_eq_add (show q + l = (l - k) + (q + k) by omega), mul_comm,
    Nat.choose_mul (Nat.le_add_left k q), Nat.choose_mul hkl, Nat.add_sub_cancel,
    Nat.choose_symm_of_eq_add (show q + l - k = (l - k) + q by omega)]

private theorem sum_choose_mul_choose_sub (q l : ℕ) (c d : R) :
    ∑ k ∈ Finset.range (l + 1),
        ((q + k).choose k * d ^ k : R) * ((q + l).choose (l - k) * c ^ (l - k)) =
      ((q + l).choose l : R) * (c + d) ^ l := by
  rw [add_comm c d, add_pow, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have h : ((q + k).choose k : R) * ((q + l).choose (l - k) : R) =
      ((q + l).choose l : R) * (l.choose k : R) := by
    rw [← Nat.cast_mul, ← Nat.cast_mul,
      choose_add_mul_choose_add_sub (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))]
  linear_combination (d ^ k * c ^ (l - k)) * h

private theorem sum_smul_sum_choose (w : ℕ → RootModule τ R) (n q : ℕ) (c d : R) :
    ∑ k ∈ Finset.range (n + 1), (((q + k).choose k : R) * d ^ k) •
        ∑ m ∈ Finset.range (n - k + 1), (((q + k + m).choose m : R) * c ^ m) • w (k + m) =
      ∑ l ∈ Finset.range (n + 1), (((q + l).choose l : R) * (c + d) ^ l) • w l := by
  calc _ = ∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.Ico k (n + 1),
        ((((q + k).choose k : R) * d ^ k) * (((q + l).choose (l - k) : R) * c ^ (l - k))) •
          w l := by
        refine Finset.sum_congr rfl fun k hk => ?_
        rw [Finset.sum_Ico_eq_sum_range, Finset.smul_sum,
          show n + 1 - k = n - k + 1 by have := Finset.mem_range.mp hk; omega]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [smul_smul, Nat.add_sub_cancel_left, add_assoc]
    _ = ∑ l ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (l + 1),
        ((((q + k).choose k : R) * d ^ k) * (((q + l).choose (l - k) : R) * c ^ (l - k))) •
          w l := by
        refine Finset.sum_comm' fun k l => ?_
        simp only [Finset.mem_range, Finset.mem_Ico]
        omega
    _ = _ := by
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [← Finset.sum_smul, sum_choose_mul_choose_sub]

private theorem single_ne_neg_single (i : Fin τ.rank) :
    (Pi.single i 1 : Fin τ.rank → ℤ) ≠ -Pi.single i 1 := fun h => by
  simpa using congrFun h i

private theorem rootVec_of_isRoot {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) :
    rootVec τ R β = Finsupp.single (Sum.inr ⟨β, hβ⟩) 1 :=
  dite_eq_left hβ

private theorem rootVec_apply_inl (β : Fin τ.rank → ℤ) (j : Fin τ.rank) :
    rootVec τ R β (Sum.inl j) = 0 := by
  unfold rootVec
  split_ifs <;> simp

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

theorem xOp_mul_xOp (h : UpTransport τ) (i : Fin τ.rank) (c d : R) :
    xOp τ R i c * xOp τ R i d = xOp τ R i (c + d) := by
  refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, Module.End.mul_apply]
  rcases b with j | ⟨α, hα⟩
  · change xOp τ R i c (xOp τ R i d (hVec τ R j)) = xOp τ R i (c + d) (hVec τ R j)
    rw [xOp_hVec, xOp_hVec, map_add, map_smul, xOp_hVec, xOp_rootVec_single]
    module
  · rw [← rootVec_of_isRoot hα]
    by_cases h₁ : α = Pi.single i 1
    · subst h₁
      rw [xOp_rootVec_single, xOp_rootVec_single, xOp_rootVec_single]
    by_cases h₂ : α = -Pi.single i 1
    · subst h₂
      rw [xOp_rootVec_neg_single, xOp_rootVec_neg_single, map_add, map_add, map_smul, map_smul,
        xOp_rootVec_neg_single, xOp_hVec, xOp_rootVec_single, τ.cartan_self,
        show (((2 : ℤ).natAbs : ℕ) : R) = 2 by norm_num]
      module
    have hsum := sum_smul_sum_choose (fun l => rootVec τ R (α + (l : ℤ) • Pi.single i 1))
      (stringUp τ i α) (stringDown τ i α) c d
    rw [xOp_rootVec_of_ne i d hα h₁ h₂, map_sum, xOp_rootVec_of_ne i (c + d) hα h₁ h₂, ← hsum]
    refine Finset.sum_congr rfl fun k hk => ?_
    obtain ⟨hr, hr₁, hr₂, hup, hdown⟩ :=
      h i α hα h₁ h₂ k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
    rw [map_smul, xOp_rootVec_of_ne i c hr hr₁ hr₂, hup, hdown]
    refine congrArg _ (Finset.sum_congr rfl fun m _ => ?_)
    rw [Nat.cast_add, add_smul, ← add_assoc]

theorem yOp_mul_yOp (h : DownTransport τ) (i : Fin τ.rank) (c d : R) :
    yOp τ R i c * yOp τ R i d = yOp τ R i (c + d) := by
  refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, Module.End.mul_apply]
  rcases b with j | ⟨α, hα⟩
  · change yOp τ R i c (yOp τ R i d (hVec τ R j)) = yOp τ R i (c + d) (hVec τ R j)
    rw [yOp_hVec, yOp_hVec, map_add, map_smul, yOp_hVec, yOp_rootVec_neg_single]
    module
  · rw [← rootVec_of_isRoot hα]
    by_cases h₂ : α = -Pi.single i 1
    · subst h₂
      rw [yOp_rootVec_neg_single, yOp_rootVec_neg_single, yOp_rootVec_neg_single]
    by_cases h₁ : α = Pi.single i 1
    · subst h₁
      rw [yOp_rootVec_single, yOp_rootVec_single, map_add, map_add, map_smul, map_smul,
        yOp_rootVec_single, yOp_hVec, yOp_rootVec_neg_single, τ.cartan_self,
        show (((2 : ℤ).natAbs : ℕ) : R) = 2 by norm_num]
      module
    have hsum := sum_smul_sum_choose (fun l => rootVec τ R (α - (l : ℤ) • Pi.single i 1))
      (stringDown τ i α) (stringUp τ i α) c d
    rw [yOp_rootVec_of_ne i d hα h₁ h₂, map_sum, yOp_rootVec_of_ne i (c + d) hα h₁ h₂, ← hsum]
    refine Finset.sum_congr rfl fun k hk => ?_
    obtain ⟨hr, hr₁, hr₂, hdown, hup⟩ :=
      h i α hα h₁ h₂ k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
    rw [map_smul, yOp_rootVec_of_ne i c hr hr₁ hr₂, hdown, hup]
    refine congrArg _ (Finset.sum_congr rfl fun m _ => ?_)
    rw [Nat.cast_add, add_smul, sub_add_eq_sub_sub]

theorem xOp_zero (i : Fin τ.rank) : xOp τ R i 0 = 1 := by
  refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, Module.End.one_apply]
  rcases b with j | ⟨α, hα⟩
  · change xOp τ R i 0 (hVec τ R j) = hVec τ R j
    rw [xOp_hVec, mul_zero, zero_smul, add_zero]
  · rw [← rootVec_of_isRoot hα]
    by_cases h₁ : α = Pi.single i 1
    · subst h₁
      exact xOp_rootVec_single i 0
    by_cases h₂ : α = -Pi.single i 1
    · subst h₂
      rw [xOp_rootVec_neg_single, zero_smul, add_zero, zero_pow two_ne_zero, zero_smul,
        add_zero]
    rw [xOp_rootVec_of_ne i 0 hα h₁ h₂, Finset.sum_range_succ',
      Finset.sum_eq_zero fun k _ => by simp]
    simp

theorem yOp_zero (i : Fin τ.rank) : yOp τ R i 0 = 1 := by
  refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, Module.End.one_apply]
  rcases b with j | ⟨α, hα⟩
  · change yOp τ R i 0 (hVec τ R j) = hVec τ R j
    rw [yOp_hVec, mul_zero, zero_smul, add_zero]
  · rw [← rootVec_of_isRoot hα]
    by_cases h₂ : α = -Pi.single i 1
    · subst h₂
      exact yOp_rootVec_neg_single i 0
    by_cases h₁ : α = Pi.single i 1
    · subst h₁
      rw [yOp_rootVec_single, zero_smul, add_zero, zero_pow two_ne_zero, zero_smul,
        add_zero]
    rw [yOp_rootVec_of_ne i 0 hα h₁ h₂, Finset.sum_range_succ',
      Finset.sum_eq_zero fun k _ => by simp]
    simp

theorem xOp_mul_xOp_neg (h : UpTransport τ) (i : Fin τ.rank) (c : R) :
    xOp τ R i c * xOp τ R i (-c) = 1 := by
  rw [xOp_mul_xOp h, add_neg_cancel, xOp_zero]

theorem xOp_neg_mul_xOp (h : UpTransport τ) (i : Fin τ.rank) (c : R) :
    xOp τ R i (-c) * xOp τ R i c = 1 := by
  rw [xOp_mul_xOp h, neg_add_cancel, xOp_zero]

theorem yOp_mul_yOp_neg (h : DownTransport τ) (i : Fin τ.rank) (c : R) :
    yOp τ R i c * yOp τ R i (-c) = 1 := by
  rw [yOp_mul_yOp h, add_neg_cancel, yOp_zero]

theorem yOp_neg_mul_yOp (h : DownTransport τ) (i : Fin τ.rank) (c : R) :
    yOp τ R i (-c) * yOp τ R i c = 1 := by
  rw [yOp_mul_yOp h, neg_add_cancel, yOp_zero]

theorem xOp_injective (i : Fin τ.rank) : Function.Injective (xOp τ R i) := by
  intro c d hcd
  have h := congrArg (fun A : Module.End R (RootModule τ R) =>
    A (rootVec τ R (-Pi.single i 1)) (Sum.inl i)) hcd
  simpa [xOp_rootVec_neg_single, rootVec_apply_inl, hVec] using h

theorem yOp_injective (i : Fin τ.rank) : Function.Injective (yOp τ R i) := by
  intro c d hcd
  have h := congrArg (fun A : Module.End R (RootModule τ R) =>
    A (rootVec τ R (Pi.single i 1)) (Sum.inl i)) hcd
  simpa [yOp_rootVec_single, rootVec_apply_inl, hVec] using h

variable (τ R) in
theorem simple_root_parameter_addition (hup : UpTransport τ) (hdown : DownTransport τ)
    (i : Fin τ.rank) :
    (∀ c d : R, xOp τ R i c * xOp τ R i d = xOp τ R i (c + d)) ∧
      (∀ c d : R, yOp τ R i c * yOp τ R i d = yOp τ R i (c + d)) ∧
      xOp τ R i 0 = 1 ∧ yOp τ R i 0 = 1 ∧
      (∀ c : R, xOp τ R i c * xOp τ R i (-c) = 1 ∧ xOp τ R i (-c) * xOp τ R i c = 1) ∧
      (∀ c : R, yOp τ R i c * yOp τ R i (-c) = 1 ∧ yOp τ R i (-c) * yOp τ R i c = 1) ∧
      Function.Injective (xOp τ R i) ∧ Function.Injective (yOp τ R i) :=
  ⟨xOp_mul_xOp hup i, yOp_mul_yOp hdown i, xOp_zero i, yOp_zero i,
    fun c => ⟨xOp_mul_xOp_neg hup i c, xOp_neg_mul_xOp hup i c⟩,
    fun c => ⟨yOp_mul_yOp_neg hdown i c, yOp_neg_mul_yOp hdown i c⟩,
    xOp_injective i, yOp_injective i⟩

end CFSG.Blueprint.Chevalley
