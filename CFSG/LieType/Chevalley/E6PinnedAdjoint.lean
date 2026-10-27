module

public import CFSG.Blueprint.ChevalleyRootGroupsTorus
public import CFSG.Blueprint.ChevalleySimpleRootOperators

public section

namespace CFSG.LieType.Chevalley.E6PinnedAdjoint

open CFSG.Blueprint.Chevalley

theorem e6_no_sandwich_aux : ∀ β ∈ rootFinset TwistTag.E6.tag, ∀ j : Fin TwistTag.E6.tag.rank,
    β + Pi.single j 1 ∈ rootFinset TwistTag.E6.tag →
      β - Pi.single j 1 ∉ rootFinset TwistTag.E6.tag := by
  decide +kernel

theorem e6_no_sandwich (j : Fin TwistTag.E6.tag.rank)
    {β : Fin TwistTag.E6.tag.rank → ℤ} (hβ : IsRoot TwistTag.E6.tag β)
    (h₁ : IsRoot TwistTag.E6.tag (β + Pi.single j 1))
    (h₂ : IsRoot TwistTag.E6.tag (β - Pi.single j 1)) : False :=
  e6_no_sandwich_aux β (mem_rootFinset.2 hβ) j (mem_rootFinset.2 h₁) (mem_rootFinset.2 h₂)

section SimpleOps

variable {K : Type*} [Field K]

theorem xOp_rootVec_E6
    (j : Fin TwistTag.E6.tag.rank) (c : K)
    {μ : Fin TwistTag.E6.tag.rank → ℤ} (hμ : IsRoot TwistTag.E6.tag μ)
    (h₁ : μ ≠ Pi.single j 1) (h₂ : μ ≠ -Pi.single j 1) :
    xOp TwistTag.E6.tag K j c (rootVec TwistTag.E6.tag K μ) =
      rootVec TwistTag.E6.tag K μ + c • rootVec TwistTag.E6.tag K (μ + Pi.single j 1) := by
  rw [xOp_apply_rootVec_of_ne j c hμ h₁ h₂]
  obtain ⟨-, hstr⟩ := isRoot_add_smul_single_iff hμ j h₁ h₂
  by_cases hr : IsRoot TwistTag.E6.tag (μ + Pi.single j 1)
  · have hp1 : 1 ≤ stringUp TwistTag.E6.tag j μ := by
      have := (hstr 1).1 (by simpa using hr)
      exact_mod_cast this.2
    have hq0 : stringDown TwistTag.E6.tag j μ = 0 := by
      by_contra hq
      have h' : IsRoot TwistTag.E6.tag (μ + (-1 : ℤ) • Pi.single j 1) :=
        (hstr (-1)).2 ⟨by omega, by omega⟩
      exact e6_no_sandwich j hμ hr (by simpa [sub_eq_add_neg] using h')
    have hp : stringUp TwistTag.E6.tag j μ = 1 := by
      by_contra hp
      have h' : IsRoot TwistTag.E6.tag (μ + (2 : ℤ) • Pi.single j 1) :=
        (hstr 2).2 ⟨by omega, by omega⟩
      refine e6_no_sandwich j hr ?_ ?_
      · have e : μ + Pi.single j 1 + Pi.single j 1 = μ + (2 : ℤ) • Pi.single j 1 := by
          rw [two_smul, add_assoc]
        rwa [e]
      · simpa using hμ
    rw [hp, hq0]
    simp [Finset.sum_range_succ]
  · have hp0 : stringUp TwistTag.E6.tag j μ = 0 := by
      by_contra hp
      exact hr (by simpa using (hstr 1).2 ⟨by omega, by exact_mod_cast Nat.pos_of_ne_zero hp⟩)
    have h0 : rootVec TwistTag.E6.tag K (μ + Pi.single j 1) = 0 := dif_neg hr
    rw [hp0, h0]
    simp

theorem yOp_rootVec_E6
    (j : Fin TwistTag.E6.tag.rank) (c : K)
    {μ : Fin TwistTag.E6.tag.rank → ℤ} (hμ : IsRoot TwistTag.E6.tag μ)
    (h₁ : μ ≠ Pi.single j 1) (h₂ : μ ≠ -Pi.single j 1) :
    yOp TwistTag.E6.tag K j c (rootVec TwistTag.E6.tag K μ) =
      rootVec TwistTag.E6.tag K μ + c • rootVec TwistTag.E6.tag K (μ - Pi.single j 1) := by
  rw [yOp_apply_rootVec_of_ne j c hμ h₁ h₂]
  obtain ⟨-, hstr⟩ := isRoot_add_smul_single_iff hμ j h₁ h₂
  by_cases hr : IsRoot TwistTag.E6.tag (μ - Pi.single j 1)
  · have hq1 : 1 ≤ stringDown TwistTag.E6.tag j μ := by
      have := (hstr (-1)).1 (by simpa [sub_eq_add_neg] using hr)
      omega
    have hp0 : stringUp TwistTag.E6.tag j μ = 0 := by
      by_contra hp
      have h' : IsRoot TwistTag.E6.tag (μ + (1 : ℤ) • Pi.single j 1) :=
        (hstr 1).2 ⟨by omega, by omega⟩
      exact e6_no_sandwich j hμ (by simpa using h') hr
    have hq : stringDown TwistTag.E6.tag j μ = 1 := by
      by_contra hq
      have h' : IsRoot TwistTag.E6.tag (μ + (-2 : ℤ) • Pi.single j 1) :=
        (hstr (-2)).2 ⟨by omega, by omega⟩
      refine e6_no_sandwich j hr ?_ ?_
      · simpa using hμ
      · have e : μ - Pi.single j 1 - Pi.single j 1 = μ + (-2 : ℤ) • Pi.single j 1 := by
          rw [neg_smul, two_smul, sub_sub, sub_eq_add_neg, neg_add]
        rwa [e]
    rw [hp0, hq]
    simp [Finset.sum_range_succ, sub_eq_add_neg]
  · have hq0 : stringDown TwistTag.E6.tag j μ = 0 := by
      by_contra hq
      exact hr (by simpa [sub_eq_add_neg] using
        (hstr (-1)).2 ⟨by omega, by omega⟩)
    have h0 : rootVec TwistTag.E6.tag K (μ - Pi.single j 1) = 0 := dif_neg hr
    rw [hq0, h0]
    simp

end SimpleOps

section Weyl

variable {τ : Tag} {K : Type*} [Field K]

theorem wordReflect_isRoot (w : List ℕ) : ∀ {ν : Fin τ.rank → ℤ}, IsRoot τ ν →
    IsRoot τ (wordReflect τ w ν) := by
  induction w with
  | nil => intro ν h; exact h
  | cons i w ih => intro ν h; exact ih (IsRoot.reflect _ h)

theorem wordReflectInv_isRoot (w : List ℕ) : ∀ {ν : Fin τ.rank → ℤ}, IsRoot τ ν →
    IsRoot τ (wordReflectInv τ w ν) := by
  induction w with
  | nil => intro ν h; exact h
  | cons i w ih => intro ν h; exact IsRoot.reflect _ (ih h)

theorem wordReflectInv_wordReflect (w : List ℕ) :
    ∀ v : Fin τ.rank → ℤ, wordReflectInv τ w (wordReflect τ w v) = v := by
  induction w with
  | nil => intro v; rfl
  | cons i w ih =>
    intro v
    rw [wordReflect_cons, wordReflectInv_cons, ih, reflect_reflect]

theorem weylElt_one_rootVec
    (i : Fin τ.rank) {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    (weylElt τ K i 1 : Module.End K (RootModule τ K)) (rootVec τ K α) =
      ((-1 : K) ^ stringDown τ i α) • rootVec τ K (reflect τ i α) := by
  rw [weylElt_rootVec i 1 hα]
  simp

theorem weylElt_one_rootVec_sgn
    (i : Fin τ.rank) {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    ∃ s : K, (s = 1 ∨ s = -1) ∧
      (weylElt τ K i 1 : Module.End K (RootModule τ K)) (rootVec τ K α) =
        s • rootVec τ K (reflect τ i α) :=
  ⟨(-1) ^ stringDown τ i α, neg_one_pow_eq_or K _, weylElt_one_rootVec i hα⟩

theorem prodWeyl_rootVec_sgn
    (w : List ℕ) : ∀ {ν : Fin τ.rank → ℤ}, IsRoot τ ν →
    ∃ s : K, (s = 1 ∨ s = -1) ∧
      ((((w.map fun i => weylElt τ K (τ.idx i) 1).reverse).prod :
          (Module.End K (RootModule τ K))ˣ) : Module.End K (RootModule τ K)) (rootVec τ K ν) =
        s • rootVec τ K (wordReflect τ w ν) := by
  induction w with
  | nil => intro ν hν; exact ⟨1, Or.inl rfl, by simp [wordReflect]⟩
  | cons i w ih =>
    intro ν hν
    obtain ⟨s₁, hs₁, h₁⟩ := weylElt_one_rootVec_sgn (K := K) (τ.idx i) hν
    obtain ⟨s₂, hs₂, h₂⟩ := ih (IsRoot.reflect (τ.idx i) hν)
    refine ⟨s₁ * s₂, ?_, ?_⟩
    · rcases hs₁ with rfl | rfl <;> rcases hs₂ with rfl | rfl <;> simp
    · rw [List.map_cons, List.reverse_cons, List.prod_append, List.prod_singleton, Units.val_mul,
        Module.End.mul_apply, h₁, map_smul, h₂, smul_smul, wordReflect_cons]

end Weyl

theorem units_inv_apply_of_apply_eq {K : Type*} [Field K] {M : Type*} [AddCommGroup M]
    [Module K M] (g : (Module.End K M)ˣ) {x y : M} (s : K) (hs : s = 1 ∨ s = -1)
    (h : (g : Module.End K M) x = s • y) :
    ((g⁻¹ : (Module.End K M)ˣ) : Module.End K M) y = s • x := by
  have h1 := congrArg (fun z => ((g⁻¹ : (Module.End K M)ˣ) : Module.End K M) z) h
  simp only [map_smul] at h1
  rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Module.End.one_apply] at h1
  have hss : s * s = 1 := by rcases hs with rfl | rfl <;> simp
  rw [h1, smul_smul, hss, one_smul]


section Pinned

variable {K : Type*} [Field K]

theorem pinnedX_rootVec_of_add_root
    {δ μ : Fin TwistTag.E6.tag.rank → ℤ} (hδ : IsRoot TwistTag.E6.tag δ)
    (hμ : IsRoot TwistTag.E6.tag μ) (h : IsRoot TwistTag.E6.tag (μ + δ)) :
    ∃ s : K, (s = 1 ∨ s = -1) ∧ ∀ c : K,
      (pinnedX TwistTag.E6.tag K δ c : Module.End K (RootModule TwistTag.E6.tag K))
          (rootVec TwistTag.E6.tag K μ) =
        rootVec TwistTag.E6.tag K μ + (s * c) • rootVec TwistTag.E6.tag K (μ + δ) := by
  set w := (pinnedData TwistTag.E6.tag δ).2.1 with hw
  set j := (pinnedData TwistTag.E6.tag δ).1 with hj
  have hfold : wordReflect TwistTag.E6.tag w (Pi.single j 1) = δ := foldl_reflect_pinnedData hδ
  set μ' := wordReflectInv TwistTag.E6.tag w μ with hμ'
  have hμ'r : IsRoot TwistTag.E6.tag μ' := wordReflectInv_isRoot w hμ
  have hsum : wordReflect TwistTag.E6.tag w (μ' + Pi.single j 1) = μ + δ := by
    rw [wordReflect_add, wordReflect_wordReflectInv, hfold]
  have hroot : IsRoot TwistTag.E6.tag (μ' + Pi.single j 1) := by
    have e : μ' + Pi.single j 1 = wordReflectInv TwistTag.E6.tag w (μ + δ) := by
      rw [← hsum, wordReflectInv_wordReflect]
    rw [e]
    exact wordReflectInv_isRoot w h
  obtain ⟨s₁, hs₁, h₁⟩ := prodWeyl_rootVec_sgn (K := K) w hμ'r
  obtain ⟨s₂, hs₂, h₂⟩ := prodWeyl_rootVec_sgn (K := K) w hroot
  rw [wordReflect_wordReflectInv] at h₁
  rw [hsum] at h₂
  have hW₁ : (pinnedWeyl TwistTag.E6.tag K δ : Module.End K (RootModule TwistTag.E6.tag K))
      (rootVec TwistTag.E6.tag K μ') = s₁ • rootVec TwistTag.E6.tag K μ := h₁
  have hW₂ : (pinnedWeyl TwistTag.E6.tag K δ : Module.End K (RootModule TwistTag.E6.tag K))
      (rootVec TwistTag.E6.tag K (μ' + Pi.single j 1)) =
        s₂ • rootVec TwistTag.E6.tag K (μ + δ) := h₂
  have hne₁ : μ' ≠ Pi.single j 1 := by
    intro e
    rw [e] at hroot
    have : (Pi.single j 1 + Pi.single j 1 : Fin TwistTag.E6.tag.rank → ℤ) =
        (2 : ℤ) • Pi.single j 1 := (two_smul ℤ _).symm
    rw [this, isRoot_smul_single_iff] at hroot
    omega
  have hne₂ : μ' ≠ -Pi.single j 1 := by
    intro e
    rw [e, neg_add_cancel] at hroot
    exact hroot.ne_zero rfl
  have hε : (((pinnedData TwistTag.E6.tag δ).2.2 : ℤ) : K) = 1 ∨
      (((pinnedData TwistTag.E6.tag δ).2.2 : ℤ) : K) = -1 := by
    rcases pinnedSign_eq TwistTag.E6.tag δ with h | h <;> rw [h] <;> simp
  have hs₁sq : s₁ * s₁ = 1 := by rcases hs₁ with rfl | rfl <;> simp
  refine ⟨s₁ * s₂ * (((pinnedData TwistTag.E6.tag δ).2.2 : ℤ) : K), ?_, fun c => ?_⟩
  · rcases hs₁ with rfl | rfl <;> rcases hs₂ with rfl | rfl <;> rcases hε with h | h <;>
      rw [h] <;> simp
  · have hWinv := units_inv_apply_of_apply_eq (pinnedWeyl TwistTag.E6.tag K δ) s₁ hs₁ hW₁
    have hx : (xOp TwistTag.E6.tag K j (((pinnedData TwistTag.E6.tag δ).2.2 • c : K)))
        (rootVec TwistTag.E6.tag K μ') = rootVec TwistTag.E6.tag K μ' +
          (((pinnedData TwistTag.E6.tag δ).2.2 • c : K)) •
            rootVec TwistTag.E6.tag K (μ' + Pi.single j 1) :=
      xOp_rootVec_E6 j _ hμ'r hne₁ hne₂
    have hpin : (pinnedX TwistTag.E6.tag K δ c : Module.End K (RootModule TwistTag.E6.tag K)) =
        (pinnedWeyl TwistTag.E6.tag K δ : Module.End K (RootModule TwistTag.E6.tag K)) *
          xOp TwistTag.E6.tag K j (((pinnedData TwistTag.E6.tag δ).2.2 • c : K)) *
          ((pinnedWeyl TwistTag.E6.tag K δ)⁻¹ : (Module.End K (RootModule TwistTag.E6.tag K))ˣ) :=
      rfl
    rw [hpin, Module.End.mul_apply, Module.End.mul_apply, hWinv, map_smul, hx]
    simp only [smul_add, map_add, map_smul, hW₁, hW₂, smul_smul, hs₁sq, one_smul, zsmul_eq_mul]
    congr 2
    ring

end Pinned

end CFSG.LieType.Chevalley.E6PinnedAdjoint
