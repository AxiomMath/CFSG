module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Frame
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.Heis.CoordSpec
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.Heis.Opposite
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Frames

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
open CFSG.LieType.Steinberg.Adjoint

set_option linter.unusedSectionVars false


namespace CoordsAux

theorem wordProd_smul_foldr {τ : Tag} (l : List (Fin τ.rank)) (v : Fin τ.rank → ℤ) :
    (coxeterSystem τ).wordProd l • v = l.foldr (reflect τ) v := by
  induction l with
  | nil => rw [CoxeterSystem.wordProd_nil, one_smul, List.foldr_nil]
  | cons i l ih => rw [CoxeterSystem.wordProd_cons, mul_smul, ih, simple_smul, List.foldr_cons]

@[expose] def wordOf : (c : TwClass) → List (Fin c.tag.rank)
  | .f4Six => TwClass.wordF4
  | .e6Six => TwClass.wordE6
  | .e8Ten => TwClass.wordE8Ten
  | .e8Twelve => TwClass.wordE8Twelve

theorem w_eq_wordProd (c : TwClass) : c.w = (coxeterSystem c.tag).wordProd (wordOf c) := by
  cases c <;> rfl

theorem w_smul_eq_foldr (c : TwClass) (v : Fin c.tag.rank → ℤ) :
    c.w • v = (wordOf c).foldr (reflect c.tag) v := by
  rw [w_eq_wordProd, wordProd_smul_foldr]

theorem w_smul_highRoot (c : TwClass) : c.w • highRoot c.tag = highRoot c.tag := by
  rw [w_smul_eq_foldr]
  cases c <;> decide +kernel

theorem iθ_not_mem_J₂ (c : TwClass) : (iθ c.tag).val ∉ c.J₂ := by
  cases c <;> decide

private theorem iform_highRoot_eq_zero (c : TwClass) {α : Fin c.tag.rank → ℤ} (hα : α ∈ c.S₂) :
    iform (highRoot c.tag) α = 0 := by
  rw [iform_highRoot_apply, hα.2 _ (iθ_not_mem_J₂ c), mul_zero]

theorem highRoot_mem_S₁ (c : TwClass) : highRoot c.tag ∈ c.S₁ :=
  ⟨isRoot_highRoot _, fun _ hα => iform_highRoot_eq_zero c hα⟩

theorem neg_highRoot_mem_S₁ (c : TwClass) : -highRoot c.tag ∈ c.S₁ :=
  ⟨isRoot_neg_highRoot _, fun _ hα => by
    rw [iform_neg_left, iform_highRoot_eq_zero c hα, neg_zero]⟩

theorem highRoot_sub_mem (τ : Tag) :
    ∀ β ∈ rootFinset τ, β (iθ τ) = 1 → highRoot τ - β ∈ rootFinset τ := by
  simp only [rootFinset, List.mem_toFinset]
  cases τ <;> decide +kernel

theorem partner_mem (c : TwClass) {β : Fin c.tag.rank → ℤ} (hβ : β ∈ Deg1 c.tag)
    (hS : β ∈ c.S₁) : highRoot c.tag - β ∈ Deg1 c.tag ∧ highRoot c.tag - β ∈ c.S₁ := by
  have hr : IsRoot c.tag (highRoot c.tag - β) :=
    mem_rootFinset.1 (highRoot_sub_mem c.tag β (mem_rootFinset.2 hβ.1) hβ.2)
  have hβ2 : β (iθ c.tag) = 1 := (CoordAux.mem_Deg1.1 hβ).2
  refine ⟨CoordAux.mem_Deg1.2 ⟨hr, ?_⟩, hr, fun α hα => ?_⟩
  · simp only [Pi.sub_apply, hβ2, CoordAux.highRoot_degree]
    norm_num
  · rw [sub_eq_add_neg, iform_add_left, iform_neg_left, iform_highRoot_eq_zero c hα, hS.2 α hα]
    simp

@[expose] def LeviCheck1 (τ : Tag) (J₁ : Finset ℕ) (word : List (Fin τ.rank)) : Prop :=
  ∀ β ∈ rootFinset τ, (∀ i : Fin τ.rank, i.val ∉ J₁ → β i = 0) → 0 < height β →
    0 < height (word.foldr (reflect τ) β)

@[expose] def LeviCheck2 (τ : Tag) (J₂ J₁ : Finset ℕ) (word : List (Fin τ.rank)) : Prop :=
  ∀ γ ∈ rootFinset τ, (∀ i : Fin τ.rank, i.val ∉ J₁ → γ i = 0) →
    word.foldr (reflect τ) γ ∈ rootFinset τ ∧
    ∀ β ∈ rootFinset τ, (∀ i : Fin τ.rank, i.val ∉ J₂ → β i = 0) →
      iform (word.foldr (reflect τ) γ) β = 0

@[expose] def LeviCheck3 (τ : Tag) (J₂ J₁ : Finset ℕ) : Prop :=
  ((rootFinset τ).filter (fun γ => ∀ i : Fin τ.rank, i.val ∉ J₁ → γ i = 0)).card =
    ((rootFinset τ).filter (fun α => ∀ β ∈ rootFinset τ,
      (∀ i : Fin τ.rank, i.val ∉ J₂ → β i = 0) → iform α β = 0)).card

@[expose] def LeviCheck (τ : Tag) (J₂ J₁ : Finset ℕ) (word : List (Fin τ.rank)) : Prop :=
  LeviCheck1 τ J₁ word ∧ LeviCheck2 τ J₂ J₁ word ∧ LeviCheck3 τ J₂ J₁

theorem lc1_f4 : LeviCheck1 Tag.F4 {0, 1} [1, 2, 0, 1, 2, 3, 0, 1, 2] := by
  unfold LeviCheck1; simp only [rootFinset, List.mem_toFinset]; decide +kernel

theorem lc2_f4 : LeviCheck2 Tag.F4 {2, 3} {0, 1} [1, 2, 0, 1, 2, 3, 0, 1, 2] := by
  unfold LeviCheck2; simp only [rootFinset, List.mem_toFinset]; decide +kernel

theorem lc3_f4 : LeviCheck3 Tag.F4 {2, 3} {0, 1} := by
  unfold LeviCheck3; decide +kernel

theorem lc1_e6 : LeviCheck1 Tag.E6 {0, 2} [3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3] := by
  unfold LeviCheck1; simp only [rootFinset, List.mem_toFinset]; decide +kernel

theorem lc2_e6 : LeviCheck2 Tag.E6 {0, 2, 4, 5} {0, 2} [3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3] := by
  unfold LeviCheck2; simp only [rootFinset, List.mem_toFinset]; decide +kernel

theorem lc3_e6 : LeviCheck3 Tag.E6 {0, 2, 4, 5} {0, 2} := by
  unfold LeviCheck3; decide +kernel

theorem lc1_e8Ten : LeviCheck1 Tag.E8 {0, 2, 3, 4}
    [4, 5, 6, 7, 3, 4, 5, 6, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 1, 3, 4, 2, 3, 0, 2,
      1, 3, 4, 5, 6, 4, 3, 2, 1, 3, 4, 5, 0, 2, 3, 1] := by
  unfold LeviCheck1; simp only [rootFinset, List.mem_toFinset]; decide +kernel

theorem lc2_e8Ten : LeviCheck2 Tag.E8 {0, 1, 2, 3} {0, 2, 3, 4}
    [4, 5, 6, 7, 3, 4, 5, 6, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 1, 3, 4, 2, 3, 0, 2,
      1, 3, 4, 5, 6, 4, 3, 2, 1, 3, 4, 5, 0, 2, 3, 1] := by
  unfold LeviCheck2; simp only [rootFinset, List.mem_toFinset]; decide +kernel

theorem lc3_e8Ten : LeviCheck3 Tag.E8 {0, 1, 2, 3} {0, 2, 3, 4} := by
  unfold LeviCheck3; decide +kernel

theorem lc1_e8Twelve : LeviCheck1 Tag.E8 {1, 2, 3, 4}
    [5, 6, 7, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 5, 3, 4, 2, 3, 0, 2, 1,
      3, 4, 5, 6, 2, 3, 0, 2, 1, 3, 4, 5, 1, 3, 2, 0] := by
  unfold LeviCheck1; simp only [rootFinset, List.mem_toFinset]; decide +kernel

theorem lc2_e8Twelve : LeviCheck2 Tag.E8 {1, 2, 3, 4} {1, 2, 3, 4}
    [5, 6, 7, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 5, 3, 4, 2, 3, 0, 2, 1,
      3, 4, 5, 6, 2, 3, 0, 2, 1, 3, 4, 5, 1, 3, 2, 0] := by
  unfold LeviCheck2; simp only [rootFinset, List.mem_toFinset]; decide +kernel

theorem lc3_e8Twelve : LeviCheck3 Tag.E8 {1, 2, 3, 4} {1, 2, 3, 4} := by
  unfold LeviCheck3; decide +kernel

theorem exists_levi_data (c : TwClass) : ∃ (J : Set (Fin c.tag.rank)) (v : WeylGroup c.tag),
    (∀ β ∈ parabolicPosRoots c.tag J, 0 < height (v • β)) ∧
    (∀ α, α ∈ c.S₁ ↔ ∃ γ ∈ parabolicRoots c.tag J, v • γ = α) := by
  have key : ∃ (J₁ : Finset ℕ) (word : List (Fin c.tag.rank)), LeviCheck c.tag c.J₂ J₁ word := by
    cases c
    · exact ⟨{0, 1}, [1, 2, 0, 1, 2, 3, 0, 1, 2], lc1_f4, lc2_f4, lc3_f4⟩
    · exact ⟨{0, 2}, [3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3], lc1_e6, lc2_e6, lc3_e6⟩
    · exact ⟨{0, 2, 3, 4}, [4, 5, 6, 7, 3, 4, 5, 6, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7,
        1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 4, 3, 2, 1, 3, 4, 5, 0, 2, 3, 1],
        lc1_e8Ten, lc2_e8Ten, lc3_e8Ten⟩
    · exact ⟨{1, 2, 3, 4}, [5, 6, 7, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7,
        5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 2, 3, 0, 2, 1, 3, 4, 5, 1, 3, 2, 0],
        lc1_e8Twelve, lc2_e8Twelve, lc3_e8Twelve⟩
  obtain ⟨J₁, word, h1, h2, h3⟩ := key
  refine ⟨{i | i.val ∈ J₁}, (coxeterSystem c.tag).wordProd word, ?_, ?_⟩
  · intro β hβ
    rw [wordProd_smul_foldr]
    exact h1 β (mem_rootFinset.2 hβ.1.1) (fun i hi => hβ.1.2 i hi) hβ.2.2
  · classical
    set v : WeylGroup c.tag := (coxeterSystem c.tag).wordProd word with hv
    set PJ := (rootFinset c.tag).filter (fun γ => ∀ i : Fin c.tag.rank, i.val ∉ J₁ → γ i = 0)
      with hPJ
    set S1f := (rootFinset c.tag).filter (fun α => ∀ β ∈ rootFinset c.tag,
      (∀ i : Fin c.tag.rank, i.val ∉ c.J₂ → β i = 0) → iform α β = 0) with hS1f
    have himg : PJ.image (fun γ => v • γ) = S1f := by
      refine Finset.eq_of_subset_of_card_le ?_ ?_
      · intro α hα
        obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.1 hα
        obtain ⟨hγr, hγJ⟩ := Finset.mem_filter.1 hγ
        obtain ⟨hmem, horth⟩ := h2 γ hγr hγJ
        rw [hv, wordProd_smul_foldr]
        exact Finset.mem_filter.2 ⟨hmem, horth⟩
      · rw [Finset.card_image_of_injective _ (MulAction.injective v)]
        exact h3.ge
    refine fun α => ⟨fun hα => ?_, ?_⟩
    · have hα' : α ∈ S1f := Finset.mem_filter.2 ⟨mem_rootFinset.2 hα.1, fun β hβ hβJ =>
        hα.2 β ⟨mem_rootFinset.1 hβ, hβJ⟩⟩
      rw [← himg] at hα'
      obtain ⟨γ, hγ, hγα⟩ := Finset.mem_image.1 hα'
      obtain ⟨hγr, hγJ⟩ := Finset.mem_filter.1 hγ
      exact ⟨γ, ⟨mem_rootFinset.1 hγr, hγJ⟩, hγα⟩
    · rintro ⟨γ, ⟨hγ, hγJ⟩, rfl⟩
      obtain ⟨hmem, horth⟩ := h2 γ (mem_rootFinset.2 hγ) hγJ
      rw [hv, wordProd_smul_foldr]
      exact ⟨mem_rootFinset.1 hmem, fun β hβ => horth β (mem_rootFinset.2 hβ.1) hβ.2⟩

@[expose] def S₂Stable (τ : Tag) (J₂ : Finset ℕ) (word : List (Fin τ.rank)) : Prop :=
  ∀ α ∈ rootFinset τ, ((∀ i : Fin τ.rank, i.val ∉ J₂ → α i = 0) ↔
    (∀ i : Fin τ.rank, i.val ∉ J₂ → (word.foldr (reflect τ) α) i = 0))

theorem s₂Stable_f4 : S₂Stable Tag.F4 {2, 3} (wordOf .f4Six) := by
  unfold S₂Stable wordOf TwClass.wordF4; simp only [rootFinset, List.mem_toFinset]; decide +kernel

theorem s₂Stable_e6 : S₂Stable Tag.E6 {0, 2, 4, 5} (wordOf .e6Six) := by
  unfold S₂Stable wordOf TwClass.wordE6; simp only [rootFinset, List.mem_toFinset]; decide +kernel

theorem s₂Stable_e8Ten : S₂Stable Tag.E8 {0, 1, 2, 3} (wordOf .e8Ten) := by
  unfold S₂Stable wordOf TwClass.wordE8Ten; simp only [rootFinset, List.mem_toFinset]
  decide +kernel

theorem s₂Stable_e8Twelve : S₂Stable Tag.E8 {1, 2, 3, 4} (wordOf .e8Twelve) := by
  unfold S₂Stable wordOf TwClass.wordE8Twelve; simp only [rootFinset, List.mem_toFinset]
  decide +kernel

theorem s₂Stable (c : TwClass) : ∀ α : Fin c.tag.rank → ℤ, IsRoot c.tag α →
    (α ∈ c.S₂ ↔ c.w • α ∈ c.S₂) := by
  have key : S₂Stable c.tag c.J₂ (wordOf c) := by
    cases c
    · exact s₂Stable_f4
    · exact s₂Stable_e6
    · exact s₂Stable_e8Ten
    · exact s₂Stable_e8Twelve
  intro α hα
  rw [w_smul_eq_foldr]
  have h := key α (mem_rootFinset.2 hα)
  constructor
  · rintro ⟨-, h1⟩
    refine ⟨?_, h.1 h1⟩
    rw [← w_smul_eq_foldr]
    exact IsRoot.smul hα c.w
  · rintro ⟨-, h1⟩
    exact ⟨hα, h.2 h1⟩

theorem w_smul_mem_S₁_iff (c : TwClass) {α : Fin c.tag.rank → ℤ} (hα : IsRoot c.tag α) :
    c.w • α ∈ c.S₁ ↔ α ∈ c.S₁ := by
  have hS₂ := s₂Stable c
  constructor
  · rintro ⟨-, h⟩
    refine ⟨hα, fun β hβ => ?_⟩
    have hβ' : c.w • β ∈ c.S₂ := (hS₂ β hβ.1).1 hβ
    have := h _ hβ'
    rwa [iform_smul] at this
  · rintro ⟨-, h⟩
    refine ⟨IsRoot.smul hα c.w, fun β hβ => ?_⟩
    have hr : IsRoot c.tag (c.w⁻¹ • β) := IsRoot.smul hβ.1 c.w⁻¹
    have hβ' : c.w⁻¹ • β ∈ c.S₂ := by
      refine (hS₂ _ hr).2 ?_
      rw [smul_inv_smul]
      exact hβ
    have := h _ hβ'
    rw [← iform_smul c.w α, smul_inv_smul] at this
    exact this

theorem f4_not_isRoot_add : ∀ α ∈ rootFinset Tag.F4,
    (∀ β ∈ rootFinset Tag.F4, (∀ i : Fin Tag.F4.rank, i.val ∉ TwClass.f4Six.J₂ → β i = 0) →
      iform α β = 0) →
    ∀ β ∈ rootFinset Tag.F4, (∀ i : Fin Tag.F4.rank, i.val ∉ TwClass.f4Six.J₂ → β i = 0) →
      α + β ∉ rootFinset Tag.F4 := by
  decide +kernel

theorem not_isRoot_add_f4 {α β : Fin Tag.F4.rank → ℤ} (hα : α ∈ TwClass.f4Six.S₁)
    (hβ : β ∈ TwClass.f4Six.S₂) : ¬ IsRoot Tag.F4 (α + β) := fun h =>
  f4_not_isRoot_add α (mem_rootFinset.2 hα.1)
    (fun β' hβ' hs => hα.2 β' ⟨mem_rootFinset.1 hβ', hs⟩) β (mem_rootFinset.2 hβ.1) hβ.2
    (mem_rootFinset.2 h)

theorem rootSpan_commute (c : TwClass) (L : Type) [Field L] :
    ∀ x ∈ rootSpan c.tag L c.S₁, ∀ y ∈ rootSpan c.tag L c.S₂, x * y = y * x := by
  cases c with
  | f4Six =>
    refine rootSpan_commute_of_gen' fun α hα β hβ c d => ?_
    exact pinnedX_commute_of_iform_eq_zero L hα.1 hβ.1 (hα.2 β hβ) (not_isRoot_add_f4 hα hβ) c d
  | e6Six =>
    exact CFSG.RankThree.PartOne.KE.rootSpan_commute_of_orth (Or.inr (Or.inl rfl))
      (fun r hr => hr.1) (fun r hr => hr.1)
      (fun α hα β hβ => (dotProduct_mulVec_symmetrizedCartan_eq_sum α β).trans (hα.2 β hβ))
  | e8Ten =>
    exact CFSG.RankThree.PartOne.KE.rootSpan_commute_of_orth (Or.inr (Or.inr (Or.inr rfl)))
      (fun r hr => hr.1) (fun r hr => hr.1)
      (fun α hα β hβ => (dotProduct_mulVec_symmetrizedCartan_eq_sum α β).trans (hα.2 β hβ))
  | e8Twelve =>
    exact CFSG.RankThree.PartOne.KE.rootSpan_commute_of_orth (Or.inr (Or.inr (Or.inr rfl)))
      (fun r hr => hr.1) (fun r hr => hr.1)
      (fun α hα β hβ => (dotProduct_mulVec_symmetrizedCartan_eq_sum α β).trans (hα.2 β hβ))

end CoordsAux

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame
