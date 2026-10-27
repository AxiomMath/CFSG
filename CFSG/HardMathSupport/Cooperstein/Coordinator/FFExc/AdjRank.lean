module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc.FilteredRank
public import CFSG.Blueprint.ChevalleyRootArtifact

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc

open CFSG.Blueprint.Chevalley Module

variable {τ : Tag} {K : Type*} [Field K]

theorem rootVec_eq_single' {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) :
    rootVec τ K β = Finsupp.single (Sum.inr ⟨β, hβ⟩) 1 :=
  dite_eq_left hβ

theorem stringDown_eq_zero {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) (i : Fin τ.rank)
    (h₁ : α ≠ Pi.single i 1) (h₂ : α ≠ -Pi.single i 1) (hnot : ¬ IsRoot τ (α - Pi.single i 1)) :
    stringDown τ i α = 0 := by
  obtain ⟨-, h⟩ := isRoot_add_smul_single_iff hα i h₁ h₂
  by_contra hq
  apply hnot
  have h0 := (h 0).1 (by simpa using hα)
  have := (h (-1)).2 ⟨by omega, by omega⟩
  simpa [sub_eq_add_neg] using this

open Classical in
theorem card_add_two_le_finrank_infE (j l0 : Fin τ.rank) (hl0 : τ.cartan l0 j = -1)
    (Rj : Finset (Fin τ.rank → ℤ))
    (hRj : ∀ β, β ∈ Rj ↔ IsRoot τ β ∧ β ≠ Pi.single j 1 ∧ β ≠ -Pi.single j 1 ∧
      IsRoot τ (β + Pi.single j 1))
    (hq : ∀ β ∈ Rj, ¬ IsRoot τ (β - Pi.single j 1)) :
    Rj.card + 2 ≤ finrank K (LinearMap.range (infE τ K j)) := by
  have : Fintype (Label τ) := Fintype.ofFinite _
  let lab : (Fin τ.rank → ℤ) → Label τ := fun β =>
    if h : IsRoot τ β then Sum.inr ⟨β, h⟩ else Sum.inl j
  have hlab : ∀ {β} (h : IsRoot τ β), lab β = Sum.inr ⟨β, h⟩ := fun h => dite_eq_left h
  have hlabinj : ∀ {β δ}, IsRoot τ β → IsRoot τ δ → lab β = lab δ → β = δ := by
    intro β δ hβ hδ h
    rw [hlab hβ, hlab hδ] at h
    exact congrArg Subtype.val (Sum.inr.inj h)
  let σ : Label τ → Label τ := fun b =>
    match b with
    | Sum.inl _ => lab (Pi.single j 1)
    | Sum.inr α => if α.1 = -Pi.single j 1 then Sum.inl j else lab (α.1 + Pi.single j 1)
  have hneg : IsRoot τ (-Pi.single j 1 : Fin τ.rank → ℤ) := isRoot_neg_single τ j
  have hpos : IsRoot τ (Pi.single j 1 : Fin τ.rank → ℤ) := isRoot_single τ j
  have hnegRj : (-Pi.single j 1 : Fin τ.rank → ℤ) ∉ Rj := fun h => ((hRj _).1 h).2.2.1 rfl
  let S : Finset (Label τ) := insert (Sum.inl l0) (insert (lab (-Pi.single j 1)) (Rj.image lab))
  have hlabRj : ∀ β ∈ Rj, IsRoot τ β := fun β h => ((hRj β).1 h).1
  have hinjR : Set.InjOn lab Rj := fun β hβ δ hδ h => hlabinj (hlabRj β hβ) (hlabRj δ hδ) h
  have hnotin1 : lab (-Pi.single j 1) ∉ Rj.image lab := by
    intro h
    obtain ⟨β, hβ, hβe⟩ := Finset.mem_image.1 h
    exact hnegRj (hlabinj hneg (hlabRj β hβ) hβe.symm ▸ hβ)
  have hnotin0 : (Sum.inl l0 : Label τ) ∉ insert (lab (-Pi.single j 1)) (Rj.image lab) := by
    intro h
    rcases Finset.mem_insert.1 h with h | h
    · rw [hlab hneg] at h; exact Sum.inl_ne_inr h
    · obtain ⟨β, hβ, hβe⟩ := Finset.mem_image.1 h
      rw [hlab (hlabRj β hβ)] at hβe; exact Sum.inl_ne_inr hβe.symm
  have hcard : S.card = Rj.card + 2 := by
    rw [Finset.card_insert_of_notMem hnotin0, Finset.card_insert_of_notMem hnotin1,
      Finset.card_image_of_injOn hinjR]
  have hσR : ∀ β ∈ Rj, σ (lab β) = lab (β + Pi.single j 1) := by
    intro β hβ
    have hb := hlabRj β hβ
    rw [hlab hb]
    simp only [σ]
    rw [ite_eq_right ((hRj β).1 hβ).2.2.1]
  have hσneg : σ (lab (-Pi.single j 1)) = Sum.inl j := by
    rw [hlab hneg]; simp [σ]
  have hσ0 : σ (Sum.inl l0) = lab (Pi.single j 1) := rfl
  have hRrt : ∀ β ∈ Rj, IsRoot τ (β + Pi.single j 1) := fun β h => ((hRj β).1 h).2.2.2
  have hσinj : Set.InjOn σ S := by
    intro a ha b hb hab
    simp only [S, Finset.coe_insert, Finset.coe_image, Set.mem_insert_iff, Set.mem_image,
      Finset.mem_coe] at ha hb
    have hne0 : ∀ β ∈ Rj, β + Pi.single j 1 ≠ Pi.single j 1 := by
      intro β hβ h
      have : β = 0 := by simpa using h
      exact ((hlabRj β hβ).ne_zero) this
    rcases ha with rfl | rfl | ⟨β, hβ, rfl⟩ <;> rcases hb with rfl | rfl | ⟨δ, hδ, rfl⟩
    · rfl
    · rw [hσ0, hσneg, hlab hpos] at hab; exact absurd hab (by simp)
    · rw [hσ0, hσR δ hδ, hlab hpos, hlab (hRrt δ hδ)] at hab
      exact absurd (congrArg Subtype.val (Sum.inr.inj hab)).symm (hne0 δ hδ)
    · rw [hσ0, hσneg, hlab hpos] at hab; exact absurd hab.symm (by simp)
    · rfl
    · rw [hσneg, hσR δ hδ, hlab (hRrt δ hδ)] at hab; exact absurd hab (by simp)
    · rw [hσ0, hσR β hβ, hlab hpos, hlab (hRrt β hβ)] at hab
      exact absurd (congrArg Subtype.val (Sum.inr.inj hab)) (hne0 β hβ)
    · rw [hσneg, hσR β hβ, hlab (hRrt β hβ)] at hab; exact absurd hab.symm (by simp)
    · rw [hσR β hβ, hσR δ hδ, hlab (hRrt β hβ), hlab (hRrt δ hδ)] at hab
      have := congrArg Subtype.val (Sum.inr.inj hab)
      have hβδ : β = δ := add_right_cancel this
      rw [hβδ]
  have hE : ∀ b ∈ S, infE τ K j (Finsupp.single b 1) =
      (fun _ => (1 : K)) b • Finsupp.single (σ b) 1 := by
    intro b hb
    simp only [S, Finset.mem_insert, Finset.mem_image] at hb
    rcases hb with rfl | rfl | ⟨β, hβ, rfl⟩
    · have h := infE_hVec (τ := τ) (R := K) j l0
      change infE τ K j (hVec τ K l0) = _
      rw [h, hl0, hσ0, hlab hpos, rootVec_eq_single' hpos]
      simp
    · rw [hlab hneg, ← rootVec_eq_single' hneg, infE_rootVec_neg_single, ← hlab hneg, hσneg]
      simp [hVec]
    · have hb := hlabRj β hβ
      obtain ⟨-, h₁, h₂, -⟩ := (hRj β).1 hβ
      rw [hlab hb, ← rootVec_eq_single' hb, infE_rootVec_of_ne j hb h₁ h₂,
        stringDown_eq_zero hb j h₁ h₂ (hq β hβ), ← hlab hb, hσR β hβ, hlab (hRrt β hβ),
        rootVec_eq_single' (hRrt β hβ)]
      simp
  have := card_le_finrank_range_of_perm (infE τ K j) S σ (fun _ => (1 : K)) hσinj
    (fun _ _ => one_ne_zero) hE
  rwa [hcard] at this

@[expose] def toVec (n : ℕ) (l : List ℤ) : Fin n → ℤ := fun i => l.getD i 0

theorem toVec_ofFn {n : ℕ} (γ : Fin n → ℤ) : toVec n (List.ofFn γ) = γ := by
  funext i; simp [toVec]

theorem ofFn_toVec {n : ℕ} {l : List ℤ} (h : l.length = n) : List.ofFn (toVec n l) = l := by
  subst h
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    simp [toVec, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₂]

theorem zipWith_add_ofFn' {n : ℕ} (a b : Fin n → ℤ) :
    List.zipWith (· + ·) (List.ofFn a) (List.ofFn b) = List.ofFn (a + b) := by
  apply List.ext_getElem <;> simp

theorem zipWith_sub_ofFn' {n : ℕ} (a b : Fin n → ℤ) :
    List.zipWith (· - ·) (List.ofFn a) (List.ofFn b) = List.ofFn (a - b) := by
  apply List.ext_getElem <;> simp

@[expose] def eL (τ : Tag) (j : Fin τ.rank) : List ℤ := List.ofFn (Pi.single j 1 : Fin τ.rank → ℤ)

@[expose] def nL (τ : Tag) (j : Fin τ.rank) : List ℤ := List.ofFn (-Pi.single j 1 : Fin τ.rank → ℤ)

@[expose] def Lj (τ : Tag) (j : Fin τ.rank) : List (List ℤ) :=
  τ.artifactRoots.filter fun l => decide (l ≠ eL τ j) && decide (l ≠ nL τ j) &&
    decide (List.zipWith (· + ·) l (eL τ j) ∈ τ.artifactRoots)

@[expose] def JOk (τ : Tag) (j : Fin τ.rank) (N : ℕ) : Prop :=
  (Lj τ j).length = N ∧
    (∀ l ∈ Lj τ j, List.zipWith (· - ·) l (eL τ j) ∉ τ.artifactRoots) ∧
    ∃ l0 : Fin τ.rank, τ.cartan l0 j = -1

instance (τ : Tag) (j : Fin τ.rank) (N : ℕ) : Decidable (JOk τ j N) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem jOk_E6 : ∀ j : Fin Tag.E6.rank, JOk .E6 j 20 := by decide +kernel
theorem jOk_E7 : ∀ j : Fin Tag.E7.rank, JOk .E7 j 32 := by decide +kernel
theorem finrank_infE_ge (τ : Tag) (j : Fin τ.rank) (N : ℕ) (h : JOk τ j N) :
    N + 2 ≤ finrank K (LinearMap.range (infE τ K j)) := by
  classical
  obtain ⟨hN, hq, l0, hl0⟩ := h
  let Rj : Finset (Fin τ.rank → ℤ) := (Lj τ j).toFinset.image (toVec τ.rank)
  have hmemL : ∀ l ∈ Lj τ j, l ∈ τ.artifactRoots := fun l hl => (List.mem_filter.1 hl).1
  have hlen : ∀ l ∈ Lj τ j, l.length = τ.rank := fun l hl => length_of_mem_artifactRoots (hmemL l hl)
  have hinj : Set.InjOn (toVec τ.rank) ((Lj τ j).toFinset : Set (List ℤ)) := by
    intro l hl l' hl' h
    rw [← ofFn_toVec (hlen l (List.mem_toFinset.1 hl)), ← ofFn_toVec (hlen l' (List.mem_toFinset.1 hl')), h]
  have hcard : Rj.card = N := by
    rw [Finset.card_image_of_injOn hinj, List.toFinset_card_of_nodup, hN]
    exact (nodup_artifactRoots τ).filter _
  have hRj : ∀ β, β ∈ Rj ↔ IsRoot τ β ∧ β ≠ Pi.single j 1 ∧ β ≠ -Pi.single j 1 ∧
      IsRoot τ (β + Pi.single j 1) := by
    intro β
    simp only [Rj, Finset.mem_image, List.mem_toFinset]
    constructor
    · rintro ⟨l, hl, rfl⟩
      have hl' := List.mem_filter.1 hl
      have hlen' := hlen l hl
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hl'
      obtain ⟨hlr, ⟨h1, h2⟩, h3⟩ := hl'
      have hof := ofFn_toVec hlen'
      refine ⟨isRoot_iff_mem_artifactRoots.2 (by rw [hof]; exact hlr), ?_, ?_, ?_⟩
      · intro h; apply h1; rw [← hof, h]; rfl
      · intro h; apply h2; rw [← hof, h]; rfl
      · rw [isRoot_iff_mem_artifactRoots, ← zipWith_add_ofFn', hof]; exact h3
    · rintro ⟨hr, h1, h2, h3⟩
      refine ⟨List.ofFn β, ?_, toVec_ofFn β⟩
      rw [Lj, List.mem_filter]
      refine ⟨isRoot_iff_mem_artifactRoots.1 hr, ?_⟩
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨⟨fun h => h1 (List.ofFn_injective h), fun h => h2 (List.ofFn_injective h)⟩, ?_⟩
      rw [eL, zipWith_add_ofFn']
      exact isRoot_iff_mem_artifactRoots.1 h3
  have hqR : ∀ β ∈ Rj, ¬ IsRoot τ (β - Pi.single j 1) := by
    intro β hβ
    simp only [Rj, Finset.mem_image, List.mem_toFinset] at hβ
    obtain ⟨l, hl, rfl⟩ := hβ
    rw [isRoot_iff_mem_artifactRoots, ← zipWith_sub_ofFn', ofFn_toVec (hlen l hl)]
    exact hq l hl
  have := card_add_two_le_finrank_infE (K := K) j l0 hl0 Rj hRj hqR
  rwa [hcard] at this

theorem finrank_infE_E6 (j : Fin Tag.E6.rank) :
    22 ≤ finrank K (LinearMap.range (infE .E6 K j)) := by
  have := finrank_infE_ge (K := K) .E6 j 20 (jOk_E6 j); omega

theorem finrank_infE_E7 (j : Fin Tag.E7.rank) :
    34 ≤ finrank K (LinearMap.range (infE .E7 K j)) := by
  have := finrank_infE_ge (K := K) .E7 j 32 (jOk_E7 j); omega

end CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc
