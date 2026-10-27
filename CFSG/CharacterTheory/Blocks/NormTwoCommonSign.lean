module

public import CFSG.CharacterTheory.Blocks.NormTwoNonprincipal
public import CFSG.CharacterTheory.Blocks.NormTwoConnector

public noncomputable section

namespace CFSG

open TwoRankLowerBound.Helpers
open scoped BigOperators Classical

theorem blocksInnerProduct_irreducible_differences
    {G : Type} [Group G] [Fintype G] (a b c d : BlocksIrr G) :
    BlocksInnerProduct ((a : G → ℂ) - (b : G → ℂ))
        ((c : G → ℂ) - (d : G → ℂ)) =
      (if a = c then (1 : ℂ) else 0) - (if a = d then 1 else 0) -
        (if b = c then 1 else 0) + (if b = d then 1 else 0) := by
  have hp (x y : BlocksIrr G) : characterPairing (x : G → ℂ) (y : G → ℂ) =
      if x = y then 1 else 0 := by
    rw [← blocksInnerProduct_eq_characterPairing _ (AddSubgroup.subset_closure y.property)]
    exact blocksInnerProduct_irreducible x y
  rw [blocksInnerProduct_eq_characterPairing _ ((BlocksVChar G).sub_mem
    (AddSubgroup.subset_closure c.property) (AddSubgroup.subset_closure d.property)),
    characterPairing_sub_left, characterPairing_sub_right, characterPairing_sub_right,
    hp, hp, hp, hp]
  ring

theorem blocksIrr_differences_share_of_pairing_one
    {G : Type} [Group G] [Fintype G] (a b c d : BlocksIrr G)
    (hpair : BlocksInnerProduct ((a : G → ℂ) - (b : G → ℂ))
      ((c : G → ℂ) - (d : G → ℂ)) = 1) : a = c ∨ b = d := by
  by_cases hac : a = c
  · exact Or.inl hac
  by_cases hbd : b = d
  · exact Or.inr hbd
  rw [blocksInnerProduct_irreducible_differences] at hpair
  simp only [hac, hbd, ↓reduceIte, zero_sub, add_zero] at hpair
  split_ifs at hpair <;> norm_num at hpair

theorem pairwise_shared_pairs_have_common_coordinate
    {index label : Type*} [Nonempty index] (a b : index → label)
    (hshare : ∀ i j, i ≠ j → a i = a j ∨ b i = b j) :
    (∃ common, ∀ i, a i = common) ∨ (∃ common, ∀ i, b i = common) := by
  classical
  let base : index := Classical.arbitrary index
  by_cases ha : ∀ i, a i = a base
  · exact Or.inl ⟨a base, ha⟩
  obtain ⟨other, hother⟩ := not_forall.mp ha
  have hotherne : other ≠ base := by
    intro h
    exact hother (congrArg a h)
  have hb : b other = b base :=
    (hshare other base hotherne).resolve_left hother
  refine Or.inr ⟨b base, ?_⟩
  intro i
  by_cases hi : i = base
  · exact congrArg b hi
  by_cases hbi : b i = b base
  · exact hbi
  have hai : a i = a base := (hshare i base hi).resolve_right hbi
  have hione : i ≠ other := by
    intro h
    exact hother ((congrArg a h).symm.trans hai)
  rcases hshare i other hione with heq | heq
  · exact (hother (heq.symm.trans hai)).elim
  · exact heq.trans hb

theorem blocksVChar_norm_two_differences_common_sign
    {G : Type} [Group G] [Fintype G] {m : ℕ} (hm : 1 ≤ m)
    (f : Fin m → G → ℂ) (hf : ∀ i, f i ∈ BlocksVChar G)
    (hdegree : ∀ i, f i 1 = 0) (hprincipal : ∀ i, BlocksInnerProduct (f i) 1 = 0)
    (hgram : ∀ i j, BlocksInnerProduct (f i) (f j) =
      1 + if i = j then 1 else 0) :
    ∃ (χ : Fin (m + 1) → BlocksIrr G) (ε : ℤ), Function.Injective χ ∧
      (ε = 1 ∨ ε = -1) ∧ (∀ i, (χ i : G → ℂ) ≠ 1) ∧
      (∀ i, (χ i : G → ℂ) 1 = (χ 0 : G → ℂ) 1) ∧
      ∀ i, f i = (ε : ℂ) • ((χ i.succ : G → ℂ) - (χ 0 : G → ℂ)) := by
  let base : Fin m := ⟨0, hm⟩
  let : Nonempty (Fin m) := ⟨base⟩
  have hnorm (i : Fin m) : BlocksInnerProduct (f i) (f i) = 2 := by
    simpa only [↓reduceIte, one_add_one_eq_two] using hgram i i
  have hfinjective : Function.Injective f := by
    intro i j hequal
    by_contra hne
    have hpair := hgram i j
    rw [hequal, hnorm j] at hpair
    norm_num [hne] at hpair
  choose a b hab ha hb hdeg hrepresentation using fun i =>
    blocksVChar_degree_zero_norm_two_nonprincipal_difference
      (hf i) (hnorm i) (hdegree i) (hprincipal i)
  have hshare (i j : Fin m) (hne : i ≠ j) : a i = a j ∨ b i = b j := by
    apply blocksIrr_differences_share_of_pairing_one
    rw [← hrepresentation i, ← hrepresentation j]
    simpa only [hne, ↓reduceIte, add_zero] using hgram i j
  rcases pairwise_shared_pairs_have_common_coordinate a b hshare with
    ⟨common, hcommon⟩ | ⟨common, hcommon⟩
  · have hinj : Function.Injective b := by
      intro i j hequal
      apply hfinjective
      rw [hrepresentation i, hrepresentation j, hcommon i, hcommon j, hequal]
    have hnot : common ∉ Set.range b := by
      rintro ⟨i, hi⟩
      exact hab i ((hcommon i).trans hi.symm)
    refine ⟨Fin.cons common b, -1, Fin.cons_injective_of_injective hnot hinj,
      Or.inr rfl, ?_, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa only [Fin.cons_zero, ← hcommon base] using ha base
      · simpa only [Fin.cons_succ] using hb j
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · simpa only [Fin.cons_succ, Fin.cons_zero, ← hcommon j] using (hdeg j).symm
    · intro i
      simp only [Int.cast_neg, Int.cast_one, neg_one_smul, Fin.cons_succ, Fin.cons_zero,
        neg_sub]
      rw [hrepresentation i, hcommon i]
  · have hinj : Function.Injective a := by
      intro i j hequal
      apply hfinjective
      rw [hrepresentation i, hrepresentation j, hcommon i, hcommon j, hequal]
    have hnot : common ∉ Set.range a := by
      rintro ⟨i, hi⟩
      exact hab i (hi.trans (hcommon i).symm)
    refine ⟨Fin.cons common a, 1, Fin.cons_injective_of_injective hnot hinj,
      Or.inl rfl, ?_, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa only [Fin.cons_zero, ← hcommon base] using hb base
      · simpa only [Fin.cons_succ] using ha j
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · simpa only [Fin.cons_succ, Fin.cons_zero, ← hcommon j] using hdeg j
    · intro i
      simp only [Int.cast_one, one_smul, Fin.cons_succ, Fin.cons_zero]
      rw [hrepresentation i, hcommon i]

end CFSG
