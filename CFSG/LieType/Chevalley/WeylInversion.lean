module

public import CFSG.LieType.Chevalley.WeylExchange

public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley

variable {τ : Tag}

@[expose] def inversionSet
    (w : WeylGroup τ) : Set (Fin τ.rank → ℤ) :=
  {α | IsRoot τ α ∧ 0 < height α ∧ w • α ∈ {β | IsRoot τ β ∧ height β < 0}}

theorem inversionSet_finite
    (w : WeylGroup τ) : (inversionSet w).Finite :=
  (finite_setOf_isRoot τ).subset fun _ hα => hα.1

theorem inversionSet_one
    : inversionSet (1 : WeylGroup τ) = ∅ := by
  ext α
  simp only [inversionSet, one_smul, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨-, hpos, -, hneg⟩
  omega

theorem inversionSet_mul_simple
    {w : WeylGroup τ} {i : Fin τ.rank}
    (h : (coxeterSystem τ).length (w * simple τ i) = (coxeterSystem τ).length w + 1) :
    inversionSet (w * simple τ i) = insert (Pi.single i 1) (reflect τ i '' inversionSet w) ∧
      Pi.single i 1 ∉ reflect τ i '' inversionSet w := by
  have hnd : ¬ (coxeterSystem τ).IsRightDescent w i := fun hd => by
    rw [isRightDescent_iff_length] at hd
    omega
  have hroot := IsRoot.smul (isRoot_single τ i) w
  have hpos : 0 < height (w • (Pi.single i 1 : Fin τ.rank → ℤ)) :=
    ((mem_posRoots_iff_not_mem_negRoots hroot).2 fun hm =>
      hnd ((smul_single_mem_negRoots_iff w i).1 hm)).2
  have hnot : Pi.single i 1 ∉ reflect τ i '' inversionSet w := by
    rintro ⟨β, ⟨-, hβpos, -⟩, hβ⟩
    have : β = -Pi.single i 1 := by
      rw [← reflect_reflect τ i β, hβ, reflect_single_self]
    rw [this, height_neg, height_single] at hβpos
    omega
  refine ⟨Set.ext fun α => ?_, hnot⟩
  simp only [inversionSet, Set.mem_insert_iff, Set.mem_image, Set.mem_ofPred_eq, mul_smul,
    simple_smul]
  constructor
  · rintro ⟨hα, hαpos, -, hneg⟩
    by_cases hαi : α = Pi.single i 1
    · exact Or.inl hαi
    refine Or.inr ⟨reflect τ i α, ⟨(isRoot_reflect_iff i).2 hα,
      height_reflect_pos hα hαpos hαi, IsRoot.smul ((isRoot_reflect_iff i).2 hα) w, hneg⟩,
      reflect_reflect τ i α⟩
  · rintro (rfl | ⟨β, ⟨hβ, hβpos, -, hβneg⟩, rfl⟩)
    · refine ⟨isRoot_single τ i, by rw [height_single]; exact one_pos, ?_, ?_⟩
      · rw [reflect_single_self, smul_neg]
        exact IsRoot.neg hroot
      · rw [reflect_single_self, smul_neg, height_neg]
        omega
    · have hβi : β ≠ Pi.single i 1 := by
        rintro rfl
        omega
      refine ⟨(isRoot_reflect_iff i).2 hβ, height_reflect_pos hβ hβpos hβi, ?_, ?_⟩
      · rw [reflect_reflect]
        exact IsRoot.smul hβ w
      · rw [reflect_reflect]
        exact hβneg

theorem weyl_inversion_length
    (τ : Tag) :
    (∀ w : WeylGroup τ, (coxeterSystem τ).length w = (inversionSet w).ncard) ∧
    ∀ (w : WeylGroup τ) (i : Fin τ.rank),
      (coxeterSystem τ).length (w * simple τ i) = (coxeterSystem τ).length w + 1 →
        inversionSet (w * simple τ i) = insert (Pi.single i 1) (reflect τ i '' inversionSet w) ∧
          Pi.single i 1 ∉ reflect τ i '' inversionSet w := by
  refine ⟨fun w => ?_, fun w i h => inversionSet_mul_simple h⟩
  induction h : (coxeterSystem τ).length w generalizing w with
  | zero =>
    rw [(coxeterSystem τ).length_eq_zero_iff.1 h, inversionSet_one, Set.ncard_empty]
  | succ n ih =>
    have hw : w ≠ 1 := fun h1 => by
      rw [h1, (coxeterSystem τ).length_one] at h
      omega
    obtain ⟨i, hi⟩ := (coxeterSystem τ).exists_rightDescent_of_ne_one hw
    rw [isRightDescent_iff_length] at hi
    set w' := w * simple τ i with hw'
    have hlen : (coxeterSystem τ).length w' = n := by omega
    have hww : w' * simple τ i = w := by rw [hw', mul_assoc, simple_mul_simple_self, mul_one]
    have hl : (coxeterSystem τ).length (w' * simple τ i) =
        (coxeterSystem τ).length w' + 1 := by rw [hww]; omega
    obtain ⟨heq, hnot⟩ := inversionSet_mul_simple hl
    rw [← hww, heq, Set.ncard_insert_of_notMem hnot ((inversionSet_finite w').image _),
      Set.ncard_image_of_injective _ (fun u v huv => by
        rw [← reflect_reflect τ i u, huv, reflect_reflect]), ← ih w' hlen]

end CFSG.LieType.Chevalley
