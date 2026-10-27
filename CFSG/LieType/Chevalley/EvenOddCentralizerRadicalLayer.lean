module

public import CFSG.LieType.Chevalley.EvenOddCentralizerRadicalLevels
public import CFSG.LieType.Chevalley.EvenOddCentralizerRadicalRoots

public noncomputable section

namespace CFSG.LieType.Chevalley.EvenOddRadical

open CFSG.Blueprint.Chevalley
open scoped commutatorElement

variable {τ : Tag} {K : Type} [Field K]

variable (τ) in
@[expose] def layerRoots (J : Set (Fin τ.rank)) (d : ℤ) : Set (Fin τ.rank → ℤ) :=
  {α | IsRoot τ α ∧ 0 < height α ∧ parabolicDegree τ J α = d}

theorem layerRoots_subset (J : Set (Fin τ.rank)) (d : ℤ) :
    layerRoots τ J d ⊆ levelRoots τ J d :=
  fun _ hα => ⟨hα.1, hα.2.1, hα.2.2.ge⟩

theorem levelRoots_eq_union (J : Set (Fin τ.rank)) (d : ℤ) :
    levelRoots τ J d = layerRoots τ J d ∪ levelRoots τ J (d + 1) := by
  ext α
  simp only [levelRoots, layerRoots, Set.mem_union, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2, h3⟩
    rcases h3.eq_or_lt with h | h
    · exact Or.inl ⟨h1, h2, h.symm⟩
    · exact Or.inr ⟨h1, h2, h⟩
  · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
    · exact ⟨h1, h2, h3.ge⟩
    · exact ⟨h1, h2, by omega⟩

theorem disjoint_layerRoots (J : Set (Fin τ.rank)) (d : ℤ) :
    Disjoint (layerRoots τ J d) (levelRoots τ J (d + 1)) :=
  Set.disjoint_left.2 fun _ h h' => by have := h.2.2; have := h'.2.2; omega

theorem ncard_levelRoots
    (J : Set (Fin τ.rank)) (d : ℤ) :
    (levelRoots τ J d).ncard = (layerRoots τ J d).ncard + (levelRoots τ J (d + 1)).ncard := by
  rw [levelRoots_eq_union J d]
  exact Set.ncard_union_eq (disjoint_layerRoots J d)
    ((finite_setOf_isRoot τ).subset fun _ h => h.1)
    ((finite_setOf_isRoot τ).subset fun _ h => h.1)

theorem height_pos_of_degree
    {J : Set (Fin τ.rank)} {α : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (hd : 1 ≤ parabolicDegree τ J α) : 0 < height α := by
  rcases IsRoot.height_pos_or_neg hα with h | h
  · exact h
  · exfalso
    have hle := (IsRoot.height_neg_iff hα).1 h
    have : parabolicDegree τ J α ≤ 0 :=
      Finset.sum_nonpos fun i _ => by split_ifs; exacts [le_rfl, hle i]
    omega

theorem levelRadical_succ_le
    (J : Set (Fin τ.rank)) (d : ℤ) :
    levelRadical τ K J (d + 1) ≤ levelRadical τ K J d :=
  levelRadical_anti J (by omega)

instance normal_levelRadical_succ
    (J : Set (Fin τ.rank)) (d : ℤ) :
    ((levelRadical τ K J (d + 1)).subgroupOf (levelRadical τ K J d)).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (levelRadical_succ_le J d)).2
    ((levelRadical_le_posUnipotent J d).trans (le_sup_right.trans
      (borelGroup_le_normalizer J (d + 1))))

variable (τ K) in
abbrev Layer
    (J : Set (Fin τ.rank)) (n : ℕ) : Type :=
  ↥(levelRadical τ K J (n + 1)) ⧸
    (levelRadical τ K J (n + 1 + 1)).subgroupOf (levelRadical τ K J (n + 1))

theorem layer_mul_comm
    (J : Set (Fin τ.rank)) (n : ℕ) (a b : Layer τ K J n) :
    a * b = b * a := by
  induction a using QuotientGroup.induction_on with | _ a => ?_
  induction b using QuotientGroup.induction_on with | _ b => ?_
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
  have h1 : (((a * b)⁻¹ * (b * a) : levelRadical τ K J (n + 1)) : ModGL τ K) =
      ⁅((b⁻¹ : levelRadical τ K J (n + 1)) : ModGL τ K), ((a⁻¹ : levelRadical τ K J (n + 1)) :
        ModGL τ K)⁆ := by
    simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [h1]
  have h2 := commutator_levelRadical_le (K := K) J (n + 1) (n + 1)
    (Subgroup.commutator_mem_commutator (b⁻¹ : levelRadical τ K J (n + 1)).2
      (a⁻¹ : levelRadical τ K J (n + 1)).2)
  exact levelRadical_anti J (by omega : (n : ℤ) + 1 + 1 ≤ n + 1 + (n + 1)) h2

instance layerCommGroup
    (J : Set (Fin τ.rank)) (n : ℕ) : CommGroup (Layer τ K J n) :=
  { (QuotientGroup.Quotient.group _ : Group (Layer τ K J n)) with
    mul_comm := layer_mul_comm J n }

open _root_.Classical in
@[expose] def layerFactor
    (J : Set (Fin τ.rank)) (n : ℕ) (β : {v // IsRoot τ v}) (c : K) :
    Layer τ K J n :=
  if h : β.1 ∈ layerRoots τ J (n + 1) then
    QuotientGroup.mk (⟨pinnedX τ K β.1 c, pinnedX_mem_levelRadical
      (layerRoots_subset J (n + 1) h) c⟩ : levelRadical τ K J (n + 1))
  else 1

theorem layerFactor_add
    (J : Set (Fin τ.rank)) (n : ℕ) (β : {v // IsRoot τ v}) (c c' : K) :
    layerFactor J n β (c + c') = layerFactor J n β c * layerFactor J n β c' := by
  unfold layerFactor
  split_ifs with h
  · rw [← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext (pinnedX_add τ K β.1 c c')
  · rw [mul_one]

theorem layerFactor_zero
    (J : Set (Fin τ.rank)) (n : ℕ) (β : {v // IsRoot τ v}) :
    layerFactor J n β (0 : K) = 1 := by
  unfold layerFactor
  split_ifs with h
  · have : (⟨pinnedX τ K β.1 0, pinnedX_mem_levelRadical (layerRoots_subset J (n + 1) h) 0⟩ :
        levelRadical τ K J (n + 1)) = 1 := Subtype.ext (pinnedX_zero τ K β.1)
    rw [this, QuotientGroup.mk_one]
  · rfl

@[expose] def layerMap
    (J : Set (Fin τ.rank)) (n : ℕ) (x : RootModule τ K) :
    Layer τ K J n :=
  ∏ β : {v // IsRoot τ v}, layerFactor J n β (x (Sum.inr β))

theorem layerMap_add
    (J : Set (Fin τ.rank)) (n : ℕ) (x y : RootModule τ K) :
    layerMap J n (x + y) = layerMap J n x * layerMap J n y := by
  simp only [layerMap, Finsupp.add_apply, layerFactor_add]
  exact Finset.prod_mul_distrib

theorem layerMap_zero
    (J : Set (Fin τ.rank)) (n : ℕ) :
    layerMap J n (0 : RootModule τ K) = 1 := by
  simp only [layerMap, Finsupp.coe_zero, Pi.zero_apply, layerFactor_zero]
  exact Finset.prod_const_one

theorem layerMap_neg
    (J : Set (Fin τ.rank)) (n : ℕ) (x : RootModule τ K) :
    layerMap J n (-x) = (layerMap J n x)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← layerMap_add, neg_add_cancel, layerMap_zero]

theorem layerMap_sum
    (J : Set (Fin τ.rank)) (n : ℕ) {ι : Type*} (s : Finset ι)
    (f : ι → RootModule τ K) :
    layerMap J n (∑ i ∈ s, f i) = ∏ i ∈ s, layerMap J n (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [layerMap_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, layerMap_add, ih]

theorem layerMap_smul_rootVec
    (J : Set (Fin τ.rank)) (n : ℕ) {β : Fin τ.rank → ℤ}
    (hβ : β ∈ layerRoots τ J (n + 1)) (c : K) :
    layerMap J n (c • rootVec τ K β) =
      QuotientGroup.mk (⟨pinnedX τ K β c, pinnedX_mem_levelRadical
        (layerRoots_subset J (n + 1) hβ) c⟩ : levelRadical τ K J (n + 1)) := by
  rw [layerMap, Finset.prod_eq_single (⟨β, hβ.1⟩ : {v // IsRoot τ v})]
  · rw [rootVec_of_isRoot hβ.1, Finsupp.smul_single, smul_eq_mul, mul_one,
      Finsupp.single_eq_same, layerFactor, dite_eq_left hβ]
  · intro γ _ hγ
    rw [rootVec_of_isRoot hβ.1, Finsupp.smul_single, smul_eq_mul, mul_one,
      Finsupp.single_eq_of_ne (fun h => hγ (Sum.inr_injective h)), layerFactor_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem layerMap_smul_rootVec_of_ne
    (J : Set (Fin τ.rank)) (n : ℕ) {β : Fin τ.rank → ℤ}
    (hβ : IsRoot τ β) (hne : parabolicDegree τ J β ≠ n + 1) (c : K) :
    layerMap J n (c • rootVec τ K β) = 1 := by
  refine Finset.prod_eq_one fun γ _ => ?_
  rw [rootVec_of_isRoot hβ, Finsupp.smul_single, smul_eq_mul, mul_one]
  by_cases hγ : (Sum.inr γ : Label τ) = Sum.inr ⟨β, hβ⟩
  · rw [hγ, Finsupp.single_eq_same, layerFactor, dite_eq_right]
    intro h
    have hγβ : γ.1 = β := congrArg Subtype.val (Sum.inr_injective hγ)
    have := h.2.2
    rw [hγβ] at this
    exact hne this
  · rw [Finsupp.single_eq_of_ne hγ, layerFactor_zero]

theorem layerMap_smul_rootVec_of_not
    (J : Set (Fin τ.rank)) (n : ℕ) {β : Fin τ.rank → ℤ}
    (hβ : ¬IsRoot τ β) (c : K) : layerMap J n (c • rootVec τ K β) = 1 := by
  rw [rootVec_of_not hβ, smul_zero, layerMap_zero]

theorem rootVec_mem_parabolicGraded {J : Set (Fin τ.rank)} {d : ℤ} {β : Fin τ.rank → ℤ}
    (hβ : IsRoot τ β) (hd : parabolicDegree τ J β = d) :
    rootVec τ K β ∈ parabolicGraded τ K J d :=
  Submodule.subset_span (Or.inl ⟨β, hβ, hd, rfl⟩)

theorem mem_layerRoots_of_mem_gradedLabels
    {J : Set (Fin τ.rank)} {n : ℕ} {b : Label τ}
    (hb : b ∈ gradedLabels τ J (n + 1)) :
    ∃ α : Fin τ.rank → ℤ, ∃ hα : α ∈ layerRoots τ J (n + 1), b = Sum.inr ⟨α, hα.1⟩ := by
  rcases b with i | ⟨α, hα⟩
  · exfalso
    simp only [gradedLabels, Set.mem_ofPred_eq, labelWt, parabolicDegree_zero] at hb
    omega
  · simp only [gradedLabels, Set.mem_ofPred_eq, labelWt] at hb
    exact ⟨α, ⟨hα, height_pos_of_degree (J := J) hα (by omega), hb⟩, rfl⟩

theorem exists_layerMap_eq
    (J : Set (Fin τ.rank)) (n : ℕ) (ℓ : Layer τ K J n) :
    ∃ x ∈ parabolicGraded τ K J (n + 1), layerMap J n x = ℓ := by
  induction ℓ using QuotientGroup.induction_on with | _ u => ?_
  obtain ⟨u, hu⟩ := u
  have hu' := hu
  rw [levelRadical_eq_closure] at hu'
  induction hu' using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨γ, hγ, c, rfl⟩ := hg
    rcases hγ.2.2.eq_or_lt with h | h
    · have hγ' : γ ∈ layerRoots τ J (n + 1) := ⟨hγ.1, hγ.2.1, h.symm⟩
      exact ⟨c • rootVec τ K γ, Submodule.smul_mem _ _ (rootVec_mem_parabolicGraded hγ.1 h.symm),
        layerMap_smul_rootVec J n hγ' c⟩
    · refine ⟨0, Submodule.zero_mem _, ?_⟩
      rw [layerMap_zero]
      symm
      rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact pinnedX_mem_levelRadical ⟨hγ.1, hγ.2.1, by omega⟩ c
  | one =>
    exact ⟨0, Submodule.zero_mem _, by rw [layerMap_zero]; rfl⟩
  | mul g h hg hh ihg ihh =>
    have hgQ : g ∈ levelRadical τ K J (n + 1) := by rw [levelRadical_eq_closure]; exact hg
    have hhQ : h ∈ levelRadical τ K J (n + 1) := by rw [levelRadical_eq_closure]; exact hh
    obtain ⟨x, hx, hxe⟩ := ihg hgQ
    obtain ⟨y, hy, hye⟩ := ihh hhQ
    refine ⟨x + y, Submodule.add_mem _ hx hy, ?_⟩
    rw [layerMap_add, hxe, hye, ← QuotientGroup.mk_mul]
    rfl
  | inv g hg ihg =>
    have hgQ : g ∈ levelRadical τ K J (n + 1) := by rw [levelRadical_eq_closure]; exact hg
    obtain ⟨x, hx, hxe⟩ := ihg hgQ
    refine ⟨-x, Submodule.neg_mem _ hx, ?_⟩
    rw [layerMap_neg, hxe, ← QuotientGroup.mk_inv]
    rfl

end CFSG.LieType.Chevalley.EvenOddRadical
