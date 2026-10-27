module

public import CFSG.LieType.Chevalley.SimpleBruhatMultiplication
public import CFSG.LieType.Chevalley.BorelWeylGeneration
public import CFSG.LieType.Chevalley.BorelWeylIntersection
public import Mathlib.GroupTheory.DoubleCoset

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley
open scoped Pointwise

variable {τ : Tag} {K : Type} [Field K]

theorem bruhatCell_eq_doubleCoset
    (w : WeylGroup τ) :
    bruhatCell τ K w = DoubleCoset.doubleCoset (canonicalRep (coxeterSystem τ) K w)
      (borelGroup τ K : Set (ModGL τ K)) (borelGroup τ K) :=
  rfl

theorem canonicalRep_mem_bruhatCell
    (w : WeylGroup τ) :
    canonicalRep (coxeterSystem τ) K w ∈ bruhatCell τ K w :=
  DoubleCoset.mem_doubleCoset_self _ _ _

theorem one_mem_bruhatCell_one
    : (1 : ModGL τ K) ∈ bruhatCell τ K 1 := by
  have h := canonicalRep_mem_bruhatCell (K := K) (τ := τ) 1
  rwa [canonicalRep_one] at h

theorem doubleCoset_eq_bruhatCell_of_mem
    {w : WeylGroup τ} {x : ModGL τ K}
    (hx : x ∈ bruhatCell τ K w) :
    (borelGroup τ K : Set (ModGL τ K)) * {x} * (borelGroup τ K : Set (ModGL τ K)) =
      bruhatCell τ K w :=
  DoubleCoset.doubleCoset_eq_of_mem hx

theorem bruhatCell_eq_of_mem
    {w v : WeylGroup τ} {x : ModGL τ K} (hw : x ∈ bruhatCell τ K w)
    (hv : x ∈ bruhatCell τ K v) : bruhatCell τ K w = bruhatCell τ K v :=
  (doubleCoset_eq_bruhatCell_of_mem hw).symm.trans (doubleCoset_eq_bruhatCell_of_mem hv)

theorem bruhatCell_simple_mul_subset
    (i : Fin τ.rank) (w : WeylGroup τ) :
    bruhatCell τ K (simple τ i) * bruhatCell τ K w ⊆
      bruhatCell τ K (simple τ i * w) ∪ bruhatCell τ K w := by
  rcases length_simple_mul_cases w i with h | h
  · rw [bruhatCell_simple_mul_of_length_eq_add_one h]
    exact Set.subset_union_left
  · rw [bruhatCell_simple_mul_of_length_eq_sub_one (by omega)]

theorem smul_set_eq_of_forall {G : Type*} [Group G] {g : G} {X : Set G}
    (h₁ : ∀ x ∈ X, g * x ∈ X) (h₂ : ∀ x ∈ X, g⁻¹ * x ∈ X) : g • X = X := by
  refine Set.Subset.antisymm (Set.smul_set_subset_iff.2 fun x hx => h₁ x hx) ?_
  rw [Set.subset_smul_set_iff]
  exact Set.smul_set_subset_iff.2 fun x hx => h₂ x hx

theorem adjointGroup_eq_iUnion_bruhatCell :
    (adjointGroup τ K : Set (ModGL τ K)) = ⋃ w, bruhatCell τ K w := by
  refine Set.Subset.antisymm (fun g hg => ?_)
    (Set.iUnion_subset fun w => bruhatCell_subset_adjointGroup w)
  set X := ⋃ w, bruhatCell τ K w
  have hB : ∀ b ∈ borelGroup τ K, ∀ x ∈ X, b * x ∈ X := fun b hb x hx => by
    obtain ⟨w, hw⟩ := Set.mem_iUnion.1 hx
    obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := mem_bruhatCell.1 hw
    exact Set.mem_iUnion.2 ⟨w, mem_bruhatCell.2 ⟨b * b₁, mul_mem hb hb₁, b₂, hb₂, by group⟩⟩
  have hn : ∀ i, ∀ x ∈ X, weylElt τ K i 1 * x ∈ X := fun i x hx => by
    obtain ⟨w, hw⟩ := Set.mem_iUnion.1 hx
    have hmem : weylElt τ K i 1 * x ∈ bruhatCell τ K (simple τ i) * bruhatCell τ K w := by
      refine Set.mem_mul.2 ⟨_, ?_, x, hw, rfl⟩
      rw [← canonicalRep_simple (coxeterSystem τ) K i]
      exact canonicalRep_mem_bruhatCell _
    rcases bruhatCell_simple_mul_subset i w hmem with h | h
    exacts [Set.mem_iUnion.2 ⟨_, h⟩, Set.mem_iUnion.2 ⟨_, h⟩]
  have hS : adjointGroup τ K ≤ MulAction.stabilizer (ModGL τ K) X := by
    rw [(borel_weyl_generation τ K).1]
    refine sup_le (fun b hb => ?_) ((Subgroup.closure_le _).2 ?_)
    · exact smul_set_eq_of_forall (hB b hb) (hB b⁻¹ (inv_mem hb))
    · rintro _ ⟨i, rfl⟩
      refine smul_set_eq_of_forall (hn i) fun x hx => ?_
      have e : (weylElt τ K i 1)⁻¹ = (torusElt τ K i (-1))⁻¹ * weylElt τ K i 1 := by
        rw [← weylElt_one_mul_self, mul_inv_rev, inv_mul_cancel_right]
      rw [e, mul_assoc]
      exact hB _ (inv_mem (torusGroup_le_borelGroup (torusElt_mem_torusGroup i (-1)))) _
        (hn i x hx)
  have hg' : g • X = X := hS hg
  rw [← hg']
  exact ⟨1, Set.mem_iUnion.2 ⟨1, one_mem_bruhatCell_one⟩, mul_one g⟩

theorem eq_one_of_bruhatCell_one_eq
    {v : WeylGroup τ} (h : bruhatCell τ K 1 = bruhatCell τ K v) :
    v = 1 := by
  have hv : canonicalRep (coxeterSystem τ) K v ∈ bruhatCell τ K 1 :=
    h ▸ canonicalRep_mem_bruhatCell v
  obtain ⟨b, hb, b', hb', hbb⟩ := mem_bruhatCell.1 hv
  rw [canonicalRep_one, mul_one] at hbb
  have hN : canonicalRep (coxeterSystem τ) K v ∈ monomialSubgroup τ K :=
    Subgroup.mem_sup_right (canonicalRep_mem_closure _ K v)
  have hH : canonicalRep (coxeterSystem τ) K v ∈ torusGroup τ K := by
    rw [← (borel_weyl_intersection τ K).1]
    exact Subgroup.mem_inf.2 ⟨hbb ▸ mul_mem hb hb', hN⟩
  exact ((mapsRootLines_of_mem_torusGroup hH).unique (mapsRootLines_canonicalRep v)).symm

theorem exists_length_simple_mul_eq_sub_one
    {w : WeylGroup τ} (hw : w ≠ 1) :
    ∃ i, (coxeterSystem τ).length (simple τ i * w) = (coxeterSystem τ).length w - 1 := by
  obtain ⟨i, hi⟩ := (weyl_exchange_condition τ).2.2.2 w⁻¹ (inv_ne_one.2 hw)
  exact ⟨i, ((weyl_exchange_condition τ).1 w i).1 hi⟩

theorem bruhatCell_injective
    : Function.Injective (bruhatCell τ K) := by
  have key : ∀ (m : ℕ) (w : WeylGroup τ), (coxeterSystem τ).length w = m →
      ∀ v, bruhatCell τ K w = bruhatCell τ K v → w = v := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro w hm v h
      by_cases hw : w = 1
      · subst hw
        exact (eq_one_of_bruhatCell_one_eq h).symm
      obtain ⟨i, hi⟩ := exists_length_simple_mul_eq_sub_one hw
      have hlen : (coxeterSystem τ).length (simple τ i * w) < m := by
        have := (coxeterSystem τ).length_eq_zero_iff.not.2 hw
        omega
      have hmem : canonicalRep (coxeterSystem τ) K (simple τ i * w) ∈
          bruhatCell τ K (simple τ i) * bruhatCell τ K v := by
        rw [← h, bruhatCell_simple_mul_of_length_eq_sub_one hi]
        exact Or.inl (canonicalRep_mem_bruhatCell _)
      rcases bruhatCell_simple_mul_subset i v hmem with h' | h'
      · exact mul_left_cancel (ih _ hlen _ rfl _
          (bruhatCell_eq_of_mem (canonicalRep_mem_bruhatCell _) h'))
      · have hsw := ih _ hlen _ rfl _ (bruhatCell_eq_of_mem (canonicalRep_mem_bruhatCell _)
          (h ▸ h'))
        have h1 : (coxeterSystem τ).simple i = 1 := mul_eq_right.1 hsw
        have := (coxeterSystem τ).length_simple i
        rw [h1, (coxeterSystem τ).length_one] at this
        exact absurd this zero_ne_one
  exact fun w v h => key _ w rfl v h

theorem disjoint_bruhatCell
    {w w' : WeylGroup τ} (h : w ≠ w') :
    Disjoint (bruhatCell τ K w) (bruhatCell τ K w') :=
  Set.disjoint_left.2 fun _ hx hx' => h (bruhatCell_injective (bruhatCell_eq_of_mem hx hx'))

theorem existsUnique_doubleCoset_eq_bruhatCell
    {g : ModGL τ K} (hg : g ∈ adjointGroup τ K) :
    ∃! w : WeylGroup τ,
      (borelGroup τ K : Set (ModGL τ K)) * {g} * (borelGroup τ K : Set (ModGL τ K)) =
        bruhatCell τ K w := by
  have hg' : g ∈ (adjointGroup τ K : Set (ModGL τ K)) := hg
  rw [adjointGroup_eq_iUnion_bruhatCell] at hg'
  obtain ⟨w, hw⟩ := Set.mem_iUnion.1 hg'
  exact ⟨w, doubleCoset_eq_bruhatCell_of_mem hw, fun v hv =>
    bruhatCell_injective (hv.symm.trans (doubleCoset_eq_bruhatCell_of_mem hw))⟩

theorem bijective_doubleCoset_mk_canonicalRep :
    Function.Bijective fun w : WeylGroup τ =>
      DoubleCoset.mk ((borelGroup τ K).subgroupOf (adjointGroup τ K))
        ((borelGroup τ K).subgroupOf (adjointGroup τ K))
        (⟨canonicalRep (coxeterSystem τ) K w, canonicalRep_mem_adjointGroup _ K w⟩ :
          adjointGroup τ K) := by
  have hBC := ((triangular_borel_structure.{0, 0} τ K).2.2.2.2.2.2.2.2.2.2.2 K).1
  refine ⟨fun w v h => ?_, fun q => ?_⟩
  · obtain ⟨b, hb, b', hb', hbb⟩ := DoubleCoset.eq.1 h
    have hv : canonicalRep (coxeterSystem τ) K v ∈ bruhatCell τ K w :=
      mem_bruhatCell.2 ⟨b, Subgroup.mem_subgroupOf.1 hb, b', Subgroup.mem_subgroupOf.1 hb',
        (congrArg Subtype.val hbb).symm⟩
    exact bruhatCell_injective (bruhatCell_eq_of_mem hv (canonicalRep_mem_bruhatCell v))
  · obtain ⟨g, rfl⟩ := Quotient.mk''_surjective q
    have hg' : (g : ModGL τ K) ∈ (adjointGroup τ K : Set (ModGL τ K)) := g.2
    rw [adjointGroup_eq_iUnion_bruhatCell] at hg'
    obtain ⟨w, hw⟩ := Set.mem_iUnion.1 hg'
    obtain ⟨b, hb, b', hb', hbb⟩ := mem_bruhatCell.1 hw
    refine ⟨w, DoubleCoset.eq.2 ⟨⟨b, hBC hb⟩, Subgroup.mem_subgroupOf.2 hb, ⟨b', hBC hb'⟩,
      Subgroup.mem_subgroupOf.2 hb', Subtype.ext hbb.symm⟩⟩

variable (τ K) in
theorem bruhat_decomposition :
    (adjointGroup τ K : Set (ModGL τ K)) = ⋃ w, bruhatCell τ K w ∧
    (∀ w w' : WeylGroup τ, w ≠ w' → Disjoint (bruhatCell τ K w) (bruhatCell τ K w')) ∧
    Function.Injective (bruhatCell τ K) ∧
    (∀ g ∈ adjointGroup τ K, ∃! w : WeylGroup τ,
      (borelGroup τ K : Set (ModGL τ K)) * {g} * (borelGroup τ K : Set (ModGL τ K)) =
        bruhatCell τ K w) ∧
    Function.Bijective fun w : WeylGroup τ =>
      DoubleCoset.mk ((borelGroup τ K).subgroupOf (adjointGroup τ K))
        ((borelGroup τ K).subgroupOf (adjointGroup τ K))
        (⟨canonicalRep (coxeterSystem τ) K w, canonicalRep_mem_adjointGroup _ K w⟩ :
          adjointGroup τ K) :=
  ⟨adjointGroup_eq_iUnion_bruhatCell, fun _ _ h => disjoint_bruhatCell h, bruhatCell_injective,
    fun _ hg => existsUnique_doubleCoset_eq_bruhatCell hg, bijective_doubleCoset_mk_canonicalRep⟩

end CFSG.LieType.Chevalley
