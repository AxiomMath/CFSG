module

public import CFSG.LieType.Chevalley.ParabolicRadicalLevi

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped commutatorElement

section Roots

variable {τ : Tag} {J : Set (Fin τ.rank)}

@[expose] def degSet (τ : Tag) (J : Set (Fin τ.rank)) (d : ℤ) : Set (Fin τ.rank → ℤ) :=
  {α | α ∈ parabolicRadicalRoots τ J ∧ d ≤ parabolicDegree τ J α}

theorem degSet_one : degSet τ J 1 = parabolicRadicalRoots τ J :=
  Set.ext fun _ => ⟨fun h => h.1, fun h => ⟨h, one_le_parabolicDegree_of_mem h⟩⟩

theorem degSet_anti {d d' : ℤ} (h : d ≤ d') : degSet τ J d' ⊆ degSet τ J d :=
  fun _ hα => ⟨hα.1, h.trans hα.2⟩

theorem degSet_pos {d : ℤ} {α : Fin τ.rank → ℤ} (hα : α ∈ degSet τ J d) :
    IsRoot τ α ∧ 0 < height α := hα.1.1

theorem add_mem_degSet {d d' : ℤ} (hd : 1 ≤ d) (hd' : 1 ≤ d') {α β : Fin τ.rank → ℤ}
    (hα : α ∈ degSet τ J d) (hβ : β ∈ degSet τ J d') {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hr : IsRoot τ (a • α + b • β)) : a • α + b • β ∈ degSet τ J (d + d') := by
  refine ⟨add_mem_parabolicRadicalRoots hα.1.1 hβ.1 ha hb hr, ?_⟩
  rw [parabolicDegree_add, parabolicDegree_nsmul, parabolicDegree_nsmul]
  have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
  have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
  have h1 := hα.2
  have h2 := hβ.2
  nlinarith

theorem add_mem_degSet_of_pos {d : ℤ} {α β : Fin τ.rank → ℤ} (hα : IsRoot τ α ∧ 0 < height α)
    (hβ : β ∈ degSet τ J d) {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hr : IsRoot τ (a • α + b • β)) :
    a • α + b • β ∈ degSet τ J d := by
  refine ⟨add_mem_parabolicRadicalRoots hα hβ.1 ha hb hr, ?_⟩
  rw [parabolicDegree_add, parabolicDegree_nsmul, parabolicDegree_nsmul]
  have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
  have ha' : (0 : ℤ) ≤ a := by exact_mod_cast Nat.zero_le a
  have h0 := parabolicDegree_nonneg (J := J) ((IsRoot.height_pos_iff hα.1).1 hα.2)
  have h1 := hβ.2
  have h2 := one_le_parabolicDegree_of_mem hβ.1
  nlinarith

theorem degSet_closed {d : ℤ} (hd : 1 ≤ d) : ∀ α ∈ degSet τ J d, ∀ β ∈ degSet τ J d, ∀ a b : ℕ,
    1 ≤ a → 1 ≤ b → IsRoot τ (a • α + b • β) → a • α + b • β ∈ degSet τ J d :=
  fun _ hα _ hβ _ _ ha hb hr => degSet_anti (show d ≤ d + d by omega) (add_mem_degSet hd hd hα hβ ha hb hr)

theorem image_reflect_degSet {d : ℤ} {j : Fin τ.rank} (hj : j ∈ J) :
    reflect τ j '' degSet τ J d = degSet τ J d := by
  have h : ∀ α ∈ degSet τ J d, reflect τ j α ∈ degSet τ J d := fun α hα =>
    ⟨reflect_mem_parabolicRadicalRoots hj hα.1, by rw [parabolicDegree_reflect hj]; exact hα.2⟩
  refine Set.Subset.antisymm ?_ fun α hα => ⟨reflect τ j α, h α hα, reflect_reflect τ j α⟩
  rintro _ ⟨α, hα, rfl⟩
  exact h α hα

end Roots

section Series

variable {τ : Tag} {K : Type} [Field K] {J : Set (Fin τ.rank)}

@[expose] def degSeries (τ : Tag) (K : Type) [Field K] (J : Set (Fin τ.rank)) (d : ℤ) :
    Subgroup (ModGL τ K) :=
  rootSpan τ K (degSet τ J d)

theorem degSeries_one : degSeries τ K J 1 = parabolicRadical τ K J := by
  unfold degSeries parabolicRadical
  rw [degSet_one]

theorem degSeries_anti {d d' : ℤ} (h : d ≤ d') : degSeries τ K J d' ≤ degSeries τ K J d :=
  iSup₂_le fun α hα => le_iSup₂_of_le α (degSet_anti h hα) le_rfl

theorem degSeries_le_posUnipotent {d : ℤ} : degSeries τ K J d ≤ posUnipotent τ K :=
  rootSpan_le_posUnipotent fun _ hα => degSet_pos hα

theorem card_degSeries [Finite K] {d : ℤ} (hd : 1 ≤ d) :
    Nat.card (degSeries τ K J d) = Nat.card K ^ (degSet τ J d).ncard :=
  card_rootSpan (fun _ hα => degSet_pos hα) (degSet_closed hd)

theorem borelGroup_le_normalizer_degSeries (d : ℤ) :
    borelGroup τ K ≤ Subgroup.normalizer (degSeries τ K J d : Set (ModGL τ K)) :=
  sup_le (torusGroup_le_normalizer_rootSpan fun _ hα => (degSet_pos hα).1)
    (posUnipotent_le_normalizer_of_absorbs (fun _ hα => degSet_pos hα)
      fun _ hα _ hβ _ _ ha hb hr => add_mem_degSet_of_pos hα hβ ha hb hr)

theorem weylElt_mem_normalizer_degSeries {d : ℤ} {j : Fin τ.rank} (hj : j ∈ J) :
    weylElt τ K j 1 ∈ Subgroup.normalizer (degSeries τ K J d : Set (ModGL τ K)) := by
  refine mem_normalizer_of_map_eq ?_
  rw [degSeries, map_conj_weylElt_rootSpan K j 1 fun _ hα => (degSet_pos hα).1,
    image_reflect_degSet hj]

theorem parabolicSubgroup_le_normalizer_degSeries (d : ℤ) :
    parabolicSubgroup τ K J ≤ Subgroup.normalizer (degSeries τ K J d : Set (ModGL τ K)) :=
  sup_le (borelGroup_le_normalizer_degSeries d) ((Subgroup.closure_le _).2
    fun _ ⟨_, hj, he⟩ => he ▸ weylElt_mem_normalizer_degSeries hj)

theorem rootDiagUnit_mem_normalizer_degSeries (a : Fin τ.rank → Kˣ) (d : ℤ) :
    rootDiagUnit τ a ∈ Subgroup.normalizer (degSeries τ K J d : Set (ModGL τ K)) := by
  refine mem_normalizer_of_map_eq ?_
  rw [degSeries]
  exact map_rootSpan_of_forall fun α hα =>
    map_conj_rootDiagUnit_rootSubgroup a (degSet_pos hα).1

theorem posUnipotent_le_normalizer_degSeries (d : ℤ) :
    posUnipotent τ K ≤ Subgroup.normalizer (degSeries τ K J d : Set (ModGL τ K)) :=
  le_trans le_sup_right (borelGroup_le_normalizer_degSeries d)

theorem commutator_degSeries_le {d d' : ℤ} (hd : 1 ≤ d) (hd' : 1 ≤ d') :
    ⁅degSeries τ K J d, degSeries τ K J d'⁆ ≤ degSeries τ K J (d + d') := by
  have e1 := rootSpan_eq_closure K (degSet τ J d)
  have e2 := rootSpan_eq_closure K (degSet τ J d')
  have hs := degSeries_le_posUnipotent (τ := τ) (K := K) (J := J) (d := d)
  have ht := degSeries_le_posUnipotent (τ := τ) (K := K) (J := J) (d := d')
  unfold degSeries at hs ht ⊢
  rw [e1] at hs ⊢
  rw [e2] at ht ⊢
  refine commutator_closure_le_of_le_normalizer hs ht
    (posUnipotent_le_normalizer_degSeries (d + d')) ?_
  rintro _ ⟨α, hα, c, rfl⟩ _ ⟨β, hβ, e, rfl⟩
  by_cases hab : α = β
  · subst hab
    rw [commutatorElement_def, rootSubgroup_mul_comm K (Subgroup.subset_closure ⟨c, rfl⟩)
      (Subgroup.subset_closure ⟨e, rfl⟩), mul_inv_cancel_right, mul_inv_cancel]
    exact Subgroup.one_mem _
  have hmem := commutator_rootSubgroup_le K (degSet_pos hα).1 (degSet_pos hβ).1
    (degSet_pos hα).2 (degSet_pos hβ).2 hab
    (Subgroup.commutator_mem_commutator (Subgroup.subset_closure ⟨c, rfl⟩)
      (Subgroup.subset_closure ⟨e, rfl⟩))
  have hle : (⨆ (γ : Fin τ.rank → ℤ) (_ : IsRoot τ γ ∧
      ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ γ = a • α + b • β), rootSubgroup τ K γ) ≤
      rootSpan τ K (degSet τ J (d + d')) := by
    refine iSup₂_le fun γ hγ => ?_
    obtain ⟨hγr, a, b, ha, hb, rfl⟩ := hγ
    exact le_iSup₂_of_le _ (add_mem_degSet hd hd' hα hβ ha hb hγr) le_rfl
  exact hle hmem

end Series

section Center

local instance : NeZero Tag.D4.rank := ⟨by decide⟩

end Center

end CFSG.LocalAnalysis.GLTheoremA
