module

public import CFSG.LieType.Chevalley.C2E6SubsystemBruhatCells

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley
open scoped Pointwise

variable {τ : Tag} {K : Type} [Field K] {A : Set (Fin τ.rank)}

theorem subsystemCell_eq_doubleCoset
    (w : WeylGroup τ) :
    subsystemCell τ K A w = DoubleCoset.doubleCoset (canonicalRep (coxeterSystem τ) K w)
      (subsystemBorel τ K A : Set (ModGL τ K)) (subsystemBorel τ K A : Set (ModGL τ K)) :=
  rfl

theorem existsUnique_doubleCoset_eq_subsystemCell
    {g : ModGL τ K}
    (hg : g ∈ subsystemGroup τ K A) :
    ∃! w, w ∈ parabolicWeylGroup τ A ∧
      (subsystemBorel τ K A : Set (ModGL τ K)) * {g} * (subsystemBorel τ K A : Set _) =
        subsystemCell τ K A w := by
  have hg' : g ∈ subsystemCells τ K A := subsystemGroup_subset_subsystemCells hg
  obtain ⟨w, hw, hgw⟩ := mem_subsystemCells.1 hg'
  have hdc : (subsystemBorel τ K A : Set (ModGL τ K)) * {g} * (subsystemBorel τ K A : Set _) =
      subsystemCell τ K A w := by
    rw [subsystemCell_eq_doubleCoset] at hgw ⊢
    exact DoubleCoset.doubleCoset_eq_of_mem hgw
  refine ⟨w, ⟨hw, hdc⟩, fun w' ⟨_, hw'⟩ => ?_⟩
  by_contra hne
  have hg1 : g ∈ subsystemCell τ K A w' := by
    rw [← hw']
    exact DoubleCoset.mem_doubleCoset_self _ _ _
  exact Set.disjoint_left.1 (disjoint_subsystemCell (K := K) (A := A) hne) hg1 hgw

theorem subsystemGroup_inf_borelGroup :
    subsystemGroup τ K A ⊓ borelGroup τ K = subsystemBorel τ K A := by
  refine le_antisymm (fun g hg => ?_) (le_inf subsystemBorel_le_subsystemGroup
    subsystemBorel_le_borelGroup)
  obtain ⟨hgS, hgB⟩ := Subgroup.mem_inf.1 hg
  obtain ⟨w, hw, hgw⟩ := mem_subsystemCells.1 (subsystemGroup_subset_subsystemCells hgS)
  have hg1 : g ∈ bruhatCell τ K 1 :=
    mem_bruhatCell.2 ⟨g, hgB, 1, one_mem _, by rw [canonicalRep_one, mul_one, mul_one]⟩
  have hw1 : w = 1 := by
    by_contra hne
    exact Set.disjoint_left.1 (disjoint_bruhatCell (K := K) hne)
      (subsystemCell_subset_bruhatCell w hgw) hg1
  subst hw1
  obtain ⟨b, hb, b', hb', rfl⟩ := mem_subsystemCell.1 hgw
  rw [canonicalRep_one, mul_one]
  exact mul_mem hb hb'

theorem subsystemGroup_inf_torusGroup :
    subsystemGroup τ K A ⊓ torusGroup τ K = subsystemTorus τ K A := by
  refine le_antisymm (fun g hg => ?_) (le_inf subsystemTorus_le_subsystemGroup
    subsystemTorus_le_torusGroup)
  obtain ⟨hgS, hgH⟩ := Subgroup.mem_inf.1 hg
  have hgB : g ∈ subsystemBorel τ K A := by
    rw [← subsystemGroup_inf_borelGroup]
    exact Subgroup.mem_inf.2 ⟨hgS, Subgroup.mem_sup_left hgH⟩
  rw [← SetLike.mem_coe, coe_subsystemBorel] at hgB
  obtain ⟨t, ht, v, hv, rfl⟩ := hgB
  have hvH : v ∈ torusGroup τ K := by
    have := mul_mem (inv_mem (subsystemTorus_le_torusGroup ht)) hgH
    rwa [inv_mul_cancel_left] at this
  have hv1 : v = 1 := by
    have hmem : v ∈ torusGroup τ K ⊓ posUnipotent τ K :=
      Subgroup.mem_inf.2 ⟨hvH, parabolicLeviUnipotent_le_posUnipotent A hv⟩
    rwa [(triangular_borel_structure.{0, 0} τ K).2.2.2.1, Subgroup.mem_bot] at hmem
  subst hv1
  simpa using ht

theorem card_subsystemBorel :
    Nat.card (subsystemBorel τ K A) =
      Nat.card (subsystemTorus τ K A) * Nat.card (parabolicLeviUnipotent τ K A) := by
  have hbij : Set.BijOn (fun p : ModGL τ K × ModGL τ K => p.1 * p.2)
      ((subsystemTorus τ K A : Set (ModGL τ K)) ×ˢ (parabolicLeviUnipotent τ K A : Set _))
      (subsystemBorel τ K A : Set (ModGL τ K)) := by
    refine ⟨fun p hp => ?_, fun p hp q hq h => ?_, fun x hx => ?_⟩
    · rw [coe_subsystemBorel]
      exact ⟨p.1, hp.1, p.2, hp.2, rfl⟩
    · obtain ⟨h1, h2⟩ := eq_of_mul_eq_subsystem hp.1 hq.1 hp.2 hq.2 h
      exact Prod.ext h1 h2
    · rw [coe_subsystemBorel] at hx
      obtain ⟨t, ht, v, hv, rfl⟩ := hx
      exact ⟨(t, v), ⟨ht, hv⟩, rfl⟩
  calc Nat.card (subsystemBorel τ K A) = Nat.card ((subsystemTorus τ K A : Set (ModGL τ K)) ×ˢ
        (parabolicLeviUnipotent τ K A : Set (ModGL τ K))) := Nat.card_congr hbij.equiv.symm
    _ = Nat.card (subsystemTorus τ K A) * Nat.card (parabolicLeviUnipotent τ K A) := by
      rw [Nat.card_congr (Equiv.Set.prod _ _), Nat.card_prod]
      rfl

theorem card_parabolicLeviUnipotent :
    Nat.card (parabolicLeviUnipotent τ K A) = Nat.card K ^ (parabolicPosRoots τ A).ncard :=
  card_rootSpan (fun _ hα => hα.2) fun _ hα _ hβ _ _ ha hb hr =>
    add_mem_parabolicPosRoots hα hβ ha hb hr

theorem card_subsystemCell
    {w : WeylGroup τ} (hw : w ∈ parabolicWeylGroup τ A) :
    Nat.card (subsystemCell τ K A w) = Nat.card (subsystemTorus τ K A) *
      Nat.card K ^ ((parabolicPosRoots τ A).ncard + (coxeterSystem τ).length w) := by
  calc Nat.card (subsystemCell τ K A w) = Nat.card ((subsystemBorel τ K A : Set (ModGL τ K)) ×ˢ
        (rootSpan τ K (inversionSet w) : Set (ModGL τ K))) :=
        Nat.card_congr (bijOn_subsystemCell hw).equiv.symm
    _ = Nat.card (subsystemBorel τ K A) * Nat.card (rootSpan τ K (inversionSet w)) := by
      rw [Nat.card_congr (Equiv.Set.prod _ _), Nat.card_prod]
      rfl
    _ = _ := by
      rw [card_subsystemBorel, card_parabolicLeviUnipotent, card_rootSpan_inversionSet, pow_add,
        mul_assoc]

theorem card_subsystemGroup
    [Finite K] :
    Nat.card (subsystemGroup τ K A) = Nat.card (subsystemTorus τ K A) *
      Nat.card K ^ (parabolicPosRoots τ A).ncard *
        ∑ᶠ w : parabolicWeylGroup τ A, Nat.card K ^ (coxeterSystem τ).length w := by
  classical
  have : Fintype (WeylGroup τ) := Fintype.ofFinite _
  have : Finite (Module.End K (RootModule τ K)) := Module.finite_of_finite K
  have e : (subsystemGroup τ K A : Set (ModGL τ K)) ≃
      Σ w : parabolicWeylGroup τ A, subsystemCell τ K A w := by
    have hU : subsystemCells τ K A = ⋃ w : parabolicWeylGroup τ A, subsystemCell τ K A w := by
      ext x
      simp only [subsystemCells, Set.mem_iUnion, exists_prop, Subtype.exists]
    rw [subsystemGroup_eq_subsystemCells, hU]
    exact Set.unionEqSigmaOfDisjoint fun w w' h =>
      disjoint_subsystemCell fun h' => h (Subtype.ext h')
  calc Nat.card (subsystemGroup τ K A) =
        Nat.card (Σ w : parabolicWeylGroup τ A, subsystemCell τ K A w) := Nat.card_congr e
    _ = ∑ w : parabolicWeylGroup τ A, Nat.card (subsystemCell τ K A w) := Nat.card_sigma
    _ = _ := by
      rw [finsum_eq_sum_of_fintype, Finset.mul_sum]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [card_subsystemCell w.2, pow_add, mul_assoc]

variable (τ K A) in
theorem subsystem_root_group_bruhat :
    ((subsystemBorel τ K A : Set (ModGL τ K)) =
        (subsystemTorus τ K A : Set (ModGL τ K)) * (parabolicLeviUnipotent τ K A : Set _) ∧
      ∀ t ∈ subsystemTorus τ K A, ∀ t' ∈ subsystemTorus τ K A,
        ∀ v ∈ parabolicLeviUnipotent τ K A, ∀ v' ∈ parabolicLeviUnipotent τ K A,
          t * v = t' * v' → t = t' ∧ v = v') ∧
    (∀ w ∈ parabolicWeylGroup τ A, inversionSet w ⊆ parabolicPosRoots τ A) ∧
    (subsystemGroup τ K A : Set (ModGL τ K)) = ⋃ w ∈ parabolicWeylGroup τ A,
      (subsystemBorel τ K A : Set (ModGL τ K)) * {canonicalRep (coxeterSystem τ) K w} *
        (rootSpan τ K (inversionSet w) : Set (ModGL τ K)) ∧
    (∀ w ∈ parabolicWeylGroup τ A, ∀ w' ∈ parabolicWeylGroup τ A, w ≠ w' →
      Disjoint ((subsystemBorel τ K A : Set (ModGL τ K)) * {canonicalRep (coxeterSystem τ) K w} *
          (rootSpan τ K (inversionSet w) : Set (ModGL τ K)))
        ((subsystemBorel τ K A : Set (ModGL τ K)) * {canonicalRep (coxeterSystem τ) K w'} *
          (rootSpan τ K (inversionSet w') : Set (ModGL τ K)))) ∧
    (∀ w ∈ parabolicWeylGroup τ A,
      (subsystemBorel τ K A : Set (ModGL τ K)) * {canonicalRep (coxeterSystem τ) K w} *
          (subsystemBorel τ K A : Set (ModGL τ K)) =
        (subsystemBorel τ K A : Set (ModGL τ K)) * {canonicalRep (coxeterSystem τ) K w} *
          (rootSpan τ K (inversionSet w) : Set (ModGL τ K)) ∧
      Set.BijOn (fun p : ModGL τ K × ModGL τ K => p.1 * canonicalRep (coxeterSystem τ) K w * p.2)
        ((subsystemBorel τ K A : Set (ModGL τ K)) ×ˢ (rootSpan τ K (inversionSet w) : Set _))
        ((subsystemBorel τ K A : Set (ModGL τ K)) * {canonicalRep (coxeterSystem τ) K w} *
          (subsystemBorel τ K A : Set (ModGL τ K)))) ∧
    (∀ g ∈ subsystemGroup τ K A, ∃! w, w ∈ parabolicWeylGroup τ A ∧
      (subsystemBorel τ K A : Set (ModGL τ K)) * {g} * (subsystemBorel τ K A : Set _) =
        (subsystemBorel τ K A : Set (ModGL τ K)) * {canonicalRep (coxeterSystem τ) K w} *
          (subsystemBorel τ K A : Set (ModGL τ K))) ∧
    (∀ [Finite K], Nat.card (subsystemGroup τ K A) = Nat.card (subsystemTorus τ K A) *
      Nat.card K ^ (parabolicPosRoots τ A).ncard *
        ∑ᶠ w : parabolicWeylGroup τ A, Nat.card K ^ (coxeterSystem τ).length w) ∧
    subsystemGroup τ K A ⊓ borelGroup τ K = subsystemBorel τ K A ∧
    subsystemGroup τ K A ⊓ torusGroup τ K = subsystemTorus τ K A := by
  refine ⟨⟨coe_subsystemBorel, fun t ht t' ht' v hv v' hv' h => eq_of_mul_eq_subsystem ht ht' hv
    hv' h⟩, fun w hw => inversionSet_subset_parabolicPosRoots hw, ?_,
    fun w hw w' hw' hne => ?_, fun w hw => ⟨subsystemCell_eq_mul hw, bijOn_subsystemCell hw⟩,
    fun g hg => existsUnique_doubleCoset_eq_subsystemCell hg, card_subsystemGroup,
    subsystemGroup_inf_borelGroup, subsystemGroup_inf_torusGroup⟩
  · rw [subsystemGroup_eq_subsystemCells]
    ext x
    simp only [subsystemCells, Set.mem_iUnion, exists_prop]
    exact exists_congr fun w => and_congr_right fun hw => by rw [← subsystemCell_eq_mul hw]
  · have := disjoint_subsystemCell (K := K) (A := A) hne
    rwa [subsystemCell_eq_mul hw, subsystemCell_eq_mul hw'] at this

end CFSG.LieType.Chevalley
