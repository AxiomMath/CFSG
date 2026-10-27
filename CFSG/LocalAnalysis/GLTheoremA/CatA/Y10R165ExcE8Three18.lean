module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE8Three11
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyNormalizer
public import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCoverRoots
public import CFSG.RankThree.PartOne.KLR.RootKernel

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE8Three

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint
  CFSG.RankThree.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KE6
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.Torality
open CFSG.RankThree.E6 (weylMatrix weylMatrix_mulVec)

open scoped Matrix MatrixGroups

set_option linter.unusedSectionVars false

section Certs


private def e8T3ZKernelB : Set (Fin Tag.E8.rank → ℤ) :=
  {v | e8T3ZA v = 0 ∧ e8T3ZD v = 0 ∧ CFSG.LieType.Chevalley.RootOps.isRootB Tag.E8 v = true}

private theorem e8T3ZKernel_eq_B : e8T3ZKernel = e8T3ZKernelB := by
  ext v
  simp only [e8T3ZKernel, e8T3ZKernelB, Set.mem_setOf_eq,
    CFSG.LieType.Chevalley.RootOps.isRootB_iff]
  tauto

private def e8T3ZKernelList : List (Fin Tag.E8.rank → ℤ) := [
  toVec Tag.E8.rank [-1, -2, -2, -4, -3, -2, -2, -1],
  toVec Tag.E8.rank [-1, -2, -2, -3, -3, -2, -2, -1],
  toVec Tag.E8.rank [-1, -2, -2, -3, -2, -1, -1, -1],
  toVec Tag.E8.rank [-1, -1, -2, -3, -3, -2, -2, -1],
  toVec Tag.E8.rank [-1, -1, -2, -3, -2, -1, -1, -1],
  toVec Tag.E8.rank [-1, -1, -2, -2, -2, -1, -1, -1],
  toVec Tag.E8.rank [-1, -1, -1, -2, -2, -2, -1, -1],
  toVec Tag.E8.rank [-1, 0, 0, 0, 0, 0, 0, 0],
  toVec Tag.E8.rank [0, -1, -1, -2, -2, -2, -1, -1],
  toVec Tag.E8.rank [0, -1, 0, -1, -1, -1, -1, 0],
  toVec Tag.E8.rank [0, -1, 0, -1, 0, 0, 0, 0],
  toVec Tag.E8.rank [0, -1, 0, 0, 0, 0, 0, 0],
  toVec Tag.E8.rank [0, 0, 0, -1, -1, -1, -1, 0],
  toVec Tag.E8.rank [0, 0, 0, -1, 0, 0, 0, 0],
  toVec Tag.E8.rank [0, 0, 0, 0, -1, -1, -1, 0],
  toVec Tag.E8.rank [0, 0, 0, 0, 1, 1, 1, 0],
  toVec Tag.E8.rank [0, 0, 0, 1, 0, 0, 0, 0],
  toVec Tag.E8.rank [0, 0, 0, 1, 1, 1, 1, 0],
  toVec Tag.E8.rank [0, 1, 0, 0, 0, 0, 0, 0],
  toVec Tag.E8.rank [0, 1, 0, 1, 0, 0, 0, 0],
  toVec Tag.E8.rank [0, 1, 0, 1, 1, 1, 1, 0],
  toVec Tag.E8.rank [0, 1, 1, 2, 2, 2, 1, 1],
  toVec Tag.E8.rank [1, 0, 0, 0, 0, 0, 0, 0],
  toVec Tag.E8.rank [1, 1, 1, 2, 2, 2, 1, 1],
  toVec Tag.E8.rank [1, 1, 2, 2, 2, 1, 1, 1],
  toVec Tag.E8.rank [1, 1, 2, 3, 2, 1, 1, 1],
  toVec Tag.E8.rank [1, 1, 2, 3, 3, 2, 2, 1],
  toVec Tag.E8.rank [1, 2, 2, 3, 2, 1, 1, 1],
  toVec Tag.E8.rank [1, 2, 2, 3, 3, 2, 2, 1],
  toVec Tag.E8.rank [1, 2, 2, 4, 3, 2, 2, 1]]

private theorem e8T3ZKernelList_mem :
    e8T3ZKernelList.all (fun v => decide (e8T3ZA v = 0 ∧ e8T3ZD v = 0 ∧
      CFSG.LieType.Chevalley.RootOps.isRootB Tag.E8 v = true)) = true := by
  decide +kernel

private theorem e8T3ZKernelList_nodup : e8T3ZKernelList.Nodup := by
  decide +kernel

private theorem e8T3ZKernelList_subset :
    ({v : Fin Tag.E8.rank → ℤ | v ∈ e8T3ZKernelList} : Set _) ⊆ e8T3ZKernel := by
  intro v hv
  have hv' : e8T3ZA v = 0 ∧ e8T3ZD v = 0 ∧
      CFSG.LieType.Chevalley.RootOps.isRootB Tag.E8 v = true :=
    of_decide_eq_true (List.all_eq_true.1 e8T3ZKernelList_mem v hv)
  rw [e8T3ZKernel_eq_B]
  show e8T3ZA v = 0 ∧ e8T3ZD v = 0 ∧
    CFSG.LieType.Chevalley.RootOps.isRootB Tag.E8 v = true
  exact hv'

private theorem finite_e8T3ZKernel : e8T3ZKernel.Finite :=
  (finite_setOf_isRoot Tag.E8).subset fun v hv => hv.1

private theorem ncard_e8T3ZKernel : e8T3ZKernel.ncard = 30 := by
  rw [show e8T3ZKernel = {v : Fin Tag.E8.rank → ℤ |
      IsRoot Tag.E8 v ∧ e8T3ZA v = 0 ∧ e8T3ZD v = 0} by rfl]
  rw [ncard_isRoot_and (P := fun v => e8T3ZA v = 0 ∧ e8T3ZD v = 0)]
  decide +kernel

private theorem ncard_e8T3ZKernelList :
    ({v : Fin Tag.E8.rank → ℤ | v ∈ e8T3ZKernelList} : Set _).ncard = 30 := by
  rw [show ({v : Fin Tag.E8.rank → ℤ | v ∈ e8T3ZKernelList} : Set _) =
      (e8T3ZKernelList.toFinset : Set _) by ext v; simp]
  rw [Set.ncard_coe_finset, List.toFinset_card_of_nodup e8T3ZKernelList_nodup]
  rfl

private theorem e8T3ZKernel_eq_list :
    e8T3ZKernel = {v : Fin Tag.E8.rank → ℤ | v ∈ e8T3ZKernelList} := by
  refine (Set.eq_of_subset_of_ncard_le (s := {v : Fin Tag.E8.rank → ℤ | v ∈ e8T3ZKernelList})
    (t := e8T3ZKernel) e8T3ZKernelList_subset ?_ finite_e8T3ZKernel).symm
  rw [ncard_e8T3ZKernel, ncard_e8T3ZKernelList]

private theorem e8T3ZKernel_cases {P : (Fin Tag.E8.rank → ℤ) → Prop}
    (h1 : P (toVec Tag.E8.rank [-1, -2, -2, -4, -3, -2, -2, -1]))
    (h2 : P (toVec Tag.E8.rank [-1, -2, -2, -3, -3, -2, -2, -1]))
    (h3 : P (toVec Tag.E8.rank [-1, -2, -2, -3, -2, -1, -1, -1]))
    (h4 : P (toVec Tag.E8.rank [-1, -1, -2, -3, -3, -2, -2, -1]))
    (h5 : P (toVec Tag.E8.rank [-1, -1, -2, -3, -2, -1, -1, -1]))
    (h6 : P (toVec Tag.E8.rank [-1, -1, -2, -2, -2, -1, -1, -1]))
    (h7 : P (toVec Tag.E8.rank [-1, -1, -1, -2, -2, -2, -1, -1]))
    (h8 : P (toVec Tag.E8.rank [-1, 0, 0, 0, 0, 0, 0, 0]))
    (h9 : P (toVec Tag.E8.rank [0, -1, -1, -2, -2, -2, -1, -1]))
    (h10 : P (toVec Tag.E8.rank [0, -1, 0, -1, -1, -1, -1, 0]))
    (h11 : P (toVec Tag.E8.rank [0, -1, 0, -1, 0, 0, 0, 0]))
    (h12 : P (toVec Tag.E8.rank [0, -1, 0, 0, 0, 0, 0, 0]))
    (h13 : P (toVec Tag.E8.rank [0, 0, 0, -1, -1, -1, -1, 0]))
    (h14 : P (toVec Tag.E8.rank [0, 0, 0, -1, 0, 0, 0, 0]))
    (h15 : P (toVec Tag.E8.rank [0, 0, 0, 0, -1, -1, -1, 0]))
    (h16 : P (toVec Tag.E8.rank [0, 0, 0, 0, 1, 1, 1, 0]))
    (h17 : P (toVec Tag.E8.rank [0, 0, 0, 1, 0, 0, 0, 0]))
    (h18 : P (toVec Tag.E8.rank [0, 0, 0, 1, 1, 1, 1, 0]))
    (h19 : P (toVec Tag.E8.rank [0, 1, 0, 0, 0, 0, 0, 0]))
    (h20 : P (toVec Tag.E8.rank [0, 1, 0, 1, 0, 0, 0, 0]))
    (h21 : P (toVec Tag.E8.rank [0, 1, 0, 1, 1, 1, 1, 0]))
    (h22 : P (toVec Tag.E8.rank [0, 1, 1, 2, 2, 2, 1, 1]))
    (h23 : P (toVec Tag.E8.rank [1, 0, 0, 0, 0, 0, 0, 0]))
    (h24 : P (toVec Tag.E8.rank [1, 1, 1, 2, 2, 2, 1, 1]))
    (h25 : P (toVec Tag.E8.rank [1, 1, 2, 2, 2, 1, 1, 1]))
    (h26 : P (toVec Tag.E8.rank [1, 1, 2, 3, 2, 1, 1, 1]))
    (h27 : P (toVec Tag.E8.rank [1, 1, 2, 3, 3, 2, 2, 1]))
    (h28 : P (toVec Tag.E8.rank [1, 2, 2, 3, 2, 1, 1, 1]))
    (h29 : P (toVec Tag.E8.rank [1, 2, 2, 3, 3, 2, 2, 1]))
    (h30 : P (toVec Tag.E8.rank [1, 2, 2, 4, 3, 2, 2, 1]))
    {α : Fin Tag.E8.rank → ℤ} (hα : α ∈ e8T3ZKernel) : P α := by
  have hmem : α ∈ e8T3ZKernelList := by
    have h : α ∈ ({v : Fin Tag.E8.rank → ℤ | v ∈ e8T3ZKernelList} : Set _) := by
      rw [← e8T3ZKernel_eq_list]; exact hα
    simpa only [Set.mem_setOf_eq] using h
  simp only [e8T3ZKernelList, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30]

private def e8T3ZCount (α : Fin Tag.E8.rank → ℤ) : ℕ :=
  (e8T3ZKernelList.filter fun β =>
    CFSG.LieType.Chevalley.RootOps.isRootB Tag.E8 (α + β)).length

@[expose] def e8A2RootCount (α : Fin Tag.E8.rank → ℤ) : ℕ :=
  cond (e8A2RootsB α) 2 8

private theorem ncard_add_e8T3ZKernel_eq_count (α : Fin Tag.E8.rank → ℤ) :
    (e8T3ZKernel ∩ {β | IsRoot Tag.E8 (α + β)}).ncard = e8T3ZCount α := by
  have hset : e8T3ZKernel ∩ {β | IsRoot Tag.E8 (α + β)} =
      ((e8T3ZKernelList.filter fun β =>
        CFSG.LieType.Chevalley.RootOps.isRootB Tag.E8 (α + β)).toFinset : Set _) := by
    ext β
    constructor
    · rintro ⟨hβZK, hβroot⟩
      have hβlist : β ∈ e8T3ZKernelList := by
        have h := hβZK
        rw [e8T3ZKernel_eq_list] at h
        simpa only [Set.mem_setOf_eq] using h
      exact List.mem_toFinset.mpr
        (List.mem_filter.mpr ⟨hβlist, CFSG.LieType.Chevalley.RootOps.isRootB_iff.mpr hβroot⟩)
    · intro hβ
      obtain ⟨hβlist, hβroot⟩ :=
        List.mem_filter.mp (List.mem_toFinset.mp hβ)
      refine ⟨?_, CFSG.LieType.Chevalley.RootOps.isRootB_iff.mp hβroot⟩
      rw [e8T3ZKernel_eq_list]
      exact hβlist
  rw [hset, Set.ncard_coe_finset,
    List.toFinset_card_of_nodup (e8T3ZKernelList_nodup.filter _)]
  rfl

private theorem ncard_add_case1 :
    (e8T3ZKernel ∩
      {β | IsRoot Tag.E8 (toVec Tag.E8.rank [-1, -2, -2, -4, -3, -2, -2, -1] + β)}).ncard =
      e8A2RootCount (toVec Tag.E8.rank [-1, -2, -2, -4, -3, -2, -2, -1]) := by
  rw [ncard_add_e8T3ZKernel_eq_count]
  decide +kernel

private theorem ncard_add_case2 :
    (e8T3ZKernel ∩
      {β | IsRoot Tag.E8 (toVec Tag.E8.rank [-1, -2, -2, -3, -3, -2, -2, -1] + β)}).ncard =
      e8A2RootCount (toVec Tag.E8.rank [-1, -2, -2, -3, -3, -2, -2, -1]) := by
  rw [ncard_add_e8T3ZKernel_eq_count]
  decide +kernel

private theorem ncard_add_case3 :
    (e8T3ZKernel ∩
      {β | IsRoot Tag.E8 (toVec Tag.E8.rank [-1, -2, -2, -3, -2, -1, -1, -1] + β)}).ncard =
      e8A2RootCount (toVec Tag.E8.rank [-1, -2, -2, -3, -2, -1, -1, -1]) := by
  rw [ncard_add_e8T3ZKernel_eq_count]
  decide +kernel

private theorem ncard_add_case4 :
    (e8T3ZKernel ∩
      {β | IsRoot Tag.E8 (toVec Tag.E8.rank [-1, -1, -2, -3, -3, -2, -2, -1] + β)}).ncard =
      e8A2RootCount (toVec Tag.E8.rank [-1, -1, -2, -3, -3, -2, -2, -1]) := by
  rw [ncard_add_e8T3ZKernel_eq_count]
  decide +kernel

private theorem ncard_add_case5 :
    (e8T3ZKernel ∩
      {β | IsRoot Tag.E8 (toVec Tag.E8.rank [-1, -1, -2, -3, -2, -1, -1, -1] + β)}).ncard =
      e8A2RootCount (toVec Tag.E8.rank [-1, -1, -2, -3, -2, -1, -1, -1]) := by
  rw [ncard_add_e8T3ZKernel_eq_count]
  decide +kernel

private theorem ncard_add_case6 :
    (e8T3ZKernel ∩
      {β | IsRoot Tag.E8 (toVec Tag.E8.rank [-1, -1, -2, -2, -2, -1, -1, -1] + β)}).ncard =
      e8A2RootCount (toVec Tag.E8.rank [-1, -1, -2, -2, -2, -1, -1, -1]) := by
  rw [ncard_add_e8T3ZKernel_eq_count]
  decide +kernel

private theorem ncard_add_case7 :
    (e8T3ZKernel ∩
      {β | IsRoot Tag.E8 (toVec Tag.E8.rank [-1, -1, -1, -2, -2, -2, -1, -1] + β)}).ncard =
      e8A2RootCount (toVec Tag.E8.rank [-1, -1, -1, -2, -2, -2, -1, -1]) := by
  rw [ncard_add_e8T3ZKernel_eq_count]
  decide +kernel

private theorem ncard_add_case8 :
    (e8T3ZKernel ∩ {β | IsRoot Tag.E8 (toVec Tag.E8.rank [-1, 0, 0, 0, 0, 0, 0, 0] + β)}).ncard =
      e8A2RootCount (toVec Tag.E8.rank [-1, 0, 0, 0, 0, 0, 0, 0]) := by
  rw [ncard_add_e8T3ZKernel_eq_count]
  decide +kernel

private theorem ncard_add_case9 :
    (e8T3ZKernel ∩
      {β | IsRoot Tag.E8 (toVec Tag.E8.rank [0, -1, -1, -2, -2, -2, -1, -1] + β)}).ncard =
      e8A2RootCount (toVec Tag.E8.rank [0, -1, -1, -2, -2, -2, -1, -1]) := by
  rw [ncard_add_e8T3ZKernel_eq_count]
  decide +kernel

private theorem ncard_add_case10 :
    (e8T3ZKernel ∩
      {β | IsRoot Tag.E8 (toVec Tag.E8.rank [0, -1, 0, -1, -1, -1, -1, 0] + β)}).ncard =
      e8A2RootCount (toVec Tag.E8.rank [0, -1, 0, -1, -1, -1, -1, 0]) := by
  rw [ncard_add_e8T3ZKernel_eq_count]
  decide +kernel

private theorem ncard_add_case11 :
    (e8T3ZKernel ∩ {β | IsRoot Tag.E8 (toVec Tag.E8.rank [0, -1, 0, -1, 0, 0, 0, 0] + β)}).ncard =
      e8A2RootCount (toVec Tag.E8.rank [0, -1, 0, -1, 0, 0, 0, 0]) := by
  rw [ncard_add_e8T3ZKernel_eq_count]
  decide +kernel

private theorem ncard_add_case12 :
    (e8T3ZKernel ∩ {β | IsRoot Tag.E8 (toVec Tag.E8.rank [0, -1, 0, 0, 0, 0, 0, 0] + β)}).ncard =
      e8A2RootCount (toVec Tag.E8.rank [0, -1, 0, 0, 0, 0, 0, 0]) := by
  rw [ncard_add_e8T3ZKernel_eq_count]
  decide +kernel

private theorem ncard_add_case13 :
    (e8T3ZKernel ∩ {β | IsRoot Tag.E8 (toVec Tag.E8.rank [0, 0, 0, -1, -1, -1, -1, 0] + β)}).ncard =
      e8A2RootCount (toVec Tag.E8.rank [0, 0, 0, -1, -1, -1, -1, 0]) := by
  rw [ncard_add_e8T3ZKernel_eq_count]
  decide +kernel

private theorem ncard_add_case14 :
    (e8T3ZKernel ∩ {β | IsRoot Tag.E8 (toVec Tag.E8.rank [0, 0, 0, -1, 0, 0, 0, 0] + β)}).ncard =
      e8A2RootCount (toVec Tag.E8.rank [0, 0, 0, -1, 0, 0, 0, 0]) := by
  rw [ncard_add_e8T3ZKernel_eq_count]
  decide +kernel

private theorem ncard_add_case15 :
    (e8T3ZKernel ∩ {β | IsRoot Tag.E8 (toVec Tag.E8.rank [0, 0, 0, 0, -1, -1, -1, 0] + β)}).ncard =
      e8A2RootCount (toVec Tag.E8.rank [0, 0, 0, 0, -1, -1, -1, 0]) := by
  rw [ncard_add_e8T3ZKernel_eq_count]
  decide +kernel

private theorem ncard_add_case16 :
    (e8T3ZKernel ∩ {β | IsRoot Tag.E8 (toVec Tag.E8.rank [0, 0, 0, 0, 1, 1, 1, 0] + β)}).ncard =
      e8A2RootCount (toVec Tag.E8.rank [0, 0, 0, 0, 1, 1, 1, 0]) := by
  rw [ncard_add_e8T3ZKernel_eq_count]
  decide +kernel

private theorem ncard_add_case17 :
    (e8T3ZKernel ∩ {β | IsRoot Tag.E8 (toVec Tag.E8.rank [0, 0, 0, 1, 0, 0, 0, 0] + β)}).ncard =
      e8A2RootCount (toVec Tag.E8.rank [0, 0, 0, 1, 0, 0, 0, 0]) := by
  rw [ncard_add_e8T3ZKernel_eq_count]
  decide +kernel

private theorem ncard_add_case18 :
    (e8T3ZKernel ∩ {β | IsRoot Tag.E8 (toVec Tag.E8.rank [0, 0, 0, 1, 1, 1, 1, 0] + β)}).ncard =
      e8A2RootCount (toVec Tag.E8.rank [0, 0, 0, 1, 1, 1, 1, 0]) := by
  rw [ncard_add_e8T3ZKernel_eq_count]
  decide +kernel

private theorem ncard_add_case19 :
    (e8T3ZKernel ∩ {β | IsRoot Tag.E8 (toVec Tag.E8.rank [0, 1, 0, 0, 0, 0, 0, 0] + β)}).ncard =
      e8A2RootCount (toVec Tag.E8.rank [0, 1, 0, 0, 0, 0, 0, 0]) := by
  rw [ncard_add_e8T3ZKernel_eq_count]
  decide +kernel

private theorem ncard_add_case20 :
    (e8T3ZKernel ∩ {β | IsRoot Tag.E8 (toVec Tag.E8.rank [0, 1, 0, 1, 0, 0, 0, 0] + β)}).ncard =
      e8A2RootCount (toVec Tag.E8.rank [0, 1, 0, 1, 0, 0, 0, 0]) := by
  rw [ncard_add_e8T3ZKernel_eq_count]
  decide +kernel

private theorem ncard_add_case21 :
    (e8T3ZKernel ∩ {β | IsRoot Tag.E8 (toVec Tag.E8.rank [0, 1, 0, 1, 1, 1, 1, 0] + β)}).ncard =
      e8A2RootCount (toVec Tag.E8.rank [0, 1, 0, 1, 1, 1, 1, 0]) := by
  rw [ncard_add_e8T3ZKernel_eq_count]
  decide +kernel

private theorem ncard_add_case22 :
    (e8T3ZKernel ∩ {β | IsRoot Tag.E8 (toVec Tag.E8.rank [0, 1, 1, 2, 2, 2, 1, 1] + β)}).ncard =
      e8A2RootCount (toVec Tag.E8.rank [0, 1, 1, 2, 2, 2, 1, 1]) := by
  rw [ncard_add_e8T3ZKernel_eq_count]
  decide +kernel

private theorem ncard_add_case23 :
    (e8T3ZKernel ∩ {β | IsRoot Tag.E8 (toVec Tag.E8.rank [1, 0, 0, 0, 0, 0, 0, 0] + β)}).ncard =
      e8A2RootCount (toVec Tag.E8.rank [1, 0, 0, 0, 0, 0, 0, 0]) := by
  rw [ncard_add_e8T3ZKernel_eq_count]
  decide +kernel

private theorem ncard_add_case24 :
    (e8T3ZKernel ∩ {β | IsRoot Tag.E8 (toVec Tag.E8.rank [1, 1, 1, 2, 2, 2, 1, 1] + β)}).ncard =
      e8A2RootCount (toVec Tag.E8.rank [1, 1, 1, 2, 2, 2, 1, 1]) := by
  rw [ncard_add_e8T3ZKernel_eq_count]
  decide +kernel

private theorem ncard_add_case25 :
    (e8T3ZKernel ∩ {β | IsRoot Tag.E8 (toVec Tag.E8.rank [1, 1, 2, 2, 2, 1, 1, 1] + β)}).ncard =
      e8A2RootCount (toVec Tag.E8.rank [1, 1, 2, 2, 2, 1, 1, 1]) := by
  rw [ncard_add_e8T3ZKernel_eq_count]
  decide +kernel

private theorem ncard_add_case26 :
    (e8T3ZKernel ∩ {β | IsRoot Tag.E8 (toVec Tag.E8.rank [1, 1, 2, 3, 2, 1, 1, 1] + β)}).ncard =
      e8A2RootCount (toVec Tag.E8.rank [1, 1, 2, 3, 2, 1, 1, 1]) := by
  rw [ncard_add_e8T3ZKernel_eq_count]
  decide +kernel

private theorem ncard_add_case27 :
    (e8T3ZKernel ∩ {β | IsRoot Tag.E8 (toVec Tag.E8.rank [1, 1, 2, 3, 3, 2, 2, 1] + β)}).ncard =
      e8A2RootCount (toVec Tag.E8.rank [1, 1, 2, 3, 3, 2, 2, 1]) := by
  rw [ncard_add_e8T3ZKernel_eq_count]
  decide +kernel

private theorem ncard_add_case28 :
    (e8T3ZKernel ∩ {β | IsRoot Tag.E8 (toVec Tag.E8.rank [1, 2, 2, 3, 2, 1, 1, 1] + β)}).ncard =
      e8A2RootCount (toVec Tag.E8.rank [1, 2, 2, 3, 2, 1, 1, 1]) := by
  rw [ncard_add_e8T3ZKernel_eq_count]
  decide +kernel

private theorem ncard_add_case29 :
    (e8T3ZKernel ∩ {β | IsRoot Tag.E8 (toVec Tag.E8.rank [1, 2, 2, 3, 3, 2, 2, 1] + β)}).ncard =
      e8A2RootCount (toVec Tag.E8.rank [1, 2, 2, 3, 3, 2, 2, 1]) := by
  rw [ncard_add_e8T3ZKernel_eq_count]
  decide +kernel

private theorem ncard_add_case30 :
    (e8T3ZKernel ∩ {β | IsRoot Tag.E8 (toVec Tag.E8.rank [1, 2, 2, 4, 3, 2, 2, 1] + β)}).ncard =
      e8A2RootCount (toVec Tag.E8.rank [1, 2, 2, 4, 3, 2, 2, 1]) := by
  rw [ncard_add_e8T3ZKernel_eq_count]
  decide +kernel

theorem ncard_add_e8T3ZKernel {α : Fin Tag.E8.rank → ℤ} (hα : α ∈ e8T3ZKernel) :
    (e8T3ZKernel ∩ {β | IsRoot Tag.E8 (α + β)}).ncard = e8A2RootCount α := by
  refine e8T3ZKernel_cases (P := fun α =>
    (e8T3ZKernel ∩ {β | IsRoot Tag.E8 (α + β)}).ncard = e8A2RootCount α)
    ncard_add_case1 ncard_add_case2 ncard_add_case3 ncard_add_case4 ncard_add_case5
    ncard_add_case6 ncard_add_case7 ncard_add_case8 ncard_add_case9 ncard_add_case10
    ncard_add_case11 ncard_add_case12 ncard_add_case13 ncard_add_case14 ncard_add_case15
    ncard_add_case16 ncard_add_case17 ncard_add_case18 ncard_add_case19 ncard_add_case20
    ncard_add_case21 ncard_add_case22 ncard_add_case23 ncard_add_case24 ncard_add_case25
    ncard_add_case26 ncard_add_case27 ncard_add_case28 ncard_add_case29 ncard_add_case30 hα

theorem e8A2RootCount_eq_two_iff {α : Fin Tag.E8.rank → ℤ} :
    e8A2RootCount α = 2 ↔ α ∈ e8A2Roots := by
  constructor
  · intro h
    by_contra hS
    have hb : e8A2RootsB α = false := by
      by_contra h'
      have h1 : e8A2RootsB α = true := by
        cases h'' : e8A2RootsB α
        · exact absurd h'' h'
        · rfl
      exact hS (e8A2RootsB_iff.1 h1)
    rw [e8A2RootCount, hb] at h
    exact absurd h (by norm_num)
  · intro hS
    rw [e8A2RootCount, e8A2RootsB_iff.2 hS]
    rfl

theorem iform_e8A2Roots_eq_zero_of_mem_e8T3ZKernel
    {α β : Fin Tag.E8.rank → ℤ} (hα : α ∈ e8T3ZKernel) (hαS : α ∉ e8A2Roots)
    (hβ : β ∈ e8A2Roots) : iform α β = 0 := by
  have horth : ∀ α ∈ e8T3ZKernel, e8A2RootsB α = false →
      iform α (Pi.single (0 : Fin Tag.E8.rank) 1) = 0 ∧
      iform α e8A2Beta = 0 ∧ iform α e8A2Delta = 0 := by
    intro α hα
    refine e8T3ZKernel_cases (P := fun α => e8A2RootsB α = false →
      iform α (Pi.single (0 : Fin Tag.E8.rank) 1) = 0 ∧
      iform α e8A2Beta = 0 ∧ iform α e8A2Delta = 0)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      ?_ hα
    all_goals decide +kernel
  have hb : e8A2RootsB α = false := by
    by_contra h
    have h1 : e8A2RootsB α = true := by
      cases htrue : e8A2RootsB α
      · exact absurd htrue h
      · rfl
    exact hαS (e8A2RootsB_iff.1 h1)
  obtain ⟨h1, h2, h3⟩ := horth α hα hb
  simp only [e8A2Roots, Set.mem_setOf_eq] at hβ
  rcases hβ with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h1
  · rw [iform_neg_right, h1, neg_zero]
  · rw [e8A2Beta_lit]
    exact h2
  · rw [e8A2NegBeta_lit, e8A2NegBeta_eq_neg, iform_neg_right, h2, neg_zero]
  · rw [e8A2Delta_lit]
    exact h3
  · rw [e8A2Gamma_lit, e8A2Gamma_eq_neg_delta, iform_neg_right, h3, neg_zero]

theorem commute_e8A2Roots_of_mem_e8T3ZKernel {L : Type} [Field L]
    {α β : Fin Tag.E8.rank → ℤ} (hα : α ∈ e8T3ZKernel) (hαS : α ∉ e8A2Roots)
    (hβ : β ∈ e8A2Roots) :
    ∀ x ∈ rootSubgroup Tag.E8 L α, ∀ y ∈ rootSubgroup Tag.E8 L β, Commute x y := by
  have hαroot := hα.1
  have hβroot := isRoot_of_mem_e8A2Roots hβ
  have h0 : iform α β = 0 := iform_e8A2Roots_eq_zero_of_mem_e8T3ZKernel hα hαS hβ
  have hne : α ≠ β := fun h => hαS (h ▸ hβ)
  have hne' : α ≠ -β := fun h => hαS (h ▸ neg_mem_e8A2Roots hβ)
  have hnot : ¬ IsRoot Tag.E8 (α + β) :=
    CFSG.LieType.Chevalley.SimplyLacedCover.not_isRoot_add (fun i => by
      simpa [show Tag.E8.symmetrizer =
        (1 : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ) from rfl]) hαroot hβroot
      (by simpa [h0] using (le_refl (0 : ℤ)))
  exact commute_of_forall_not_isRoot hαroot hβroot hne hne'
    (fun a b ha hb => not_isRoot_nsmul_add_nsmul hαroot hβroot h0 hnot ha hb) L

theorem smul_mem_e8A2Roots_of_mem_rootCharStabilizer {L : Type} [Field L]
    {b : Fin Tag.E8.rank → Lˣ} (hker : rootCharKernel b = e8T3ZKernel)
    {w : WeylGroup Tag.E8} (hw : w ∈ rootCharStabilizer b) :
    ∀ α ∈ e8A2Roots, w • α ∈ e8A2Roots := by
  have hfam : familyKernel (fun _ : Unit => b) = rootCharKernel b := by
    ext α
    simp [familyKernel, rootCharKernel]
  have hZK : (fun α => w • α) '' e8T3ZKernel = e8T3ZKernel := by
    have h := image_familyKernel (a := fun _ : Unit => b) (w := w) (fun _ => hw)
    rwa [hfam, hker] at h
  have hinj : Function.Injective (fun β : Fin Tag.E8.rank → ℤ => w • β) := by
    intro a b h
    have := congrArg (fun x => w⁻¹ • x) h
    simpa using this
  intro α hα
  have hαZK : α ∈ e8T3ZKernel := e8A2Roots_subset_e8T3ZKernel hα
  have hwα : w • α ∈ e8T3ZKernel := by
    rw [← hZK]
    exact ⟨α, hαZK, rfl⟩
  have himg : (e8T3ZKernel ∩ {β | IsRoot Tag.E8 (w • α + β)}) =
      (fun β => w • β) '' (e8T3ZKernel ∩ {β | IsRoot Tag.E8 (α + β)}) := by
    ext β
    constructor
    · intro hβ
      obtain ⟨hβZK, hβroot⟩ := hβ
      have hγZK : w⁻¹ • β ∈ e8T3ZKernel := by
        have h : w • (w⁻¹ • β) ∈ (fun α => w • α) '' e8T3ZKernel := by
          rw [hZK]
          simpa using hβZK
        obtain ⟨x, hx, hxw⟩ := h
        have hx' : x = w⁻¹ • β := hinj (by simpa using hxw)
        rwa [hx'] at hx
      have hγroot : IsRoot Tag.E8 (α + w⁻¹ • β) := by
        have h : IsRoot Tag.E8 (w⁻¹ • (w • α + β)) := IsRoot.smul hβroot w⁻¹
        simpa [smul_add] using h
      exact ⟨w⁻¹ • β, ⟨hγZK, hγroot⟩, by simp⟩
    · rintro ⟨γ, ⟨hγZK, hγroot⟩, rfl⟩
      change w • γ ∈ e8T3ZKernel ∩ {β | IsRoot Tag.E8 (w • α + β)}
      refine ⟨?_, ?_⟩
      · rw [← hZK]
        exact ⟨γ, hγZK, rfl⟩
      · change IsRoot Tag.E8 (w • α + w • γ)
        have h : w • α + w • γ = w • (α + γ) := by rw [smul_add]
        rw [h]
        exact IsRoot.smul hγroot w
  have hcount : (e8T3ZKernel ∩ {β | IsRoot Tag.E8 (w • α + β)}).ncard =
      (e8T3ZKernel ∩ {β | IsRoot Tag.E8 (α + β)}).ncard := by
    rw [himg, Set.ncard_image_of_injective _ hinj]
  have h2 : (e8T3ZKernel ∩ {β | IsRoot Tag.E8 (w • α + β)}).ncard = 2 := by
    rw [hcount, ncard_add_e8T3ZKernel hαZK]
    simp [e8A2RootCount, e8A2RootsB_iff.2 hα]
  have h3 : e8A2RootCount (w • α) = 2 := by
    rw [← ncard_add_e8T3ZKernel hwα]
    exact h2
  exact e8A2RootCount_eq_two_iff.1 h3

theorem familyCentralizer_e8T3ZColumn_le_normalizer_rootSpan {L : Type} [Field L]
    {p : ℕ} [NeZero p] {ζ : Lˣ} (hζ : IsPrimitiveRoot ζ p) (hp : p.Prime) (hp3 : 3 < p)
    {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {q : ZMod p}
    (hq : q ^ 2 + (ε : ZMod p) * q + 1 = 0) :
    familyCentralizer Tag.E8 L (fun _ : Unit => fun i => ζ ^ (e8T3ZColumn ε q i).val) ≤
      Subgroup.normalizer (rootSpan Tag.E8 L e8A2Roots : Set (ModGL Tag.E8 L)) := by
  have hker : familyKernel (fun _ : Unit => fun i => ζ ^ (e8T3ZColumn ε q i).val) =
      e8T3ZKernel := by
    rw [show familyKernel (fun _ : Unit => fun i => ζ ^ (e8T3ZColumn ε q i).val) =
        rootCharKernel (fun i => ζ ^ (e8T3ZColumn ε q i).val) by
      ext α; simp [familyKernel, rootCharKernel],
      CFSG.RankThree.PartOne.KLR.rootCharKernel_zetaPow_eq hζ (e8T3ZColumn ε q),
      rootKernel_e8T3ZColumn hp hp3 hε hq]
  refine familyCentralizer_le_normalizer_rootSpan_of_subset _ ?_ ?_ ?_
  · rw [hker]
    exact e8A2Roots_subset_e8T3ZKernel
  · intro w hw α hα
    have hw' : w ∈ rootCharStabilizer (fun i => ζ ^ (e8T3ZColumn ε q i).val) := by
      have h := hw
      simp only [familyStabilizer, Set.mem_setOf_eq] at h
      exact h ()
    have hker' : rootCharKernel (fun i => ζ ^ (e8T3ZColumn ε q i).val) = e8T3ZKernel := by
      rw [← hker]
      ext α
      simp [familyKernel, rootCharKernel]
    exact smul_mem_e8A2Roots_of_mem_rootCharStabilizer hker' hw' α hα
  · intro α hα β hβ x hx y hy
    rw [hker] at hα
    exact commute_e8A2Roots_of_mem_e8T3ZKernel hα.1 hα.2 hβ x hx y hy

end Certs

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE8Three
