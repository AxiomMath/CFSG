module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.A15LocalPerm

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.AGLEmbedding.A15Local

open Equiv CFSG.Open

open scoped Pointwise

namespace BlocksMax

theorem zmod_three_cases_sub (i j l : ZMod 3) (h : i ≠ j) :
    l = i ∨ l = j ∨ l = j + (j - i) := by
  revert i j l
  decide

theorem zmod_five_exists_mul (z w u : ZMod 5) (h : z ≠ w) :
    ∃ k : ℕ, u = z + (k : ZMod 5) * (w - z) := by
  have key : ∃ k : ℕ, k < 5 ∧ u = z + (k : ZMod 5) * (w - z) := by
    revert z w u
    decide
  obtain ⟨k, -, hk⟩ := key
  exact ⟨k, hk⟩

theorem blockShift_pow_apply (m : ℕ) (p : Pt) : (blockShift ^ m) p = (p.1 + m, p.2) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', Perm.mul_apply, ih]
    simp [add_assoc]

theorem blockShift_pow_val_apply (m : ZMod 3) (p : Pt) :
    (blockShift ^ m.val) p = (p.1 + m, p.2) := by
  rw [blockShift_pow_apply, ZMod.natCast_zmod_val]

theorem isPretransitive_of_le {Y' : Subgroup (Perm Pt)} (hT : sylowT ≤ Y')
    (hτ : blockShift ∈ Y') : MulAction.IsPretransitive Y' Pt := by
  refine ⟨fun x y => ?_⟩
  refine ⟨⟨shiftPerm (fun k => if k = y.1 then y.2 - x.2 else 0) *
    blockShift ^ (y.1 - x.1).val,
    mul_mem (hT (shiftPerm_mem_sylowT _)) (pow_mem hτ _)⟩, ?_⟩
  obtain ⟨i, z⟩ := x
  obtain ⟨j, w⟩ := y
  change shiftPerm (fun k => if k = j then w - z else 0) ((blockShift ^ (j - i).val) (i, z)) =
    (j, w)
  simp [blockShift_pow_val_apply]

theorem apply_mem_of_isBlock {Y' : Subgroup (Perm Pt)} {C : Set Pt}
    (hC : MulAction.IsBlock Y' C) {g : Perm Pt} (hg : g ∈ Y') {a : Pt} (ha : a ∈ C)
    (hga : g a ∈ C) {y : Pt} (hy : y ∈ C) : g y ∈ C := by
  have h := hC.smul_eq_of_mem (g := (⟨g, hg⟩ : Y')) ha hga
  have h' : (⟨g, hg⟩ : Y') • y ∈ (⟨g, hg⟩ : Y') • C := Set.smul_mem_smul_set hy
  rw [h] at h'
  exact h'

theorem block_subset_of_fst_ne {Y' : Subgroup (Perm Pt)} (hT : sylowT ≤ Y') {C : Set Pt}
    (hC : MulAction.IsBlock Y' C) {x y : Pt} (hx : x ∈ C) (hy : y ∈ C) (hxy : x.1 ≠ y.1)
    (u : ZMod 5) : (y.1, u) ∈ C := by
  have hg : shiftPerm (fun k => if k = y.1 then 1 else 0) ∈ Y' :=
    hT (shiftPerm_mem_sylowT _)
  have hgx : shiftPerm (fun k => if k = y.1 then 1 else 0) x = x := by
    simp [hxy]
  have key : ∀ k : ℕ, (y.1, y.2 + (k : ZMod 5)) ∈ C := by
    intro k
    induction k with
    | zero => simpa using hy
    | succ k ih =>
      have h := apply_mem_of_isBlock hC hg hx (by rw [hgx]; exact hx) ih
      simpa [add_assoc] using h
  have h := key (u - y.2).val
  rwa [ZMod.natCast_zmod_val, add_sub_cancel] at h

theorem eq_univ_of_fst_ne {Y' : Subgroup (Perm Pt)} (hT : sylowT ≤ Y')
    (hτ : blockShift ∈ Y') {C : Set Pt} (hC : MulAction.IsBlock Y' C) {x y : Pt} (hx : x ∈ C)
    (hy : y ∈ C) (hxy : x.1 ≠ y.1) : C = Set.univ := by
  have hy' := block_subset_of_fst_ne hT hC hx hy hxy
  have hx' := block_subset_of_fst_ne hT hC hy hx hxy.symm
  have hg : blockShift ^ (y.1 - x.1).val ∈ Y' := pow_mem hτ _
  have hga : (blockShift ^ (y.1 - x.1).val) (x.1, 0) ∈ C := by
    simpa [blockShift_pow_val_apply] using hy' 0
  have h3 : ∀ u, (y.1 + (y.1 - x.1), u) ∈ C := fun u => by
    simpa [blockShift_pow_val_apply] using apply_mem_of_isBlock hC hg (hx' 0) hga (hy' u)
  refine Set.eq_univ_of_forall fun ⟨l, u⟩ => ?_
  rcases zmod_three_cases_sub x.1 y.1 l hxy with rfl | rfl | rfl
  · exact hx' u
  · exact hy' u
  · exact h3 u

theorem block_subset_of_ne {Y' : Subgroup (Perm Pt)} (hT : sylowT ≤ Y') {C : Set Pt}
    (hC : MulAction.IsBlock Y' C) {x y : Pt} (hx : x ∈ C) (hy : y ∈ C) (hne : x ≠ y)
    (hfst : x.1 = y.1) (u : ZMod 5) : (x.1, u) ∈ C := by
  obtain ⟨i, z⟩ := x
  obtain ⟨j, w⟩ := y
  simp only at hfst
  subst hfst
  have hzw : z ≠ w := fun h => hne (by rw [h])
  have hg : shiftPerm (fun k => if k = i then w - z else 0) ∈ Y' :=
    hT (shiftPerm_mem_sylowT _)
  have h1 : shiftPerm (fun k => if k = i then w - z else 0) (i, z) = (i, w) := by simp
  have key : ∀ k : ℕ, (i, z + (k : ZMod 5) * (w - z)) ∈ C := by
    intro k
    induction k with
    | zero => simpa using hx
    | succ k ih =>
      have h := apply_mem_of_isBlock hC hg hx (by rw [h1]; exact hy) ih
      have e : (i, z + ((k + 1 : ℕ) : ZMod 5) * (w - z)) =
          shiftPerm (fun k => if k = i then w - z else 0) (i, z + (k : ZMod 5) * (w - z)) := by
        simp only [shiftPerm_apply, ite_true, Prod.mk.injEq, true_and]
        push_cast
        ring
      rw [e]
      exact h
  obtain ⟨k, hk⟩ := zmod_five_exists_mul z w u hzw
  rw [hk]
  exact key k

theorem exists_eq_fiber_of_isBlock {Y' : Subgroup (Perm Pt)} (hT : sylowT ≤ Y')
    (hτ : blockShift ∈ Y') {C : Set Pt} (hC : MulAction.IsBlock Y' C)
    (hnt : ¬ MulAction.IsTrivialBlock C) : ∃ i, C = {p : Pt | p.1 = i} := by
  rw [MulAction.IsTrivialBlock, not_or] at hnt
  obtain ⟨hns, hnu⟩ := hnt
  obtain ⟨x, hx, y, hy, hxy⟩ := Set.not_subsingleton_iff.1 hns
  have hfst : ∀ p ∈ C, ∀ q ∈ C, p.1 = q.1 := fun p hp q hq => by
    by_contra h
    exact hnu (eq_univ_of_fst_ne hT hτ hC hp hq h)
  refine ⟨x.1, Set.ext fun p => ⟨fun hp => hfst p hp x hx, fun hp => ?_⟩⟩
  have h := block_subset_of_ne hT hC hx hy hxy (hfst x hx y hy) p.2
  have hp' : p.1 = x.1 := hp
  have hpx : p = (x.1, p.2) := Prod.ext hp' rfl
  rw [hpx]
  exact h

theorem le_wr_of_not_isPreprimitive {Y' : Subgroup (Perm Pt)} (hT : sylowT ≤ Y')
    (hτ : blockShift ∈ Y') (hnp : ¬ MulAction.IsPreprimitive Y' Pt) : Y' ≤ wr := by
  have := isPretransitive_of_le hT hτ
  obtain ⟨C, hC, hnt⟩ : ∃ C : Set Pt, MulAction.IsBlock Y' C ∧ ¬ MulAction.IsTrivialBlock C := by
    by_contra hcon
    refine hnp (MulAction.IsPreprimitive.of_isTrivialBlock_base (0, 0) fun {C} _ hC => ?_)
    by_contra hC'
    exact hcon ⟨C, hC, hC'⟩
  obtain ⟨i₀, rfl⟩ := exists_eq_fiber_of_isBlock hT hτ hC hnt
  have hfib : ∀ i, MulAction.IsBlock Y' {p : Pt | p.1 = i} := fun i => by
    have h := hC.translate (⟨blockShift ^ (i - i₀).val, pow_mem hτ _⟩ : Y')
    convert h using 1
    ext ⟨j, z⟩
    simp [Set.mem_smul_set, blockShift_pow_val_apply, eq_comm]
  have hfib_nt : ∀ i, ¬ MulAction.IsTrivialBlock {p : Pt | p.1 = i} := fun i => by
    rw [MulAction.IsTrivialBlock, not_or]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have h01 := h (show ((i, 0) : Pt) ∈ {p : Pt | p.1 = i} from rfl)
        (show ((i, 1) : Pt) ∈ {p : Pt | p.1 = i} from rfl)
      have hne : (0 : ZMod 5) ≠ 1 := by decide
      exact hne (congrArg Prod.snd h01)
    · have := h.symm ▸ (Set.mem_univ ((i + 1, 0) : Pt))
      simp at this
  have hmap : ∀ g ∈ Y', FibConst g := by
    intro g hg p q hpq
    have h := (hfib p.1).translate (⟨g, hg⟩ : Y')
    have hnt' : ¬ MulAction.IsTrivialBlock ((⟨g, hg⟩ : Y') • {r : Pt | r.1 = p.1}) :=
      fun h' => hfib_nt p.1 ((MulAction.IsTrivialBlock.smul_iff _).1 h')
    obtain ⟨j, hj⟩ := exists_eq_fiber_of_isBlock hT hτ h hnt'
    have hp : g p ∈ (⟨g, hg⟩ : Y') • {r : Pt | r.1 = p.1} := Set.smul_mem_smul_set rfl
    have hq : g q ∈ (⟨g, hg⟩ : Y') • {r : Pt | r.1 = p.1} := Set.smul_mem_smul_set hpq.symm
    rw [hj] at hp hq
    exact hp.trans hq.symm
  intro g hg
  exact ⟨hmap g hg, hmap g⁻¹ (inv_mem hg)⟩

end BlocksMax

theorem le_wr_or_alternatingGroup_le {Y' : Subgroup (Perm Pt)} (hT : sylowT ≤ Y')
    (hτ : blockShift ∈ Y') (h3 : ∃ g ∈ Y', g.IsThreeCycle) :
    Y' ≤ wr ∨ alternatingGroup Pt ≤ Y' := by
  by_cases hprim : MulAction.IsPreprimitive Y' Pt
  · obtain ⟨g, hg, hg3⟩ := h3
    exact Or.inr (Perm.alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem hprim hg3 hg)
  · exact Or.inl (BlocksMax.le_wr_of_not_isPreprimitive hT hτ hprim)

end CFSG.AGLEmbedding.A15Local
