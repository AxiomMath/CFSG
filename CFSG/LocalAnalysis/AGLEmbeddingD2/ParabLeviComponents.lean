module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.ParabLevi

public section

namespace CFSG.AGLEmbeddingD2.ParabLevi

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem CFSG.LieType.Steinberg

variable {K : Type*} [Group K]

section Defs

variable (D : UniversalRootDatum K)

@[expose] def NodeAdj (J : Set (Fin D.rank)) (i j : Fin D.rank) : Prop :=
  i ∈ J ∧ j ∈ J ∧ (TauCeti.diagramGraph D.cartan).Adj i j

@[expose] def nodeComponent (J : Set (Fin D.rank)) (i : Fin D.rank) : Set (Fin D.rank) :=
  {j | Relation.ReflTransGen (NodeAdj D J) i j}

@[expose] def IsNodeConnected (C : Set (Fin D.rank)) : Prop :=
  C.Nonempty ∧ ∀ i ∈ C, ∀ j ∈ C, Relation.ReflTransGen (NodeAdj D C) i j

end Defs

variable {D : UniversalRootDatum K} {J : Set (Fin D.rank)} {i j : Fin D.rank}

theorem NodeAdj.symm (h : NodeAdj D J i j) : NodeAdj D J j i :=
  ⟨h.2.1, h.1, h.2.2.symm⟩

private theorem nodeAdj_lt_of_val {C : Set (Fin D.rank)} {j x y : Fin D.rank} (hj : j ∉ C)
    (hadj : ∀ ⦃i j : Fin D.rank⦄, NodeAdj D C i j → i.val + 1 = j.val ∨ j.val + 1 = i.val)
    (h : NodeAdj D C x y) (hx : x.val < j.val) : y.val < j.val := by
  have hyC : y ∈ C := h.2.1
  have hne : y.val ≠ j.val := fun he => hj (Fin.ext he ▸ hyC)
  rcases hadj h with h1 | h1
  · rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact hlt
    · omega
  · omega

private theorem lt_of_reflTransGen_of_val {C : Set (Fin D.rank)} {j : Fin D.rank} (hj : j ∉ C)
    (hadj : ∀ ⦃i j : Fin D.rank⦄, NodeAdj D C i j → i.val + 1 = j.val ∨ j.val + 1 = i.val)
    {x y : Fin D.rank} (h : Relation.ReflTransGen (NodeAdj D C) x y) :
    x.val < j.val → y.val < j.val := by
  induction h with
  | refl => exact id
  | tail _ hbc ih => exact fun hx => nodeAdj_lt_of_val hj hadj hbc (ih hx)

private theorem convex_of_path_of_val {C : Set (Fin D.rank)} {a b : Fin D.rank} (ha : a ∈ C)
    (hadj : ∀ ⦃i j : Fin D.rank⦄, NodeAdj D C i j → i.val + 1 = j.val ∨ j.val + 1 = i.val)
    (hpath : Relation.ReflTransGen (NodeAdj D C) a b) :
    ∀ j : Fin D.rank, a.val ≤ j.val → j.val ≤ b.val → j ∈ C := by
  intro j haj hjb
  by_contra hj
  have haj' : a.val < j.val := lt_of_le_of_ne haj (fun h => hj (Fin.ext h ▸ ha))
  exact absurd (lt_of_reflTransGen_of_val hj hadj hpath haj') (by omega)

theorem IsNodeConnected.exists_eq_Icc {C : Set (Fin D.rank)} (hC : IsNodeConnected D C)
    (hadj : ∀ ⦃i j : Fin D.rank⦄, NodeAdj D C i j → i.val + 1 = j.val ∨ j.val + 1 = i.val) :
    ∃ a b : Fin D.rank, a ∈ C ∧ b ∈ C ∧ C = Set.Icc a b := by
  classical
  have hne : C.toFinset.Nonempty := by
    obtain ⟨x, hx⟩ := hC.1
    exact ⟨x, Set.mem_toFinset.mpr hx⟩
  refine ⟨C.toFinset.min' hne, C.toFinset.max' hne, ?_, ?_, ?_⟩
  · exact Set.mem_toFinset.mp (C.toFinset.min'_mem hne)
  · exact Set.mem_toFinset.mp (C.toFinset.max'_mem hne)
  · apply Set.Subset.antisymm
    · intro x hx
      let hx' : x ∈ C.toFinset := Set.mem_toFinset.mpr hx
      have hproof : (⟨x, hx'⟩ : C.toFinset.Nonempty) = hne := Subsingleton.elim _ _
      refine ⟨?_, ?_⟩
      · have h := C.toFinset.min'_le x hx'
        rwa [hproof] at h
      · have h := C.toFinset.le_max' x hx'
        rwa [hproof] at h
    · intro x hx
      exact convex_of_path_of_val (C := C) (a := C.toFinset.min' hne) (b := C.toFinset.max' hne)
        (Set.mem_toFinset.mp (C.toFinset.min'_mem hne)) hadj
        (hC.2 (C.toFinset.min' hne) (Set.mem_toFinset.mp (C.toFinset.min'_mem hne))
          (C.toFinset.max' hne) (Set.mem_toFinset.mp (C.toFinset.max'_mem hne)))
        x (Fin.le_def.mp hx.1) (Fin.le_def.mp hx.2)

theorem mem_nodeComponent_self (J : Set (Fin D.rank)) (i : Fin D.rank) :
    i ∈ nodeComponent D J i :=
  Relation.ReflTransGen.refl

private theorem nodeComponent_reverse {a b : Fin D.rank}
    (h : Relation.ReflTransGen (NodeAdj D J) a b) :
    Relation.ReflTransGen (NodeAdj D J) b a := by
  induction h with
  | refl => exact .refl
  | tail _ hbc ih => exact ih.head hbc.symm

private theorem nodeComponent_path {a b : Fin D.rank}
    (h : Relation.ReflTransGen (NodeAdj D J) i a)
    (hab : Relation.ReflTransGen (NodeAdj D J) a b) :
    Relation.ReflTransGen (NodeAdj D (nodeComponent D J i)) a b := by
  induction hab with
  | refl => exact .refl
  | tail hac hcd ih =>
    exact ih.tail ⟨h.trans hac, h.trans (hac.tail hcd), hcd.2.2⟩

theorem nodeComponent_subset (hi : i ∈ J) : nodeComponent D J i ⊆ J := by
  intro j hj
  induction hj with
  | refl => exact hi
  | tail _ hbc _ => exact hbc.2.1

theorem nodeComponent_eq_of_mem (hj : j ∈ nodeComponent D J i) :
    nodeComponent D J j = nodeComponent D J i := by
  refine le_antisymm ?_ ?_
  · intro k hk
    exact hj.trans hk
  · intro k hk
    exact (nodeComponent_reverse hj).trans hk

theorem isNodeConnected_nodeComponent (hi : i ∈ J) : IsNodeConnected D (nodeComponent D J i) := by
  have _ : i ∈ J := hi
  refine ⟨⟨i, Relation.ReflTransGen.refl⟩, fun j hj k hk => ?_⟩
  exact nodeComponent_path hj ((nodeComponent_reverse hj).trans hk)

theorem cartan_eq_zero_of_nodeComponent_ne (hi : i ∈ J) (hj : j ∈ J)
    (hne : nodeComponent D J i ≠ nodeComponent D J j) {k l : Fin D.rank}
    (hk : k ∈ nodeComponent D J i) (hl : l ∈ nodeComponent D J j) : D.cartan k l = 0 := by
  by_contra hc
  have hkl : k ≠ l := by
    rintro rfl
    exact hne ((nodeComponent_eq_of_mem hk).symm.trans (nodeComponent_eq_of_mem hl))
  have hadj : NodeAdj D J k l :=
    ⟨nodeComponent_subset hi hk, nodeComponent_subset hj hl,
      D.isFiniteType.diagramGraph_adj_iff.mpr ⟨hkl, hc⟩⟩
  have hl' : l ∈ nodeComponent D J k := Relation.ReflTransGen.single hadj
  exact hne ((nodeComponent_eq_of_mem hk).symm.trans
    ((nodeComponent_eq_of_mem hl').symm.trans (nodeComponent_eq_of_mem hl)))

theorem leviM_eq_iSup_leviM_nodeComponent :
    leviM D J = ⨆ i ∈ J, leviM D (nodeComponent D J i) := by
  refine le_antisymm ?_ ?_
  · refine iSup₂_le fun i hi => ?_
    exact le_iSup₂_of_le i hi (rankOne_le_leviM (mem_nodeComponent_self (D := D) J i))
  · refine iSup₂_le fun i hi => ?_
    refine iSup₂_le fun j hj => ?_
    exact le_iSup₂_of_le j (nodeComponent_subset hi hj) le_rfl

theorem eq_univ_of_two_le_ncard (hr : D.rank ≤ 2) {C : Set (Fin D.rank)} (hC : 2 ≤ C.ncard) :
    C = Set.univ := by
  refine Set.eq_of_subset_of_ncard_le (Set.subset_univ C) ?_
  rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
  omega

end CFSG.AGLEmbeddingD2.ParabLevi
