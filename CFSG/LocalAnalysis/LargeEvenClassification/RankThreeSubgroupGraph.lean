module

public import CFSG.LocalAnalysis.LargeEvenClassification.SubgroupTransport

public section

namespace CFSG.LargeEvenClassification

open CFSG.Open

universe u v

@[expose] def E3 (G : Type u) [Group G] : Set (Subgroup G) :=
  {A | IsElemAbelian 2 A ∧ Nat.card A = 8}

@[expose] def RankThreeVertex (G : Type u) [Group G] :=
  {A : Subgroup G // A ∈ E3 G}

@[expose] def RankThreeSubgroupGraph (G : Type u) [Group G] :
    SimpleGraph (RankThreeVertex G) where
  Adj A B := Nat.card (A.val ⊓ B.val : Subgroup G) = 4
  symm := by
    constructor
    intro A B h
    simpa only [inf_comm] using h
  loopless := by
    constructor
    intro A h
    have hcard : Nat.card A.val = 8 := A.property.2
    simp only [inf_idem, hcard] at h
    norm_num at h

@[expose] def RankThreeSubgroupPath {G : Type u} [Group G]
    (A B : Subgroup G) : Prop :=
  ∃ n : ℕ, ∃ path : Fin (n + 1) → RankThreeVertex G,
    (path 0).val = A ∧ (path (Fin.last n)).val = B ∧
      ∀ i : Fin n, Nat.card ((path i.castSucc).val ⊓ (path i.succ).val : Subgroup G) = 4

@[expose] def Conn3 (G : Type u) [Group G] : Prop :=
  (E3 G).Nonempty ∧ ∀ A B : RankThreeVertex G, RankThreeSubgroupPath A.val B.val

variable {G : Type u} [Group G]

theorem mem_E3_iff (A : Subgroup G) :
    A ∈ E3 G ↔ IsElemAbelian 2 A ∧ Nat.card A = 8 := Iff.rfl

theorem rankThree_graph_adj_iff (A B : RankThreeVertex G) :
    (RankThreeSubgroupGraph G).Adj A B ↔ Nat.card (A.val ⊓ B.val : Subgroup G) = 4 :=
  Iff.rfl

instance rankThreeVertex_finite [Finite G] : Finite (RankThreeVertex G) :=
  inferInstanceAs (Finite {A : Subgroup G // A ∈ E3 G})

theorem rankThree_path_iff_subgroup_sequence (A B : Subgroup G) :
    RankThreeSubgroupPath A B ↔
      ∃ n : ℕ, ∃ path : Fin (n + 1) → Subgroup G,
        path 0 = A ∧ path (Fin.last n) = B ∧
        (∀ i, IsElemAbelian 2 (path i) ∧ Nat.card (path i) = 8) ∧
        ∀ i : Fin n, Nat.card (path i.castSucc ⊓ path i.succ : Subgroup G) = 4 := by
  constructor
  · rintro ⟨n, path, hfirst, hlast, hsteps⟩
    exact ⟨n, fun i => (path i).val, hfirst, hlast, fun i => (path i).property, hsteps⟩
  · rintro ⟨n, path, hfirst, hlast, hvertices, hsteps⟩
    exact ⟨n, fun i => ⟨path i, hvertices i⟩, hfirst, hlast, hsteps⟩

theorem rankThree_path_endpoints {A B : Subgroup G} (h : RankThreeSubgroupPath A B) :
    A ∈ E3 G ∧ B ∈ E3 G := by
  obtain ⟨n, path, hfirst, hlast, _⟩ := h
  exact ⟨hfirst ▸ (path 0).property, hlast ▸ (path (Fin.last n)).property⟩

theorem rankThree_path_refl (A : Subgroup G) (hA : A ∈ E3 G) :
    RankThreeSubgroupPath A A := by
  exact ⟨0, fun _ => ⟨A, hA⟩, rfl, rfl, fun i => Fin.elim0 i⟩

theorem rankThree_path_of_intersection_four (A B : Subgroup G)
    (hA : A ∈ E3 G) (hB : B ∈ E3 G) (hcard : Nat.card (A ⊓ B : Subgroup G) = 4) :
    RankThreeSubgroupPath A B := by
  let path : Fin 2 → RankThreeVertex G := Fin.cons ⟨A, hA⟩ (fun _ => ⟨B, hB⟩)
  refine ⟨1, path, rfl, rfl, ?_⟩
  intro i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  exact hcard

theorem rankThree_sequence_reachable {n : ℕ} (path : Fin (n + 1) → RankThreeVertex G)
    (hsteps : ∀ i : Fin n,
      Nat.card ((path i.castSucc).val ⊓ (path i.succ).val : Subgroup G) = 4) :
    (RankThreeSubgroupGraph G).Reachable (path 0) (path (Fin.last n)) := by
  induction n with
  | zero => exact SimpleGraph.Reachable.rfl
  | succ n induction =>
    let tail : Fin (n + 1) → RankThreeVertex G := fun i => path i.succ
    have htail : ∀ i : Fin n,
        Nat.card ((tail i.castSucc).val ⊓ (tail i.succ).val : Subgroup G) = 4 := by
      intro i
      simpa only [tail, Fin.succ_castSucc] using hsteps i.succ
    have hrest := induction tail htail
    have hfirst : (RankThreeSubgroupGraph G).Adj (path 0) (tail 0) := hsteps 0
    simpa only [tail, Fin.succ_last] using hfirst.reachable.trans hrest

theorem rankThree_walk_subgroup_path {A B : RankThreeVertex G}
    (walk : (RankThreeSubgroupGraph G).Walk A B) : RankThreeSubgroupPath A.val B.val := by
  refine ⟨walk.length, fun i => walk.getVert i.val, ?_, ?_, ?_⟩
  · exact congrArg Subtype.val walk.getVert_zero
  · exact congrArg Subtype.val walk.getVert_length
  · intro i
    exact walk.adj_getVert_succ i.isLt

theorem rankThree_path_iff_reachable (A B : RankThreeVertex G) :
    RankThreeSubgroupPath A.val B.val ↔ (RankThreeSubgroupGraph G).Reachable A B := by
  constructor
  · rintro ⟨n, path, hfirst, hlast, hsteps⟩
    have hfirstVertex : path 0 = A := Subtype.ext hfirst
    have hlastVertex : path (Fin.last n) = B := Subtype.ext hlast
    exact hfirstVertex ▸ hlastVertex ▸ rankThree_sequence_reachable path hsteps
  · rintro ⟨walk⟩
    exact rankThree_walk_subgroup_path walk

theorem rankThree_sequence_reverse {n : ℕ} (path : Fin (n + 1) → RankThreeVertex G)
    (hsteps : ∀ i : Fin n,
      Nat.card ((path i.castSucc).val ⊓ (path i.succ).val : Subgroup G) = 4) :
    (fun i : Fin (n + 1) => path i.rev) 0 = path (Fin.last n) ∧
    (fun i : Fin (n + 1) => path i.rev) (Fin.last n) = path 0 ∧
    ∀ i : Fin n,
      Nat.card ((path i.castSucc.rev).val ⊓ (path i.succ.rev).val : Subgroup G) = 4 := by
  refine ⟨by simp only [Fin.rev_zero], by simp only [Fin.rev_last], ?_⟩
  intro i
  simpa only [Fin.rev_castSucc, Fin.rev_succ, inf_comm] using hsteps i.rev

theorem rankThree_path_symm {A B : Subgroup G} (h : RankThreeSubgroupPath A B) :
    RankThreeSubgroupPath B A := by
  obtain ⟨n, path, hfirst, hlast, hsteps⟩ := h
  obtain ⟨hreverseFirst, hreverseLast, hreverseSteps⟩ :=
    rankThree_sequence_reverse path hsteps
  exact ⟨n, fun i => path i.rev, congrArg Subtype.val hreverseFirst |>.trans hlast,
    congrArg Subtype.val hreverseLast |>.trans hfirst, hreverseSteps⟩

theorem rankThree_path_trans {A B C : Subgroup G}
    (hAB : RankThreeSubgroupPath A B) (hBC : RankThreeSubgroupPath B C) :
    RankThreeSubgroupPath A C := by
  obtain ⟨hA, hB⟩ := rankThree_path_endpoints hAB
  obtain ⟨_, hC⟩ := rankThree_path_endpoints hBC
  exact (rankThree_path_iff_reachable ⟨A, hA⟩ ⟨C, hC⟩).mpr
    (((rankThree_path_iff_reachable ⟨A, hA⟩ ⟨B, hB⟩).mp hAB).trans
      ((rankThree_path_iff_reachable ⟨B, hB⟩ ⟨C, hC⟩).mp hBC))

theorem rankThree_path_map {H : Type v} [Group H] (f : G →* H)
    (hinjective : Function.Injective f) {A B : Subgroup G}
    (h : RankThreeSubgroupPath A B) : RankThreeSubgroupPath (A.map f) (B.map f) := by
  obtain ⟨n, path, hfirst, hlast, hvertices, hsteps⟩ :=
    (rankThree_path_iff_subgroup_sequence A B).mp h
  apply (rankThree_path_iff_subgroup_sequence (A.map f) (B.map f)).mpr
  refine ⟨n, fun i => (path i).map f, congrArg (fun X => X.map f) hfirst,
    congrArg (fun X => X.map f) hlast, ?_, ?_⟩
  · intro i
    exact ⟨Helpers.elementary_map (path i) (hvertices i).1 f,
      (Subgroup.card_map_of_injective hinjective).trans (hvertices i).2⟩
  · intro i
    rw [← Subgroup.map_inf _ _ f hinjective, Subgroup.card_map_of_injective hinjective]
    exact hsteps i

theorem conn3_iff_graph_connected : Conn3 G ↔ (RankThreeSubgroupGraph G).Connected := by
  rw [SimpleGraph.connected_iff]
  constructor
  · rintro ⟨⟨A, hA⟩, hpaths⟩
    exact ⟨fun A B => (rankThree_path_iff_reachable A B).mp (hpaths A B), ⟨⟨A, hA⟩⟩⟩
  · rintro ⟨hconnected, ⟨A⟩⟩
    exact ⟨⟨A.val, A.property⟩,
      fun A B => (rankThree_path_iff_reachable A B).mpr (hconnected A B)⟩

end CFSG.LargeEvenClassification
