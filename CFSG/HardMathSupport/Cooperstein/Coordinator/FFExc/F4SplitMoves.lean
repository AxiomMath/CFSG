module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc.F4SplitTables

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc

open CFSG.Blueprint.Chevalley Matrix

@[expose] def mvIdx : ℕ → ℕ → ℕ
  | 0, k => Tag.E6.rootCertificate.image k ⟨1, by decide⟩
  | 1, k => Tag.E6.rootCertificate.image k ⟨3, by decide⟩
  | 2, k => Tag.E6.rootCertificate.image (Tag.E6.rootCertificate.image k ⟨5, by decide⟩) ⟨0, by decide⟩
  | _, k => Tag.E6.rootCertificate.image (Tag.E6.rootCertificate.image k ⟨4, by decide⟩) ⟨2, by decide⟩

@[expose] def ord : List (ℕ × ℕ × ℕ) := [(6, 0, 2), (7, 0, 3), (8, 1, 0), (9, 1, 1), (11, 2, 1), (10, 2, 3), (12, 3, 1), (23, 3, 3), (13, 4, 1), (15, 4, 2), (14, 4, 3), (16, 5, 2), (17, 6, 3), (18, 7, 1), (19, 8, 1), (32, 9, 3), (20, 11, 0), (22, 10, 1), (34, 12, 3), (40, 23, 2), (21, 13, 0), (25, 13, 2), (24, 14, 1), (26, 14, 2), (27, 17, 1), (28, 18, 0), (29, 18, 3), (41, 19, 3), (43, 32, 1), (49, 32, 2), (30, 22, 0), (47, 34, 2), (33, 21, 2), (35, 25, 3), (31, 24, 0), (36, 24, 2), (37, 27, 0), (38, 27, 3), (39, 28, 3), (50, 41, 1), (54, 41, 2), (56, 43, 2), (44, 33, 3), (42, 31, 2), (45, 36, 3), (46, 37, 3), (48, 39, 1), (60, 50, 2), (66, 56, 3), (52, 44, 1), (51, 42, 3), (53, 46, 1), (55, 48, 3), (67, 60, 3), (68, 66, 1), (58, 52, 3), (57, 51, 1), (59, 53, 3), (61, 55, 2), (69, 67, 1), (70, 68, 0), (62, 58, 2), (63, 57, 3), (64, 59, 2), (71, 69, 0), (65, 63, 2)]

theorem ord_step_check : ∀ t ∈ ord, t.1 < 72 ∧ t.2.1 < 72 ∧ mvIdx t.2.2 t.2.1 = t.1 ∧
    (gamK t.1 = t.1 ↔ gamK t.2.1 = t.2.1) ∧ gamK t.1 = mvIdx t.2.2 (gamK t.2.1) := by
  decide +kernel

theorem ord_chain : ∀ i < ord.length, (ord.getD i (0, 0, 0)).2.1 < 6 ∨
    ∃ j < i, (ord.getD j (0, 0, 0)).1 = (ord.getD i (0, 0, 0)).2.1 := by
  decide +kernel

theorem ord_cover : ∀ k < 72, k < 6 ∨ ∃ i < ord.length, (ord.getD i (0, 0, 0)).1 = k := by
  decide +kernel

theorem e6root_inj : ∀ a < 72, ∀ b < 72, e6root a = e6root b → a = b := by
  decide +kernel

theorem e6root_simple : ∀ k : Fin Tag.E6.rank, e6root k = Pi.single k 1 := by
  decide +kernel

theorem reach_all (P : ℕ → Prop) (base : ∀ k < 6, P k)
    (step : ∀ k p m, (k, p, m) ∈ ord → P p → P k) : ∀ k < 72, P k := by
  have key : ∀ i, i < ord.length → P (ord.getD i (0, 0, 0)).1 := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      have hmem : ord.getD i (0, 0, 0) ∈ ord := by
        rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi
      refine step _ (ord.getD i (0, 0, 0)).2.1 (ord.getD i (0, 0, 0)).2.2 hmem ?_
      rcases ord_chain i hi with h | ⟨j, hj, hjk⟩
      · exact base _ h
      · rw [← hjk]; exact ih j hj (by omega)
  intro k hk
  rcases ord_cover k hk with h | ⟨i, hi, rfl⟩
  · exact base k h
  · exact key i hi

theorem Em2_start : Em2 0 *ᵥ s3Z = Pi.single ⟨10, by decide⟩ 1 := by decide +kernel

@[expose] def wtree : List (ℕ × ℕ × ℕ) := [(8, 10, 2), (12, 10, 6), (6, 10, 11), (13, 10, 16), (5, 10, 20), (4, 10, 23), (16, 10, 26), (3, 10, 32), (18, 10, 36), (20, 10, 42), (2, 10, 43), (22, 10, 47), (23, 10, 54), (0, 10, 55), (24, 10, 60), (25, 10, 65), (11, 8, 16), (14, 8, 26), (1, 8, 43), (19, 8, 47), (21, 8, 54), (15, 12, 16), (17, 12, 26), (9, 6, 16), (7, 13, 20), (26, 13, 65)]

theorem wtree_step : ∀ t ∈ wtree, t.1 < 27 ∧ t.2.1 < 27 ∧ t.2.2 < 72 ∧ tgt t.2.2 t.2.1 = t.1 + 1 := by
  decide +kernel

theorem wtree_chain : ∀ i < wtree.length, (wtree.getD i (0, 0, 0)).2.1 = 10 ∨
    ∃ j < i, (wtree.getD j (0, 0, 0)).1 = (wtree.getD i (0, 0, 0)).2.1 := by
  decide +kernel

theorem wtree_cover : ∀ a < 27, a = 10 ∨ ∃ i < wtree.length, (wtree.getD i (0, 0, 0)).1 = a := by
  decide +kernel

theorem wtree_reach (P : ℕ → Prop) (base : P 10)
    (step : ∀ a p k, (a, p, k) ∈ wtree → P p → P a) : ∀ a < 27, P a := by
  have key : ∀ i, i < wtree.length → P (wtree.getD i (0, 0, 0)).1 := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      have hmem : wtree.getD i (0, 0, 0) ∈ wtree := by
        rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi
      have hmem' : ((wtree.getD i (0, 0, 0)).1, (wtree.getD i (0, 0, 0)).2.1,
          (wtree.getD i (0, 0, 0)).2.2) ∈ wtree := hmem
      refine step _ _ _ hmem' ?_
      rcases wtree_chain i hi with h | ⟨j, hj, hjk⟩
      · rw [h]; exact base
      · rw [← hjk]; exact ih j hj (by omega)
  intro a ha
  rcases wtree_cover a ha with h | ⟨i, hi, rfl⟩
  · rw [h]; exact base
  · exact key i hi

end CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc
