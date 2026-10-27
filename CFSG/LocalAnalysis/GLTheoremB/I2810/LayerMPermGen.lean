module

public import CFSG.LocalAnalysis.GLTheoremB.Prop95IvDefs
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434AltGen

public section

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.LayerM

namespace PermGenAux

open Equiv Equiv.Perm Subgroup
open CFSG.LocalAnalysis.ComponentInitial (altThreeCyclePerm)
open CFSG.RankThree.PartTwo.Sec4.Item434AltPerm (alternatingGroup_le_closure)

theorem top_le_iSup_conj {n k r : ℕ} (H : Subgroup ↥(alternatingGroup (Fin n)))
    (y : Fin k → ↥(alternatingGroup (Fin n))) (ι : Fin r → Fin k)
    (η : Fin r → ↥(alternatingGroup (Fin n))) (hη : ∀ j, η j ∈ H)
    (hgen : alternatingGroup (Fin n) ≤ closure (Set.range fun j =>
      (y (ι j) : Perm (Fin n)) * (η j : Perm (Fin n)) * (y (ι j) : Perm (Fin n))⁻¹)) :
    ⊤ ≤ ⨆ i, H.map (MulAut.conj (y i)).toMonoidHom := by
  have h1 : closure (Set.range fun j =>
      (y (ι j) : Perm (Fin n)) * (η j : Perm (Fin n)) * (y (ι j) : Perm (Fin n))⁻¹) ≤
      (⨆ i, H.map (MulAut.conj (y i)).toMonoidHom).map (alternatingGroup (Fin n)).subtype := by
    rw [closure_le]
    rintro _ ⟨j, rfl⟩
    exact ⟨y (ι j) * η j * (y (ι j))⁻¹, mem_iSup_of_mem (ι j) ⟨η j, hη j, rfl⟩, rfl⟩
  intro x _
  obtain ⟨z, hz, hzx⟩ := h1 (hgen x.2)
  exact (Subtype.ext hzx : z = x) ▸ hz

theorem top_le_iSup_conj_of_words {m k r : ℕ} (H : Subgroup ↥(alternatingGroup (Fin (m + 2))))
    (y : Fin k → ↥(alternatingGroup (Fin (m + 2)))) (ι : Fin r → Fin k)
    (η : Fin r → ↥(alternatingGroup (Fin (m + 2)))) (hη : ∀ j, η j ∈ H)
    (w : Fin m → List (Fin r))
    (hw : ∀ i, altThreeCyclePerm i = ((w i).map fun j =>
      (y (ι j) : Perm (Fin (m + 2))) * (η j : Perm (Fin (m + 2))) *
        (y (ι j) : Perm (Fin (m + 2)))⁻¹).prod) :
    ⊤ ≤ ⨆ i, H.map (MulAut.conj (y i)).toMonoidHom :=
  top_le_iSup_conj H y ι η hη (alternatingGroup_le_closure _ w hw)

theorem klein_ab_sq {G : Type*} [Group G] {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (hab : b * a = a * b) : a * b * (a * b) = 1 := by
  rw [mul_assoc, ← mul_assoc b a b, hab, mul_assoc a b b, hb, mul_one, ha]

@[expose] def kleinOf {G : Type*} [Group G] (a b : G) (ha : a * a = 1) (hb : b * b = 1)
    (hab : b * a = a * b) : Subgroup G where
  carrier := {1, a, b, a * b}
  one_mem' := Or.inl rfl
  mul_mem' := by
    intro x y hx hy
    have e4 : a * (a * b) = b := by rw [← mul_assoc, ha, one_mul]
    have e5 : b * (a * b) = a := by rw [← mul_assoc, hab, mul_assoc, hb, mul_one]
    have e6 : a * b * a = b := by rw [mul_assoc, hab, e4]
    have e7 : a * b * b = a := by rw [mul_assoc, hb, mul_one]
    have e8 : a * b * (a * b) = 1 := klein_ab_sq ha hb hab
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy ⊢
    rcases hx with h | h | h | h <;> rcases hy with h' | h' | h' | h' <;> rw [h, h'] <;>
      simp [ha, hb, hab, e4, e5, e6, e7, e8]
  inv_mem' := by
    intro x hx
    have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
    have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    rcases hx with h | h | h | h <;> rw [h]
    · simp
    · simp [ha']
    · simp [hb']
    · simp [mul_inv_rev, ha', hb', hab]

theorem mem_kleinOf_iff {G : Type*} [Group G] {a b : G} {ha : a * a = 1} {hb : b * b = 1}
    {hab : b * a = a * b} {x : G} :
    x ∈ kleinOf a b ha hb hab ↔ x = 1 ∨ x = a ∨ x = b ∨ x = a * b := by
  show x ∈ ({1, a, b, a * b} : Set G) ↔ _
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]

theorem exists_rootFour {n : ℕ} (a b : ↥(alternatingGroup (Fin n)))
    (ha : a * a = 1) (hb : b * b = 1) (hab : b * a = a * b) (ha1 : a ≠ 1) (hb1 : b ≠ 1)
    (hne : a ≠ b)
    (hmv : (Finset.univ.filter fun i : Fin n =>
      ¬ ((a : Perm (Fin n)) i = i ∧ (b : Perm (Fin n)) i = i)).card = 4) :
    ∃ W : Subgroup ↥(alternatingGroup (Fin n)), IsRootFour W ∧ a ∈ W ∧ b ∈ W := by
  have haW : a ∈ kleinOf a b ha hb hab := mem_kleinOf_iff.2 (Or.inr (Or.inl rfl))
  have hbW : b ∈ kleinOf a b ha hb hab := mem_kleinOf_iff.2 (Or.inr (Or.inr (Or.inl rfl)))
  refine ⟨kleinOf a b ha hb hab, And.intro ?_ (And.intro ?_ ?_), haW, hbW⟩
  · have h : Nat.card ↥(kleinOf a b ha hb hab) =
        Set.ncard ({1, a, b, a * b} : Set ↥(alternatingGroup (Fin n))) :=
      Nat.card_coe_set_eq _
    have hab1 : a * b ≠ 1 := fun h =>
      hne ((inv_eq_of_mul_eq_one_right ha).symm.trans (inv_eq_of_mul_eq_one_right h))
    have h1 : (1 : ↥(alternatingGroup (Fin n))) ∉ ({a, b, a * b} : Set _) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨ha1.symm, hb1.symm, hab1.symm⟩
    have h2 : a ∉ ({b, a * b} : Set ↥(alternatingGroup (Fin n))) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hne, fun h => hb1 (by simpa using h)⟩
    have h3 : b ≠ a * b := fun h => ha1 (by simpa using h)
    rw [h, Set.ncard_insert_of_notMem h1, Set.ncard_insert_of_notMem h2, Set.ncard_pair h3]
  · intro v hv
    rcases mem_kleinOf_iff.1 hv with h | h | h | h <;> rw [h]
    · exact one_pow 2
    · rw [sq]; exact ha
    · rw [sq]; exact hb
    · rw [sq]; exact klein_ab_sq ha hb hab
  · have hiff : ∀ i : Fin n, (¬ ∀ v ∈ kleinOf a b ha hb hab, (v : Perm (Fin n)) i = i) ↔
        ¬ ((a : Perm (Fin n)) i = i ∧ (b : Perm (Fin n)) i = i) := by
      intro i
      refine not_congr ⟨fun h => ⟨h a haW, h b hbW⟩, ?_⟩
      rintro ⟨h1, h2⟩ v hv
      rcases mem_kleinOf_iff.1 hv with h | h | h | h <;> rw [h]
      · rfl
      · exact h1
      · exact h2
      · show (a : Perm (Fin n)) ((b : Perm (Fin n)) i) = i
        rw [h2, h1]
    rw [Nat.card_congr (Equiv.subtypeEquivRight hiff), Nat.card_eq_fintype_card,
      Fintype.card_subtype]
    exact hmv

section Seven

@[expose] def a7 : ↥(alternatingGroup (Fin 7)) :=
  ⟨swap 0 1 * swap 2 3, mem_alternatingGroup.2 (by decide +kernel)⟩

@[expose] def b7 : ↥(alternatingGroup (Fin 7)) :=
  ⟨swap 0 2 * swap 1 3, mem_alternatingGroup.2 (by decide +kernel)⟩

theorem a7_sq : a7 * a7 = 1 := by decide +kernel

theorem b7_sq : b7 * b7 = 1 := by decide +kernel

theorem b7_a7 : b7 * a7 = a7 * b7 := by decide +kernel

theorem a7_ne_one : a7 ≠ 1 := by decide +kernel

theorem b7_ne_one : b7 ≠ 1 := by decide +kernel

theorem a7_ne_b7 : a7 ≠ b7 := by decide +kernel

theorem moved7 : (Finset.univ.filter fun i : Fin 7 =>
    ¬ ((a7 : Perm (Fin 7)) i = i ∧ (b7 : Perm (Fin 7)) i = i)).card = 4 := by decide +kernel

@[expose] def yP7a : Fin 3 → Perm (Fin 7) :=
  ![swap 1 6 * swap 6 5, swap 0 5 * swap 3 6, swap 2 4 * swap 4 6]

theorem yP7a_even : ∀ i, yP7a i ∈ alternatingGroup (Fin 7) := fun i =>
  mem_alternatingGroup.2 (by revert i; decide +kernel)

@[expose] def y7a : Fin 3 → ↥(alternatingGroup (Fin 7)) := fun i => ⟨yP7a i, yP7a_even i⟩

@[expose] def words7a : Fin 5 → List (Fin 3) :=
  ![[1, 2, 0, 1, 2, 1, 0, 2, 0, 1], [0, 1, 0, 2, 1, 2, 1], [2, 1, 2, 1, 2, 0, 1, 0, 2],
    [1, 2, 1, 2], [1, 2, 1, 0, 2, 0, 1, 2, 1, 0]]

theorem gen7a : ⊤ ≤ ⨆ i, (zpowers a7).map (MulAut.conj (y7a i)).toMonoidHom :=
  top_le_iSup_conj_of_words (m := 5) (zpowers a7) y7a (fun j => j) (fun _ => a7)
    (fun _ => mem_zpowers a7) words7a (by decide +kernel)

@[expose] def yP7w : Fin 2 → Perm (Fin 7) := ![swap 0 6 * swap 2 5, swap 0 4 * swap 4 1]

theorem yP7w_even : ∀ i, yP7w i ∈ alternatingGroup (Fin 7) := fun i =>
  mem_alternatingGroup.2 (by revert i; decide +kernel)

@[expose] def y7w : Fin 2 → ↥(alternatingGroup (Fin 7)) := fun i => ⟨yP7w i, yP7w_even i⟩

@[expose] def ι7w : Fin 4 → Fin 2 := ![0, 0, 1, 1]

@[expose] def η7w : Fin 4 → ↥(alternatingGroup (Fin 7)) := ![a7, b7, a7, b7]

theorem η7w_cases : ∀ j, η7w j = a7 ∨ η7w j = b7 := by decide +kernel

@[expose] def words7w : Fin 5 → List (Fin 4) :=
  ![[3, 1, 2, 3, 1, 2], [3, 1, 3, 1], [3, 1, 2, 1, 2, 3], [0, 3, 0, 1, 3, 1], [0, 1, 3, 0, 3, 1]]

theorem gen7w {W : Subgroup ↥(alternatingGroup (Fin 7))} (ha : a7 ∈ W) (hb : b7 ∈ W) :
    ⊤ ≤ ⨆ i, W.map (MulAut.conj (y7w i)).toMonoidHom :=
  top_le_iSup_conj_of_words (m := 5) W y7w ι7w η7w
    (fun j => (η7w_cases j).elim (fun h => h ▸ ha) (fun h => h ▸ hb)) words7w (by decide +kernel)

end Seven

section Nine

@[expose] def a9 : ↥(alternatingGroup (Fin 9)) :=
  ⟨swap 0 1 * swap 2 3, mem_alternatingGroup.2 (by decide +kernel)⟩

@[expose] def b9 : ↥(alternatingGroup (Fin 9)) :=
  ⟨swap 0 2 * swap 1 3, mem_alternatingGroup.2 (by decide +kernel)⟩

theorem a9_sq : a9 * a9 = 1 := by decide +kernel

theorem b9_sq : b9 * b9 = 1 := by decide +kernel

theorem b9_a9 : b9 * a9 = a9 * b9 := by decide +kernel

theorem a9_ne_one : a9 ≠ 1 := by decide +kernel

theorem b9_ne_one : b9 ≠ 1 := by decide +kernel

theorem a9_ne_b9 : a9 ≠ b9 := by decide +kernel

theorem moved9 : (Finset.univ.filter fun i : Fin 9 =>
    ¬ ((a9 : Perm (Fin 9)) i = i ∧ (b9 : Perm (Fin 9)) i = i)).card = 4 := by decide +kernel

@[expose] def yP9a : Fin 4 → Perm (Fin 9) :=
  ![swap 0 1 * swap 2 8 * swap 3 5 * swap 4 6,
    swap 0 6 * swap 6 3 * swap 3 1 * swap 2 4,
    swap 0 8 * swap 8 1,
    swap 0 3 * swap 3 7]

theorem yP9a_even : ∀ i, yP9a i ∈ alternatingGroup (Fin 9) := fun i =>
  mem_alternatingGroup.2 (by revert i; decide +kernel)

@[expose] def y9a : Fin 4 → ↥(alternatingGroup (Fin 9)) := fun i => ⟨yP9a i, yP9a_even i⟩

@[expose] def words9a : Fin 7 → List (Fin 4) :=
  ![[2, 3, 2, 0, 2, 3, 2, 0], [3, 0, 3, 0], [3, 0, 3, 0, 1, 3, 1, 3], [2, 1, 0, 1, 2, 0, 1, 0, 1],
    [0, 3, 1, 3, 0, 3, 1, 3], [2, 3, 2, 3, 0, 2, 3, 2, 3, 0], [1, 0, 1, 2, 1, 0, 1, 2, 0]]

theorem gen9a : ⊤ ≤ ⨆ i, (zpowers a9).map (MulAut.conj (y9a i)).toMonoidHom :=
  top_le_iSup_conj_of_words (m := 7) (zpowers a9) y9a (fun j => j) (fun _ => a9)
    (fun _ => mem_zpowers a9) words9a (by decide +kernel)

@[expose] def yP9w : Fin 3 → Perm (Fin 9) :=
  ![swap 1 7 * swap 7 3 * swap 3 4 * swap 2 5,
    swap 0 8 * swap 8 4 * swap 4 7 * swap 1 5,
    swap 1 6 * swap 6 5 * swap 5 2 * swap 3 8]

theorem yP9w_even : ∀ i, yP9w i ∈ alternatingGroup (Fin 9) := fun i =>
  mem_alternatingGroup.2 (by revert i; decide +kernel)

@[expose] def y9w : Fin 3 → ↥(alternatingGroup (Fin 9)) := fun i => ⟨yP9w i, yP9w_even i⟩

@[expose] def ι9w : Fin 6 → Fin 3 := ![0, 0, 1, 1, 2, 2]

@[expose] def η9w : Fin 6 → ↥(alternatingGroup (Fin 9)) := ![a9, b9, a9, b9, a9, b9]

theorem η9w_cases : ∀ j, η9w j = a9 ∨ η9w j = b9 := by decide +kernel

@[expose] def words9w : Fin 7 → List (Fin 6) :=
  ![[4, 3, 5, 3, 4, 5], [3, 5, 1, 5, 1, 3], [5, 0, 1, 5, 0, 1], [5, 1, 5, 1], [1, 4, 2, 5, 1, 2],
    [5, 0, 5, 0], [1, 2, 4, 2, 4, 1]]

theorem gen9w {W : Subgroup ↥(alternatingGroup (Fin 9))} (ha : a9 ∈ W) (hb : b9 ∈ W) :
    ⊤ ≤ ⨆ i, W.map (MulAut.conj (y9w i)).toMonoidHom :=
  top_le_iSup_conj_of_words (m := 7) W y9w ι9w η9w
    (fun j => (η9w_cases j).elim (fun h => h ▸ ha) (fun h => h ▸ hb)) words9w (by decide +kernel)

end Nine

end PermGenAux

theorem gen_nine : ∃ (W : Subgroup ↥(alternatingGroup (Fin 9))) (a : ↥(alternatingGroup (Fin 9))),
    IsRootFour W ∧ a ∈ W ∧ a ≠ 1 ∧
    (∃ y : Fin 4 → ↥(alternatingGroup (Fin 9)),
      ⊤ ≤ ⨆ i, (Subgroup.zpowers a).map (MulAut.conj (y i)).toMonoidHom) ∧
    (∃ y : Fin 3 → ↥(alternatingGroup (Fin 9)),
      ⊤ ≤ ⨆ i, W.map (MulAut.conj (y i)).toMonoidHom) := by
  obtain ⟨W, hW, haW, hbW⟩ := PermGenAux.exists_rootFour PermGenAux.a9 PermGenAux.b9
    PermGenAux.a9_sq PermGenAux.b9_sq PermGenAux.b9_a9 PermGenAux.a9_ne_one
    PermGenAux.b9_ne_one PermGenAux.a9_ne_b9 PermGenAux.moved9
  exact ⟨W, PermGenAux.a9, hW, haW, PermGenAux.a9_ne_one, ⟨PermGenAux.y9a, PermGenAux.gen9a⟩,
    ⟨PermGenAux.y9w, PermGenAux.gen9w haW hbW⟩⟩

theorem gen_seven : ∃ (W : Subgroup ↥(alternatingGroup (Fin 7))) (a : ↥(alternatingGroup (Fin 7))),
    IsRootFour W ∧ a ∈ W ∧ a ≠ 1 ∧
    (∃ y : Fin 3 → ↥(alternatingGroup (Fin 7)),
      ⊤ ≤ ⨆ i, (Subgroup.zpowers a).map (MulAut.conj (y i)).toMonoidHom) ∧
    (∃ y : Fin 2 → ↥(alternatingGroup (Fin 7)),
      ⊤ ≤ ⨆ i, W.map (MulAut.conj (y i)).toMonoidHom) := by
  obtain ⟨W, hW, haW, hbW⟩ := PermGenAux.exists_rootFour PermGenAux.a7 PermGenAux.b7
    PermGenAux.a7_sq PermGenAux.b7_sq PermGenAux.b7_a7 PermGenAux.a7_ne_one
    PermGenAux.b7_ne_one PermGenAux.a7_ne_b7 PermGenAux.moved7
  exact ⟨W, PermGenAux.a7, hW, haW, PermGenAux.a7_ne_one, ⟨PermGenAux.y7a, PermGenAux.gen7a⟩,
    ⟨PermGenAux.y7w, PermGenAux.gen7w haW hbW⟩⟩

end CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.LayerM
