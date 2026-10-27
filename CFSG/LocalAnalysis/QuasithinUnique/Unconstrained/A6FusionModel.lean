module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.Basic

public section

namespace CFSG.QuasithinUnique.A6Fusion

open Equiv A6Models CFSG.Open

@[expose] def pd0 : Perm (Fin 10) := 1

@[expose] def pd1 : Perm (Fin 10) :=
  ⟨![0, 2, 1, 6, 8, 7, 3, 5, 4, 9], ![0, 2, 1, 6, 8, 7, 3, 5, 4, 9], by decide, by decide⟩

@[expose] def pd2 : Perm (Fin 10) :=
  ⟨![3, 1, 2, 9, 8, 7, 0, 4, 5, 6], ![6, 1, 2, 0, 7, 8, 9, 5, 4, 3], by decide, by decide⟩

@[expose] def pd3 : Perm (Fin 10) :=
  ⟨![3, 2, 1, 0, 5, 4, 9, 7, 8, 6], ![3, 2, 1, 0, 5, 4, 9, 7, 8, 6], by decide, by decide⟩

@[expose] def pd4 : Perm (Fin 10) :=
  ⟨![6, 1, 2, 0, 7, 8, 9, 5, 4, 3], ![3, 1, 2, 9, 8, 7, 0, 4, 5, 6], by decide, by decide⟩

@[expose] def pd5 : Perm (Fin 10) :=
  ⟨![6, 2, 1, 9, 4, 5, 0, 8, 7, 3], ![6, 2, 1, 9, 4, 5, 0, 8, 7, 3], by decide, by decide⟩

@[expose] def pd6 : Perm (Fin 10) :=
  ⟨![9, 1, 2, 6, 5, 4, 3, 8, 7, 0], ![9, 1, 2, 6, 5, 4, 3, 8, 7, 0], by decide, by decide⟩

@[expose] def pd7 : Perm (Fin 10) :=
  ⟨![9, 2, 1, 3, 7, 8, 6, 4, 5, 0], ![9, 2, 1, 3, 7, 8, 6, 4, 5, 0], by decide, by decide⟩

@[expose] def pg : Perm (Fin 10) :=
  ⟨![5, 2, 1, 8, 9, 0, 7, 6, 3, 4], ![5, 2, 1, 8, 9, 0, 7, 6, 3, 4], by decide, by decide⟩

@[expose] def pd : Fin 8 → Perm (Fin 10) := ![pd0, pd1, pd2, pd3, pd4, pd5, pd6, pd7]

@[expose] def pq : Fin 16 → Perm (Fin 10) :=
  fun i => if h : i.val < 8 then pd ⟨i.val, h⟩ else pg * pd ⟨i.val - 8, by omega⟩

@[expose] def tbl8 : Fin 8 → Fin 8 → Fin 8 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7], ![1, 0, 5, 4, 3, 2, 7, 6], ![2, 3, 6, 7, 0, 1, 4, 5],
    ![3, 2, 1, 0, 7, 6, 5, 4], ![4, 5, 0, 1, 6, 7, 2, 3], ![5, 4, 7, 6, 1, 0, 3, 2],
    ![6, 7, 4, 5, 2, 3, 0, 1], ![7, 6, 3, 2, 5, 4, 1, 0]]

@[expose] def inv8 : Fin 8 → Fin 8 := ![0, 1, 4, 3, 2, 5, 6, 7]

@[expose] def cj : Fin 8 → Fin 8 := ![0, 5, 4, 7, 2, 1, 6, 3]

@[expose] def tbl16 : Fin 16 → Fin 16 → Fin 16 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    ![1, 0, 5, 4, 3, 2, 7, 6, 13, 12, 15, 14, 9, 8, 11, 10],
    ![2, 3, 6, 7, 0, 1, 4, 5, 12, 13, 8, 9, 14, 15, 10, 11],
    ![3, 2, 1, 0, 7, 6, 5, 4, 15, 14, 11, 10, 13, 12, 9, 8],
    ![4, 5, 0, 1, 6, 7, 2, 3, 10, 11, 14, 15, 8, 9, 12, 13],
    ![5, 4, 7, 6, 1, 0, 3, 2, 9, 8, 13, 12, 11, 10, 15, 14],
    ![6, 7, 4, 5, 2, 3, 0, 1, 14, 15, 12, 13, 10, 11, 8, 9],
    ![7, 6, 3, 2, 5, 4, 1, 0, 11, 10, 9, 8, 15, 14, 13, 12],
    ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7],
    ![9, 8, 13, 12, 11, 10, 15, 14, 5, 4, 7, 6, 1, 0, 3, 2],
    ![10, 11, 14, 15, 8, 9, 12, 13, 4, 5, 0, 1, 6, 7, 2, 3],
    ![11, 10, 9, 8, 15, 14, 13, 12, 7, 6, 3, 2, 5, 4, 1, 0],
    ![12, 13, 8, 9, 14, 15, 10, 11, 2, 3, 6, 7, 0, 1, 4, 5],
    ![13, 12, 15, 14, 9, 8, 11, 10, 1, 0, 5, 4, 3, 2, 7, 6],
    ![14, 15, 12, 13, 10, 11, 8, 9, 6, 7, 4, 5, 2, 3, 0, 1],
    ![15, 14, 11, 10, 13, 12, 9, 8, 3, 2, 1, 0, 7, 6, 5, 4]]

@[expose] def inv16 : Fin 16 → Fin 16 := ![0, 1, 4, 3, 2, 5, 6, 7, 8, 13, 10, 15, 12, 9, 14, 11]

set_option maxRecDepth 100000 in
theorem mul_tbl8 : ∀ i j : Fin 8, pd i * pd j = pd (tbl8 i j) := by decide

set_option maxRecDepth 100000 in
theorem inv_tbl8 : ∀ i : Fin 8, (pd i)⁻¹ = pd (inv8 i) := by decide

set_option maxRecDepth 100000 in
theorem pd_injective : Function.Injective pd := by
  have : ∀ i j : Fin 8, pd i = pd j → i = j := by decide
  exact fun i j h => this i j h

set_option maxRecDepth 100000 in
theorem conj_tbl : ∀ i : Fin 8, pg * pd i * pg⁻¹ = pd (cj i) := by decide

set_option maxRecDepth 100000 in
theorem mul_tbl16 : ∀ i j : Fin 16, pq i * pq j = pq (tbl16 i j) := by decide

set_option maxRecDepth 100000 in
theorem inv_tbl16 : ∀ i : Fin 16, (pq i)⁻¹ = pq (inv16 i) := by decide

set_option maxRecDepth 100000 in
theorem pq_injective : Function.Injective pq := by
  have : ∀ i j : Fin 16, pq i = pq j → i = j := by decide
  exact fun i j h => this i j h

theorem pd_zero : pd 0 = 1 := rfl

theorem pq_zero : pq 0 = 1 := rfl

@[expose] def D : Subgroup (Perm (Fin 10)) where
  carrier := Set.range pd
  mul_mem' := by
    rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
    exact ⟨tbl8 i j, (mul_tbl8 i j).symm⟩
  one_mem' := ⟨0, pd_zero⟩
  inv_mem' := by
    rintro _ ⟨i, rfl⟩
    exact ⟨inv8 i, (inv_tbl8 i).symm⟩

@[expose] def Q : Subgroup (Perm (Fin 10)) where
  carrier := Set.range pq
  mul_mem' := by
    rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
    exact ⟨tbl16 i j, (mul_tbl16 i j).symm⟩
  one_mem' := ⟨0, pq_zero⟩
  inv_mem' := by
    rintro _ ⟨i, rfl⟩
    exact ⟨inv16 i, (inv_tbl16 i).symm⟩

theorem card_D : Nat.card D = 8 := by
  have h : Nat.card D = Nat.card (Set.range pd) := rfl
  rw [h, Nat.card_range_of_injective pd_injective]
  simp

theorem card_Q : Nat.card Q = 16 := by
  have h : Nat.card Q = Nat.card (Set.range pq) := rfl
  rw [h, Nat.card_range_of_injective pq_injective]
  simp

theorem isPGroup_Q : IsPGroup 2 Q :=
  IsPGroup.of_card (p := 2) (n := 4) (by rw [card_Q]; norm_num)

theorem pd_mem_Q (i : Fin 8) : pd i ∈ Q := ⟨⟨i.val, by omega⟩, by simp [pq]⟩

theorem pg_mem_Q : pg ∈ Q := ⟨8, by simp [pq, pd, pd0]⟩

theorem D_le_Q : D ≤ Q := by
  rintro _ ⟨i, rfl⟩
  exact pd_mem_Q i

set_option maxRecDepth 100000 in
theorem w1 : pd1 = tSq * tSq := by decide

set_option maxRecDepth 100000 in
theorem w2 : pd2 = tSq * tAdd * tInv * tAdd * tAdd * tSq := by decide

set_option maxRecDepth 100000 in
theorem w3 : pd3 = tInv * tSq * tAdd * tInv * tAdd * tAdd * tSq := by decide

set_option maxRecDepth 100000 in
theorem w4 : pd4 = tSq * tAdd * tAdd * tInv * tAdd * tSq := by decide

set_option maxRecDepth 100000 in
theorem w5 : pd5 = tInv * tSq * tAdd * tAdd * tInv * tAdd * tSq := by decide

set_option maxRecDepth 100000 in
theorem w6 : pd6 = tInv * tSq * tSq := by decide

set_option maxRecDepth 100000 in
theorem w7 : pd7 = tInv := by decide

set_option maxRecDepth 100000 in
theorem wg : pg = tAdd * tSq * tInv * tAdd * tInv * tMul * tAdd := by decide

theorem tAdd_mem : tAdd ∈ psl29 := Subgroup.subset_closure (Set.mem_insert _ _)

theorem tSq_mem : tSq ∈ psl29 :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))

theorem tInv_mem : tInv ∈ psl29 :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))

theorem pd1_mem : pd1 ∈ psl29 := by
  rw [w1]
  exact psl29.mul_mem tSq_mem tSq_mem

theorem pd2_mem : pd2 ∈ psl29 := by
  rw [w2]
  exact psl29.mul_mem (psl29.mul_mem (psl29.mul_mem (psl29.mul_mem (psl29.mul_mem tSq_mem tAdd_mem)
    tInv_mem) tAdd_mem) tAdd_mem) tSq_mem

theorem pd3_mem : pd3 ∈ psl29 := by
  rw [w3]
  exact psl29.mul_mem (psl29.mul_mem (psl29.mul_mem (psl29.mul_mem (psl29.mul_mem
    (psl29.mul_mem tInv_mem tSq_mem) tAdd_mem) tInv_mem) tAdd_mem) tAdd_mem) tSq_mem

theorem pd4_mem : pd4 ∈ psl29 := by
  rw [w4]
  exact psl29.mul_mem (psl29.mul_mem (psl29.mul_mem (psl29.mul_mem (psl29.mul_mem tSq_mem tAdd_mem)
    tAdd_mem) tInv_mem) tAdd_mem) tSq_mem

theorem pd5_mem : pd5 ∈ psl29 := by
  rw [w5]
  exact psl29.mul_mem (psl29.mul_mem (psl29.mul_mem (psl29.mul_mem (psl29.mul_mem
    (psl29.mul_mem tInv_mem tSq_mem) tAdd_mem) tAdd_mem) tInv_mem) tAdd_mem) tSq_mem

theorem pd6_mem : pd6 ∈ psl29 := by
  rw [w6]
  exact psl29.mul_mem (psl29.mul_mem tInv_mem tSq_mem) tSq_mem

theorem pd7_mem : pd7 ∈ psl29 := by
  rw [w7]
  exact tInv_mem

theorem pd_mem_psl29 (i : Fin 8) : pd i ∈ psl29 := by
  fin_cases i
  exacts [psl29.one_mem, pd1_mem, pd2_mem, pd3_mem, pd4_mem, pd5_mem, pd6_mem, pd7_mem]

theorem D_le_psl29 : D ≤ psl29 := by
  rintro _ ⟨i, rfl⟩
  exact pd_mem_psl29 i

theorem tAdd_memA : tAdd ∈ autA6 := Subgroup.subset_closure (Set.mem_insert _ _)

theorem tSq_memA : tSq ∈ autA6 :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))

theorem tInv_memA : tInv ∈ autA6 :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))

theorem tMul_memA : tMul ∈ autA6 :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
    (Set.mem_insert_of_mem _ (Set.mem_insert _ _))))

theorem psl29_le_autA6 : psl29 ≤ autA6 := by
  unfold psl29
  rw [Subgroup.closure_le]
  intro x hx
  rcases hx with rfl | rfl | rfl
  · exact tAdd_memA
  · exact tSq_memA
  · exact tInv_memA

theorem pg_mem_autA6 : pg ∈ autA6 := by
  rw [wg]
  exact autA6.mul_mem (autA6.mul_mem (autA6.mul_mem (autA6.mul_mem (autA6.mul_mem
    (autA6.mul_mem tAdd_memA tSq_memA) tInv_memA) tAdd_memA) tInv_memA) tMul_memA) tAdd_memA

theorem Q_le_autA6 : Q ≤ autA6 := by
  rintro _ ⟨i, rfl⟩
  unfold pq
  split_ifs with h
  · exact psl29_le_autA6 (pd_mem_psl29 _)
  · exact autA6.mul_mem pg_mem_autA6 (psl29_le_autA6 (pd_mem_psl29 _))

set_option maxRecDepth 100000 in
theorem class8 : ∀ I : Finset (Fin 8), I.card = 4 → 0 ∈ I → (∀ i ∈ I, ∀ j ∈ I, tbl8 i j ∈ I) →
    (∀ i ∈ I, tbl8 i i = 0) → I = {0, 1, 6, 7} ∨ I = {0, 3, 5, 6} := by decide

theorem cj_image_A : ({0, 1, 6, 7} : Finset (Fin 8)).image cj = {0, 3, 5, 6} := by decide

theorem cj_image_B : ({0, 3, 5, 6} : Finset (Fin 8)).image cj = {0, 1, 6, 7} := by decide

open scoped Classical in
@[expose] noncomputable def idx (E : Subgroup (Perm (Fin 10))) : Finset (Fin 8) :=
  Finset.univ.filter (fun i => pd i ∈ E)

theorem mem_idx {E : Subgroup (Perm (Fin 10))} {i : Fin 8} : i ∈ idx E ↔ pd i ∈ E := by
  classical
  simp [idx]

theorem mem_iff_idx {E : Subgroup (Perm (Fin 10))} (hE : E ≤ D) {x : Perm (Fin 10)} :
    x ∈ E ↔ ∃ i ∈ idx E, pd i = x := by
  constructor
  · intro hx
    obtain ⟨i, rfl⟩ := hE hx
    exact ⟨i, mem_idx.mpr hx, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact mem_idx.mp hi

theorem card_idx {E : Subgroup (Perm (Fin 10))} (hE : E ≤ D) : (idx E).card = Nat.card E := by
  have h : (E : Set (Perm (Fin 10))) = pd '' (idx E : Set (Fin 8)) := by
    ext x
    rw [SetLike.mem_coe, mem_iff_idx hE]
    simp
  have h2 : Nat.card E = Nat.card (pd '' (idx E : Set (Fin 8))) := by
    rw [← h]
    rfl
  rw [h2, Nat.card_image_of_injective pd_injective, Nat.card_coe_set_eq, Set.ncard_coe_finset]

theorem idx_props {E : Subgroup (Perm (Fin 10))} (hE : E ≤ D) (hE4 : IsFourSubgroup E) :
    (idx E).card = 4 ∧ 0 ∈ idx E ∧ (∀ i ∈ idx E, ∀ j ∈ idx E, tbl8 i j ∈ idx E) ∧
      ∀ i ∈ idx E, tbl8 i i = 0 := by
  refine ⟨by rw [card_idx hE]; exact hE4.2, ?_, ?_, ?_⟩
  · exact mem_idx.mpr (by rw [pd_zero]; exact E.one_mem)
  · intro i hi j hj
    refine mem_idx.mpr ?_
    rw [← mul_tbl8]
    exact E.mul_mem (mem_idx.mp hi) (mem_idx.mp hj)
  · intro i hi
    have h2 : pd i ^ 2 = 1 := hE4.1.2 _ (mem_idx.mp hi)
    apply pd_injective
    rw [← mul_tbl8, pd_zero, ← h2, sq]

theorem conj_pd (i : Fin 8) : (MulAut.conj pg).toMonoidHom (pd i) = pd (cj i) := by
  rw [← conj_tbl]
  simp [MulAut.conj_apply]

theorem swap_four {E₁ E₂ : Subgroup (Perm (Fin 10))} (h₁ : E₁ ≤ D) (h₂ : E₂ ≤ D)
    (h₁4 : IsFourSubgroup E₁) (h₂4 : IsFourSubgroup E₂) (hne : E₁ ≠ E₂) :
    E₂ = E₁.map (MulAut.conj pg).toMonoidHom := by
  obtain ⟨c1, z1, m1, e1⟩ := idx_props h₁ h₁4
  obtain ⟨c2, z2, m2, e2⟩ := idx_props h₂ h₂4
  have hI : idx E₂ = (idx E₁).image cj := by
    have hne' : idx E₁ ≠ idx E₂ := by
      intro h
      apply hne
      ext x
      rw [mem_iff_idx h₁, mem_iff_idx h₂, h]
    rcases class8 _ c1 z1 m1 e1 with h1 | h1 <;> rcases class8 _ c2 z2 m2 e2 with h2 | h2
    · exact absurd (h1.trans h2.symm) hne'
    · rw [h1, h2, cj_image_A]
    · rw [h1, h2, cj_image_B]
    · exact absurd (h1.trans h2.symm) hne'
  ext x
  constructor
  · intro hx
    obtain ⟨j, hj, rfl⟩ := (mem_iff_idx h₂).mp hx
    rw [hI, Finset.mem_image] at hj
    obtain ⟨i, hi, rfl⟩ := hj
    exact ⟨pd i, mem_idx.mp hi, conj_pd i⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨i, hi, rfl⟩ := (mem_iff_idx h₁).mp hy
    rw [conj_pd]
    refine mem_idx.mp ?_
    rw [hI]
    exact Finset.mem_image_of_mem _ hi

end CFSG.QuasithinUnique.A6Fusion
