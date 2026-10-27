module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL59Base


public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33
  CFSG.ComponentClassification.AschbacherTheorem5.DeltaLocal

variable {G : Type} [Group G]

theorem fz59d_q8Hom_a_one {p q : G} (h : IsQ8Pair p q) :
    q8Hom h (QuaternionGroup.a 1) = p := by
  have h1 : (1 : ZMod 4).val = 1 := rfl
  change zmod4Pow p 1 = p
  rw [zmod4Pow, h1, pow_one]

theorem fz59d_q8Hom_xa_zero {p q : G} (h : IsQ8Pair p q) :
    q8Hom h (QuaternionGroup.xa 0) = q := by
  have h0 : (0 : ZMod 4).val = 0 := rfl
  change q * zmod4Pow p 0 = q
  rw [zmod4Pow, h0, pow_zero, mul_one]

theorem fz59d_q8Hom_a_two {p q : G} (h : IsQ8Pair p q) :
    q8Hom h (QuaternionGroup.a 2) = p ^ 2 := by
  have h2 : (2 : ZMod 4).val = 2 := rfl
  change zmod4Pow p 2 = p ^ 2
  rw [zmod4Pow, h2]

private theorem fz59d_q8Hom_commute {p q p' q' : G} (hp : IsQ8Pair p q) (hp' : IsQ8Pair p' q')
    (hpp : Commute p p') (hpq : Commute p q') (hqp : Commute q p') (hqq : Commute q q') :
    ∀ x y : Fz59Q8, Commute (q8Hom hp x) (q8Hom hp' y) := by
  intro x y
  cases x with
  | a i =>
    cases y with
    | a j => exact (hpp.pow_left i.val).pow_right j.val
    | xa j =>
      exact ((hpq.pow_left i.val)).mul_right ((hpp.pow_left i.val).pow_right j.val)
  | xa i =>
    cases y with
    | a j => exact ((hqp.pow_right j.val)).mul_left ((hpp.pow_right j.val).pow_left i.val)
    | xa j =>
      exact (hqq.mul_right (hqp.pow_right j.val)).mul_left
        ((hpq.pow_left i.val).mul_right ((hpp.pow_left i.val).pow_right j.val))

theorem fz59d_row_comm {b : Fin 3 → Fin 2 → G} (hb : Fz59Rows b) {i j : Fin 3} (hij : i ≠ j)
    (x y : Fz59Q8) : Commute (q8Hom (hb.quat i) x) (q8Hom (hb.quat j) y) :=
  fz59d_q8Hom_commute (hb.quat i) (hb.quat j) (hb.comm i j hij 0 0) (hb.comm i j hij 0 1)
    (hb.comm i j hij 1 0) (hb.comm i j hij 1 1) x y

@[expose] noncomputable def fz59dPi12 {b : Fin 3 → Fin 2 → G} (hb : Fz59Rows b) :
    Fz59Q8 × Fz59Q8 →* G :=
  (q8Hom (hb.quat 1)).noncommCoprod (q8Hom (hb.quat 2))
    (fun x y => fz59d_row_comm hb (by decide) x y)

theorem fz59dPi12_apply {b : Fin 3 → Fin 2 → G} (hb : Fz59Rows b) (y z : Fz59Q8) :
    fz59dPi12 hb (y, z) = q8Hom (hb.quat 1) y * q8Hom (hb.quat 2) z := by
  simp [fz59dPi12]

@[expose] noncomputable def fz59dPi {b : Fin 3 → Fin 2 → G} (hb : Fz59Rows b) : Fz59Mod →* G :=
  (q8Hom (hb.quat 0)).noncommCoprod (fz59dPi12 hb) (fun x yz => by
    rw [← Prod.mk.eta (p := yz), fz59dPi12_apply]
    exact (fz59d_row_comm hb (by decide) x yz.1).mul_right
      (fz59d_row_comm hb (by decide) x yz.2))

theorem fz59dPi_apply {b : Fin 3 → Fin 2 → G} (hb : Fz59Rows b) (x y z : Fz59Q8) :
    fz59dPi hb (x, y, z) =
      q8Hom (hb.quat 0) x * (q8Hom (hb.quat 1) y * q8Hom (hb.quat 2) z) := by
  simp [fz59dPi, fz59dPi12_apply]

theorem fz59dPi_gen {b : Fin 3 → Fin 2 → G} (hb : Fz59Rows b) (i : Fin 3) (k : Fin 2) :
    fz59dPi hb (fz59Gen i k) = b i k := by
  fin_cases i <;> fin_cases k <;>
    simp [fz59Gen, fz59dPi_apply, fz59d_q8Hom_a_one, fz59d_q8Hom_xa_zero]

private theorem fz59d_zz {b : Fin 3 → Fin 2 → G} (hb : Fz59Rows b) (i : Fin 3) :
    b i 0 ^ 2 * b i 0 ^ 2 = 1 :=
  (hb.quat i).sq_mul_sq

private theorem fz59d_z_ne {b : Fin 3 → Fin 2 → G} (hb : Fz59Rows b) (i : Fin 3) :
    b i 0 ^ 2 ≠ 1 :=
  (hb.quat i).2.2.2

private theorem fz59d_z_comm {b : Fin 3 → Fin 2 → G} (hb : Fz59Rows b) (i j : Fin 3) :
    b i 0 ^ 2 * b j 0 ^ 2 = b j 0 ^ 2 * b i 0 ^ 2 := by
  by_cases h : i = j
  · rw [h]
  · exact ((hb.comm i j h 0 0).pow_left 2).pow_right 2

private theorem fz59d_tab {z0 z1 z2 : G} (h00 : z0 * z0 = 1) (h11 : z1 * z1 = 1)
    (h2 : z2 = z0 * z1) (hc : z0 * z1 = z1 * z0) :
    z0 * z1 = z2 ∧ z1 * z0 = z2 ∧ z0 * z2 = z1 ∧ z2 * z0 = z1 ∧ z1 * z2 = z0 ∧
      z2 * z1 = z0 ∧ z2 * z2 = 1 := by
  refine ⟨h2.symm, by rw [← hc, h2], by rw [h2, ← mul_assoc, h00, one_mul],
    by rw [h2, mul_assoc, ← hc, ← mul_assoc, h00, one_mul],
    by rw [h2, ← mul_assoc, ← hc, mul_assoc, h11, mul_one], by rw [h2, mul_assoc, h11, mul_one],
    ?_⟩
  rw [h2]
  calc z0 * z1 * (z0 * z1) = z0 * (z1 * z0) * z1 := by group
    _ = z0 * (z0 * z1) * z1 := by rw [← hc]
    _ = (z0 * z0) * (z1 * z1) := by group
    _ = 1 := by rw [h00, h11, one_mul]

private theorem fz59d_klein {z0 z1 z2 : G} (h00 : z0 * z0 = 1) (h11 : z1 * z1 = 1)
    (h2 : z2 = z0 * z1) (hc : z0 * z1 = z1 * z0) :
    ∀ x y : G, (x = 1 ∨ x = z0 ∨ x = z1 ∨ x = z2) → (y = 1 ∨ y = z0 ∨ y = z1 ∨ y = z2) →
      (x * y = 1 ∨ x * y = z0 ∨ x * y = z1 ∨ x * y = z2) := by
  obtain ⟨h01, h10, h02, h20, h12, h21, h22⟩ := fz59d_tab h00 h11 h2 hc
  rintro x y (rfl | rfl | rfl | rfl) (rfl | rfl | rfl | rfl) <;>
    simp [h00, h11, h01, h10, h02, h20, h12, h21, h22]

theorem fz59_mem_Z {b : Fin 3 → Fin 2 → G} (hb : Fz59Rows b) (g : G) :
    g ∈ fz59Z b ↔ g = 1 ∨ g = b 0 0 ^ 2 ∨ g = b 1 0 ^ 2 ∨ g = b 2 0 ^ 2 := by
  have h00 := fz59d_zz hb 0
  have h11 := fz59d_zz hb 1
  have hc := fz59d_z_comm hb 0 1
  have h2 : b 2 0 ^ 2 = b 0 0 ^ 2 * b 1 0 ^ 2 := hb.sq_eq
  constructor
  · intro hg
    rw [fz59Z] at hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl <;> simp
    | one => exact Or.inl rfl
    | mul x y _ _ hx hy => exact fz59d_klein h00 h11 h2 hc x y hx hy
    | inv x _ hx =>
      rcases hx with rfl | rfl | rfl | rfl
      · simp
      · rw [inv_eq_of_mul_eq_one_right h00]; simp
      · rw [inv_eq_of_mul_eq_one_right h11]; simp
      · rw [inv_eq_of_mul_eq_one_right (fz59d_zz hb 2)]; simp
  · rintro (rfl | rfl | rfl | rfl)
    · exact one_mem _
    · exact subset_closure (by simp)
    · exact subset_closure (by simp)
    · rw [h2]
      exact mul_mem (subset_closure (by simp)) (subset_closure (by simp))

theorem fz59d_b_mem_R (b : Fin 3 → Fin 2 → G) (i : Fin 3) (k : Fin 2) : b i k ∈ fz59R b :=
  subset_closure ⟨(i, k), rfl⟩

theorem fz59_Z_le_R (b : Fin 3 → Fin 2 → G) : fz59Z b ≤ fz59R b := by
  rw [fz59Z, closure_le]
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl
  · exact pow_mem (fz59d_b_mem_R b 0 0) 2
  · exact pow_mem (fz59d_b_mem_R b 1 0) 2

theorem fz59_card_Z {b : Fin 3 → Fin 2 → G} (hb : Fz59Rows b) : Nat.card (fz59Z b) = 4 := by
  have hset : ((fz59Z b : Subgroup G) : Set G) = {1, b 0 0 ^ 2, b 1 0 ^ 2, b 2 0 ^ 2} := by
    ext g
    simp only [SetLike.mem_coe, fz59_mem_Z hb g, Set.mem_insert_iff, Set.mem_singleton_iff]
  have h00 := fz59d_zz hb 0
  have h11 := fz59d_zz hb 1
  have hc := fz59d_z_comm hb 0 1
  have h2 : b 2 0 ^ 2 = b 0 0 ^ 2 * b 1 0 ^ 2 := hb.sq_eq
  obtain ⟨h01, h10, h02, h20, h12, h21, h22⟩ := fz59d_tab h00 h11 h2 hc
  have n0 := fz59d_z_ne hb 0
  have n1 := fz59d_z_ne hb 1
  have n2 := fz59d_z_ne hb 2
  have d01 : b 0 0 ^ 2 ≠ b 1 0 ^ 2 := fun h => n2 (by rw [← h01, ← h, h00])
  have d02 : b 0 0 ^ 2 ≠ b 2 0 ^ 2 := fun h => n1 (by rw [← h02, ← h, h00])
  have d12 : b 1 0 ^ 2 ≠ b 2 0 ^ 2 := fun h => n0 (by rw [← h12, ← h, h11])
  have h1 : Nat.card (fz59Z b) = ((fz59Z b : Subgroup G) : Set G).ncard := by
    rw [← Nat.card_coe_set_eq, SetLike.coe_sort_coe]
  rw [h1, hset, Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_pair d12]
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨d01, d02⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨fun h => n0 h.symm, fun h => n1 h.symm, fun h => n2 h.symm⟩

private theorem fz59d_zi_central {b : Fin 3 → Fin 2 → G} (hb : Fz59Rows b) (i : Fin 3) :
    ∀ r ∈ fz59R b, b i 0 ^ 2 * r = r * b i 0 ^ 2 := by
  have hle : fz59R b ≤ centralizer ({b i 0 ^ 2} : Set G) := by
    rw [fz59R, closure_le]
    rintro _ ⟨⟨j, k⟩, rfl⟩
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
    by_cases hij : j = i
    · subst hij
      fin_cases k
      · exact ((Commute.refl (b j 0)).pow_right 2).eq
      · exact (hb.quat j).mul_comm_sq
    · exact ((hb.comm j i hij k 0).pow_right 2).eq
  intro r hr
  exact (mem_centralizer_singleton_iff.mp (hle hr)).symm

theorem fz59_Z_central {b : Fin 3 → Fin 2 → G} (hb : Fz59Rows b) :
    ∀ z ∈ fz59Z b, ∀ r ∈ fz59R b, z * r = r * z := by
  intro z hz r hr
  rcases (fz59_mem_Z hb z).mp hz with rfl | rfl | rfl | rfl
  · simp
  · exact fz59d_zi_central hb 0 r hr
  · exact fz59d_zi_central hb 1 r hr
  · exact fz59d_zi_central hb 2 r hr

private theorem fz59d_zi_mem {b : Fin 3 → Fin 2 → G} (hb : Fz59Rows b) (i : Fin 3) :
    b i 0 ^ 2 ∈ fz59Z b := by
  rw [fz59_mem_Z hb]
  fin_cases i
  · simp
  · simp
  · simp

theorem fz59dPi_zeta {b : Fin 3 → Fin 2 → G} (hb : Fz59Rows b) : fz59dPi hb fz59Zeta = 1 := by
  have h00 := fz59d_zz hb 0
  have h11 := fz59d_zz hb 1
  have hc := fz59d_z_comm hb 0 1
  change fz59dPi hb (QuaternionGroup.a 2, QuaternionGroup.a 2, QuaternionGroup.a 2) = 1
  rw [fz59dPi_apply, fz59d_q8Hom_a_two, fz59d_q8Hom_a_two, fz59d_q8Hom_a_two, hb.sq_eq]
  calc b 0 0 ^ 2 * (b 1 0 ^ 2 * (b 0 0 ^ 2 * b 1 0 ^ 2))
      = b 0 0 ^ 2 * (b 1 0 ^ 2 * b 0 0 ^ 2) * b 1 0 ^ 2 := by group
    _ = b 0 0 ^ 2 * (b 0 0 ^ 2 * b 1 0 ^ 2) * b 1 0 ^ 2 := by rw [← hc]
    _ = (b 0 0 ^ 2 * b 0 0 ^ 2) * (b 1 0 ^ 2 * b 1 0 ^ 2) := by group
    _ = 1 := by rw [h00, h11, one_mul]

private theorem fz59d_central_q8 : ∀ q : Fz59Q8, (∀ x : Fz59Q8, x * q = q * x) →
    q = 1 ∨ q = QuaternionGroup.a 2 := by decide

private theorem fz59d_central_of {p q : G} (hpq : IsQ8Pair p q) {x : Fz59Q8} {v : G}
    (h : q8Hom hpq x * v = 1) (hv : ∀ x' : Fz59Q8, Commute (q8Hom hpq x') v) :
    x = 1 ∨ x = QuaternionGroup.a 2 := by
  refine fz59d_central_q8 x fun x' => q8Hom_injective hpq ?_
  rw [map_mul, map_mul, eq_inv_of_mul_eq_one_left h]
  exact (hv x').inv_right

theorem fz59dPi_eq_one_iff {b : Fin 3 → Fin 2 → G} (hb : Fz59Rows b) (q : Fz59Mod) :
    fz59dPi hb q = 1 ↔ q = 1 ∨ q = fz59Zeta := by
  constructor
  · obtain ⟨x, y, w⟩ := q
    intro h
    rw [fz59dPi_apply] at h
    have c01 := fz59d_row_comm hb (by decide : (0 : Fin 3) ≠ 1)
    have c02 := fz59d_row_comm hb (by decide : (0 : Fin 3) ≠ 2)
    have c10 := fz59d_row_comm hb (by decide : (1 : Fin 3) ≠ 0)
    have c12 := fz59d_row_comm hb (by decide : (1 : Fin 3) ≠ 2)
    have c20 := fz59d_row_comm hb (by decide : (2 : Fin 3) ≠ 0)
    have c21 := fz59d_row_comm hb (by decide : (2 : Fin 3) ≠ 1)
    have hx := fz59d_central_of (hb.quat 0) h (fun x' => (c01 x' y).mul_right (c02 x' w))
    have hy := fz59d_central_of (hb.quat 1) (x := y)
      (v := q8Hom (hb.quat 0) x * q8Hom (hb.quat 2) w)
      (by rw [← mul_assoc, (c10 y x).eq, mul_assoc]; exact h)
      (fun y' => (c10 y' x).mul_right (c12 y' w))
    have hw := fz59d_central_of (hb.quat 2) (x := w)
      (v := q8Hom (hb.quat 0) x * q8Hom (hb.quat 1) y)
      (by rw [((c20 w x).mul_right (c21 w y)).eq, mul_assoc]; exact h)
      (fun w' => (c20 w' x).mul_right (c21 w' y))
    have h00 := fz59d_zz hb 0
    have h11 := fz59d_zz hb 1
    have hc := fz59d_z_comm hb 0 1
    have h2 : b 2 0 ^ 2 = b 0 0 ^ 2 * b 1 0 ^ 2 := hb.sq_eq
    obtain ⟨h01, h10, h02, h20, h12, h21, h22⟩ := fz59d_tab h00 h11 h2 hc
    have n0 := fz59d_z_ne hb 0
    have n1 := fz59d_z_ne hb 1
    have n2 := fz59d_z_ne hb 2
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> rcases hw with rfl | rfl
    · exact Or.inl rfl
    · simp only [map_one, fz59d_q8Hom_a_two, mul_one, one_mul] at h
      exact absurd h n2
    · simp only [map_one, fz59d_q8Hom_a_two, mul_one, one_mul] at h
      exact absurd h n1
    · simp only [map_one, fz59d_q8Hom_a_two, mul_one, one_mul] at h
      exact absurd (h12 ▸ h) n0
    · simp only [map_one, fz59d_q8Hom_a_two, mul_one, one_mul] at h
      exact absurd h n0
    · simp only [map_one, fz59d_q8Hom_a_two, mul_one, one_mul] at h
      exact absurd (h02 ▸ h) n1
    · simp only [map_one, fz59d_q8Hom_a_two, mul_one, one_mul] at h
      exact absurd (h01 ▸ h) n2
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact map_one _
    · exact fz59dPi_zeta hb

theorem fz59dPi_eq_iff {b : Fin 3 → Fin 2 → G} (hb : Fz59Rows b) (q q' : Fz59Mod) :
    fz59dPi hb q = fz59dPi hb q' ↔ (q' = q ∨ q' = q * fz59Zeta) := by
  have h : fz59dPi hb q = fz59dPi hb q' ↔ fz59dPi hb (q⁻¹ * q') = 1 := by
    rw [map_mul, map_inv, inv_mul_eq_one]
  rw [h, fz59dPi_eq_one_iff hb]
  constructor
  · rintro (h1 | h1)
    · exact Or.inl (inv_mul_eq_one.mp h1).symm
    · exact Or.inr (by rw [← h1]; group)
  · rintro (rfl | rfl)
    · exact Or.inl (by group)
    · exact Or.inr (by group)

private theorem fz59d_q8Hom_mem {p q : G} (hpq : IsQ8Pair p q) {K : Subgroup G} (hp : p ∈ K)
    (hq : q ∈ K) (r : Fz59Q8) : q8Hom hpq r ∈ K := by
  cases r with
  | a i => change p ^ i.val ∈ K; exact K.pow_mem hp _
  | xa i => change q * p ^ i.val ∈ K; exact K.mul_mem hq (K.pow_mem hp _)

theorem fz59dPi_range {b : Fin 3 → Fin 2 → G} (hb : Fz59Rows b) :
    (fz59dPi hb).range = fz59R b := by
  have hmem : ∀ (i : Fin 3) (x : Fz59Q8), q8Hom (hb.quat i) x ∈ fz59R b := fun i x =>
    fz59d_q8Hom_mem (hb.quat i) (fz59d_b_mem_R b i 0) (fz59d_b_mem_R b i 1) x
  apply le_antisymm
  · rintro _ ⟨⟨x, y, w⟩, rfl⟩
    rw [fz59dPi_apply]
    exact mul_mem (hmem 0 x) (mul_mem (hmem 1 y) (hmem 2 w))
  · rw [fz59R, closure_le]
    rintro _ ⟨⟨i, k⟩, rfl⟩
    exact ⟨fz59Gen i k, fz59dPi_gen hb i k⟩

theorem fz59dPi_card_ker {b : Fin 3 → Fin 2 → G} (hb : Fz59Rows b) :
    Nat.card (fz59dPi hb).ker = 2 := by
  have hset : (((fz59dPi hb).ker : Subgroup Fz59Mod) : Set Fz59Mod) = {1, fz59Zeta} := by
    ext x
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, fz59dPi_eq_one_iff hb, Set.mem_insert_iff,
      Set.mem_singleton_iff]
  have h1 : Nat.card (fz59dPi hb).ker =
      (((fz59dPi hb).ker : Subgroup Fz59Mod) : Set Fz59Mod).ncard := by
    rw [← Nat.card_coe_set_eq, SetLike.coe_sort_coe]
  rw [h1, hset, Set.ncard_pair (by decide)]

theorem fz59_card_R {b : Fin 3 → Fin 2 → G} (hb : Fz59Rows b) : Nat.card (fz59R b) = 2 ^ 8 := by
  have h := Subgroup.card_ker_mul_card_range (fz59dPi hb)
  have hmod : Nat.card Fz59Mod = 512 := by
    simp [Nat.card_eq_fintype_card, Fintype.card_prod, QuaternionGroup.card]
  rw [fz59dPi_card_ker hb, fz59dPi_range hb, hmod] at h
  omega

theorem fz59_comm_mem_Z {b : Fin 3 → Fin 2 → G} (hb : Fz59Rows b) :
    ∀ r ∈ fz59R b, ∀ r' ∈ fz59R b, r * r' * r⁻¹ * r'⁻¹ ∈ fz59Z b := by
  have hcen : ∀ (i : Fin 3) {x : Fz59Q8}, (x = 1 ∨ x = QuaternionGroup.a 2) →
      q8Hom (hb.quat i) x ∈ fz59Z b := by
    intro i x hx
    rcases hx with rfl | rfl
    · rw [map_one]; exact one_mem _
    · rw [fz59d_q8Hom_a_two]; exact fz59d_zi_mem hb i
  have hcomm : ∀ u v : Fz59Q8,
      (u * v * u⁻¹ * v⁻¹ = 1 ∨ u * v * u⁻¹ * v⁻¹ = QuaternionGroup.a 2) := by decide
  intro r hr r' hr'
  rw [← fz59dPi_range hb] at hr hr'
  obtain ⟨⟨x, y, w⟩, rfl⟩ := hr
  obtain ⟨⟨x', y', w'⟩, rfl⟩ := hr'
  rw [← map_mul, ← map_inv, ← map_mul, ← map_inv, ← map_mul]
  change fz59dPi hb (x * x' * x⁻¹ * x'⁻¹, y * y' * y⁻¹ * y'⁻¹, w * w' * w⁻¹ * w'⁻¹) ∈ fz59Z b
  rw [fz59dPi_apply]
  exact mul_mem (hcen 0 (hcomm x x')) (mul_mem (hcen 1 (hcomm y y')) (hcen 2 (hcomm w w')))

theorem fz59_dict {b : Fin 3 → Fin 2 → G} (hb : Fz59Rows b) :
    ∃ π : Fz59Mod →* G, (∀ i k, π (fz59Gen i k) = b i k) ∧ π.range = fz59R b ∧
      ∀ q q' : Fz59Mod, π q = π q' ↔ (q' = q ∨ q' = q * fz59Zeta) :=
  ⟨fz59dPi hb, fz59dPi_gen hb, fz59dPi_range hb, fz59dPi_eq_iff hb⟩

private theorem fz59d_rho_conj {b : Fin 3 → Fin 2 → G} {rho : G}
    (hrb : ∀ i k, rho * b i k * rho⁻¹ = b (i + 1) k) (hb : Fz59Rows b) {i j : Fin 3}
    (hij : i + 1 = j) (x : Fz59Q8) :
    rho * q8Hom (hb.quat i) x * rho⁻¹ = q8Hom (hb.quat j) x := by
  subst hij
  cases x with
  | a k =>
    change rho * b i 0 ^ k.val * rho⁻¹ = b (i + 1) 0 ^ k.val
    rw [← MulAut.conj_apply, map_pow]
    simp only [MulAut.conj_apply, hrb]
  | xa k =>
    change rho * (b i 1 * b i 0 ^ k.val) * rho⁻¹ = b (i + 1) 1 * b (i + 1) 0 ^ k.val
    rw [← MulAut.conj_apply, map_mul, map_pow]
    simp only [MulAut.conj_apply, hrb]

@[expose] def fz59dRot (q : Fz59Mod) : Fz59Mod := (q.2.2, q.1, q.2.1)

theorem fz59dPi_rot {t s lam rho : G} {b : Fin 3 → Fin 2 → G} (h : Fz59Grid t s lam rho b)
    (q : Fz59Mod) : fz59dPi h.rows (fz59dRot q) = rho * fz59dPi h.rows q * rho⁻¹ := by
  obtain ⟨x, y, w⟩ := q
  have hb := h.rows
  have e : rho * (q8Hom (hb.quat 0) x * (q8Hom (hb.quat 1) y * q8Hom (hb.quat 2) w)) * rho⁻¹ =
      (rho * q8Hom (hb.quat 0) x * rho⁻¹) * ((rho * q8Hom (hb.quat 1) y * rho⁻¹) *
        (rho * q8Hom (hb.quat 2) w * rho⁻¹)) := by group
  change fz59dPi hb (w, x, y) = _
  rw [fz59dPi_apply, fz59dPi_apply, e, fz59d_rho_conj h.rho_b hb (by decide : (0 : Fin 3) + 1 = 1),
    fz59d_rho_conj h.rho_b hb (by decide : (1 : Fin 3) + 1 = 2),
    fz59d_rho_conj h.rho_b hb (by decide : (2 : Fin 3) + 1 = 0)]
  have hc : Commute (q8Hom (hb.quat 0) w) (q8Hom (hb.quat 1) x * q8Hom (hb.quat 2) y) :=
    (fz59d_row_comm hb (by decide) w x).mul_right (fz59d_row_comm hb (by decide) w y)
  rw [hc.eq, mul_assoc]

private theorem fz59d_diag_cases : ∀ a : Fz59Q8, ∃ q' ∈ [(1 : Fz59Mod),
    (QuaternionGroup.a 1, QuaternionGroup.a 1, QuaternionGroup.a 1),
    (QuaternionGroup.xa 0, QuaternionGroup.xa 0, QuaternionGroup.xa 0),
    (QuaternionGroup.a 1, QuaternionGroup.a 1, QuaternionGroup.a 1) *
      (QuaternionGroup.xa 0, QuaternionGroup.xa 0, QuaternionGroup.xa 0)],
    q' = (a, a, a) ∨ q' = (a, a, a) * fz59Zeta := by
  decide

private theorem fz59d_rot_fixed : ∀ q : Fz59Mod, (fz59dRot q = q ∨ fz59dRot q = q * fz59Zeta) →
    ∃ a : Fz59Q8, q = (a, a, a) := by
  decide +kernel

theorem fz59_cent_rho {t s lam rho : G} {b : Fin 3 → Fin 2 → G} (h : Fz59Grid t s lam rho b) :
    ∀ r ∈ fz59R b, rho * r * rho⁻¹ = r → r = 1 ∨ r = t ∨ r = s ∨ r = t * s := by
  intro r hr hrho
  have hb := h.rows
  rw [← fz59dPi_range hb] at hr
  obtain ⟨q, rfl⟩ := hr
  rw [← fz59dPi_rot h] at hrho
  obtain ⟨a, rfl⟩ := fz59d_rot_fixed q ((fz59dPi_eq_iff hb q (fz59dRot q)).mp hrho.symm)
  obtain ⟨q', hq', hq'a⟩ := fz59d_diag_cases a
  rw [(fz59dPi_eq_iff hb (a, a, a) q').mpr hq'a]
  have ht : fz59dPi hb (QuaternionGroup.a 1, QuaternionGroup.a 1, QuaternionGroup.a 1) = t := by
    rw [fz59dPi_apply, fz59d_q8Hom_a_one, fz59d_q8Hom_a_one, fz59d_q8Hom_a_one, ← mul_assoc]
    exact h.t_eq.symm
  have hs : fz59dPi hb (QuaternionGroup.xa 0, QuaternionGroup.xa 0, QuaternionGroup.xa 0) = s := by
    rw [fz59dPi_apply, fz59d_q8Hom_xa_zero, fz59d_q8Hom_xa_zero, fz59d_q8Hom_xa_zero, ← mul_assoc]
    exact h.s_eq.symm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq'
  rcases hq' with rfl | rfl | rfl | rfl
  · exact Or.inl (map_one _)
  · exact Or.inr (Or.inl ht)
  · exact Or.inr (Or.inr (Or.inl hs))
  · exact Or.inr (Or.inr (Or.inr (by rw [map_mul, ht, hs])))

end CFSG.OddStandard.SmallF3.FritzII

