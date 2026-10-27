module

public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Data.Set.Card

public section

namespace CFSG.OddStandard.SmallF3.L33

private lemma mul_pow_eq_of_conj {G : Type*} [Group G] {a b : G} {n : ℕ}
    (h : a * b * a⁻¹ = b ^ n) (m : ℕ) : a * b ^ m = b ^ (n * m) * a := by
  have h1 : a * b ^ m * a⁻¹ = b ^ (n * m) := by
    rw [← conj_pow, h, pow_mul]
  calc
    a * b ^ m = a * b ^ m * a⁻¹ * a := by rw [mul_assoc, inv_mul_cancel, mul_one]
    _ = b ^ (n * m) * a := by rw [h1]

private lemma inv_eq_pow_pred_of_pow_eq_one {G : Type*} [Group G] {x : G} {n : ℕ}
    (hn : n ≠ 0) (h : x ^ n = 1) : x⁻¹ = x ^ (n - 1) := by
  apply inv_eq_of_mul_eq_one_right
  rw [mul_pow_sub_one hn x, h]

private lemma mul_pow_comm_of_mul_comm {G : Type*} [Group G] {a b : G}
    (h : a * b = b * a) (n : ℕ) : a * b ^ n = b ^ n * a := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      a * b ^ (n + 1) = a * (b ^ n * b) := by rw [pow_succ]
      _ = (a * b ^ n) * b := by rw [← mul_assoc]
      _ = (b ^ n * a) * b := by rw [ih]
      _ = b ^ n * (a * b) := by rw [mul_assoc]
      _ = b ^ n * (b * a) := by rw [h]
      _ = (b ^ n * b) * a := by rw [← mul_assoc]
      _ = b ^ (n + 1) * a := by rw [pow_succ]

theorem card_closure_xyk {G : Type*} [Group G] (x y k : G) (hx : x ^ 8 = 1) (hy : y ^ 2 = 1)
    (hk : k ^ 2 = 1) (hyx : y * x * y⁻¹ = x ^ 3) (hkx : k * x * k⁻¹ = x * x ^ 4)
    (hyk : y * k = k * y)
    (hinj : Function.Injective fun a : Fin 8 × Fin 2 × Fin 2 =>
      x ^ (a.1 : ℕ) * y ^ (a.2.1 : ℕ) * k ^ (a.2.2 : ℕ)) :
    Nat.card (Subgroup.closure ({x, y, k} : Set G)) = 32 := by
  let w : Fin 8 × Fin 2 × Fin 2 → G := fun a =>
    x ^ (a.1 : ℕ) * y ^ (a.2.1 : ℕ) * k ^ (a.2.2 : ℕ)
  let S : Set G := Set.range w
  have hkx5 : k * x * k⁻¹ = x ^ 5 := by rw [hkx, ← pow_succ' x 4]
  have hky : ∀ m : ℕ, k * y ^ m = y ^ m * k := mul_pow_comm_of_mul_comm hyk.symm
  have hmem : ∀ i j l : ℕ, x ^ i * y ^ j * k ^ l ∈ S := by
    intro i j l
    refine ⟨(⟨i % 8, Nat.mod_lt i (by decide)⟩, ⟨j % 2, Nat.mod_lt j (by decide)⟩,
      ⟨l % 2, Nat.mod_lt l (by decide)⟩), ?_⟩
    dsimp [w]
    rw [← pow_eq_pow_mod i hx, ← pow_eq_pow_mod j hy, ← pow_eq_pow_mod l hk]
  have hmulx : ∀ i j l : ℕ, x * (x ^ i * y ^ j * k ^ l) ∈ S := by
    intro i j l
    refine (show x * (x ^ i * y ^ j * k ^ l) = x ^ (i + 1) * y ^ j * k ^ l from ?_)
      ▸ hmem (i + 1) j l
    calc
      x * (x ^ i * y ^ j * k ^ l) = (x * x ^ i) * y ^ j * k ^ l := by
        simp only [← mul_assoc]
      _ = x ^ (i + 1) * y ^ j * k ^ l := by rw [← pow_succ']
  have hmuly : ∀ i j l : ℕ, y * (x ^ i * y ^ j * k ^ l) ∈ S := by
    intro i j l
    refine (show y * (x ^ i * y ^ j * k ^ l) = x ^ (3 * i) * y ^ (j + 1) * k ^ l from ?_)
      ▸ hmem (3 * i) (j + 1) l
    calc
      y * (x ^ i * y ^ j * k ^ l) = (y * x ^ i) * y ^ j * k ^ l := by
        simp only [← mul_assoc]
      _ = (x ^ (3 * i) * y) * y ^ j * k ^ l := by rw [mul_pow_eq_of_conj hyx i]
      _ = x ^ (3 * i) * (y * y ^ j) * k ^ l := by
        rw [mul_assoc (x ^ (3 * i)) y (y ^ j)]
      _ = x ^ (3 * i) * y ^ (j + 1) * k ^ l := by rw [← pow_succ' y j]
  have hmulk : ∀ i j l : ℕ, k * (x ^ i * y ^ j * k ^ l) ∈ S := by
    intro i j l
    refine (show k * (x ^ i * y ^ j * k ^ l) = x ^ (5 * i) * y ^ j * k ^ (l + 1) from ?_)
      ▸ hmem (5 * i) j (l + 1)
    calc
      k * (x ^ i * y ^ j * k ^ l) = (k * x ^ i) * y ^ j * k ^ l := by
        simp only [← mul_assoc]
      _ = (x ^ (5 * i) * k) * y ^ j * k ^ l := by rw [mul_pow_eq_of_conj hkx5 i]
      _ = x ^ (5 * i) * (k * y ^ j) * k ^ l := by
        rw [mul_assoc (x ^ (5 * i)) k (y ^ j)]
      _ = x ^ (5 * i) * (y ^ j * k) * k ^ l := by rw [hky j]
      _ = x ^ (5 * i) * y ^ j * k * k ^ l := by
        rw [← mul_assoc (x ^ (5 * i)) (y ^ j) k]
      _ = x ^ (5 * i) * y ^ j * (k * k ^ l) := by
        rw [mul_assoc (x ^ (5 * i) * y ^ j) k (k ^ l)]
      _ = x ^ (5 * i) * y ^ j * k ^ (l + 1) := by rw [← pow_succ' k l]
  have hxinv : x⁻¹ = x ^ 7 :=
    inv_eq_pow_pred_of_pow_eq_one (by decide : (8 : ℕ) ≠ 0) hx
  have hyinv : y⁻¹ = y := by
    rw [inv_eq_pow_pred_of_pow_eq_one (by decide : (2 : ℕ) ≠ 0) hy]
    simp
  have hkinv : k⁻¹ = k := by
    rw [inv_eq_pow_pred_of_pow_eq_one (by decide : (2 : ℕ) ≠ 0) hk]
    simp
  have hmulxinv : ∀ i j l : ℕ, x⁻¹ * (x ^ i * y ^ j * k ^ l) ∈ S := by
    intro i j l
    refine (show x⁻¹ * (x ^ i * y ^ j * k ^ l) = x ^ (7 + i) * y ^ j * k ^ l from ?_)
      ▸ hmem (7 + i) j l
    calc
      x⁻¹ * (x ^ i * y ^ j * k ^ l) = (x⁻¹ * x ^ i) * y ^ j * k ^ l := by
        simp only [← mul_assoc]
      _ = (x ^ 7 * x ^ i) * y ^ j * k ^ l := by rw [hxinv]
      _ = x ^ (7 + i) * y ^ j * k ^ l := by rw [← pow_add]
  have hsub : (Subgroup.closure ({x, y, k} : Set G) : Set G) = S := by
    refine le_antisymm ?_ ?_
    · intro g hg
      refine Subgroup.closure_induction_left (p := fun g _ => g ∈ S) ?_ ?_ ?_ hg
      · simpa using hmem 0 0 0
      · intro a ha b hb ih
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
        rcases ha with rfl | rfl | rfl
        · obtain ⟨⟨i, j, l⟩, rfl⟩ := ih
          dsimp [w]
          exact hmulx (i : ℕ) (j : ℕ) (l : ℕ)
        · obtain ⟨⟨i, j, l⟩, rfl⟩ := ih
          dsimp [w]
          exact hmuly (i : ℕ) (j : ℕ) (l : ℕ)
        · obtain ⟨⟨i, j, l⟩, rfl⟩ := ih
          dsimp [w]
          exact hmulk (i : ℕ) (j : ℕ) (l : ℕ)
      · intro a ha b hb ih
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
        rcases ha with rfl | rfl | rfl
        · obtain ⟨⟨i, j, l⟩, rfl⟩ := ih
          dsimp [w]
          exact hmulxinv (i : ℕ) (j : ℕ) (l : ℕ)
        · obtain ⟨⟨i, j, l⟩, rfl⟩ := ih
          dsimp [w]
          rw [hyinv]
          exact hmuly (i : ℕ) (j : ℕ) (l : ℕ)
        · obtain ⟨⟨i, j, l⟩, rfl⟩ := ih
          dsimp [w]
          rw [hkinv]
          exact hmulk (i : ℕ) (j : ℕ) (l : ℕ)
    · intro g hg
      obtain ⟨a, rfl⟩ := hg
      obtain ⟨i, j, l⟩ := a
      have hxg : x ∈ ({x, y, k} : Set G) := by simp
      have hyg : y ∈ ({x, y, k} : Set G) := by simp
      have hkg : k ∈ ({x, y, k} : Set G) := by simp
      dsimp [w]
      exact Subgroup.mul_mem (Subgroup.closure ({x, y, k} : Set G))
        (Subgroup.mul_mem (Subgroup.closure ({x, y, k} : Set G))
          (Subgroup.pow_mem (Subgroup.closure ({x, y, k} : Set G))
            (Subgroup.subset_closure hxg) (i : ℕ))
          (Subgroup.pow_mem (Subgroup.closure ({x, y, k} : Set G))
            (Subgroup.subset_closure hyg) (j : ℕ)))
        (Subgroup.pow_mem (Subgroup.closure ({x, y, k} : Set G))
          (Subgroup.subset_closure hkg) (l : ℕ))
  have hS_card : S.ncard = 32 := by
    have h1 : S.ncard = Nat.card (Fin 8 × Fin 2 × Fin 2) := Set.ncard_range_of_injective hinj
    rw [h1, Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_prod, Fintype.card_fin]
    decide
  have hcard : Nat.card (Subgroup.closure ({x, y, k} : Set G)) = S.ncard := by
    rw [← SetLike.coe_sort_coe (Subgroup.closure ({x, y, k} : Set G)),
      Nat.card_coe_set_eq, hsub]
  exact hcard.trans hS_card

theorem card_closure_xy {G : Type*} [Group G] (x y : G) (hx : x ^ 8 = 1) (hy : y ^ 2 = 1)
    (hyx : y * x * y⁻¹ = x ^ 3)
    (hinj : Function.Injective fun a : Fin 8 × Fin 2 => x ^ (a.1 : ℕ) * y ^ (a.2 : ℕ)) :
    Nat.card (Subgroup.closure ({x, y} : Set G)) = 16 := by
  let v : Fin 8 × Fin 2 → G := fun a => x ^ (a.1 : ℕ) * y ^ (a.2 : ℕ)
  let S : Set G := Set.range v
  have hmem : ∀ i j : ℕ, x ^ i * y ^ j ∈ S := by
    intro i j
    refine ⟨(⟨i % 8, Nat.mod_lt i (by decide)⟩, ⟨j % 2, Nat.mod_lt j (by decide)⟩), ?_⟩
    dsimp [v]
    rw [← pow_eq_pow_mod i hx, ← pow_eq_pow_mod j hy]
  have hmulx : ∀ i j : ℕ, x * (x ^ i * y ^ j) ∈ S := by
    intro i j
    refine (show x * (x ^ i * y ^ j) = x ^ (i + 1) * y ^ j from ?_) ▸ hmem (i + 1) j
    calc
      x * (x ^ i * y ^ j) = (x * x ^ i) * y ^ j := by simp only [← mul_assoc]
      _ = x ^ (i + 1) * y ^ j := by rw [← pow_succ']
  have hmuly : ∀ i j : ℕ, y * (x ^ i * y ^ j) ∈ S := by
    intro i j
    refine (show y * (x ^ i * y ^ j) = x ^ (3 * i) * y ^ (j + 1) from ?_) ▸ hmem (3 * i) (j + 1)
    calc
      y * (x ^ i * y ^ j) = (y * x ^ i) * y ^ j := by simp only [← mul_assoc]
      _ = (x ^ (3 * i) * y) * y ^ j := by rw [mul_pow_eq_of_conj hyx i]
      _ = x ^ (3 * i) * (y * y ^ j) := by rw [mul_assoc (x ^ (3 * i)) y (y ^ j)]
      _ = x ^ (3 * i) * y ^ (j + 1) := by rw [← pow_succ' y j]
  have hxinv : x⁻¹ = x ^ 7 :=
    inv_eq_pow_pred_of_pow_eq_one (by decide : (8 : ℕ) ≠ 0) hx
  have hyinv : y⁻¹ = y := by
    rw [inv_eq_pow_pred_of_pow_eq_one (by decide : (2 : ℕ) ≠ 0) hy]
    simp
  have hmulxinv : ∀ i j : ℕ, x⁻¹ * (x ^ i * y ^ j) ∈ S := by
    intro i j
    refine (show x⁻¹ * (x ^ i * y ^ j) = x ^ (7 + i) * y ^ j from ?_) ▸ hmem (7 + i) j
    calc
      x⁻¹ * (x ^ i * y ^ j) = (x⁻¹ * x ^ i) * y ^ j := by simp only [← mul_assoc]
      _ = (x ^ 7 * x ^ i) * y ^ j := by rw [hxinv]
      _ = x ^ (7 + i) * y ^ j := by rw [← pow_add]
  have hsub : (Subgroup.closure ({x, y} : Set G) : Set G) = S := by
    refine le_antisymm ?_ ?_
    · intro g hg
      refine Subgroup.closure_induction_left (p := fun g _ => g ∈ S) ?_ ?_ ?_ hg
      · simpa using hmem 0 0
      · intro a ha b hb ih
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
        rcases ha with rfl | rfl
        · obtain ⟨⟨i, j⟩, rfl⟩ := ih
          dsimp [v]
          exact hmulx (i : ℕ) (j : ℕ)
        · obtain ⟨⟨i, j⟩, rfl⟩ := ih
          dsimp [v]
          exact hmuly (i : ℕ) (j : ℕ)
      · intro a ha b hb ih
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
        rcases ha with rfl | rfl
        · obtain ⟨⟨i, j⟩, rfl⟩ := ih
          dsimp [v]
          exact hmulxinv (i : ℕ) (j : ℕ)
        · obtain ⟨⟨i, j⟩, rfl⟩ := ih
          dsimp [v]
          rw [hyinv]
          exact hmuly (i : ℕ) (j : ℕ)
    · intro g hg
      obtain ⟨a, rfl⟩ := hg
      obtain ⟨i, j⟩ := a
      have hxg : x ∈ ({x, y} : Set G) := by simp
      have hyg : y ∈ ({x, y} : Set G) := by simp
      dsimp [v]
      exact Subgroup.mul_mem (Subgroup.closure ({x, y} : Set G))
        (Subgroup.pow_mem (Subgroup.closure ({x, y} : Set G))
          (Subgroup.subset_closure hxg) (i : ℕ))
        (Subgroup.pow_mem (Subgroup.closure ({x, y} : Set G))
          (Subgroup.subset_closure hyg) (j : ℕ))
  have hS_card : S.ncard = 16 := by
    have h1 : S.ncard = Nat.card (Fin 8 × Fin 2) := Set.ncard_range_of_injective hinj
    rw [h1, Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_fin]
    decide
  have hcard : Nat.card (Subgroup.closure ({x, y} : Set G)) = S.ncard := by
    rw [← SetLike.coe_sort_coe (Subgroup.closure ({x, y} : Set G)),
      Nat.card_coe_set_eq, hsub]
  exact hcard.trans hS_card

end CFSG.OddStandard.SmallF3.L33
