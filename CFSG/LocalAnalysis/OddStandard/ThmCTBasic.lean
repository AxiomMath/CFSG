module

public import CFSG.GH74.GLS.Bg.TwoGroups.L23Models

public section

namespace CFSG.OddStandard.ThmC.T

open CFSG.GH74.GLS.Bg.TwoGroups CFSG.GH74.GLS.Bg.TwoGroups.L23
open scoped commutatorElement

abbrev Tc : Type := UT3 F4c

theorem F4c_add_self (x : F4c) : x + x = 0 := by revert x; decide

theorem mul_a (x y : Tc) : (x * y).a = x.a + y.a := rfl
theorem mul_b (x y : Tc) : (x * y).b = x.b + y.b := rfl
theorem mul_c (x y : Tc) : (x * y).c = x.c + y.c + x.a * y.b := rfl

theorem mul_self_eq (x : Tc) : x * x = ⟨0, 0, x.a * x.b⟩ := by
  refine UT3.ext ?_ ?_ ?_
  · rw [mul_a, F4c_add_self]
  · rw [mul_b, F4c_add_self]
  · rw [mul_c, F4c_add_self, zero_add]

theorem central_sq : ∀ c : F4c, (⟨0, 0, c⟩ : Tc) * ⟨0, 0, c⟩ = 1 := by decide +kernel

theorem comm_eq : ∀ x y : Tc, ⁅x, y⁆ = ⟨0, 0, x.a * y.b + y.a * x.b⟩ := by
  decide +kernel

theorem conj_a : ∀ g x : Tc, (g * x * g⁻¹).a = x.a := by decide +kernel
theorem conj_b : ∀ g x : Tc, (g * x * g⁻¹).b = x.b := by decide +kernel

theorem mem_center_iff' : ∀ x : Tc, (∀ y : Tc, y * x = x * y) ↔ (x.a = 0 ∧ x.b = 0) := by
  decide +kernel

theorem mem_center_iff (x : Tc) : x ∈ Subgroup.center Tc ↔ x.a = 0 ∧ x.b = 0 := by
  rw [Subgroup.mem_center_iff]
  exact mem_center_iff' x

theorem card_Tc : Nat.card Tc = 64 := card_UT3c

theorem card_center : Nat.card (Subgroup.center Tc) = 4 := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight mem_center_iff), Nat.card_eq_fintype_card]
  decide +kernel

theorem sq_mem_center (x : Tc) : x * x ∈ Subgroup.center Tc := by
  rw [mul_self_eq, mem_center_iff]
  exact ⟨rfl, rfl⟩

theorem commutator_mem_center (x y : Tc) : ⁅x, y⁆ ∈ Subgroup.center Tc := by
  rw [comm_eq, mem_center_iff]
  exact ⟨rfl, rfl⟩

theorem sq_eq_one_of_mem_center {z : Tc} (hz : z ∈ Subgroup.center Tc) : z * z = 1 := by
  rw [mem_center_iff] at hz
  have : z = ⟨0, 0, z.c⟩ := UT3.ext hz.1 hz.2 rfl
  rw [this]
  exact central_sq _

theorem pow_four (x : Tc) : x ^ 4 = 1 := by
  have e : x ^ 4 = (x * x) * (x * x) := by
    rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
  rw [e]
  exact sq_eq_one_of_mem_center (sq_mem_center x)

theorem card_involutions : Nat.card {t : Tc // t * t = 1 ∧ t ≠ 1} = 27 := by
  rw [Nat.card_eq_fintype_card]
  exact inv_count_L

theorem card_sq : Nat.card {t : Tc // t * t = 1} = 28 := by
  rw [Nat.card_eq_fintype_card]; decide +kernel

@[expose] def A : Subgroup Tc where
  carrier := {x | x.b = 0}
  mul_mem' := by
    intro x y hx hy
    change x.b = 0 at hx
    change y.b = 0 at hy
    change (x * y).b = 0
    rw [mul_b, hx, hy, add_zero]
  one_mem' := rfl
  inv_mem' := by
    intro x hx
    change x.b = 0 at hx
    change (x⁻¹).b = 0
    show -x.b = 0
    rw [hx, neg_zero]

@[expose] def B : Subgroup Tc where
  carrier := {x | x.a = 0}
  mul_mem' := by
    intro x y hx hy
    change x.a = 0 at hx
    change y.a = 0 at hy
    change (x * y).a = 0
    rw [mul_a, hx, hy, add_zero]
  one_mem' := rfl
  inv_mem' := by
    intro x hx
    change x.a = 0 at hx
    change (x⁻¹).a = 0
    show -x.a = 0
    rw [hx, neg_zero]

theorem mem_A {x : Tc} : x ∈ A ↔ x.b = 0 := Iff.rfl
theorem mem_B {x : Tc} : x ∈ B ↔ x.a = 0 := Iff.rfl

instance A_normal : A.Normal := ⟨fun x hx g => by
  rw [mem_A] at hx ⊢
  rw [conj_b, hx]⟩

instance B_normal : B.Normal := ⟨fun x hx g => by
  rw [mem_B] at hx ⊢
  rw [conj_a, hx]⟩

theorem card_A : Nat.card A = 16 := by
  have h : Nat.card A = Nat.card {x : Tc // x.b = 0} := rfl
  rw [h, Nat.card_eq_fintype_card]; decide +kernel

theorem card_B : Nat.card B = 16 := by
  have h : Nat.card B = Nat.card {x : Tc // x.a = 0} := rfl
  rw [h, Nat.card_eq_fintype_card]; decide +kernel

theorem A_ne_B : A ≠ B := by
  intro h
  have : (⟨1, 0, 0⟩ : Tc) ∈ A := rfl
  rw [h, mem_B] at this
  exact absurd this (by decide)

theorem A_sup_B : A ⊔ B = ⊤ := by
  have key : ∀ x : Tc, x = (⟨x.a, 0, x.c + x.a * x.b⟩ : Tc) * ⟨0, x.b, 0⟩ := by
    decide +kernel
  rw [eq_top_iff]
  intro x _
  rw [key x]
  exact Subgroup.mul_mem _
    (Subgroup.mem_sup_left (show (⟨x.a, 0, x.c + x.a * x.b⟩ : Tc) ∈ A from rfl))
    (Subgroup.mem_sup_right (show (⟨0, x.b, 0⟩ : Tc) ∈ B from rfl))

theorem sq_eq_one_of_mem_A {x : Tc} (hx : x ∈ A) : x * x = 1 := by
  rw [mul_self_eq, mem_A.1 hx, mul_zero]
  rfl

theorem sq_eq_one_of_mem_B {x : Tc} (hx : x ∈ B) : x * x = 1 := by
  rw [mul_self_eq, mem_B.1 hx, zero_mul]
  rfl

theorem sq_eq_one_iff (x : Tc) : x * x = 1 ↔ x.a * x.b = 0 := by
  rw [mul_self_eq]
  constructor
  · intro h
    exact congrArg UT3.c h
  · intro h
    rw [h]
    rfl

theorem sq_eq_one_iff_mem (x : Tc) : x * x = 1 ↔ x ∈ A ∨ x ∈ B := by
  rw [sq_eq_one_iff, mul_eq_zero, mem_A, mem_B, or_comm]

theorem elemAbelian_le_or {E : Subgroup Tc} (h : ∀ x ∈ E, x * x = 1) : E ≤ A ∨ E ≤ B := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨h1, h2⟩ := hcon
  obtain ⟨x, hxE, hxA⟩ := IsConcreteLE.not_le_iff_exists.mp h1
  obtain ⟨y, hyE, hyB⟩ := IsConcreteLE.not_le_iff_exists.mp h2
  rw [mem_A] at hxA
  rw [mem_B] at hyB
  have hx := (sq_eq_one_iff x).1 (h x hxE)
  have hy := (sq_eq_one_iff y).1 (h y hyE)
  have hxa : x.a = 0 := (mul_eq_zero.1 hx).resolve_right hxA
  have hyb : y.b = 0 := (mul_eq_zero.1 hy).resolve_left hyB
  have hxy := (sq_eq_one_iff (x * y)).1 (h _ (E.mul_mem hxE hyE))
  rw [mul_a, mul_b, hxa, hyb, zero_add, add_zero] at hxy
  exact mul_ne_zero hyB hxA hxy

theorem card_le_sixteen {E : Subgroup Tc} (h : ∀ x ∈ E, x * x = 1) : Nat.card E ≤ 16 := by
  rcases elemAbelian_le_or h with hA | hB
  · exact (Subgroup.card_le_of_le hA).trans card_A.le
  · exact (Subgroup.card_le_of_le hB).trans card_B.le

theorem eq_A_or_B {E : Subgroup Tc} (h : ∀ x ∈ E, x * x = 1) (hc : Nat.card E = 16) :
    E = A ∨ E = B := by
  rcases elemAbelian_le_or h with hA | hB
  · exact Or.inl (Subgroup.eq_of_le_of_card_ge hA (by rw [card_A, hc]))
  · exact Or.inr (Subgroup.eq_of_le_of_card_ge hB (by rw [card_B, hc]))

theorem commute_iff (x y : Tc) : x * y = y * x ↔ x.a * y.b = y.a * x.b := by
  have h2 := F4c_add_self (y.a * x.b)
  rw [← commutatorElement_eq_one_iff_mul_comm, comm_eq]
  constructor
  · intro h
    have h' : x.a * y.b + y.a * x.b = 0 := congrArg UT3.c h
    linear_combination h' - h2
  · intro h
    refine UT3.ext rfl rfl ?_
    show x.a * y.b + y.a * x.b = 0
    linear_combination h + h2

theorem centralizer_of_mem_A {x : Tc} (hx : x ∈ A) (hxZ : x ∉ Subgroup.center Tc) :
    Subgroup.centralizer ({x} : Set Tc) = A := by
  have hxb : x.b = 0 := mem_A.1 hx
  have hxa : x.a ≠ 0 := by
    intro h
    exact hxZ ((mem_center_iff x).2 ⟨h, hxb⟩)
  ext y
  rw [Subgroup.mem_centralizer_singleton_iff, mem_A, commute_iff, hxb, mul_zero]
  constructor
  · intro h
    exact (mul_eq_zero.1 h.symm).resolve_left hxa
  · intro h
    rw [h, mul_zero]

theorem centralizer_of_mem_B {x : Tc} (hx : x ∈ B) (hxZ : x ∉ Subgroup.center Tc) :
    Subgroup.centralizer ({x} : Set Tc) = B := by
  have hxa : x.a = 0 := mem_B.1 hx
  have hxb : x.b ≠ 0 := by
    intro h
    exact hxZ ((mem_center_iff x).2 ⟨hxa, h⟩)
  ext y
  rw [Subgroup.mem_centralizer_singleton_iff, mem_B, commute_iff, hxa, zero_mul]
  constructor
  · intro h
    exact (mul_eq_zero.1 h).resolve_right hxb
  · intro h
    rw [h, zero_mul]

@[expose] def swap : Tc ≃* Tc where
  toFun x := ⟨x.b, x.a, x.c + x.a * x.b⟩
  invFun x := ⟨x.b, x.a, x.c + x.a * x.b⟩
  left_inv := by intro x; revert x; decide +kernel
  right_inv := by intro x; revert x; decide +kernel
  map_mul' := by decide +kernel

theorem swap_mem_A_iff {x : Tc} : swap x ∈ A ↔ x ∈ B := Iff.rfl
theorem swap_mem_B_iff {x : Tc} : swap x ∈ B ↔ x ∈ A := Iff.rfl

theorem solve_comm : ∀ a b c : F4c, (a ≠ 0 ∨ b ≠ 0) →
    ∃ y1 y2 : F4c, y1 * b + a * y2 = c := by decide +kernel

theorem exists_conj_eq_mul {x : Tc} (hx : x ∉ Subgroup.center Tc) {z : Tc}
    (hz : z ∈ Subgroup.center Tc) : ∃ y : Tc, y * x * y⁻¹ = x * z := by
  rw [mem_center_iff, not_and_or] at hx
  rw [mem_center_iff] at hz
  obtain ⟨y1, y2, hy⟩ := solve_comm x.a x.b z.c hx
  refine ⟨⟨y1, y2, 0⟩, ?_⟩
  have h1 := comm_eq ⟨y1, y2, 0⟩ x
  rw [commutatorElement_def] at h1
  have h2 : (⟨y1, y2, 0⟩ : Tc) * x * (⟨y1, y2, 0⟩ : Tc)⁻¹ = ⟨0, 0, z.c⟩ * x := by
    calc (⟨y1, y2, 0⟩ : Tc) * x * (⟨y1, y2, 0⟩ : Tc)⁻¹
        = ((⟨y1, y2, 0⟩ : Tc) * x * (⟨y1, y2, 0⟩ : Tc)⁻¹ * x⁻¹) * x := by group
      _ = ⟨0, 0, z.c⟩ * x := by
        rw [h1]
        simp only
        rw [hy]
  have h3 : z = ⟨0, 0, z.c⟩ := UT3.ext hz.1 hz.2 rfl
  rw [h2, h3]
  refine UT3.ext ?_ ?_ ?_
  · simp [UT3.mul_def]
  · simp [UT3.mul_def]
  · simp [UT3.mul_def, add_comm]

theorem normal_dichotomy {N : Subgroup Tc} (hN : N.Normal) :
    N ≤ Subgroup.center Tc ∨ Subgroup.center Tc ≤ N := by
  by_cases h : N ≤ Subgroup.center Tc
  · exact Or.inl h
  · right
    obtain ⟨x, hxN, hxZ⟩ := IsConcreteLE.not_le_iff_exists.mp h
    intro z hz
    obtain ⟨y, hy⟩ := exists_conj_eq_mul hxZ hz
    have h1 := hN.conj_mem x hxN y
    rw [hy] at h1
    have h2 := N.mul_mem (N.inv_mem hxN) h1
    rwa [inv_mul_cancel_left] at h2

end CFSG.OddStandard.ThmC.T
