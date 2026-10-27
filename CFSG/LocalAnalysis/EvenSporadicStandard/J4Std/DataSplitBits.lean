module

public import CFSG.Sporadic.J4.QTElem
public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.DataSplitLA
public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.LiftObstruction

public section

namespace CFSG.EvenSporadicStandard.J4Std.DataSplit

open CFSG.Sporadic.J4.QT Matrix

@[expose] def vecOfMask (m : ℕ) : Fin 11 → F2 := fun j => if m.testBit j then 1 else 0

theorem vecOfMask_zero : vecOfMask 0 = 0 := by
  funext j; simp [vecOfMask]

theorem vecOfMask_xor (a b : ℕ) : vecOfMask (a ^^^ b) = vecOfMask a + vecOfMask b := by
  funext j
  simp only [vecOfMask, Nat.testBit_xor, Pi.add_apply]
  cases a.testBit j <;> cases b.testBit j <;> decide

theorem vecOfMask_injOn {a b : ℕ} (ha : a < 2 ^ 11) (hb : b < 2 ^ 11)
    (h : vecOfMask a = vecOfMask b) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 11
  · have := congrFun h ⟨i, hi⟩
    simp only [vecOfMask] at this
    cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all
  · have h1 : a.testBit i = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num) (by omega)))
    have h2 : b.testBit i = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by norm_num) (by omega)))
    rw [h1, h2]

theorem vecOfMask_surj (c : Fin 11 → F2) : ∃ m < 2 ^ 11, vecOfMask m = c := by
  have hbij : Function.Bijective (fun m : Fin (2 ^ 11) => vecOfMask m) := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨fun a b h => Fin.ext (vecOfMask_injOn a.2 b.2 h), ?_⟩
    simp
  obtain ⟨m, hm⟩ := hbij.2 c
  exact ⟨m, m.2, hm⟩

@[expose] noncomputable def maskOf (c : Fin 11 → F2) : ℕ := (vecOfMask_surj c).choose

theorem maskOf_lt (c : Fin 11 → F2) : maskOf c < 2 ^ 11 := (vecOfMask_surj c).choose_spec.1

theorem vecOfMask_maskOf (c : Fin 11 → F2) : vecOfMask (maskOf c) = c :=
  (vecOfMask_surj c).choose_spec.2

theorem maskOf_vecOfMask {m : ℕ} (hm : m < 2 ^ 11) : maskOf (vecOfMask m) = m :=
  vecOfMask_injOn (maskOf_lt _) hm (vecOfMask_maskOf _)

theorem maskOf_add (c d : Fin 11 → F2) : maskOf (c + d) = maskOf c ^^^ maskOf d := by
  apply vecOfMask_injOn (maskOf_lt _) (Nat.xor_lt_two_pow (maskOf_lt _) (maskOf_lt _))
  rw [vecOfMask_maskOf, vecOfMask_xor, vecOfMask_maskOf, vecOfMask_maskOf]

theorem maskOf_injective : Function.Injective maskOf := fun c d h => by
  rw [← vecOfMask_maskOf c, ← vecOfMask_maskOf d, h]

theorem vecOfMask_rowsXor (R : ℕ → ℕ) (c : ℕ) :
    vecOfMask (rowsXor R 11 c) = vecOfMask c ᵥ* maskMatrix F2 (fun i => R i) := by
  have key : ∀ m, vecOfMask (rowsXor R m c) =
      ∑ i ∈ Finset.range m, (if c.testBit i then vecOfMask (R i) else 0) := by
    intro m
    induction m with
    | zero => simp [rowsXor_zero, vecOfMask_zero]
    | succ m ih =>
      rw [rowsXor_succ, vecOfMask_xor, ih, Finset.sum_range_succ]
      congr 1
      split_ifs
      · rfl
      · exact vecOfMask_zero
  rw [key, vecMul_eq_sum, Finset.sum_range]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases h : c.testBit i <;> simp [vecOfMask, h, maskMatrix]
  rfl

theorem eta_congr_testBit {G : Type*} [Group G] (u : ℕ → G) {n a b : ℕ}
    (h : ∀ j < n, a.testBit j = b.testBit j) : eta u n a = eta u n b := by
  induction n with
  | zero => simp [eta]
  | succ n ih =>
    rw [eta_succ, eta_succ, ih (fun j hj => h j (by omega)), h n (by omega)]

end CFSG.EvenSporadicStandard.J4Std.DataSplit
