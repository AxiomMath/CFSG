module

public import CFSG.Fischer.Classification.PartIII.U4.Points

public section

namespace CFSG.LargeExtraspecial.S12I4M

open CFSG.Fischer.Classification.LocalU4 CFSG.Fischer.Classification.Beta
  CFSG.Fischer.Classification.Unitary

local instance (priority := high) decEqF4 : DecidableEq CFSG.Fischer.F4 := fun a b =>
  decidable_of_iff (a.code = b.code) (by cases a; cases b; simp)

@[expose] def pk1 : Fin 45 → Fin 45 := ![12, 14, 13, 9, 10, 11, 12, 13, 14, 3, 4, 5, 6, 7, 8,
  0, 31, 44, 30, 34, 38, 33, 28, 41, 27, 35, 44, 42, 43, 38, 36, 37, 41, 39, 40, 25, 30, 31, 29,
  33, 34, 32, 27, 28, 26]

@[expose] def pd1 : Fin 45 → ℕ := ![2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 2, 2, 2, 2,
  2, 2, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

@[expose] def pk2 : Fin 45 → Fin 45 := ![0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 21,
  19, 22, 17, 22, 23, 18, 21, 17, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

@[expose] def pd2 : Fin 45 → ℕ := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 1, 1,
  2, 1, 1, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

@[expose] def gp : Fin 45 → Fin 45 × Fin 45 := ![(0, 0), (0, 0), (0, 1), (0, 6), (1, 6),
  (6, 2), (0, 0), (6, 8), (1, 3), (0, 12), (1, 12), (15, 5), (15, 6), (15, 7), (1, 9), (0, 0),
  (0, 0), (2, 24), (3, 36), (6, 26), (2, 22), (16, 2), (6, 36), (16, 1), (6, 38), (15, 35),
  (1, 33), (2, 34), (6, 21), (1, 34), (1, 28), (15, 37), (0, 28), (0, 31), (16, 35), (6, 14),
  (1, 43), (6, 23), (1, 40), (0, 37), (16, 25), (0, 43), (2, 40), (15, 28), (1, 39)]

@[expose] def gd : Fin 45 → ℕ := ![0, 0, 1, 1, 1, 2, 0, 3, 2, 2, 2, 3, 1, 4, 3, 0, 0, 9, 6, 6,
  7, 2, 6, 1, 8, 5, 5, 6, 3, 6, 4, 3, 4, 4, 5, 4, 5, 2, 7, 3, 6, 5, 7, 4, 4]

theorem check_pk1 : ∀ i : Fin 45, i = 15 ∨ pd1 (tauI (pk1 i) i) < pd1 i := by
  decide +kernel

theorem check_pk2 : ∀ j : Fin 45, cm 15 j → j ≠ 15 →
    j = 0 ∨ (cm (pk2 j) 15 ∧ pd2 (tauI (pk2 j) j) < pd2 j) := by
  decide +kernel

theorem check_gp : ∀ k : Fin 45, (k = 15 ∨ k = 0 ∨ k = 16 ∨ k = 1 ∨ k = 6) ∨
    (tauI (gp k).1 (gp k).2 = k ∧ gd (gp k).1 < gd k ∧ gd (gp k).2 < gd k) := by
  decide +kernel

theorem cm_tree : cm 15 0 ∧ cm 15 16 ∧ cm 15 1 ∧ cm 16 6 := by
  decide +kernel

theorem pt_mul_self (k : Fin 45) : pt k * pt k = 1 := tq_mul_self (herm_vecK_uPt k)

theorem tauI_tauI (k i : Fin 45) : tauI k (tauI k i) = i := by
  apply pt_injective
  rw [← pt_mul_mul, ← pt_mul_mul]
  calc pt k * (pt k * pt i * pt k) * pt k = pt k * pt k * pt i * (pt k * pt k) := by group
    _ = pt i := by rw [pt_mul_self, one_mul, mul_one]

theorem tauI_injective (k : Fin 45) : Function.Injective (tauI k) := fun i j h => by
  rw [← tauI_tauI k i, h, tauI_tauI]

theorem tauI_of_cm {k i : Fin 45} (h : cm k i) : tauI k i = i := by
  apply pt_injective
  rw [← pt_mul_mul, (pt_commute_iff k i).2 h, mul_assoc, pt_mul_self, mul_one]

theorem cm_tauI {i j : Fin 45} (k : Fin 45) (h : cm i j) : cm (tauI k i) (tauI k j) := by
  rw [← pt_commute_iff, ← pt_mul_mul, ← pt_mul_mul]
  have hc := (pt_commute_iff i j).2 h
  have hk := pt_mul_self k
  calc pt k * pt i * pt k * (pt k * pt j * pt k) = pt k * (pt i * pt j) * pt k := by
        rw [show pt k * pt i * pt k * (pt k * pt j * pt k) =
          pt k * pt i * (pt k * pt k) * pt j * pt k by group, hk, mul_one]
        group
    _ = pt k * (pt j * pt i) * pt k := by rw [hc]
    _ = pt k * pt j * pt k * (pt k * pt i * pt k) := by
        rw [show pt k * pt j * pt k * (pt k * pt i * pt k) =
          pt k * pt j * (pt k * pt k) * pt i * pt k by group, hk, mul_one]
        group

theorem pair_iff (R : Fin 45 → Fin 45 → Prop) (hR : ∀ k i j, R i j → R (tauI k i) (tauI k j))
    {i j : Fin 45} (hij : cm i j) (hne : i ≠ j) : R i j ↔ R 15 0 := by
  have step : ∀ k i j, R i j ↔ R (tauI k i) (tauI k j) := fun k i j =>
    ⟨hR k i j, fun h => by simpa only [tauI_tauI] using hR k _ _ h⟩
  have hstar : ∀ n, ∀ j, pd2 j = n → cm 15 j → j ≠ 15 → (R 15 j ↔ R 15 0) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro j hn hj hj15
    rcases check_pk2 j hj hj15 with rfl | ⟨hk, hlt⟩
    · exact Iff.rfl
    · have hk15 : tauI (pk2 j) 15 = 15 := tauI_of_cm hk
      rw [step (pk2 j) 15 j, hk15]
      refine ih _ (hn ▸ hlt) _ rfl ?_ fun h => hj15 (tauI_injective _ (h.trans hk15.symm))
      have := cm_tauI (pk2 j) hj
      rwa [hk15] at this
  have hall : ∀ n, ∀ i j, pd1 i = n → cm i j → i ≠ j → (R i j ↔ R 15 0) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro i j hn hij hne
    rcases check_pk1 i with rfl | hlt
    · exact hstar _ j rfl hij (Ne.symm hne)
    · rw [step (pk1 i) i j]
      exact ih _ (hn ▸ hlt) _ _ rfl (cm_tauI _ hij) fun h => hne (tauI_injective _ h)
  exact hall _ i j rfl hij hne

theorem gen_all (P : Fin 45 → Prop) (h15 : P 15) (h0 : P 0) (h16 : P 16) (h1 : P 1) (h6 : P 6)
    (hτ : ∀ i j, P i → P j → P (tauI i j)) (k : Fin 45) : P k := by
  suffices h : ∀ n k, gd k = n → P k from h _ k rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro k hn
  rcases check_gp k with h5 | ⟨he, h1', h2'⟩
  · rcases h5 with rfl | rfl | rfl | rfl | rfl <;> assumption
  · rw [← he]
    exact hτ _ _ (ih _ (hn ▸ h1') _ rfl) (ih _ (hn ▸ h2') _ rfl)

end CFSG.LargeExtraspecial.S12I4M
