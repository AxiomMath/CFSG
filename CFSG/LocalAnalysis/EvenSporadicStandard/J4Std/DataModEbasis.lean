module

public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.Interface
public import CFSG.Sporadic.J4.QTElem

public section

namespace CFSG.EvenSporadicStandard.J4Std.DataMod

open CFSG.Sporadic.J4.QT

variable {G : Type} [Group G]

theorem zmod_two_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  revert x
  decide

theorem ofFn_prod_eq_eta (u : ℕ → G) : ∀ (n m : ℕ) (c : Fin n → ZMod 2),
    (∀ j : Fin n, m.testBit j = decide (c j = 1)) →
      (List.ofFn fun i : Fin n => u i ^ (c i).val).prod = eta u n m
  | 0, m, c, _ => by simp [eta]
  | n + 1, m, c, h => by
    rw [List.ofFn_succ', List.prod_concat, eta_succ]
    have ih := ofFn_prod_eq_eta u n m (fun j => c j.castSucc) (fun j => h j.castSucc)
    simp only [Fin.val_castSucc] at ih ⊢
    rw [ih]
    congr 1
    have hl := h (Fin.last n)
    rw [Fin.val_last] at hl
    rcases zmod_two_cases (c (Fin.last n)) with h0 | h1
    · rw [h0] at hl ⊢
      have : m.testBit n = false := by simpa using hl
      simp [this]
    · rw [h1] at hl ⊢
      have : m.testBit n = true := by simpa using hl
      have hv : ZMod.val (1 : ZMod 2) = 1 := rfl
      simp [this, hv]

theorem exists_mask : ∀ (n : ℕ) (c : Fin n → ZMod 2),
    ∃ m < 2 ^ n, ∀ j : Fin n, m.testBit j = decide (c j = 1)
  | 0, c => ⟨0, by norm_num, fun j => j.elim0⟩
  | n + 1, c => by
    obtain ⟨m', hm', h'⟩ := exists_mask n (fun j => c j.castSucc)
    rcases zmod_two_cases (c (Fin.last n)) with h0 | h1
    · refine ⟨m', by rw [pow_succ]; omega, fun j => ?_⟩
      refine Fin.lastCases ?_ (fun j => ?_) j
      · rw [Fin.val_last, Nat.testBit_lt_two_pow hm', h0]
        simp
      · rw [Fin.val_castSucc]
        exact h' j
    · refine ⟨2 ^ n + m', by rw [pow_succ]; omega, fun j => ?_⟩
      refine Fin.lastCases ?_ (fun j => ?_) j
      · rw [Fin.val_last, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hm', h1]
        simp
      · rw [Fin.val_castSucc, Nat.testBit_two_pow_add_gt j.2]
        exact h' j

theorem ebasis_eq_eta (u : ℕ → G) {c : Fin 11 → ZMod 2} {m : ℕ}
    (h : ∀ j : Fin 11, m.testBit j = decide (c j = 1)) :
    ebasis (fun i : Fin 11 => u i) c = eta u 11 m :=
  ofFn_prod_eq_eta u 11 m c h

end CFSG.EvenSporadicStandard.J4Std.DataMod
