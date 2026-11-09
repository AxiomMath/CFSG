module

public import Certificates.Data.Kernel.ExactGen.Defs

public section

namespace CFSG.KC.ExactGen

open CFSG.ComponentClassification.SolMax.SwapP2.ExactFin

variable (n w : ℕ)

theorem parOK_append (cd : ChainData) (BT : ℕ → ℕ) :
    ∀ (l₁ l₂ : List (ℕ × ℤ)) (m : ℕ),
      parOK n w cd BT m (l₁ ++ l₂) = (parOK n w cd BT m l₁ && parOK n w cd BT (m + l₁.length) l₂)
  | [], l₂, m => by simp [parOK]
  | (p, l) :: rest, l₂, m => by
    have e : m + 1 + rest.length = m + (rest.length + 1) := by omega
    simp only [List.cons_append, parOK, parOK_append cd BT rest l₂ (m + 1), List.length_cons, e,
      Bool.and_assoc]

theorem parOK_of_take_drop (cd : ChainData) (BT : ℕ → ℕ) (P : List (ℕ × ℤ)) (m c : ℕ)
    (h₁ : parOK n w cd BT m (P.take c) = true)
    (h₂ : parOK n w cd BT (m + (P.take c).length) (P.drop c) = true) :
    parOK n w cd BT m P = true := by
  rw [← List.take_append_drop c P, parOK_append, h₁, h₂]
  rfl

theorem parOK_of_take_drop' (cd : ChainData) (BT : ℕ → ℕ) (P : List (ℕ × ℤ)) (m c : ℕ)
    (hc : (P.take c).length = c) (h₁ : parOK n w cd BT m (P.take c) = true)
    (h₂ : parOK n w cd BT (m + c) (P.drop c) = true) :
    parOK n w cd BT m P = true :=
  parOK_of_take_drop n w cd BT P m c h₁ (by rw [hc]; exact h₂)

theorem strictInc_window : ∀ (k : ℕ) (l : List ℕ),
    strictInc (l.take (k + 1)) = true → strictInc (l.drop k) = true → strictInc l = true
  | 0, l, _, h₂ => by simpa using h₂
  | _ + 1, [], _, _ => rfl
  | _ + 1, [_], _, _ => rfl
  | k + 1, a :: b :: l, h₁, h₂ => by
    have h₁' : (decide (a < b) && strictInc ((b :: l).take (k + 1))) = true := h₁
    rw [Bool.and_eq_true] at h₁'
    show (decide (a < b) && strictInc (b :: l)) = true
    rw [h₁'.1, strictInc_window k (b :: l) h₁'.2 h₂]
    rfl

end CFSG.KC.ExactGen

end
