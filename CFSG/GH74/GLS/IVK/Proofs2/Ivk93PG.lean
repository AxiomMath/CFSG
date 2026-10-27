module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk95Ord

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.Blueprint
  CFSG.GH74.GLS.Stage2.Final.ModelBlock CFSG.GH74.L5U5

theorem sl2_card_inj {a b : ℕ} (ha : 5 ≤ a) (hb : 5 ≤ b) (h : a * (a ^ 2 - 1) = b * (b ^ 2 - 1)) :
    a = b := by
  have key : ∀ a : ℕ, 1 ≤ a →
      a * (a ^ 2 - 1) + 3 * a ^ 2 + 3 * a = (a + 1) * ((a + 1) ^ 2 - 1) := by
    intro a ha
    have h1 : 1 ≤ a ^ 2 := Nat.one_le_pow _ _ ha
    have h2 : 1 ≤ (a + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    zify [h1, h2]
    ring
  have lt : ∀ a b : ℕ, 5 ≤ a → a < b → a * (a ^ 2 - 1) < b * (b ^ 2 - 1) := by
    intro a b ha hab
    have h1 := sl2_card_mono (show a + 1 ≤ b by omega)
    have h2 := key a (by omega)
    have h3 : 0 < 3 * a ^ 2 := by positivity
    omega
  rcases lt_trichotomy a b with hab | hab | hab
  · exact absurd h (ne_of_lt (lt a b ha hab))
  · exact hab
  · exact absurd h.symm (ne_of_lt (lt b a hb hab))

end CFSG.GH74.GLS.IVK.Proofs2
