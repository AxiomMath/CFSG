module

public import CFSG.CharacterTheory.Wreathed.MaximalOrder
public import CFSG.Open.Catalog

public noncomputable section

namespace CFSG.Wreathed

open scoped Classical

@[expose] def oddResidueEquiv (h : ℕ) (hh : 0 < h) :
    {c : ZMod (2 * h) // Odd c.val} ≃ Fin h := by
  letI : NeZero (2 * h) := ⟨by omega⟩
  exact {
    toFun c := ⟨c.val.val / 2, by
      have hlt := ZMod.val_lt c.val
      omega⟩
    invFun i := ⟨((2 * i.val + 1 : ℕ) : ZMod (2 * h)), by
      rw [ZMod.val_natCast_of_lt (by omega)]
      exact ⟨i.val, by omega⟩⟩
    left_inv c := by
      apply Subtype.ext
      change ((2 * (c.val.val / 2) + 1 : ℕ) : ZMod (2 * h)) = c.val
      apply ZMod.val_injective (2 * h)
      rw [ZMod.val_natCast_of_lt (by
        have hlt := ZMod.val_lt c.val
        have hodd := Nat.odd_iff.mp c.property
        omega)]
      have hodd := Nat.odd_iff.mp c.property
      have hdiv := Nat.mod_add_div c.val.val 2
      omega
    right_inv i := by
      apply Fin.ext
      change ((2 * i.val + 1 : ℕ) : ZMod (2 * h)).val / 2 = i.val
      rw [ZMod.val_natCast_of_lt (by omega)]
      omega }

theorem card_odd_residues (h : ℕ) (hh : 0 < h) :
    Nat.card {c : ZMod (2 * h) // Odd c.val} = h :=
  Nat.card_eq_of_equiv_fin (oddResidueEquiv h hh)

@[expose] def maximalOrderEquiv (k : ℕ) :
    {g : Wreath (2 ^ (k + 1)) // orderOf g = 2 * 2 ^ (k + 1)} ≃
      ZMod (2 ^ (k + 1)) × {c : ZMod (2 ^ (k + 1)) // Odd c.val} where
  toFun g :=
    let c := coordinateEquiv (2 ^ (k + 1)) g.val
    (c.1, ⟨c.1 + c.2.1, by
      have hg : element (2 ^ (k + 1)) c.1 c.2.1 c.2.2 = g.val :=
        (coordinateEquiv _).symm_apply_apply g.val
      have ho := g.property
      rw [← hg] at ho
      exact ((element_maximal_order_iff k c.1 c.2.1 c.2.2).mp ho).2⟩)
  invFun c := ⟨element (2 ^ (k + 1)) c.1 (c.2.val - c.1) 1, by
    apply (element_swap_maximal_order_iff k _ _).mpr
    rw [show c.1 + (c.2.val - c.1) = c.2.val by abel]
    exact c.2.property⟩
  left_inv g := by
    apply Subtype.ext
    let c := coordinateEquiv (2 ^ (k + 1)) g.val
    have hg : element (2 ^ (k + 1)) c.1 c.2.1 c.2.2 = g.val :=
      (coordinateEquiv _).symm_apply_apply g.val
    have ho := g.property
    rw [← hg] at ho
    have he := ((element_maximal_order_iff k c.1 c.2.1 c.2.2).mp ho).1
    change element (2 ^ (k + 1)) c.1 (c.1 + c.2.1 - c.1) 1 = g.val
    rw [add_sub_cancel_left, ← he]
    exact hg
  right_inv c := by
    apply Prod.ext
    · simp [coordinateEquiv, element]
    · apply Subtype.ext
      simp [coordinateEquiv, element]

theorem card_maximal_order (k : ℕ) :
    Nat.card {g : Wreath (2 ^ (k + 1)) // orderOf g = 2 * 2 ^ (k + 1)} =
      2 ^ (k + 1) * 2 ^ k := by
  rw [Nat.card_congr (maximalOrderEquiv k), Nat.card_prod, Nat.card_zmod]
  congr 1
  have hcard := card_odd_residues (2 ^ k) (pow_pos (by decide) k)
  rw [show 2 * 2 ^ k = 2 ^ (k + 1) by rw [pow_succ, Nat.mul_comm]] at hcard
  exact hcard

theorem card_maximal_order_height (n : ℕ) (hn : 1 ≤ n) :
    Nat.card {g : CFSG.Open.WreathedTwoGroup n // orderOf g = 2 * 2 ^ n} =
      (2 ^ n) ^ 2 / 2 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hcard := card_maximal_order k
  change Nat.card {g : Wreath (2 ^ (k + 1)) // orderOf g = 2 * 2 ^ (k + 1)} = _
  rw [hcard]
  rw [pow_succ]
  rw [show (2 ^ k * 2) ^ 2 = (2 ^ k * 2 * 2 ^ k) * 2 by ring]
  exact (Nat.mul_div_cancel (2 ^ k * 2 * 2 ^ k) (by decide)).symm

end CFSG.Wreathed
