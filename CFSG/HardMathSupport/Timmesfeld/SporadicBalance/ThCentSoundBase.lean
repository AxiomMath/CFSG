
module

public import Certificates.Data.CFSGNative.Timmesfeld.ThCent
public import CFSG.Assembly.Defs
public import CFSG.Sporadic.Th.ChainBase

@[expose] public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThCent

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open scoped Matrix Pointwise

theorem wordG_cons {G : Type*} [Group G] (gens : ℤ → G) (l : ℤ) (w : List ℤ) :
    wordG gens (l :: w) = gens l * wordG gens w := by
  simp only [wordG, List.map_cons, List.prod_cons]

theorem rowsMatrix_powRowsN (M : Array V4) (e : ℕ) :
    rowsMatrix (powRowsN M e) = rowsMatrix M ^ e := by
  induction e with
  | zero => rw [pow_zero]; exact rowsMatrix_idRows
  | succ e ih => rw [powRowsN, rowsMatrix_mulRows, ih, pow_succ]

theorem freshTable_eq (t : Array V4) : freshTable t = t := by
  unfold freshTable
  simp [V4.xor_self, V4.xor_zero]

theorem applyTreeInv2_eq (pl P₁ P₂ : Table) :
    ∀ k q, applyTreeInv2 pl P₁ P₂ k q = applyTreeInv pl (letters P₁ P₂) k q := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro q
    rw [applyTreeInv2.eq_def, applyTreeInv.eq_def]
    by_cases h : 0 < k ∧ treePar (pl[k]!).toNat < k
    · rw [dite_eq_left h, dite_eq_left h]
      by_cases hl : treeLab (pl[k]!).toNat = 1
      · rw [ite_eq_left hl, ih _ h.2]
        simp only [letters, hl, ite_true]
      · rw [ite_eq_right hl, ih _ h.2]
        simp only [letters, hl, ite_false]
    · rw [dite_eq_right h, dite_eq_right h]

theorem triple_get (x y v : ℕ) : (#[x, y, v] : Array ℕ)[0]! = x ∧ (#[x, y, v] : Array ℕ)[1]! = y ∧
    (#[x, y, v] : Array ℕ)[2]! = v := ⟨rfl, rfl, rfl⟩

section Facts

variable {c' : ℕ} (hC : CertFacts c')
include hC

end Facts

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThCent
