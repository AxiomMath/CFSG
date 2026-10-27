module

public import Certificates.Data.Kernel.LocalQT.Outer
public import CFSG.Certificates.Kernel.LocalQTWordSound
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1PermCheck

public section

namespace CFSG.KC.LQT.W

open Equiv CFSG.QuasithinUnique.Setup.X1

theorem letZ_codeP {n : ℕ} (hn : n ≤ 32) (L : List (Perm (Fin n))) (z : ℤ) :
    letZ n (L.map codeP) z = P.code (if 0 < z then L.getD (z.toNat - 1) 1
      else (L.getD ((-z).toNat - 1) 1)⁻¹) := by
  rcases z with (_ | k) | k
  · change P.inv n (genAt n (L.map codeP) 0) = _
    rw [genAt_map, P.code_inv hn]
    rfl
  · change genAt n (L.map codeP) k = _
    rw [genAt_map]
    congr 1
    have h0 : (0 : ℤ) < Int.ofNat (k + 1) := Int.ofNat_lt.2 (Nat.succ_pos k)
    rw [ite_eq_left h0]
    simp
  · change P.inv n (genAt n (L.map codeP) k) = _
    rw [genAt_map, P.code_inv hn]
    congr 1

theorem evalZK_codeP {n : ℕ} (hn : n ≤ 32) (L : List (Perm (Fin n))) (w : List ℤ) :
    evalZK n (L.map codeP) w = codeP (evalG L w) := by
  induction w with
  | nil => exact P.code_one
  | cons z w ih =>
    change P.mul n (letZ n (L.map codeP) z) (evalZK n (L.map codeP) w) = _
    rw [ih, evalG, letZ_codeP hn]
    exact P.code_mul hn _ _

theorem coe_evalG {n : ℕ} (H : Subgroup (Perm (Fin n))) (gs : List H) (w : List ℤ) :
    ((evalG gs w : H) : Perm (Fin n)) = evalG (gs.map Subtype.val) w := by
  have hg : ∀ i, ((gs.getD i 1 : H) : Perm (Fin n)) = (gs.map Subtype.val).getD i 1 := by
    intro i
    rw [← H.coe_one, List.getD_map]
  induction w with
  | nil => rfl
  | cons z w ih =>
    rw [evalG, evalG, Subgroup.coe_mul, ih]
    split_ifs
    · rw [hg]
    · rw [Subgroup.coe_inv, hg]

end CFSG.KC.LQT.W

end
