module

public import CFSG.Certificates.Kernel.SmithL6KWedge
public import CFSG.Certificates.Kernel.SmithL6CollSound
public import Certificates.Data.Kernel.SmithL6KF
public import Certificates.Data.SmithL6Facts

public section

namespace CFSG.SmithL6.K

open CFSG.SmithL6 CFSG.SmithL6.CollK CFSG.SmithL6.Kernel
open CFSG.SmithE (applyCols)

theorem apK_xor (l : List Nat) (a b : Nat) : apK l (a ^^^ b) = apK l a ^^^ apK l b := by
  rw [← applyCols_toArray, applyCols_xorL, applyCols_toArray, applyCols_toArray]

theorem xor_xor_xor (a b c d : Nat) : a ^^^ b ^^^ (c ^^^ d) = a ^^^ c ^^^ (b ^^^ d) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_xor]
  cases a.testBit i <;> cases b.testBit i <;> cases c.testBit i <;> cases d.testBit i <;> rfl

theorem killK_sound {F T : List Nat} {cols : Array Nat} (hT : cols.toList = T)
    (hs : cols.size = 20) (h : killK F T = true) :
    ∀ c < 2 ^ 20, apK F (applyCols cols c ^^^ c) = 0 := by
  refine xorAdd_ext (F := fun c => apK F (applyCols cols c ^^^ c)) (G := fun _ => 0)
    (fun a b => ?_) (fun _ _ => (Nat.xor_self 0).symm) 20 (fun m hm => ?_)
  · rw [applyCols_xorL, xor_xor_xor, apK_xor]
  · simp only [killK, List.all_eq_true, List.mem_range, beq_iff_eq] at h
    rw [applyCols_powL _ (by rw [hs]; exact hm), get0, hT]
    exact h m hm

theorem mfPairKind_eq {k l : Nat} (hk : k < 1953) (hl : l < 1953) :
    mfPairKind k l = kindC (codeOf (tvPair k)) (codeOf (tvPair l)) := by
  unfold mfPairKind kindC
  rw [codeOf_div (tvP_tvPair hk), codeOf_mod (tvP_tvPair hk), codeOf_div (tvP_tvPair hl),
    codeOf_mod (tvP_tvPair hl)]

theorem e4fApplyWord_append (u v : List Nat) (x : Nat) :
    e4fApplyWord (u ++ v) x = e4fApplyWord u (e4fApplyWord v x) := by
  induction u with
  | nil => rfl
  | cons r u ih => simp only [List.cons_append, e4fApplyWord, ih]

theorem wordK_eq {L : List (List Nat)} (hL : ∀ r < 1953, (tvCols r).toList = L.getD r [])
    {w : List Nat} (hw : ∀ r ∈ w, r < 1953) (x : Nat) : wordK L w x = e4fApplyWord w x := by
  induction w with
  | nil => rfl
  | cons r w ih =>
    simp only [wordK, e4fApplyWord]
    rw [ih fun r' h => hw r' (List.mem_cons_of_mem _ h), ← hL r (hw r List.mem_cons_self),
      ← applyCols_toArray, Array.toArray_toList]

end CFSG.SmithL6.K
