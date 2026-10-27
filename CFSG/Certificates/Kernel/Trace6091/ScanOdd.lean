module

public import CFSG.Certificates.Kernel.Trace6091.XReduce

public section

namespace CFSG.KC.Trace6091

open CFSG.KC CFSG.KC.KDense CFSG.KC.MonsterConv.Perm CFSG.Monster.B Finset

theorem strictZ_eq (y : Nat) (k : Nat → Int) : strictZ y k = k y := by
  cases y <;> rfl

theorem sumZ_eq (g : ℕ → ℤ) : ∀ n, sumZ n g = ∑ i ∈ range n, g i
  | 0 => by
    rw [sum_range_zero]
    rfl
  | n + 1 => by
    rw [sum_range_succ, ← sumZ_eq g n]
    rfl

theorem selZ_true (x : Int) : selZ true x = x := rfl

theorem selZ_false (x : Int) : selZ false x = 0 := rfl

theorem sgnZ_eq (b : Bool) : sgnZ b = Model.sgnI b := by
  cases b <;> rfl

theorem beq_toNat_one (b : Bool) : Nat.beq b.toNat (nat_lit 1) = b := by
  cases b <;> rfl

theorem oddCode_twin (c i : Nat) :
    Nat.xor c (selB (Nat.xor (bitN (wordT c) i) (pW (wordT c))) (nat_lit 63)) =
      Model.oddCode c i := by
  rw [pW_eq, bitN_eq, wordT_eq]
  change c ^^^ selB (((Model.wordN c).testBit i).toNat ^^^ (Model.pN c).toNat) 63 = _
  rw [← toNat_xor, selB_toNat]
  rfl

section Perm

variable {P : Nat} {p : Array Nat}

theorem xTermT_eq (hP : ∀ i < 24, pe P i = p[i]!) (a u : Nat) :
    xTermT P (betaTabT P) a u = xTerm p a u := by
  rw [xTermT, xTerm, permCT_eq hP, permDT_eq hP, kappaT_eq hP, beq_toNat_one, sgnZ_eq,
    beq_eq_decide, beq_eq_decide]
  by_cases h1 : Model.permCN p a = a
  · by_cases h2 : Model.permDN p u = u
    · rw [decide_eq_true h1, decide_eq_true h2, selZ_true, selZ_true, ite_eq_left ⟨h1, h2⟩]
    · rw [decide_eq_true h1, decide_eq_false h2, selZ_true, selZ_false,
        ite_eq_right (fun h => h2 h.2)]
  · rw [decide_eq_false h1, selZ_false, ite_eq_right (fun h => h1 h.1)]

theorem oddRowT_eq (hP : ∀ i < 24, pe P i = p[i]!) (c : Nat) :
    oddRowT P (betaTabT P) c (wordT c) (pW (wordT c)) =
      ∑ i ∈ range 24, xTerm p (Model.oddCode c i) (Model.dualN (2 ^ i)) := by
  unfold oddRowT
  rw [sumZ_eq]
  refine sum_congr rfl fun i _ => ?_
  rw [strictZ_eq, oddCode_twin, xTermT_eq hP, dualT_eq, Nat.shiftLeft_eq', Nat.one_shiftLeft]

theorem oddScanT_eq (hP : ∀ i < 24, pe P i = p[i]!) (t₀ n : Nat) :
    oddScanT P (betaTabT P) t₀ n =
      ∑ j ∈ range n, ∑ i ∈ range 24, xTerm p (Model.oddCode (2 * (t₀ + j)) i) (Model.dualN (2 ^ i)) := by
  unfold oddScanT
  rw [sumZ_eq]
  refine sum_congr rfl fun j _ => ?_
  rw [strictZ_eq, strictZ_eq, strictZ_eq]
  exact oddRowT_eq hP (2 * (t₀ + j))

end Perm

end CFSG.KC.Trace6091

end
