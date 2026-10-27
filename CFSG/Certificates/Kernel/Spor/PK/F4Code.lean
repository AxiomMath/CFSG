module

public import Certificates.Data.Kernel.Misc.T46
public import Certificates.Data.CFSGNative.F4.Unitary

public section

namespace CFSG.KS.PK

open CFSG.KC.Misc.T46 CFSG.F4.Native

private theorem letN_val (y : Nat) (k : Nat → Nat) : CFSG.KC.Misc.letN y k = k y := by
  cases y <;> rfl

private theorem recN6_eq (z : Nat) (g : Nat → Nat → Nat) :
    Nat.rec (motive := fun _ => Nat) z (fun i acc => g acc i) 6 = (List.range 6).foldl g z := rfl

private theorem range6 : List.range 6 = [0, 1, 2, 3, 4, 5] := rfl

theorem f4K_eq (x y : Nat) : f4K x y = f4mul x y := rfl

theorem crdK_eq (c i : Nat) : crdK c i = coord c i := rfl

theorem hermK_eq (c d : Nat) : hermK c d = hermC c d := by
  refine (recN6_eq 0 (fun acc i => Nat.xor acc
    (f4K (crdK c i) (CFSG.KC.Misc.letN (crdK d i) fun e => f4K e e)))).trans ?_
  unfold hermC
  simp only [crdK_eq, f4K_eq, letN_val]
  rfl

theorem scaleK_eq (a c : Nat) : scaleK a c = scaleC a c := by
  refine (recN6_eq 0 (fun acc i => Nat.add acc (Nat.mul (f4K a (crdK c i)) (Nat.pow 4 i)))).trans ?_
  unfold scaleC
  simp only [crdK_eq, f4K_eq]
  rfl

private theorem step_eq (a acc : Nat) :
    Bool.rec (motive := fun _ => Nat) a acc (Nat.beq a 0) = if a != 0 then a else acc := by
  cases a <;> rfl

theorem leadK_eq (c : Nat) : leadK c = leadC c := by
  refine (recN6_eq 0 (fun acc j => CFSG.KC.Misc.letN (crdK c (Nat.sub 5 j))
    fun e => Bool.rec (motive := fun _ => Nat) e acc (Nat.beq e 0))).trans ?_
  unfold leadC
  rw [range6]
  simp only [List.foldl_cons, List.foldl_nil, List.foldr_cons, List.foldr_nil, letN_val,
    crdK_eq, step_eq]

theorem normK_eq (c : Nat) : normK c = normC c := by
  unfold normK normC
  simp only [letN_val, scaleK_eq, f4K_eq, leadK_eq]

theorem tvK_eq (v x : Nat) : tvK v x = tvC v x := by
  unfold tvK tvC addC
  simp only [scaleK_eq, hermK_eq]
  rfl

private theorem bool_one_zero (x : Nat) :
    Bool.rec (motive := fun _ => Nat) 1 0 (Nat.beq x 0) = if x != 0 then 1 else 0 := by
  cases x <;> rfl

private theorem count_foldl (c : Nat) (l : List Nat) (acc : Nat) :
    l.foldl (fun acc i => acc + Bool.rec (motive := fun _ => Nat) 1 0 (Nat.beq (coord c i) 0)) acc
      = acc + (l.filter fun i => coord c i != 0).length := by
  induction l generalizing acc with
  | nil => simp
  | cons a l ih =>
    rw [List.foldl_cons, ih, List.filter_cons, bool_one_zero]
    by_cases h : coord c a != 0
    · simp only [if_pos h, List.length_cons]; omega
    · simp only [if_neg h]; omega

theorem weightK_eq (c : Nat) : weightK c = weightC c := by
  refine (recN6_eq 0 (fun acc i => Nat.add acc
    (Bool.rec (motive := fun _ => Nat) 1 0 (Nat.beq (crdK c i) 0)))).trans ?_
  simp only [crdK_eq]
  unfold weightC
  exact (count_foldl c (List.range 6) 0).trans (Nat.zero_add _)

theorem gensK_eq (l : List Nat) : gensK l = l.filter (fun c => weightC c == 2) ++ [85] := by
  induction l with
  | nil => rfl
  | cons c l ih =>
    have hw : Nat.beq (weightK c) 2 = (weightC c == 2) := by
      rw [weightK_eq]
      exact Bool.eq_iff_iff.mpr (by simp)
    show Bool.rec (motive := fun _ => List Nat) (gensK l) (c :: gensK l)
      (Nat.beq (weightK c) 2) = _
    rw [hw, ih]
    by_cases h : weightC c == 2 <;> simp [h, List.filter_cons]

end CFSG.KS.PK

end
