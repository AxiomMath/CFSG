module

import CFSG.Certificates.Kernel.Spor.RawOrbEval
public import Certificates.Data.Kernel.Spor.BaseMask
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.KS.BaseMask

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.PEnum

theorem testBit_foldr_lor (f : Nat → Nat) (L : List Nat) (s q : Nat) :
    (L.foldr (fun e M => Nat.lor M (Nat.shiftLeft 1 (f e))) s).testBit q = true ↔
      s.testBit q = true ∨ ∃ e ∈ L, f e = q := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.foldr_cons]
    have e1 : Nat.lor (L.foldr (fun e M => Nat.lor M (Nat.shiftLeft 1 (f e))) s)
        (Nat.shiftLeft 1 (f a)) =
        (L.foldr (fun e M => Nat.lor M (Nat.shiftLeft 1 (f e))) s) ||| 2 ^ f a := by
      rw [← Nat.one_shiftLeft]
      rfl
    rw [e1, Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true, ih, decide_eq_true_iff]
    constructor
    · rintro ((hs | ⟨e, he, rfl⟩) | rfl)
      · exact Or.inl hs
      · exact Or.inr ⟨e, List.mem_cons_of_mem _ he, rfl⟩
      · exact Or.inr ⟨a, List.mem_cons_self, rfl⟩
    · rintro (hs | ⟨e, he, rfl⟩)
      · exact Or.inl (Or.inl hs)
      · rcases List.mem_cons.1 he with rfl | he
        · exact Or.inr rfl
        · exact Or.inl (Or.inr ⟨e, he, rfl⟩)

theorem hasBit_maskK (I : Nat → Nat) (o len q : Nat) :
    hasBit (maskK I o len) q = true ↔ ∃ e < len, r32 I (o + e) = q := by
  rw [CFSG.KS.Raw.Orb.hasBit_eq]
  unfold maskK
  rw [CFSG.KS.Raw.Orb.foldN_eq]
  refine (testBit_foldr_lor (fun e => r32 I (o + e)) (List.range len) 0 q).trans ?_
  simp [List.mem_range]

theorem idx_iff_of_maskK_eq {I J : Nat → Nat} {o o' len len' : Nat}
    (h : maskK I o len = maskK J o' len') (q : Nat) :
    (∃ e < len, r32 I (o + e) = q) ↔ ∃ e < len', r32 J (o' + e) = q := by
  rw [← hasBit_maskK, ← hasBit_maskK, h]

theorem mulKeyK_of {w m b c : Nat} {T : Nat → Nat} {i j q : Nat}
    (h1 : pg w m (T i) (pg w m (T j) b) = pg w m (T q) b)
    (h2 : pg w m (T i) (pg w m (T j) c) = pg w m (T q) c) :
    mulKeyK w m b c T i j q = true := by
  unfold mulKeyK
  rw [CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true, h1, h2]
  exact ⟨Nat.beq_refl _, Nat.beq_refl _⟩

theorem commKeyK_of {w m b c : Nat} {T : Nat → Nat} {s g : Nat}
    (h1 : pg w m (T s) (pg w m (T g) b) = pg w m (T g) (pg w m (T s) b))
    (h2 : pg w m (T s) (pg w m (T g) c) = pg w m (T g) (pg w m (T s) c)) :
    commKeyK w m b c T s g = true := by
  unfold commKeyK
  rw [CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true, h1, h2]
  exact ⟨Nat.beq_refl _, Nat.beq_refl _⟩

theorem penumSl_spec {n w m nw k cnt lo len : Nat} {conj : Bool}
    {G GI T PL POS SRT SRI : Nat → Nat}
    (h : penumSlK n w m nw conj G GI k cnt T PL POS SRT SRI lo len = true) {i : Nat}
    (h1 : lo ≤ i) (h2 : i < lo + len) (hi : i < cnt) :
    penumPtK n w m nw conj G GI k cnt T PL POS SRT SRI i = true := by
  unfold penumSlK at h
  have h' := CFSG.KS.Raw.Orb.allN_iff.1 h (i - lo) (by omega)
  rw [CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.bIf_eq] at h'
  have e : Nat.add lo (i - lo) = i := by
    change lo + (i - lo) = i
    omega
  rw [e, if_pos (Nat.blt_eq.mpr hi)] at h'
  exact h'

end CFSG.KS.BaseMask

end
