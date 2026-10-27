module

public import CFSG.Certificates.Kernel.LocalQTR9CodeSound
public import CFSG.Certificates.Kernel.LocalQTSmallSound

public section

namespace CFSG.KC.LQT.R

open CFSG.QuasithinUnique.Unc25K1 CFSG.KC.Ord

theorem rmul_assoc (x y z : R9) : rmul (rmul x y) z = rmul x (rmul y z) := by
  simp only [rmul, R9.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ring

theorem rmul_one (x : R9) : rmul x rone = x := by
  obtain ⟨a, b, c, d, e, f, g, h, i⟩ := x
  simp [rmul, rone]

theorem one_rmul (x : R9) : rmul rone x = x := by
  obtain ⟨a, b, c, d, e, f, g, h, i⟩ := x
  simp [rmul, rone]

@[expose] def tr (x : R9) : R9 := ⟨x.a, x.d, x.g, x.b, x.e, x.h, x.c, x.f, x.i⟩

@[expose] def adj (x : R9) : R9 := tr (rcof x)

theorem tr_rcof (x : R9) : tr (rcof x) = adj x := rfl

theorem mul_adj {x : R9} (hx : rdet x = 1) : rmul x (adj x) = rone := by
  obtain ⟨a, b, c, d, e, f, g, h, i⟩ := x
  simp only [rdet] at hx
  simp only [rmul, adj, tr, rcof, rone, R9.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first | linear_combination hx | linear_combination (0 : ZMod 3) * hx

theorem adj_mul {x : R9} (hx : rdet x = 1) : rmul (adj x) x = rone := by
  obtain ⟨a, b, c, d, e, f, g, h, i⟩ := x
  simp only [rdet] at hx
  simp only [rmul, adj, tr, rcof, rone, R9.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first | linear_combination hx | linear_combination (0 : ZMod 3) * hx

theorem conj_iff {g : R9} (hg : rdet g = 1) (x y : R9) :
    rmul (rmul g x) (adj g) = y ↔ rmul g x = rmul y g := by
  constructor
  · rintro rfl
    rw [rmul_assoc, adj_mul hg, rmul_one]
  · intro h
    rw [h, rmul_assoc, mul_adj hg, rmul_one]

theorem transK_eq (x : ℕ) : transK x = ent x 0 + ent x 3 * 4 + ent x 6 * 16 + ent x 1 * 64 +
    ent x 4 * 256 + ent x 7 * 1024 + ent x 2 * 4096 + ent x 5 * 16384 + ent x 8 * 65536 := by
  rw [transK, mk9_eq]

theorem transK_codeR (x : R9) : transK (codeR x) = codeR (tr x) := by
  rw [transK_eq]
  simp only [ent0, ent1, ent2, ent3, ent4, ent5, ent6, ent7, ent8]
  rfl

theorem transK_cofK (x : R9) : transK (cofK (codeR x)) = codeR (adj x) := by
  rw [cofK_codeR, transK_codeR]
  rfl

theorem conjK_codeR (g x : R9) : conjK (codeR g) (codeR x) = codeR (rmul (rmul g x) (adj g)) := by
  rw [conjK, transK_cofK, mulK_codeR, mulK_codeR]

theorem rdet_one : rdet rone = 1 := by decide

theorem detK_eq_one (x : R9) : detK (codeR x) = 1 ↔ rdet x = 1 := by
  rw [detK_codeR]
  exact ⟨fun h => ZMod.val_injective 3 (h.trans (by decide)), fun h => by rw [h]; decide⟩

theorem invoK_eq (x : R9) : invoK (codeR x) = (x != rone && rmul x x == rone) := by
  rw [Bool.eq_iff_iff, invoK_codeR]
  simp

theorem filterL_mapR (L : List R9) (f : ℕ → Bool) :
    filterL (L.map codeR) f = (L.filter fun x => f (codeR x)).map codeR := by
  induction L with
  | nil => rfl
  | cons x L ih =>
    change Bool.rec (motive := fun _ => List ℕ) (filterL (L.map codeR) f)
      (codeR x :: filterL (L.map codeR) f) (f (codeR x)) = _
    rw [ih, List.filter_cons]
    cases f (codeR x) <;> rfl

theorem eqL_iff : ∀ l m : List ℕ, eqL l m = true ↔ l = m
  | [], [] => by simp [eqL]
  | [], _ :: _ => by simp [eqL]
  | _ :: _, [] => by simp [eqL]
  | x :: l, y :: m => by
    change andB (Nat.beq x y) (eqL l m) = true ↔ _
    rw [P.andB_iff, P.beq_iff, eqL_iff l m, List.cons.injEq]

theorem getL_eq : ∀ (l : List ℕ) (i : ℕ), getL l i = l.getD i 0
  | [], _ => rfl
  | x :: l, 0 => rfl
  | x :: l, i + 1 => by
    change Bool.rec (motive := fun _ => ℕ) (getL l (Nat.sub (i + 1) 1)) x (Nat.beq (i + 1) 0) = _
    rw [show Nat.beq (i + 1) 0 = false from rfl, show Nat.sub (i + 1) 1 = i from rfl, getL_eq l i]
    rfl

theorem getL_mapR (L : List R9) {i : ℕ} (hi : i < L.length) :
    getL (L.map codeR) i = codeR L[i] := by
  rw [getL_eq, List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map]

theorem distinctL_mapR (L : List R9) : S.distinctL (L.map codeR) = true ↔ L.Nodup := by
  induction L with
  | nil => simp [S.distinctL]
  | cons g L ih =>
    change andB (notB (S.memL (codeR g) (L.map codeR))) (S.distinctL (L.map codeR)) = true ↔ _
    rw [P.andB_iff, P.notB_iff, S.memL_iff, mem_mapR, ih, List.nodup_cons]

def mN (f : ℕ → Bool) : List ℕ → ℕ
  | [] => 0
  | x :: l => (if f x then 1 else 0) + 2 * mN f l

theorem maskRec_eq (f : ℕ → Bool) (l : List ℕ) : ∀ i0 : ℕ,
    List.rec (motive := fun _ => ℕ → ℕ) (fun _ => 0)
      (fun x _ ih i => Nat.add (Bool.rec (motive := fun _ => ℕ) 0 (Nat.shiftLeft 1 i) (f x))
        (ih (Nat.succ i))) l i0 = 2 ^ i0 * mN f l := by
  induction l with
  | nil => intro i0; simp [mN]
  | cons x l ih =>
    intro i0
    change Nat.add (Bool.rec (motive := fun _ => ℕ) 0 (Nat.shiftLeft 1 i0) (f x))
      (List.rec (motive := fun _ => ℕ → ℕ) (fun _ => 0)
      (fun x _ ih i => Nat.add (Bool.rec (motive := fun _ => ℕ) 0 (Nat.shiftLeft 1 i) (f x))
        (ih (Nat.succ i))) l (Nat.succ i0)) = _
    rw [ih]
    cases h : f x <;> simp [mN, h, Nat.shiftLeft_eq, pow_succ] <;> ring

theorem testBit_mN (f : ℕ → Bool) : ∀ (l : List ℕ) (i : ℕ), i < l.length →
    f (l.getD i 0) = true → (mN f l).testBit i = true
  | [], _, h, _ => absurd h (by simp)
  | x :: l, 0, _, hf => by
    simp only [List.getD_cons_zero] at hf
    simp only [mN, hf, ite_true, Nat.testBit_zero]
    simp
  | x :: l, i + 1, hi, hf => by
    simp only [List.getD_cons_succ] at hf
    rw [mN, Nat.testBit_succ]
    have e : ((if f x = true then 1 else 0) + 2 * mN f l) / 2 = mN f l := by
      split_ifs <;> omega
    rw [e]
    exact testBit_mN f l i (by simpa using hi) hf

theorem bit_maskL (l : List ℕ) (f : ℕ → Bool) {i : ℕ} (hi : i < l.length)
    (hf : f (getL l i) = true) : Nat.blt 0 (Nat.land (maskL l f) (Nat.shiftLeft 1 i)) = true := by
  rw [P.bit_eq, maskL, maskRec_eq, pow_zero, one_mul]
  rw [getL_eq] at hf
  exact testBit_mN f l i hi hf

end CFSG.KC.LQT.R

end
