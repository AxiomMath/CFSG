
module

public import CFSG.Certificates.Kernel.Th.Spec.SurjWords

@[expose] public section

namespace CFSG.KC.Th.Spec

open CFSG.KC.Th CFSG.KC.Th.BigS CFSG.KC.Th.SurjS CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.Bridge.Th

def regMat (RB : ℕ → ℕ) (l : ℕ × Bool) : Matrix (Fin 248) (Fin 248) (ZMod 2) :=
  pkMat (RB (if l.2 then l.1 + 1 else l.1 + 9))

def wordMatFrom (RB : ℕ → ℕ) (M : Matrix (Fin 248) (Fin 248) (ZMod 2))
    (w : List (ℕ × Bool)) : Matrix (Fin 248) (Fin 248) (ZMod 2) :=
  w.foldl (fun N l => N * regMat RB l) M

def wordMat (RB : ℕ → ℕ) (w : List (ℕ × Bool)) : Matrix (Fin 248) (Fin 248) (ZMod 2) :=
  wordMatFrom RB 1 w

private theorem scAndB {a b : Bool} : andB a b = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> simp [andB]

private theorem scStrictN (y : ℕ) (k : ℕ → ℕ) : CFSG.KC.Loop.strictN y k = k y := by
  cases y <;> rfl

private theorem scRegs (RB : ℕ → ℕ) (c rm ONE : ℕ) : ∀ n : ℕ,
    (Nat.rec (motive := fun _ => Bool) true
      (fun g ih => andB ih (andB (andB (layoutOK c rm (RB (Nat.succ g)))
        (layoutOK c rm (RB (Nat.add g 9))))
        (Nat.beq (mulB c rm (RB (Nat.succ g)) (RB (Nat.add g 9))) ONE))) n) = true →
    ∀ g < n, mulB c rm (RB (g + 1)) (RB (g + 9)) = ONE
  | 0, _, g, hg => absurd hg (Nat.not_lt_zero _)
  | n + 1, h, g, hg => by
    obtain ⟨h1, h2⟩ := scAndB.1 h
    obtain ⟨-, h3⟩ := scAndB.1 h2
    by_cases hgn : g = n
    · subst hgn
      exact Nat.eq_of_beq_eq_true h3
    · exact scRegs RB c rm ONE n h1 g (by omega)

theorem regsOK_mul {RB : ℕ → ℕ} {c rm ONE : ℕ} (h : regsOK RB c rm ONE = true) :
    ∀ g < 8, mulB c rm (RB (g + 1)) (RB (g + 9)) = ONE :=
  scRegs RB c rm ONE 8 h

private theorem scRegGR : ∀ g < 8, regAt GR g = g + 1 := by decide +kernel

private theorem scRegIR : ∀ g < 8, regAt IR g = g + 9 := by decide +kernel

private theorem scLetV {RB : ℕ → ℕ} {x : ℕ} (hx : x / 2 < 8) :
    letV RB GR IR x = RB (if x % 2 = 1 then x / 2 + 9 else x / 2 + 1) := by
  unfold letV
  have e1 : Nat.shiftRight x 1 = x / 2 := Nat.shiftRight_one x
  have e2 : Nat.land x 1 = x % 2 := Nat.and_one_is_mod x
  rw [e1, e2, scRegGR _ hx, scRegIR _ hx]
  rcases Nat.mod_two_eq_zero_or_one x with h | h
  · rw [h]
    rfl
  · rw [h]
    rfl

private theorem scLetMat {RB : ℕ → ℕ} {x : ℕ} (hx : x / 2 < 8) :
    pkMat (letV RB GR IR x) = regMat RB (lettOfCode x) := by
  rw [scLetV hx]
  unfold regMat lettOfCode
  rcases Nat.mod_two_eq_zero_or_one x with h | h
  · simp [h]
  · simp [h]

theorem wordV_spec {RB : ℕ → ℕ} {c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE : ℕ}
    (K : constsOK c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE = true) :
    ∀ (w : List ℕ) (acc : ℕ), (∀ x ∈ w, x / 2 < 8) →
      pkMat (wordV RB c rm w acc) = wordMatFrom RB (pkMat acc) (w.map lettOfCode)
  | [], _, _ => rfl
  | x :: w, acc, hw => by
    have e : wordV RB c rm (x :: w) acc = wordV RB c rm w (mulB c rm acc (letV RB GR IR x)) := by
      show CFSG.KC.Loop.strictN _ _ = _
      rw [scStrictN]
      rfl
    rw [e, wordV_spec K w _ (fun y hy => hw y (by simp [hy])), pkMat_mulB K, List.map_cons]
    unfold wordMatFrom
    rw [List.foldl_cons, scLetMat (hw x (by simp))]

private theorem scLettCode (g : ℕ) (b : Bool) :
    lettOfCode (2 * g + (if b then 0 else 1)) = (g, b) := by
  cases b
  · refine Prod.ext ?_ ?_
    · show (2 * g + 1) / 2 = g
      omega
    · show decide ((2 * g + 1) % 2 = 0) = false
      simp only [decide_eq_false_iff_not]
      omega
  · refine Prod.ext ?_ ?_
    · show (2 * g + 0) / 2 = g
      omega
    · show decide ((2 * g + 0) % 2 = 0) = true
      simp only [decide_eq_true_eq]
      omega

theorem relProd_spec {RB : ℕ → ℕ} {c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE : ℕ}
    (K : constsOK c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE = true) {r : List (ℕ × Bool)}
    {e : ℕ} (hl : ∀ l ∈ r, l.1 < 8) (hn : bitsN e 2 10 = r.length)
    (hb : ∀ i (hi : i < r.length),
      Nat.land (Nat.shiftRight (Nat.shiftRight e 12) (Nat.mul 8 i)) 255 =
        2 * (r[i]'hi).1 + (if (r[i]'hi).2 then 0 else 1)) :
    pkMat (Nat.rec (motive := fun _ => ℕ) ONE (fun i acc => mulB c rm acc (letV RB GR IR
      (Nat.land (Nat.shiftRight (Nat.shiftRight e 12) (Nat.mul 8 i)) 255))) (bitsN e 2 10)) =
      wordMat RB r := by
  rw [hn]
  have key : ∀ n, n ≤ r.length → pkMat (Nat.rec (motive := fun _ => ℕ) ONE (fun i acc =>
      mulB c rm acc (letV RB GR IR
        (Nat.land (Nat.shiftRight (Nat.shiftRight e 12) (Nat.mul 8 i)) 255))) n) =
      wordMatFrom RB 1 (r.take n) := by
    intro n
    induction n with
    | zero =>
      intro _
      exact pkMat_one K
    | succ n ih =>
      intro hn'
      have hlt : n < r.length := by omega
      have hx : (2 * (r[n]'hlt).1 + (if (r[n]'hlt).2 then 0 else 1)) / 2 < 8 := by
        have := hl _ (List.getElem_mem hlt)
        split_ifs <;> omega
      show pkMat (mulB c rm _ _) = _
      rw [pkMat_mulB K, ih (by omega), hb n hlt, scLetMat hx, scLettCode, List.take_succ,
        List.getElem?_eq_getElem hlt]
      simp only [wordMatFrom, List.foldl_append, Option.toList_some, List.foldl_cons,
        List.foldl_nil]
  have h := key r.length le_rfl
  rw [List.take_length] at h
  exact h

end CFSG.KC.Th.Spec

end
