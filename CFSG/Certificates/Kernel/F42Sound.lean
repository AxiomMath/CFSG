module

public import Certificates.Data.Kernel.F42Pc
public import CFSG.LocalAnalysis.EvenSmallLie.FFourTwo.NativeInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KC.F42

open CFSG.KC.Enum CFSG.EvenSmallLie.FFourTwo

theorem strictN_eq (y : ℕ) (k : ℕ → ℕ) : strictN y k = k y := by cases y <;> rfl

theorem lowK_eq (m : ℕ) : lowK m = Pc.lowIdx m := rfl

theorem dropK_eq (m : ℕ) : dropK m = Pc.dropLow m := rfl

theorem mwLoop_eq {cm : ℕ → ℕ → ℕ} {f : ℕ} {g : ℕ → ℕ → ℕ} (hg : ∀ E i, g E i = Pc.mg cm f E i) :
    ∀ fu E w, w ≤ fu → mwLoop g fu E w = Pc.mw cm f E w := by
  intro fu
  induction fu with
  | zero =>
    intro E w hw
    obtain rfl : w = 0 := by omega
    rw [Pc.mw_zero]
    rfl
  | succ fu ih =>
    intro E w hw
    by_cases h0 : w = 0
    · subst h0
      rw [Pc.mw_zero]
      rfl
    · have hb : Nat.beq w 0 = false := beq_false_of_ne h0
      have hd : Pc.dropLow w ≤ fu := by have := Pc.dropLow_lt h0; omega
      change Bool.rec (motive := fun _ => ℕ)
        (strictN (g E (lowK w)) fun E' => mwLoop g fu E' (dropK w)) E (Nat.beq w 0) = _
      rw [hb, Pc.mw_of_ne _ _ _ h0]
      change strictN (g E (lowK w)) (fun E' => mwLoop g fu E' (dropK w)) = _
      rw [strictN_eq, hg, lowK_eq, dropK_eq, ih _ _ hd]

theorem mwR_eq {cm : ℕ → ℕ → ℕ} {f : ℕ} {g : ℕ → ℕ → ℕ} (hg : ∀ E i, g E i = Pc.mg cm f E i)
    (E w : ℕ) : mwR g E w = Pc.mw cm f E w :=
  mwLoop_eq hg w E w le_rfl

theorem tlLoop_eq {cm : ℕ → ℕ → ℕ} {f : ℕ} {g : ℕ → ℕ → ℕ} (hg : ∀ E i, g E i = Pc.mg cm f E i)
    (i : ℕ) : ∀ fu r t, t ≤ fu → tlLoop cm g i fu r t = Pc.tl cm f i r t := by
  intro fu
  induction fu with
  | zero =>
    intro r t ht
    obtain rfl : t = 0 := by omega
    rw [Pc.tl_zero]
    rfl
  | succ fu ih =>
    intro r t ht
    by_cases h0 : t = 0
    · subst h0
      rw [Pc.tl_zero]
      rfl
    · have hb : Nat.beq t 0 = false := beq_false_of_ne h0
      have hd : Pc.dropLow t ≤ fu := by have := Pc.dropLow_lt h0; omega
      change Bool.rec (motive := fun _ => ℕ)
        (strictN (mwR g (g r (lowK t)) (cm (lowK t) i)) fun r' => tlLoop cm g i fu r' (dropK t))
        r (Nat.beq t 0) = _
      rw [hb, Pc.tl_of_ne _ _ _ _ h0]
      change strictN (mwR g (g r (lowK t)) (cm (lowK t) i))
        (fun r' => tlLoop cm g i fu r' (dropK t)) = _
      rw [strictN_eq, mwR_eq hg, hg, lowK_eq, dropK_eq, ih _ _ hd]

theorem mgR_eq (cm : ℕ → ℕ → ℕ) : ∀ f E i, mgR cm f E i = Pc.mg cm f E i := by
  intro f
  induction f with
  | zero => intro E i; rw [Pc.mg_zero]; rfl
  | succ f ih =>
    intro E i
    rw [Pc.mg_succ]
    exact tlLoop_eq ih i _ _ _ le_rfl

theorem invLoop_eq (cm : ℕ → ℕ → ℕ) (n : ℕ) :
    ∀ fu E, E ≤ fu → invLoop cm n fu E = Pc.inv cm n E := by
  intro fu
  induction fu with
  | zero =>
    intro E hE
    obtain rfl : E = 0 := by omega
    rw [Pc.inv]
    rfl
  | succ fu ih =>
    intro E hE
    by_cases h0 : E = 0
    · subst h0
      rw [Pc.inv]
      rfl
    · have hb : Nat.beq E 0 = false := beq_false_of_ne h0
      have hd : Pc.dropLow E ≤ fu := by have := Pc.dropLow_lt h0; omega
      change Bool.rec (motive := fun _ => ℕ)
        (strictN (invLoop cm n fu (dropK E)) fun x => mgR cm n x (lowK E)) 0 (Nat.beq E 0) = _
      rw [hb, Pc.inv]
      change strictN (invLoop cm n fu (dropK E)) (fun x => mgR cm n x (lowK E)) = _
      simp only [h0, ↓reduceDIte]
      rw [strictN_eq, mgR_eq, dropK_eq, lowK_eq, ih _ hd]

theorem invG_eq (cm : ℕ → ℕ → ℕ) (n E : ℕ) : invG cm n E = Pc.inv cm n E :=
  invLoop_eq cm n E E le_rfl

theorem cmP_fields : (List.range 625).all
    (fun k => Nat.beq (Nat.land (Nat.shiftRight cmP (25 * k)) 33554431) (cmTab.getD k 0)) = true := by
  decide +kernel

theorem cmP_blt : Nat.blt cmP (Nat.pow 2 (Nat.mul 25 625)) = true := by quickRfl

set_option exponentiation.threshold 20000 in
theorem cmP_lt : cmP < 2 ^ (25 * 625) := Nat.blt_eq ▸ cmP_blt

set_option exponentiation.threshold 20000 in
theorem cmK_eq (j i : ℕ) : cmK j i = cmF j i := by
  change Nat.land (Nat.shiftRight cmP (25 * (25 * j + i))) 33554431 = cmTab.getD (25 * j + i) 0
  generalize 25 * j + i = k
  by_cases hk : k < 625
  · have h := List.all_eq_true.1 cmP_fields k (List.mem_range.2 hk)
    exact Nat.eq_of_beq_eq_true h
  · have h1 : cmTab.getD k 0 = 0 := by
      have hs : cmTab.size = 625 := by decide +kernel
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]
      rfl
    have h2 : Nat.shiftRight cmP (25 * k) = 0 := by
      change cmP >>> (25 * k) = 0
      rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt]
      exact cmP_lt.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [h1, h2]
    rfl

theorem cmK_eq_cmF : cmK = cmF := funext fun j => funext fun i => cmK_eq j i

theorem mulR_eq (E F : ℕ) : mulR E F = mulU E F := by
  rw [mulR, mwR_eq (mgR_eq cmK 25), cmK_eq_cmF]
  rfl

end CFSG.KC.F42

end
