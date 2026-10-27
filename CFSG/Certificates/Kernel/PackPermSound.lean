module

public import Certificates.Data.Kernel.PackPerm
public import CFSG.Certificates.Kernel.Spor.PK.PermOf
public import CFSG.CGT.T75JM.N6Words
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.KC.PackPerm

open CFSG.KS.PK CFSG.CGT.T75JM

private theorem band_eq_true {a b : Bool} :
    Bool.rec (motive := fun _ => Bool) false b a = true ↔ a = true ∧ b = true := by
  cases a <;> simp

private theorem bnot_eq_true {a : Bool} :
    Bool.rec (motive := fun _ => Bool) true false a = true ↔ a = false := by
  cases a <;> simp

private theorem pack8_cons (x : Nat) (l : List Nat) (hx : x < 256) :
    pack8 (x :: l) = 256 * pack8 l + x := by
  change x ||| pack8 l <<< 8 = _
  rw [Nat.lor_comm, ← Nat.shiftLeft_add_eq_or_of_lt (by simpa using hx), Nat.shiftLeft_eq]
  ring

private theorem pget_eq (P i : Nat) : pget P i = P / 256 ^ i % 256 := by
  change (P >>> (8 * i)) &&& (2 ^ 8 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, pow_mul]
  rfl

theorem pget_pack8 (l : List Nat) (hl : ∀ y ∈ l, y < 256) (i : Nat) :
    pget (pack8 l) i = l.getD i 0 := by
  induction l generalizing i with
  | nil =>
    rw [pget_eq]
    simp [pack8]
  | cons x l ih =>
    have hx : x < 256 := hl x (by simp)
    have ih' := ih (fun y hy => hl y (by simp [hy]))
    rw [pget_eq, pack8_cons x l hx]
    cases i with
    | zero =>
      simp only [pow_zero, Nat.div_one, List.getD_cons_zero]
      omega
    | succ i =>
      rw [List.getD_cons_succ, ← ih' i, pget_eq, pow_succ', ← Nat.div_div_eq_div_mul]
      congr 2
      omega

private theorem allLt_eq_true {n : Nat} {f : Nat → Bool} :
    allLt n f = true ↔ ∀ i < n, f i = true := by
  induction n with
  | zero => simp [allLt]
  | succ n ih =>
    change Bool.rec (motive := fun _ => Bool) false (allLt n f) (f n) = true ↔ _
    rw [band_eq_true, ih]
    refine ⟨fun ⟨h1, h2⟩ i hi => ?_, fun h => ⟨h n (by omega), fun i hi => h i (by omega)⟩⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    exacts [h2 i hi, h1]

private theorem entriesLt_eq_true {d : Nat} {l : List Nat} :
    entriesLt d l = true ↔ ∀ y ∈ l, y < d := by
  induction l with
  | nil => simp [entriesLt]
  | cons x l ih =>
    change Bool.rec (motive := fun _ => Bool) false (entriesLt d l) (Nat.blt x d) = true ↔ _
    rw [band_eq_true, ih]
    simp [Nat.blt_eq]

private theorem listAll_eq_true {α : Type} {p : α → Bool} {l : List α} :
    List.rec (motive := fun _ => Bool) true (fun e _ ih => Bool.rec (motive := fun _ => Bool)
      false ih (p e)) l = true ↔ ∀ e ∈ l, p e = true := by
  induction l with
  | nil => simp
  | cons x l ih =>
    change Bool.rec (motive := fun _ => Bool) false _ (p x) = true ↔ _
    rw [band_eq_true, ih]
    simp

private theorem tabOk_sound {d : Nat} {l : List Nat} (hd : d ≤ 256)
    (h : tabOk d l (pack8 l) = true) :
    IsPermN d (fun x => l.getD x x) ∧ ∀ x < d, pget (pack8 l) x = l.getD x x := by
  change Bool.rec (motive := fun _ => Bool) false
    (Bool.rec (motive := fun _ => Bool) false _ (entriesLt d l)) (Nat.beq l.length d) = true at h
  rw [band_eq_true, band_eq_true, Nat.beq_eq, entriesLt_eq_true] at h
  obtain ⟨hlen, hlt, hinj⟩ := h
  have hget : ∀ x < d, pget (pack8 l) x = l.getD x x := by
    intro x hx
    rw [pget_pack8 l (fun y hy => by have := hlt y hy; omega)]
    simp [List.getD, hlen ▸ hx]
  have hinj' : ∀ x < d, ∀ y < x, pget (pack8 l) x ≠ pget (pack8 l) y := by
    intro x hx y hy hxy
    have := (allLt_eq_true.1 ((allLt_eq_true.1 hinj) x hx)) y hy
    rw [bnot_eq_true, hxy] at this
    simp at this
  refine ⟨⟨fun x hx => ?_, fun x hx y hy hxy => ?_⟩, hget⟩
  · exact hlt _ (by simp [List.getD, hlen ▸ hx])
  · dsimp only at hxy
    rw [← hget x hx, ← hget y hy] at hxy
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h1 | h1
    · exact hinj' y hy x h1 hxy.symm
    · exact hinj' x hx y h1 hxy

private theorem wimg_eq {d : Nat} {l₀ l₁ : List Nat} {P₀ P₁ : Nat}
    (h₀ : IsPermN d (fun x => l₀.getD x x) ∧ ∀ x < d, pget P₀ x = l₀.getD x x)
    (h₁ : IsPermN d (fun x => l₁.getD x x) ∧ ∀ x < d, pget P₁ x = l₁.getD x x) (w : List Nat)
    (x : Fin d) :
    ((evalG (permOf d fun x => l₀.getD x x) (permOf d fun x => l₁.getD x x) w x : Fin d) : Nat) =
      wimg P₀ P₁ w x := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    change _ = pget (Bool.rec (motive := fun _ => Nat) P₁ P₀ (Nat.beq i 0)) (wimg P₀ P₁ w x)
    rw [evalG, Equiv.Perm.mul_apply, ← ih]
    rcases i with _ | i
    · exact (permOf_apply h₀.1 _).trans (h₀.2 _ (Fin.isLt _)).symm
    · exact (permOf_apply h₁.1 _).trans (h₁.2 _ (Fin.isLt _)).symm

theorem relCheck_sound {d : Nat} {l₀ l₁ : List Nat} {eqs : List (List Nat × List Nat)}
    {neqs : List (List Nat)} (h : relCheck d l₀ l₁ eqs neqs = true) :
    (∀ e ∈ eqs, evalG (permOf d fun x => l₀.getD x x) (permOf d fun x => l₁.getD x x) e.1 =
      evalG (permOf d fun x => l₀.getD x x) (permOf d fun x => l₁.getD x x) e.2) ∧
    ∀ u ∈ neqs, evalG (permOf d fun x => l₀.getD x x) (permOf d fun x => l₁.getD x x) u ≠ 1 := by
  change Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false
    (Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false _ _)
      (tabOk d l₁ (pack8 l₁))) (tabOk d l₀ (pack8 l₀))) (Nat.ble d 256) = true at h
  rw [band_eq_true, band_eq_true, band_eq_true, band_eq_true, Nat.ble_eq, listAll_eq_true,
    listAll_eq_true] at h
  obtain ⟨hd, ht₀, ht₁, heq, hne⟩ := h
  have h₀ := tabOk_sound hd ht₀
  have h₁ := tabOk_sound hd ht₁
  refine ⟨fun e he => ?_, fun u hu h1 => ?_⟩
  · have := allLt_eq_true.1 (heq e he)
    refine Equiv.ext fun x => Fin.ext ?_
    rw [wimg_eq h₀ h₁, wimg_eq h₀ h₁]
    exact Nat.eq_of_beq_eq_true (this x x.isLt)
  · have := hne u hu
    change Bool.rec (motive := fun _ => Bool) true false _ = true at this
    rw [bnot_eq_true] at this
    have hall : allLt d (fun x => Nat.beq (wimg (pack8 l₀) (pack8 l₁) u x) x) = true := by
      refine allLt_eq_true.2 fun x hx => ?_
      have := wimg_eq h₀ h₁ u ⟨x, hx⟩
      rw [h1] at this
      exact Nat.beq_eq_true_eq _ _ ▸ this.symm
    rw [hall] at this
    exact Bool.noConfusion this

end CFSG.KC.PackPerm

end
