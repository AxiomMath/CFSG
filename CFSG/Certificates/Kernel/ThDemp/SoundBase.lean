
module

public import Certificates.Data.Kernel.ThDemp.Defs
public import CFSG.Certificates.Kernel.ThDemp.Chain
public import CFSG.Certificates.Kernel.Th.Spec.FwdRelBase
import CFSG.Certificates.Kernel.Th.Spec.FwdSlp

@[expose] public section

namespace CFSG.Certificates.ThDemp

open CFSG.KC.Th CFSG.KC.Th.BigS CFSG.KC.Th.Spec CFSG.KC.Th.Spec.FwdRel CFSG.KC.ThDemp
  CFSG.Certificates.ThDemp.Chain

local notation "𝕄" g:max =>
  ((Subtype.val g : GL (Fin 248) (ZMod 2)) : Matrix (Fin 248) (Fin 248) (ZMod 2))

private theorem bAnd_demp {a b : Bool} :
    Bool.rec (motive := fun _ => Bool) false b a = true ↔ a = true ∧ b = true := by
  cases a <;> simp

private theorem bIf_demp {c t : Bool} (h : Bool.rec (motive := fun _ => Bool) true t c = true)
    (hc : c = true) : t = true := by
  subst hc
  exact h

private theorem recAnd_demp (g : ℕ → Bool) : ∀ n,
    Nat.rec (motive := fun _ => Bool) true
      (fun l ih => Bool.rec (motive := fun _ => Bool) false ih (g l)) n = true ↔
      ∀ l < n, g l = true
  | 0 => ⟨fun _ l hl => absurd hl (Nat.not_lt_zero l), fun _ => rfl⟩
  | n + 1 => by
    change Bool.rec (motive := fun _ => Bool) false (Nat.rec (motive := fun _ => Bool) true
      (fun l ih => Bool.rec (motive := fun _ => Bool) false ih (g l)) n) (g n) = true ↔ _
    rw [bAnd_demp, recAnd_demp g n]
    constructor
    · rintro ⟨h1, h2⟩ l hl
      rcases Nat.lt_succ_iff_lt_or_eq.1 hl with h | h
      · exact h2 l h
      · exact h ▸ h1
    · intro h
      exact ⟨h n (Nat.lt_succ_self n), fun l hl => h l (Nat.lt_succ_of_lt hl)⟩

private theorem allBelow_demp {m hi : ℕ} {f : ℕ → Bool}
    (h : CFSG.KC.Loop.allBelow m hi f = true) (hm : m ≤ 64 * hi) : ∀ i < m, f i = true := by
  intro i him
  have h1 := (recAnd_demp (fun h => Nat.rec (motive := fun _ => Bool) true (fun l ih2 =>
      Bool.rec (motive := fun _ => Bool) false ih2
        ((fun i => Bool.rec (motive := fun _ => Bool) true (f i) (Nat.blt i m))
          (Nat.add (Nat.shiftLeft h 6) l))) 64) hi).1 h (i / 64) (by omega)
  have h2 := (recAnd_demp (fun l => (fun i => Bool.rec (motive := fun _ => Bool) true (f i)
      (Nat.blt i m)) (Nat.add (Nat.shiftLeft (i / 64) 6) l)) 64).1 h1 (i % 64)
    (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.shiftLeft (i / 64) 6) (i % 64) = i := by
    change (i / 64) <<< 6 + i % 64 = i
    rw [Nat.shiftLeft_eq, show (2 : ℕ) ^ 6 = 64 from rfl]
    omega
  dsimp only at h2
  rw [e, Nat.blt_eq.mpr him] at h2
  exact h2

private theorem regsIn_demp {L n r : ℕ} (h : regsIn L n r = true) :
    ∀ k < n, 0 < regAt L k ∧ regAt L k < r := by
  have hf := (Dce.allB_iff (fun k => regBelow (regAt L k) r) n).1 h
  intro k hk
  obtain ⟨h1, h2⟩ := Dce.andB_iff.1 (hf k hk)
  exact ⟨Nat.blt_eq.mp h1, Nat.blt_eq.mp h2⟩

private theorem shiftRight_eleven_demp (x : ℕ) : Nat.shiftRight x 11 = x / 2048 :=
  (Nat.shiftRight_eq_div_pow x 11).trans (by norm_num)

private theorem inj_of_sorted_demp {n : ℕ} {o P : ℕ → ℕ} (ho : ∀ i < n, o i < n)
    (hs : ∀ i, i + 1 < n → P (o i) < P (o (i + 1))) :
    ∀ i j, i < n → j < n → P i = P j → i = j := by
  have hmono : ∀ a k, a + 1 + k < n → P (o a) < P (o (a + 1 + k)) := by
    intro a k
    induction k with
    | zero => exact fun h => hs a h
    | succ k ih => exact fun h => (ih (by omega)).trans (hs (a + 1 + k) (by omega))
  have hlt : ∀ a b, a < b → b < n → P (o a) < P (o b) := by
    intro a b hab hb
    obtain ⟨k, rfl⟩ : ∃ k, b = a + 1 + k := ⟨b - a - 1, by omega⟩
    exact hmono a k hb
  let f : Fin n → Fin n := fun a => ⟨o a, ho a a.2⟩
  have hf : Function.Injective f := by
    intro a b hab
    have e : o a = o b := congrArg Fin.val hab
    by_contra hne
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with h | h
    · exact (hlt a b h b.2).ne (congrArg P e)
    · exact (hlt b a h a.2).ne (congrArg P e).symm
  intro i j hi hj hP
  obtain ⟨a, ha⟩ := (Finite.injective_iff_surjective.1 hf) ⟨i, hi⟩
  obtain ⟨b, hb⟩ := (Finite.injective_iff_surjective.1 hf) ⟨j, hj⟩
  have ea : o a = i := congrArg Fin.val ha
  have eb : o b = j := congrArg Fin.val hb
  rw [← ea, ← eb] at hP ⊢
  rcases lt_trichotomy (a : ℕ) b with h | h | h
  · exact absurd hP (hlt a b h b.2).ne
  · rw [h]
  · exact absurd hP.symm (hlt b a h a.2).ne

variable {D : DempData}

theorem T_of_zero {l i : ℕ} (h : D.trR l i = 0) : D.T l i = D.ONE := by
  simp [DempData.T, h]

theorem T_of_pos {l i : ℕ} (h : 0 < D.trR l i) : D.T l i = D.RB (D.trR l i) := by
  have hb : Nat.beq (D.trR l i) 0 = false := by
    cases hb : Nat.beq (D.trR l i) 0
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true hb) (by omega)
  simp only [DempData.T, hb]

theorem marked_marks {a b k : ℕ}
    (h : marked (Nat.lor (Nat.shiftLeft 1 a) (Nat.shiftLeft 1 b)) k = true) : k = a ∨ k = b := by
  have hs : ∀ x, Nat.shiftLeft 1 x = 2 ^ x := fun x => by
    rw [show Nat.shiftLeft 1 x = 1 <<< x from rfl, Nat.one_shiftLeft]
  have h1 : 0 < (2 ^ a ||| 2 ^ b) &&& 2 ^ k := by
    have h0 := Nat.blt_eq.mp h
    simp only [hs] at h0
    exact h0
  rw [Nat.and_two_pow] at h1
  have h2 : (2 ^ a ||| 2 ^ b).testBit k = true := by
    cases hb : (2 ^ a ||| 2 ^ b).testBit k
    · rw [hb] at h1
      simp at h1
    · rfl
  rw [Nat.testBit_or, Nat.testBit_two_pow, Nat.testBit_two_pow] at h2
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h2
  omega

end CFSG.Certificates.ThDemp

end
