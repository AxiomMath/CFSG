module

public import CFSG.RankThree.PartOne.KE6.E8T3SevenInputs
public import Certificates.Data.Kernel.E8Seven

@[expose] public section

namespace Certificates.E8Seven

open CFSG.RankThree.PartOne.KE6 CFSG.Blueprint.Chevalley CFSG.RankThree.Lattice K
open CFSG.RankThree.E6 (charVal)

def m7 (x : ℤ) : ℕ := (x % 7).toNat

def code (p q r s : ℤ) : ℕ := m7 s + 256 * m7 r + 65536 * m7 q + 16777216 * m7 p

def g (l : List ℤ) (i : ℕ) : ℤ := l.getD i 0

def lin2 (l : List ℤ) : ℤ × ℤ × ℤ × ℤ :=
  (-(2 * g l 0) - 5 * g l 1 - g l 2 + g l 4,
   -(5 * g l 0) - 2 * g l 1 - 6 * g l 2 - 2 * g l 3 + g l 5,
   -(2 * g l 0) - 3 * g l 1 - 4 * g l 2 - 6 * g l 3 + g l 6,
   -(2 * g l 0) - g l 1 - 3 * g l 2 - 4 * g l 3 + g l 7)

def lin4 (l : List ℤ) : ℤ × ℤ × ℤ × ℤ :=
  (-(4 * g l 0) - 3 * g l 1 - g l 2 + g l 4,
   -(2 * g l 0) - 5 * g l 1 - 4 * g l 2 - 4 * g l 3 + g l 5,
   -(4 * g l 0) - 6 * g l 1 - 6 * g l 2 - 6 * g l 3 + g l 6,
   -(4 * g l 0) - g l 1 - 5 * g l 2 - 2 * g l 3 + g l 7)

def code2 (l : List ℤ) : ℕ := code (lin2 l).1 (lin2 l).2.1 (lin2 l).2.2.1 (lin2 l).2.2.2

def code4 (l : List ℤ) : ℕ := code (lin4 l).1 (lin4 l).2.1 (lin4 l).2.2.1 (lin4 l).2.2.2

theorem m7_lt (x : ℤ) : m7 x < 7 := by
  unfold m7
  omega

theorem m7_cast (x : ℤ) : ((m7 x : ℕ) : ZMod 7) = (x : ZMod 7) := by
  have h : ((m7 x : ℕ) : ℤ) = x % 7 := by
    unfold m7
    omega
  rw [← Int.cast_natCast, h]
  exact_mod_cast ZMod.intCast_mod x 7

theorem charVal_eight (z : Fin Tag.E8.rank → ZMod 7) (x : Fin Tag.E8.rank → ℤ) :
    charVal z x = ∑ i : Fin 8, (x i : ZMod 7) * z i := rfl

theorem charVal_eig2 (a b c d : ZMod 7) (l : List ℤ) :
    charVal (e8Eig2 a b c d) (toVec Tag.E8.rank l) =
      a * ((lin2 l).1 : ZMod 7) + b * ((lin2 l).2.1 : ZMod 7) + c * ((lin2 l).2.2.1 : ZMod 7) +
        d * ((lin2 l).2.2.2 : ZMod 7) := by
  rw [charVal_eight]
  simp [Fin.sum_univ_eight, e8Eig2, toVec, vget, lin2, g]
  ring

theorem charVal_eig4 (a b c d : ZMod 7) (l : List ℤ) :
    charVal (e8Eig4 a b c d) (toVec Tag.E8.rank l) =
      a * ((lin4 l).1 : ZMod 7) + b * ((lin4 l).2.1 : ZMod 7) + c * ((lin4 l).2.2.1 : ZMod 7) +
        d * ((lin4 l).2.2.2 : ZMod 7) := by
  rw [charVal_eight]
  simp [Fin.sum_univ_eight, e8Eig4, toVec, vget, lin4, g]
  ring

theorem lane3 {a b c d P Q R S : ℕ} (ha : a < 7) (hb : b < 7) (hc : c < 7) (hd : d < 7)
    (hP : P < 7) (hQ : Q < 7) (hR : R < 7) (hS : S < 7) :
    (S + 256 * R + 65536 * Q + 16777216 * P) * (a + 256 * b + 65536 * c + 16777216 * d) /
      2 ^ 24 % 256 = a * P + b * Q + c * R + d * S := by
  have m : ∀ x y : ℕ, x < 7 → y < 7 → x * y ≤ 36 := fun x y hx hy =>
    (Nat.mul_le_mul (Nat.le_of_lt_succ hx) (Nat.le_of_lt_succ hy)).trans (by norm_num)
  have e : (S + 256 * R + 65536 * Q + 16777216 * P) * (a + 256 * b + 65536 * c + 16777216 * d) =
      (a * S + 256 * (a * R + b * S) + 65536 * (a * Q + b * R + c * S)) +
        2 ^ 24 * ((a * P + b * Q + c * R + d * S) +
          256 * (b * P + c * Q + d * R + 256 * (c * P + d * Q) + 65536 * (d * P))) := by
    ring
  have h1 := m a S ha hS
  have h2 := m a R ha hR
  have h3 := m b S hb hS
  have h4 := m a Q ha hQ
  have h5 := m b R hb hR
  have h6 := m c S hc hS
  have h7 := m a P ha hP
  have h8 := m b Q hb hQ
  have h9 := m c R hc hR
  have h10 := m d S hd hS
  rw [e, Nat.add_mul_div_left _ _ (by norm_num), Nat.div_eq_of_lt (by omega), zero_add,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

theorem bA_iff {a b : Bool} : bA a b = true ↔ a = true ∧ b = true := by cases a <;> simp [bA]
theorem allR_iff {f : ℕ → Bool} : ∀ {n : ℕ}, allR n f = true ↔ ∀ k < n, f k = true
  | 0 => ⟨fun _ k hk => absurd hk (Nat.not_lt_zero k), fun _ => rfl⟩
  | n + 1 => by
    have e : allR (n + 1) f = bA (f n) (allR n f) := rfl
    rw [e, bA_iff, allR_iff]
    constructor
    · rintro ⟨h1, h2⟩ k hk
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with h | rfl
      · exact h2 k h
      · exact h1
    · intro h
      exact ⟨h n (Nat.lt_succ_self n), fun k hk => h k (Nat.lt_succ_of_lt hk)⟩

theorem ok_iff {n : ℕ} (h : ok n = true) : n = 30 ∨ n = 72 := by
  by_contra hn
  have hlt : n < 73 ∨ 73 ≤ n := by omega
  rcases hlt with hlt | hge
  · interval_cases n <;> simp_all [ok, okMask]
  · have hz : okMask >>> n = 0 := by
      rw [Nat.shiftRight_eq_div_pow]
      exact Nat.div_eq_of_lt (lt_of_lt_of_le (by norm_num [okMask])
        (Nat.pow_le_pow_right (by norm_num) hge))
    simp [ok, hz] at h

theorem hit_eq (X c : ℕ) : hit X c = if c * X / 2 ^ 24 % 256 % 7 = 0 then 1 else 0 := by
  change Bool.rec (motive := fun _ => ℕ) 0 1 (Nat.beq (((c * X) >>> 24) % 256 % 7) 0) = _
  rw [Nat.shiftRight_eq_div_pow]
  cases hb : Nat.beq (c * X / 2 ^ 24 % 256 % 7) 0
  · rw [if_neg (Nat.ne_of_beq_eq_false hb)]
  · rw [if_pos (Nat.eq_of_beq_eq_true hb)]

theorem cnt_eq (X : ℕ) (T : List ℕ) :
    cnt X T = T.countP (fun c => c * X / 2 ^ 24 % 256 % 7 = 0) := by
  induction T with
  | nil => rfl
  | cons c T ih =>
    have e : cnt X (c :: T) = hit X c + cnt X T := rfl
    rw [e, ih, List.countP_cons, hit_eq]
    by_cases h : c * X / 2 ^ 24 % 256 % 7 = 0 <;> simp [h, Nat.add_comm]

theorem cnt_map {lin : List ℤ → ℤ × ℤ × ℤ × ℤ} (R : List (List ℤ))
    (z : ℕ → ℕ → ℕ → ℕ → Fin Tag.E8.rank → ZMod 7)
    (hz : ∀ a b c d l, charVal (z a b c d) (toVec Tag.E8.rank l) =
      (a : ZMod 7) * ((lin l).1 : ZMod 7) + (b : ZMod 7) * ((lin l).2.1 : ZMod 7) +
        (c : ZMod 7) * ((lin l).2.2.1 : ZMod 7) + (d : ZMod 7) * ((lin l).2.2.2 : ZMod 7))
    {a b c d : ℕ} (ha : a < 7) (hb : b < 7) (hc : c < 7) (hd : d < 7) :
    cnt (pack a b c d) (R.map fun l => code (lin l).1 (lin l).2.1 (lin l).2.2.1 (lin l).2.2.2) =
      (R.filter fun l => decide (charVal (z a b c d) (toVec Tag.E8.rank l) = 0)).length := by
  rw [cnt_eq, List.countP_map, ← List.countP_eq_length_filter]
  apply List.countP_congr
  intro l _
  have hp : pack a b c d = a + 256 * b + 65536 * c + 16777216 * d := by
    change a + (256 * b + (65536 * c + 16777216 * d)) = _
    ring
  simp only [Function.comp_apply, code, hp, decide_eq_true_eq]
  rw [lane3 ha hb hc hd (m7_lt _) (m7_lt _) (m7_lt _) (m7_lt _), hz, ← Nat.dvd_iff_mod_eq_zero,
    ← ZMod.natCast_eq_zero_iff]
  push_cast [m7_cast]
  rfl

theorem count_of {lin : List ℤ → ℤ × ℤ × ℤ × ℤ} {T : List ℕ}
    (z : ℕ → ℕ → ℕ → ℕ → Fin Tag.E8.rank → ZMod 7)
    (hz : ∀ a b c d l, charVal (z a b c d) (toVec Tag.E8.rank l) =
      (a : ZMod 7) * ((lin l).1 : ZMod 7) + (b : ZMod 7) * ((lin l).2.1 : ZMod 7) +
        (c : ZMod 7) * ((lin l).2.2.1 : ZMod 7) + (d : ZMod 7) * ((lin l).2.2.2 : ZMod 7))
    (hT : T = e8ArtifactRoots.map fun l => code (lin l).1 (lin l).2.1 (lin l).2.2.1 (lin l).2.2.2)
    (hc : ∀ a < 7, chk T a = true) {a b c d : ℕ} (ha : a < 7) (hb : b < 7) (hc' : c < 7)
    (hd : d < 7) (hnz : a + (b + (c + d)) ≠ 0) :
    (e8ArtifactRoots.filter fun l => decide (charVal (z a b c d) (toVec Tag.E8.rank l) = 0)).length
      = 30 ∨
    (e8ArtifactRoots.filter fun l => decide (charVal (z a b c d) (toVec Tag.E8.rank l) = 0)).length
      = 72 := by
  have h := hc a ha
  unfold chk at h
  rw [allR_iff] at h
  have h1 := h b hb
  rw [allR_iff] at h1
  have h2 := h1 c hc'
  rw [allR_iff] at h2
  have h3 := h2 d hd
  have hne : Nat.beq (Nat.add a (Nat.add b (Nat.add c d))) 0 = false := by
    cases e : Nat.beq (Nat.add a (Nat.add b (Nat.add c d))) 0
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true e) hnz
  rw [hne] at h3
  rw [← cnt_map e8ArtifactRoots z hz ha hb hc' hd, ← hT]
  exact ok_iff (n := cnt (pack a b c d) T) h3

theorem e8SevenCount_of {T2 T4 : List ℕ} (h2 : T2 = e8ArtifactRoots.map code2)
    (h4 : T4 = e8ArtifactRoots.map code4) (c2 : ∀ a < 7, chk T2 a = true)
    (c4 : ∀ a < 7, chk T4 a = true) : E8SevenCount := by
  intro a b c d hnz
  have hv : ∀ x : ZMod 7, x = ((x.val : ℕ) : ZMod 7) := fun x => (ZMod.natCast_zmod_val x).symm
  have hne : a.val + (b.val + (c.val + d.val)) ≠ 0 := by
    intro hs
    rcases hnz with h | h | h | h <;> exact h ((ZMod.val_eq_zero _).1 (by omega))
  rw [hv a, hv b, hv c, hv d]
  exact ⟨count_of (fun a b c d => e8Eig2 (a : ZMod 7) b c d)
      (fun a b c d l => charVal_eig2 _ _ _ _ l) h2 c2 (ZMod.val_lt a) (ZMod.val_lt b)
      (ZMod.val_lt c) (ZMod.val_lt d) hne,
    count_of (fun a b c d => e8Eig4 (a : ZMod 7) b c d)
      (fun a b c d l => charVal_eig4 _ _ _ _ l) h4 c4 (ZMod.val_lt a) (ZMod.val_lt b)
      (ZMod.val_lt c) (ZMod.val_lt d) hne⟩

end Certificates.E8Seven
