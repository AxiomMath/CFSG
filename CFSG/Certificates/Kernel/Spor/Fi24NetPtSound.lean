module

public import Certificates.Data.Kernel.Spor.Fi24NetPt
public import CFSG.Certificates.Kernel.Spor.Fi24NetSound

public section

namespace CFSG.KS.Fi24NetPt

open CFSG.KC.Loop CFSG.KC.Fi24Net CFSG.KC.Fi24NetPt CFSG.KS.Fi24Net CFSG.KC.Benes

theorem strictN_eq (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

theorem bit_eq (m q : Nat) : Nat.beq (Nat.land (Nat.shiftRight m q) 1) 1 = m.testBit q := by
  have h1 : Nat.land (Nat.shiftRight m q) 1 = m / 2 ^ q % 2 := by
    change (m >>> q) &&& 1 = _
    rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  rw [h1, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (m / 2 ^ q) with h | h <;> rw [h] <;> rfl

theorem swpK_eq (d m q : Nat) : swpK d m q = swp d m q := by
  unfold swpK swp
  rw [bit_eq, bit_eq]
  cases h1 : m.testBit q
  · cases h2 : Nat.ble d q
    · have h2' : ¬ d ≤ q := fun h => by rw [Nat.ble_eq_true_of_le h] at h2; cases h2
      simp only [Bool.false_eq_true, if_false, h2', false_and]
    · have h2' : d ≤ q := Nat.le_of_ble_eq_true h2
      cases h3 : m.testBit (q - d)
      · simp only [Bool.false_eq_true, if_false, and_false]
      · simp only [Bool.false_eq_true, if_false, h2', and_self, if_true]
        rfl
  · simp only [if_true]
    rfl

theorem compF_succ (τ : Nat → Nat → Nat) (a n q : Nat) :
    compF τ a (n + 1) q = τ a (compF τ (a + 1) n q) := rfl

theorem ptF_rec (M : Nat → Nat) (q : Nat) : ∀ n, n ≤ 37 →
    (Nat.rec (motive := fun _ => Nat) q
      (fun j ih => strictN ih (fun y => swpK (ldist (Nat.sub (nat_lit 36) j))
        (M (Nat.sub (nat_lit 36) j)) y)) n : Nat) =
      compF (fun l => swp (ldist l) (M l)) (37 - n) n q
  | 0, _ => rfl
  | n + 1, hn => by
    change strictN _ _ = _
    rw [strictN_eq, ptF_rec M q n (by omega), swpK_eq]
    have e : 37 - (n + 1) + 1 = 37 - n := by omega
    have e2 : Nat.sub 36 n = 37 - (n + 1) := by
      change 36 - n = 37 - (n + 1)
      omega
    rw [compF_succ, e, e2]

theorem ptF_eq (M : Nat → Nat) (q : Nat) : ptF M q = pF M q :=
  ptF_rec M q 37 (Nat.le_refl _)

theorem ptR_rec (M : Nat → Nat) (q : Nat) : ∀ n, n ≤ 37 →
    (Nat.rec (motive := fun _ => Nat) q
      (fun j ih => strictN ih (fun y => swpK (ldist j) (M j) y)) n : Nat) =
      compF (fun l => swp (ldist (36 - l)) (M (36 - l))) (37 - n) n q
  | 0, _ => rfl
  | n + 1, hn => by
    change strictN _ _ = _
    rw [strictN_eq, ptR_rec M q n (by omega), swpK_eq]
    have e : 37 - (n + 1) + 1 = 37 - n := by omega
    have e2 : 36 - (37 - (n + 1)) = n := by omega
    rw [compF_succ, e, e2]

theorem ptR_eq (M : Nat → Nat) (q : Nat) : ptR M q = pR M q :=
  ptR_rec M q 37 (Nat.le_refl _)

theorem land_one (l : Nat) : Nat.land l 1 = l % 2 := Nat.and_one_is_mod l

theorem shr_one (l : Nat) : Nat.shiftRight l 1 = l / 2 := by
  change l >>> 1 = _
  rw [Nat.shiftRight_eq_div_pow, pow_one]

theorem letN_eq (NW : Nat → Nat → Nat) (l x : Nat) : letN NW l x = LN NW l x := by
  unfold letN LN
  rw [land_one, shr_one]
  by_cases h : l % 2 = 0
  · have hb : Nat.beq (l % 2) 0 = true := by rw [h]; rfl
    rw [hb, if_pos h]
    exact ptF_eq _ x
  · have hb : Nat.beq (l % 2) 0 = false := by
      cases e : Nat.beq (l % 2) 0
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true e) h
    rw [hb, if_neg h]
    exact ptR_eq _ x

theorem testBit_planeL {NW : Nat → Nat → Nat} {l : Nat} (hv : NV (NW (l / 2))) (v q : Nat) :
    (planeL NW l v).testBit q = v.testBit (LN NW l q) := by
  unfold planeL LN
  rw [land_one, shr_one]
  by_cases h : l % 2 = 0
  · have hb : Nat.beq (l % 2) 0 = true := by rw [h]; rfl
    rw [hb, if_pos h]
    exact testBit_netF hv v q
  · have hb : Nat.beq (l % 2) 0 = false := by
      cases e : Nat.beq (l % 2) 0
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true e) h
    rw [hb, if_neg h]
    exact testBit_netR hv v q

end CFSG.KS.Fi24NetPt

end
