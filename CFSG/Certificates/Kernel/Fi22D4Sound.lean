module

public import Certificates.Data.Kernel.Fi22.D4Set
public import CFSG.Certificates.Kernel.BfsPinBaseSound

public section

namespace CFSG.KC.Fi22D4

open CFSG.KC.Enum CFSG.KS
open CFSG.KC.BfsPin (allN_intro)

theorem pg_eq (w P i : Nat) : pg w (mask w) P i = P / 2 ^ (w * i) % 2 ^ w := by
  change Nat.land (Nat.shiftRight P (w * i)) (Nat.sub (1 <<< w) 1) = _
  rw [Nat.shiftLeft_eq, one_mul]
  change (P >>> (w * i)) &&& (2 ^ w - 1) = _
  rw [Nat.shiftRight_eq_div_pow]
  exact Nat.and_two_pow_sub_one_eq_mod _ _

theorem lt_of_blt {a b : Nat} (h : Nat.blt a b = true) : a < b := cast Nat.blt_eq h

theorem blt_of_lt {a b : Nat} (h : a < b) : Nat.blt a b = true := cast Nat.blt_eq.symm h

theorem beq_false_of_ne {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases hb : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true hb) h

theorem packL_cons (a : Nat) (t : List Nat) : packL (a :: t) = a + packL t * 4096 := by
  change a + (packL t <<< 12) = _
  rw [Nat.shiftLeft_eq]

theorem f12_packL : ∀ (l : List Nat), (∀ a ∈ l, a < 4096) →
    ∀ (k : Nat) (hk : k < l.length), f12 (packL l) k = l[k]
  | [], _, k, hk => absurd hk (by simp)
  | a :: t, h, 0, _ => by
    have ha : a < 4096 := h a (by simp)
    rw [f12, pg_eq, packL_cons]
    simp only [Nat.mul_zero, pow_zero, Nat.div_one, List.getElem_cons_zero]
    rw [show (2 : Nat) ^ 12 = 4096 by norm_num, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ha]
  | a :: t, h, k + 1, hk => by
    have ha : a < 4096 := h a (by simp)
    have ih := f12_packL t (fun b hb => h b (by simp [hb])) k (by simpa using hk)
    rw [f12, pg_eq] at ih
    rw [f12, pg_eq, packL_cons, List.getElem_cons_succ, ← ih]
    congr 1
    rw [show 12 * (k + 1) = 12 + 12 * k by ring, pow_add, ← Nat.div_div_eq_div_mul,
      show (2 : Nat) ^ 12 = 4096 by norm_num, Nat.add_mul_div_right _ _ (by norm_num),
      Nat.div_eq_of_lt ha, Nat.zero_add]

theorem ltL_spec : ∀ (l : List Nat) (b : Nat), ltL l b = true → ∀ a ∈ l, a < b
  | [], _, _, a, ha => absurd ha (by simp)
  | x :: t, b, h, a, ha => by
    have h' : bAnd(Nat.blt x b, ltL t b) = true := h
    rw [bAnd_iff] at h'
    rcases List.mem_cons.1 ha with rfl | ha
    · exact lt_of_blt h'.1
    · exact ltL_spec t b h'.2 a ha

theorem bijK_spec {O Q : Nat} (h : bijK O Q = true) {k : Nat} (hk : k < 360) :
    f12 O k < 3510 ∧ f9 Q (f12 O k) = k := by
  have h1 := allN_spec h k hk
  rw [bAnd_iff] at h1
  exact ⟨lt_of_blt h1.1, Nat.eq_of_beq_eq_true h1.2⟩

theorem inK_spec {O Q q : Nat} (h : inK O Q q = true) : f9 Q q < 360 ∧ f12 O (f9 Q q) = q := by
  unfold inK at h
  rw [bAnd_iff] at h
  exact ⟨lt_of_blt h.1, Nat.eq_of_beq_eq_true h.2⟩

theorem presK_spec {O Q T : Nat} (h : presK O Q T = true) {k : Nat} (hk : k < 360) :
    f9 Q (f12 T (f12 O k)) < 360 ∧ f12 O (f9 Q (f12 T (f12 O k))) = f12 T (f12 O k) :=
  inK_spec (allN_spec h k hk)

theorem outK_spec {O Q T : Nat} (h : outK O Q T = true) :
    ∃ k < 360, 360 ≤ f9 Q (f12 T (f12 O k)) := by
  unfold outK at h
  by_contra hne
  push Not at hne
  have hall : allN 360 (fun k => Nat.blt (f9 Q (f12 T (f12 O k))) 360) = true :=
    allN_intro fun k hk => blt_of_lt (hne k hk)
  rw [hall] at h
  exact Bool.false_ne_true h

theorem resK_spec {O R T : Nat} (h : resK O R T = true) {k : Nat} (hk : k < 360) :
    f9 R k < 360 ∧ f12 O (f9 R k) = f12 T (f12 O k) := by
  have h1 := allN_spec h k hk
  rw [bAnd_iff] at h1
  exact ⟨lt_of_blt h1.1, Nat.eq_of_beq_eq_true h1.2⟩

theorem itK_succ (T k p : Nat) : itK T (k + 1) p = f12 T (itK T k p) := rfl

theorem faithK_spec {O X Y : Nat} (h : faithK O X Y = true) {i j : Nat} (hi : i < 5) (hj : j < 5)
    (hij : i ≠ 0 ∨ j ≠ 0) : ∃ k < 360, itK X i (itK Y j (f12 O k)) ≠ f12 O k := by
  have h1 := allN_spec (allN_spec h i hi) j hj
  have h0 : bAnd(Nat.beq i 0, Nat.beq j 0) = false := by
    rcases hij with hi0 | hj0
    · rw [show Nat.beq i 0 = false from beq_false_of_ne hi0]
    · cases Nat.beq i 0
      · rfl
      · exact beq_false_of_ne hj0
  change bIf(bAnd(Nat.beq i 0, Nat.beq j 0), true,
      bIf(allN 360 (fun k => Nat.beq (itK X i (itK Y j (f12 O k))) (f12 O k)), false, true)) =
    true at h1
  rw [h0] at h1
  by_contra hne
  push Not at hne
  have hall : allN 360 (fun k => Nat.beq (itK X i (itK Y j (f12 O k))) (f12 O k)) = true :=
    allN_intro fun k hk => by rw [hne k hk]; exact Nat.beq_refl _
  rw [hall] at h1
  exact Bool.false_ne_true h1

end CFSG.KC.Fi22D4

end
