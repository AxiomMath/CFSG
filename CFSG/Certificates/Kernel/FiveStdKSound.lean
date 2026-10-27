module

public import Certificates.Data.Kernel.FiveStdK
public import CFSG.GH74.GLS.LU.Local.FiveStdInputs
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.KC.FiveStdK

open CFSG.GH74.GLS.LU.Local.FiveStd

theorem andB_eq (a b : Bool) : andB a b = (a && b) := by cases a <;> rfl

theorem ifN_zero (t e : Nat) : ifN 0 t e = e := rfl

theorem ifN_one (t e : Nat) : ifN 1 t e = t := rfl

theorem ifN_eq (n t e : Nat) : ifN n t e = if n = 0 then e else t := by cases n <;> rfl

theorem letB_eq {α : Type} (y : Nat) (k : Nat → α) : letB y k = k y := by cases y <;> rfl

theorem allN_iff (n : Nat) (f : Nat → Bool) : allN n f = true ↔ ∀ i < n, f i = true := by
  induction n with
  | zero => exact ⟨fun _ i hi => absurd hi (Nat.not_lt_zero i), fun _ => rfl⟩
  | succ n ih =>
    change andB (f n) (allN n f) = true ↔ _
    rw [andB_eq, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | rfl
      · exact h2 i h
      · exact h1
    · intro h
      exact ⟨h n (Nat.lt_succ_self n), fun i hi => h i (Nat.lt_succ_of_lt hi)⟩

theorem nat_div (a b : Nat) : Nat.div a b = a / b := rfl
theorem nat_mod (a b : Nat) : Nat.mod a b = a % b := rfl
theorem nat_add (a b : Nat) : Nat.add a b = a + b := rfl
theorem nat_mul (a b : Nat) : Nat.mul a b = a * b := rfl

@[expose] def bv (b : Bool) : Nat := if b then 1 else 0

theorem fields_codeE (x : E) :
    fA0 (codeE x) = x.a0.val ∧ fA1 (codeE x) = x.a1.val ∧ fA2 (codeE x) = x.a2.val ∧
      fA3 (codeE x) = x.a3.val ∧ fB0 (codeE x) = x.b0.val ∧ fB1 (codeE x) = x.b1.val ∧
      fB2 (codeE x) = x.b2.val ∧ fB3 (codeE x) = x.b3.val ∧ fS (codeE x) = bv x.s := by
  obtain ⟨⟨a0, h0⟩, ⟨a1, h1⟩, ⟨a2, h2⟩, ⟨a3, h3⟩, ⟨b0, h4⟩, ⟨b1, h5⟩, ⟨b2, h6⟩, ⟨b3, h7⟩, s⟩ := x
  simp only [codeE, fA0, fA1, fA2, fA3, fB0, fB1, fB2, fB3, fS, bv, nat_div, nat_mod]
  cases s <;> simp only [Bool.false_eq_true, if_false, if_true] <;> omega

theorem codeE_lt (x : E) : codeE x < 781250 := by
  obtain ⟨⟨a0, h0⟩, ⟨a1, h1⟩, ⟨a2, h2⟩, ⟨a3, h3⟩, ⟨b0, h4⟩, ⟨b1, h5⟩, ⟨b2, h6⟩, ⟨b3, h7⟩, s⟩ := x
  simp only [codeE]
  cases s <;> simp only [Bool.false_eq_true, if_false, if_true] <;> omega

theorem codeE_injective : Function.Injective codeE := by
  intro x y h
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8⟩ := fields_codeE x
  obtain ⟨y0, y1, y2, y3, y4, y5, y6, y7, y8⟩ := fields_codeE y
  rw [h] at x0 x1 x2 x3 x4 x5 x6 x7 x8
  obtain ⟨a0, a1, a2, a3, b0, b1, b2, b3, s⟩ := x
  obtain ⟨c0, c1, c2, c3, d0, d1, d2, d3, t⟩ := y
  simp only at x0 x1 x2 x3 x4 x5 x6 x7 x8 y0 y1 y2 y3 y4 y5 y6 y7 y8
  have hs : s = t := by
    cases s <;> cases t <;> simp_all [bv]
  rw [E.mk.injEq]
  exact ⟨Fin.ext (x0.symm.trans y0), Fin.ext (x1.symm.trans y1), Fin.ext (x2.symm.trans y2),
    Fin.ext (x3.symm.trans y3), Fin.ext (x4.symm.trans y4), Fin.ext (x5.symm.trans y5),
    Fin.ext (x6.symm.trans y6), Fin.ext (x7.symm.trans y7), hs⟩

theorem codeE_oneE : codeE oneE = oneK := rfl

theorem cinv_mod (d : Nat) : cinv (d % 5) = cinv d := by
  have h : d % 5 ≡ d [MOD 5] := Nat.mod_modEq d 5
  exact h.mul (h.mul h)

theorem val_inv5 : ∀ u : Fin 5, (inv5 u).val = cinv u.val := by decide

theorem val_sub5 : ∀ u v : Fin 5, (u - v).val = (u.val + 4 * v.val) % 5 := by decide

theorem val_neg5 : ∀ u : Fin 5, (-u).val = (4 * u.val) % 5 := by decide

theorem val_mul_add (a b c d : Fin 5) : (a.val * b.val + c.val * d.val) % 5 = (a * b + c * d).val := by
  rw [Fin.val_add, Fin.val_mul, Fin.val_mul, ← Nat.add_mod]

theorem val_det (a b c d : Fin 5) :
    (a.val * b.val + 4 * (c.val * d.val)) % 5 = (a * b - c * d).val := by
  rw [val_sub5, Fin.val_mul, Fin.val_mul]
  generalize a.val * b.val = P
  generalize c.val * d.val = Q
  omega

theorem mul_mod_of (c r v : Nat) (h : r % 5 = v) : c * r % 5 = c * v % 5 := by
  subst h
  exact (Nat.mul_mod_mod c r 5).symm

theorem nrm_eq (z : E) (r0 r1 r2 r3 r4 r5 r6 r7 s : Nat) (h0 : r0 % 5 = z.a0.val)
    (h1 : r1 % 5 = z.a1.val) (h2 : r2 % 5 = z.a2.val) (h3 : r3 % 5 = z.a3.val)
    (h4 : r4 % 5 = z.b0.val) (h5 : r5 % 5 = z.b1.val) (h6 : r6 % 5 = z.b2.val)
    (h7 : r7 % 5 = z.b3.val) (hs : s = bv z.s) :
    nrm r0 r1 r2 r3 r4 r5 r6 r7 s = codeE (normE z) := by
  obtain ⟨a0, a1, a2, a3, b0, b1, b2, b3, zs⟩ := z
  simp only at h0 h1 h2 h3 h4 h5 h6 h7 hs
  have hc : cinv (ifN (Nat.mod r0 5) r0 r1) = (inv5 (if a0 ≠ 0 then a0 else a1)).val := by
    rw [val_inv5, nat_mod, ifN_eq]
    by_cases hz : a0 = 0
    · have : r0 % 5 = 0 := by rw [h0, hz]; rfl
      rw [if_pos this, if_neg (not_not.2 hz), ← cinv_mod r1, h1]
    · have : r0 % 5 ≠ 0 := by rw [h0]; exact fun h => hz (Fin.ext h)
      rw [if_neg this, if_pos hz, ← cinv_mod r0, h0]
  unfold nrm
  rw [letB_eq, hc]
  simp only [normE, codeE, Fin.val_mul, nat_add, nat_mul, nat_mod]
  rw [mul_mod_of _ _ _ h0, mul_mod_of _ _ _ h1, mul_mod_of _ _ _ h2, mul_mod_of _ _ _ h3,
    mul_mod_of _ _ _ h4, mul_mod_of _ _ _ h5, mul_mod_of _ _ _ h6, mul_mod_of _ _ _ h7, hs]
  cases zs <;> simp only [bv, Bool.false_eq_true, if_false, if_true] <;> ring

theorem mulK_eq (p q : Nat) : mulK p q =
    ifN (fS p)
      (mul8 (fA0 p) (fA1 p) (fA2 p) (fA3 p) (fB0 p) (fB1 p) (fB2 p) (fB3 p)
        (fB0 q) (fB1 q) (fB2 q) (fB3 q) (fA0 q) (fA1 q) (fA2 q) (fA3 q) (Nat.mod (Nat.add (fS p) (fS q)) 2))
      (mul8 (fA0 p) (fA1 p) (fA2 p) (fA3 p) (fB0 p) (fB1 p) (fB2 p) (fB3 p)
        (fA0 q) (fA1 q) (fA2 q) (fA3 q) (fB0 q) (fB1 q) (fB2 q) (fB3 q) (Nat.mod (Nat.add (fS p) (fS q)) 2)) := by
  simp only [mulK, letB_eq]

theorem mul8_eq (x y : E) (s : Nat) (z : E) (hz : z = ⟨x.a0 * y.a0 + x.a1 * y.a2, x.a0 * y.a1 + x.a1 * y.a3,
      x.a2 * y.a0 + x.a3 * y.a2, x.a2 * y.a1 + x.a3 * y.a3, x.b0 * y.b0 + x.b1 * y.b2,
      x.b0 * y.b1 + x.b1 * y.b3, x.b2 * y.b0 + x.b3 * y.b2, x.b2 * y.b1 + x.b3 * y.b3, z.s⟩)
    (hs : s = bv z.s) :
    mul8 x.a0.val x.a1.val x.a2.val x.a3.val x.b0.val x.b1.val x.b2.val x.b3.val
      y.a0.val y.a1.val y.a2.val y.a3.val y.b0.val y.b1.val y.b2.val y.b3.val s = codeE (normE z) := by
  unfold mul8
  rw [hz] at hs ⊢
  exact nrm_eq _ _ _ _ _ _ _ _ _ _ (val_mul_add _ _ _ _) (val_mul_add _ _ _ _) (val_mul_add _ _ _ _)
    (val_mul_add _ _ _ _) (val_mul_add _ _ _ _) (val_mul_add _ _ _ _) (val_mul_add _ _ _ _)
    (val_mul_add _ _ _ _) hs

@[expose] def swapE (y : E) : E := ⟨y.b0, y.b1, y.b2, y.b3, y.a0, y.a1, y.a2, y.a3, y.s⟩

theorem bv_false : bv false = 0 := rfl

theorem bv_true : bv true = 1 := rfl

theorem bv_xor (a b : Bool) : Nat.mod (Nat.add (bv a) (bv b)) 2 = bv (a != b) := by
  cases a <;> cases b <;> rfl

theorem codeE_mulE (x y : E) : codeE (mulE x y) = mulK (codeE x) (codeE y) := by
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8⟩ := fields_codeE x
  obtain ⟨y0, y1, y2, y3, y4, y5, y6, y7, y8⟩ := fields_codeE y
  rw [mulK_eq, x0, x1, x2, x3, x4, x5, x6, x7, x8, y0, y1, y2, y3, y4, y5, y6, y7, y8, bv_xor]
  cases hx : x.s <;> cases hy : y.s
  · rw [bv_false, ifN_zero, mulE, hx, hy]
    exact (mul8_eq x y _ _ rfl rfl).symm
  · rw [bv_false, ifN_zero, mulE, hx, hy]
    exact (mul8_eq x y _ _ rfl rfl).symm
  · rw [bv_true, ifN_one, mulE, hx, hy]
    exact (mul8_eq x (swapE y) _ _ rfl rfl).symm
  · rw [bv_true, ifN_one, mulE, hx, hy]
    exact (mul8_eq x (swapE y) _ _ rfl rfl).symm

theorem invK_eq (p : Nat) : invK p =
    inv8 (fA0 p) (fA1 p) (fA2 p) (fA3 p) (fB0 p) (fB1 p) (fB2 p) (fB3 p)
      (cinv (Nat.add (Nat.mul (fA0 p) (fA3 p)) (Nat.mul 4 (Nat.mul (fA1 p) (fA2 p)))))
      (cinv (Nat.add (Nat.mul (fB0 p) (fB3 p)) (Nat.mul 4 (Nat.mul (fB1 p) (fB2 p))))) (fS p) := by
  simp only [invK, letB_eq]

theorem cinv_det (a b c d : Fin 5) :
    cinv (Nat.add (Nat.mul a.val b.val) (Nat.mul 4 (Nat.mul c.val d.val))) = (inv5 (a * b - c * d)).val := by
  rw [val_inv5, ← val_det, nat_add, nat_mul, nat_mul, nat_mul, cinv_mod]

theorem mod_dmul (d : Fin 5) (u : Fin 5) : d.val * u.val % 5 = (d * u).val := (Fin.val_mul d u).symm

theorem mod_ndmul (d : Fin 5) (u : Fin 5) : 4 * (d.val * u.val) % 5 = (-(d * u)).val := by
  rw [val_neg5, Fin.val_mul, Nat.mul_mod_mod]

theorem codeE_invE (x : E) : codeE (invE x) = invK (codeE x) := by
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8⟩ := fields_codeE x
  rw [invK_eq, x0, x1, x2, x3, x4, x5, x6, x7, x8, cinv_det, cinv_det]
  unfold inv8
  have hA : invA x = (inv5 (detA x) * x.a3, -(inv5 (detA x) * x.a1), -(inv5 (detA x) * x.a2),
      inv5 (detA x) * x.a0) := rfl
  have hB : invB x = (inv5 (detB x) * x.b3, -(inv5 (detB x) * x.b1), -(inv5 (detB x) * x.b2),
      inv5 (detB x) * x.b0) := rfl
  cases hx : x.s
  · simp only [bv, Bool.false_eq_true, if_false, ifN_zero, nat_mul]
    rw [invE, hx, hA, hB]
    exact (nrm_eq _ _ _ _ _ _ _ _ _ _ (mod_dmul _ _) (mod_ndmul _ _) (mod_ndmul _ _) (mod_dmul _ _)
      (mod_dmul _ _) (mod_ndmul _ _) (mod_ndmul _ _) (mod_dmul _ _) rfl).symm
  · simp only [bv, if_true, ifN_one, nat_mul]
    rw [invE, hx, hA, hB]
    exact (nrm_eq _ _ _ _ _ _ _ _ _ _ (mod_dmul _ _) (mod_ndmul _ _) (mod_ndmul _ _) (mod_dmul _ _)
      (mod_dmul _ _) (mod_ndmul _ _) (mod_ndmul _ _) (mod_dmul _ _) rfl).symm

theorem beq_one5 : ∀ u : Fin 5, Nat.beq u.val 1 = decide (u = 1) := by decide

theorem beq_zero5 : ∀ u : Fin 5, Nat.beq u.val 0 = decide (u = 0) := by decide

theorem beq_one5' : ∀ u : Fin 5, Nat.beq u.val 1 = (u == 1) := by decide

theorem rec_or (a b : Bool) : Bool.rec (motive := fun _ => Bool) b true a = (a || b) := by
  cases a <;> rfl

theorem validK_codeE (x : E) : validK (codeE x) = validE x := by
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, -⟩ := fields_codeE x
  unfold validK
  rw [x0, x1, x2, x3, x4, x5, x6, x7]
  have hlt : Nat.blt (codeE x) 781250 = true := by
    rw [Nat.blt_eq]
    exact codeE_lt x
  rw [hlt]
  have hdet : Nat.mod (Nat.mul (Nat.add (Nat.mul x.a0.val x.a3.val) (Nat.mul 4 (Nat.mul x.a1.val x.a2.val)))
      (Nat.add (Nat.mul x.b0.val x.b3.val) (Nat.mul 4 (Nat.mul x.b1.val x.b2.val)))) 5 =
      (detA x * detB x).val := by
    rw [Fin.val_mul, detA, detB, ← val_det, ← val_det]
    simp only [nat_mod, nat_mul, nat_add]
    rw [Nat.mul_mod]
  rw [hdet, beq_one5' (detA x * detB x), beq_one5 x.a0, beq_zero5 x.a0, beq_one5 x.a1, rec_or]
  simp only [andB_eq, Bool.true_and]
  rfl

theorem beq_oneK (y : E) : Nat.beq (codeE y) oneK = decide (y = oneE) := by
  by_cases h : y = oneE
  · rw [h, decide_eq_true rfl, codeE_oneE]
    exact Nat.beq_refl oneK
  · rw [decide_eq_false h]
    cases hb : Nat.beq (codeE y) oneK
    · rfl
    · exact absurd (codeE_injective ((Nat.eq_of_beq_eq_true hb).trans codeE_oneE.symm)) h

theorem ordAux_codeE (x : E) : ∀ (fuel : Nat) (y : E) (k : Nat),
    ordAuxK (codeE x) fuel (codeE y) k = ordAux x fuel y k
  | 0, _, _ => rfl
  | fuel + 1, y, k => by
    change Bool.rec (motive := fun _ => Nat) (ordAuxK (codeE x) fuel (mulK (codeE y) (codeE x)) (Nat.succ k)) k
      (Nat.beq (codeE y) oneK) = _
    rw [beq_oneK, ← codeE_mulE, ordAux_codeE x fuel (mulE y x) (Nat.succ k)]
    by_cases h : y = oneE
    · rw [decide_eq_true h]
      simp [ordAux, h]
    · rw [decide_eq_false h]
      simp [ordAux, h]

theorem ordK_codeE (x : E) : ordK (codeE x) = ordE x := ordAux_codeE x 300 x 1

end CFSG.KC.FiveStdK

end
