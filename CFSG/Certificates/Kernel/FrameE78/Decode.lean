module

public import CFSG.Certificates.Kernel.FrameE78.Sound
public import CFSG.Certificates.Kernel.FrameE78.Roots
public import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.IntervalCases
public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.KC.FrameE78

open CFSG.KC.Enum CFSG.KC.FrameE78.Refl Matrix

@[expose] noncomputable def dec (n x : ℕ) : Fin n → ZMod 3 := fun q => (ln x q : ZMod 3)

@[expose] noncomputable def Cm (n C : ℕ) : Matrix (Fin n) (Fin n) (ZMod 3) :=
  fun p q => (cij C p q : ZMod 3)

theorem dec_apply (n x : ℕ) (q : Fin n) : dec n x q = (ln x q : ZMod 3) := rfl

private theorem cast_mod3 (a : ℕ) : ((a % 3 : ℕ) : ZMod 3) = (a : ZMod 3) := ZMod.natCast_mod a 3

private theorem sum_fin_range (n : ℕ) (f : ℕ → ℕ) :
    ((∑ q ∈ Finset.range n, f q : ℕ) : ZMod 3) = ∑ q : Fin n, (f q : ZMod 3) := by
  rw [Nat.cast_sum, Finset.sum_range]

theorem dec_cvec (n C c : ℕ) : dec n (cvec n C c) = Cm n C *ᵥ dec n c := by
  funext p
  rw [dec_apply, ln_cvec C c p.isLt, cast_mod3, sum_fin_range]
  simp only [Nat.cast_mul, mulVec, dotProduct, Cm, dec_apply]

theorem dot3_cast (n u v : ℕ) : (dot3 n u v : ZMod 3) = dec n u ⬝ᵥ dec n v := by
  rw [dot3_eq, cast_mod3, sum_fin_range]
  simp only [Nat.cast_mul, dotProduct, dec_apply]

private theorem two_eq : (2 : ZMod 3) = -1 := by decide

theorem mulVec_ev {n : ℕ} (M : Matrix (Fin n) (Fin n) (ZMod 3)) (j : Fin n) :
    M *ᵥ ev j = fun p => M p j := by
  funext p
  simp [mulVec, dotProduct, Pi.single_apply]

theorem dec_sV {n C x : ℕ} (hx : ∀ q < n, ln x q ≤ 2) (j : Fin n) :
    dec n (sV n C j x) = sS (Cm n C) j *ᵥ dec n x := by
  funext p
  rw [dec_apply, ln_sV p.isLt (hx p p.isLt), cast_mod3, rf_mulVec, mulVec_ev]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
    single_dotProduct, one_mul, Cm, dec_apply, two_eq]
  ring

private theorem cast_neg3 {v : ℕ} (hv : v ≤ 2) : (((3 - v) % 3 : ℕ) : ZMod 3) = -(v : ZMod 3) := by
  interval_cases v <;> decide

theorem dec_negL {n y : ℕ} (hn : n ≤ 8) (hy : ∀ q < n, ln y q ≤ 2) :
    dec n (negL y) = -dec n y := by
  funext q
  rw [Pi.neg_apply, dec_apply, dec_apply, ln_negL (by omega) (hy q q.isLt), cast_neg3 (hy q q.isLt)]

theorem dec_sRt (n C c : ℕ) (i : Fin n) :
    dec n (sRt c (cvec n C c) i) = sR (Cm n C) i (dec n c) := by
  funext q
  have hb : Refl.bf (Cm n C) (ev i) (dec n c) = (ln (cvec n C c) i : ZMod 3) := by
    rw [Refl.bf, ← dec_cvec, single_dotProduct, one_mul, dec_apply]
  rw [dec_apply, ln_sRt]
  simp only [sR, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hb]
  by_cases h : q = i
  · subst h
    simp only [ev, Pi.single_eq_same, if_true, cast_mod3, dec_apply, Nat.cast_add, Nat.cast_mul,
      Nat.cast_ofNat, two_eq]
    ring
  · rw [if_neg (fun e => h (Fin.ext e))]
    simp only [ev, Pi.single_eq_of_ne h, mul_zero, sub_zero, dec_apply]

theorem dec_shl_one (n : ℕ) (i : Fin n) : dec n (1 <<< (2 * (i : ℕ))) = ev i := by
  funext q
  rw [dec_apply, ln_shl (by decide)]
  by_cases h : q = i
  · subst h
    simp only [ev, if_true, Pi.single_eq_same, Nat.cast_one]
  · rw [if_neg (fun e => h (Fin.ext e))]
    simp only [ev, Pi.single_eq_of_ne h, Nat.cast_zero]

private theorem bits21845_odd : ∀ k, Nat.testBit 21845 (2 * k + 1) = false := by
  intro k
  by_cases hk : k < 8
  · revert k
    decide
  · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le (by decide : (21845 : ℕ) < 2 ^ 16)
      (Nat.pow_le_pow_right (by decide) (by omega)))

private theorem four_pow' (n : ℕ) : (4 : ℕ) ^ n = 2 ^ (2 * n) := by
  rw [pow_mul]
  rfl

theorem VOK_negL {n y : ℕ} (hn : n ≤ 8) (hy : VOK n y) : VOK n (negL y) := by
  refine ⟨?_, fun q hq => ?_⟩
  · rw [four_pow']
    apply Nat.lt_pow_two_of_testBit
    intro i hi
    have hy' : y < 2 ^ (2 * n) := by rw [← four_pow']; exact hy.1
    change (((y &&& 21845) <<< 1) ||| ((y &&& 43690) >>> 1)).testBit i = false
    rw [Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftRight, Nat.testBit_and,
      Nat.testBit_and, Nat.testBit_lt_two_pow (lt_of_lt_of_le hy'
        (Nat.pow_le_pow_right (by decide) (by omega)) : y < 2 ^ (1 + i)), Bool.false_and,
      Bool.or_false]
    by_cases h1 : 2 * n ≤ i - 1
    · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hy' (Nat.pow_le_pow_right (by decide) h1)),
        Bool.false_and, Bool.and_false]
    · obtain ⟨k, hk⟩ : ∃ k, i - 1 = 2 * k + 1 := ⟨n - 1, by omega⟩
      rw [hk, bits21845_odd, Bool.and_false, Bool.and_false]
  · rw [ln_negL (by omega) (hy.2 q hq)]
    omega

@[expose] noncomputable def enc (n : ℕ) (x : Fin n → ZMod 3) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0
    (fun p ih => ih ||| ((if h : p < n then (x ⟨p, h⟩).val else 0) % 3) <<< (2 * p)) n

theorem VOK_enc (n : ℕ) (x : Fin n → ZMod 3) : VOK n (enc n x) := by
  refine ⟨pack_lt _ n, fun q hq => ?_⟩
  rw [enc, ln_pack, if_pos hq]
  omega

theorem dec_enc (n : ℕ) (x : Fin n → ZMod 3) : dec n (enc n x) = x := by
  funext q
  rw [dec_apply, enc, ln_pack, if_pos q.isLt, dif_pos q.isLt,
    Nat.mod_eq_of_lt (ZMod.val_lt (x ⟨q, q.isLt⟩)), ZMod.natCast_zmod_val]

theorem dec_inj {n x y : ℕ} (hx : VOK n x) (hy : VOK n y) (h : dec n x = dec n y) : x = y := by
  refine VOK_ext hx hy fun q hq => ?_
  have e : (ln x q : ZMod 3) = (ln y q : ZMod 3) := congrFun h ⟨q, hq⟩
  have e2 := congrArg ZMod.val e
  have h1 := hx.2 q hq
  have h2 := hy.2 q hq
  rwa [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at e2

end CFSG.KC.FrameE78

end
