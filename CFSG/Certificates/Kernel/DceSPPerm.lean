module

public import CFSG.Certificates.Kernel.Bounds.HNAlt.DceSP
public import CFSG.Certificates.Kernel.DceLoops
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Nat.Bitwise
public import Mathlib.Algebra.Group.End
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.Certificates.DSP

open CFSG.KC.HNA.DceS CFSG.Certificates.DceLoop

set_option exponentiation.threshold 400

theorem andL_iff {a b : Bool} : andB a b = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> decide

theorem orL_iff {a b : Bool} : orB a b = true ↔ a = true ∨ b = true := by
  cases a <;> cases b <;> decide

theorem notL_eq (b : Bool) : notB b = true ↔ b = false := by
  cases b <;> decide

theorem allL_iff (f : ℕ → Bool) : ∀ n,
    Nat.rec (motive := fun _ => Bool) true (fun k ih => andB ih (f k)) n = true ↔ ∀ k < n, f k = true
  | 0 => ⟨fun _ k hk => absurd hk (Nat.not_lt_zero k), fun _ => rfl⟩
  | n + 1 => by
    change andB (Nat.rec (motive := fun _ => Bool) true (fun k ih => andB ih (f k)) n) (f n) = true ↔ _
    rw [andL_iff, allL_iff f n]
    constructor
    · rintro ⟨h1, h2⟩ k hk
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with h | rfl
      · exact h1 k h
      · exact h2
    · intro h
      exact ⟨fun k hk => h k (by omega), h n (by omega)⟩

theorem fld_eq (X i : ℕ) : fld X i = X / 2 ^ (6 * i) % 64 := by
  unfold fld
  change (X >>> (6 * i)) &&& (2 ^ 6 - 1) = _
  rw [land_low, Nat.shiftRight_eq_div_pow]
  rfl

theorem fld_lt (X i : ℕ) : fld X i < 64 := by
  rw [fld_eq]
  exact Nat.mod_lt _ (by norm_num)

@[expose] noncomputable def pack (f : ℕ → ℕ) (k : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) (nat_lit 0)
    (fun i acc => Nat.lor acc (Nat.shiftLeft (f i) (Nat.mul (nat_lit 6) i))) k

theorem mulP_eq (X Y : ℕ) : mulP X Y = pack (fun i => fld Y (fld X i)) 55 := rfl

theorem pack_spec (f : ℕ → ℕ) : ∀ k, (∀ i < k, f i < 64) →
    pack f k < 2 ^ (6 * k) ∧ ∀ j < k, fld (pack f k) j = f j
  | 0, _ => ⟨by change 0 < 1; norm_num, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  | k + 1, hf => by
    obtain ⟨hlt, hfld⟩ := pack_spec f k fun i hi => hf i (by omega)
    have hk := hf k (by omega)
    have e : pack f (k + 1) = pack f k + f k * 2 ^ (6 * k) := by
      change pack f k ||| f k <<< (6 * k) = _
      rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt hlt, Nat.shiftLeft_eq, Nat.add_comm]
    have hp : (2 : ℕ) ^ (6 * (k + 1)) = 2 ^ (6 * k) * 64 := by
      rw [Nat.mul_succ, pow_add]
      norm_num
    refine ⟨?_, fun j hj => ?_⟩
    · rw [e, hp]
      have h1 : f k * 2 ^ (6 * k) ≤ 63 * 2 ^ (6 * k) := Nat.mul_le_mul_right _ (by omega)
      linarith
    · rw [fld_eq, e]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · have h1 := hfld j hj
        rw [fld_eq] at h1
        rw [← h1, ← Nat.mod_mul_right_div_self, ← Nat.mod_mul_right_div_self (pack f k)]
        congr 1
        have hd : 2 ^ (6 * j) * 64 ∣ 2 ^ (6 * k) := by
          rw [show (64 : ℕ) = 2 ^ 6 from rfl, ← pow_add]
          exact Nat.pow_dvd_pow 2 (by omega)
        rw [← Nat.mod_mod_of_dvd (pack f k + f k * 2 ^ (6 * k)) hd,
          ← Nat.mod_mod_of_dvd (pack f k) hd, Nat.add_mul_mod_self_right]
      · rw [Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hlt, Nat.zero_add,
          Nat.mod_eq_of_lt hk]

theorem mod_fld (A k : ℕ) : A % 2 ^ (6 * (k + 1)) = A % 2 ^ (6 * k) + 2 ^ (6 * k) * fld A k := by
  rw [fld_eq, show 6 * (k + 1) = 6 * k + 6 by ring, pow_add, Nat.mod_mul]
  rfl

theorem eq_of_fld {A B : ℕ} (hA : A < 2 ^ 330) (hB : B < 2 ^ 330)
    (h : ∀ i < 55, fld A i = fld B i) : A = B := by
  have key : ∀ k ≤ 55, A % 2 ^ (6 * k) = B % 2 ^ (6 * k) := by
    intro k
    induction k with
    | zero =>
      intro _
      rw [Nat.mul_zero, pow_zero, Nat.mod_one, Nat.mod_one]
    | succ k ih =>
      intro hk
      rw [mod_fld A k, mod_fld B k, ih (by omega), h k (by omega)]
  have := key 55 le_rfl
  rwa [Nat.mod_eq_of_lt hA, Nat.mod_eq_of_lt hB] at this

theorem mulP_fld (X Y : ℕ) {i : ℕ} (hi : i < 55) : fld (mulP X Y) i = fld Y (fld X i) :=
  (pack_spec _ 55 fun _ _ => fld_lt _ _).2 i hi

theorem mulP_lt (X Y : ℕ) : mulP X Y < 2 ^ 330 :=
  (pack_spec _ 55 fun _ _ => fld_lt _ _).1

@[expose] def PV (X : ℕ) : Prop :=
  X < 2 ^ 330 ∧ (∀ i < 55, fld X i < 55) ∧ ∀ i < 55, ∀ j < 55, fld X i = fld X j → i = j

@[expose] noncomputable def pmK (X k : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) B55
    (fun i acc => (fun e => Bool.rec (motive := fun _ => ℕ) (nat_lit 0)
        (Nat.lor acc (Nat.shiftLeft (nat_lit 1) e))
        (andB (Nat.blt (nat_lit 0) acc) (andB (Nat.blt e (nat_lit 55))
          (Nat.beq (Nat.land acc (Nat.shiftLeft (nat_lit 1) e)) (nat_lit 0)))))
      (fld X i)) k

theorem pmask_eq (X : ℕ) : pmask X = pmK X (nat_lit 55) := by
  unfold pmask pmK
  exact Eq.refl _

theorem pmK_inv (X : ℕ) : ∀ k, pmK X k ≠ 0 →
    (∀ i < k, fld X i < 55 ∧ (pmK X k).testBit (fld X i) = true) ∧
      ∀ i < k, ∀ j < k, fld X i = fld X j → i = j
  | 0, _ => ⟨fun i hi => absurd hi (Nat.not_lt_zero i), fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | k + 1, h => by
    have e : pmK X (k + 1) = Bool.rec (motive := fun _ => ℕ) 0
        (Nat.lor (pmK X k) (Nat.shiftLeft 1 (fld X k)))
        (andB (Nat.blt 0 (pmK X k)) (andB (Nat.blt (fld X k) 55)
          (Nat.beq (Nat.land (pmK X k) (Nat.shiftLeft 1 (fld X k))) 0))) := rfl
    rw [e] at h ⊢
    cases hc : andB (Nat.blt 0 (pmK X k)) (andB (Nat.blt (fld X k) 55)
        (Nat.beq (Nat.land (pmK X k) (Nat.shiftLeft 1 (fld X k))) 0))
    · rw [hc] at h
      exact absurd rfl h
    dsimp only
    obtain ⟨c1, c2⟩ := andL_iff.1 hc
    obtain ⟨c2, c3⟩ := andL_iff.1 c2
    have hpos : pmK X k ≠ 0 := by
      have := Nat.blt_eq.mp c1
      omega
    obtain ⟨ih1, ih2⟩ := pmK_inv X k hpos
    have hbit : (pmK X k).testBit (fld X k) = false := by
      have e3 : pmK X k &&& 1 <<< fld X k = 0 := Nat.eq_of_beq_eq_true c3
      rw [Nat.one_shiftLeft, Nat.and_two_pow] at e3
      cases hb : (pmK X k).testBit (fld X k)
      · rfl
      · rw [hb] at e3
        simp at e3
    have hne : ∀ i < k, fld X i ≠ fld X k := fun i hi he => by
      have := (ih1 i hi).2
      rw [he, hbit] at this
      exact absurd this (by decide)
    have tb : ∀ b, (Nat.lor (pmK X k) (Nat.shiftLeft 1 (fld X k))).testBit b =
        ((pmK X k).testBit b || (2 ^ fld X k).testBit b) := fun b => by
      change (pmK X k ||| 1 <<< fld X k).testBit b = _
      rw [Nat.testBit_or, Nat.one_shiftLeft]
    refine ⟨fun i hi => ?_, fun i hi j hj hij => ?_⟩
    · rw [tb]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · rw [(ih1 i hi).2, Bool.true_or]
        exact ⟨(ih1 i hi).1, rfl⟩
      · rw [Nat.testBit_two_pow_self, Bool.or_true]
        exact ⟨Nat.blt_eq.mp c2, rfl⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl <;>
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · exact ih2 i hi j hj hij
      · exact absurd hij (hne i hi)
      · exact absurd hij.symm (hne j hj)
      · rfl

theorem validP_spec {X : ℕ} (h : validP X = true) : PV X := by
  unfold validP at h
  obtain ⟨h1, h2⟩ := andL_iff.1 h
  have e : pmask X = FULL56 := Nat.eq_of_beq_eq_true h2
  rw [pmask_eq] at e
  obtain ⟨i1, i2⟩ := pmK_inv X 55 (by rw [e]; decide)
  exact ⟨Nat.blt_eq.mp h1, fun i hi => (i1 i hi).1, i2⟩

@[expose] noncomputable def pf (X : ℕ) (i : Fin 55) : Fin 55 :=
  ⟨fld X i % 55, Nat.mod_lt _ (by norm_num)⟩

theorem pf_val {X : ℕ} (h : PV X) (i : Fin 55) : (pf X i : ℕ) = fld X i :=
  Nat.mod_eq_of_lt (h.2.1 i i.2)

theorem pf_inj {X : ℕ} (h : PV X) : Function.Injective (pf X) := fun i j e => by
  have e' := congrArg Fin.val e
  rw [pf_val h, pf_val h] at e'
  exact Fin.ext (h.2.2 i i.2 j j.2 e')

@[expose] noncomputable def pm (X : ℕ) : Equiv.Perm (Fin 55) :=
  open scoped Classical in
  if h : PV X then Equiv.ofBijective (pf X) (Finite.injective_iff_bijective.1 (pf_inj h)) else 1

theorem pm_val {X : ℕ} (h : PV X) (i : Fin 55) : (pm X i : ℕ) = fld X i := by
  unfold pm
  rw [dite_eq_left h]
  exact pf_val h i

@[expose] noncomputable def mP (X : ℕ) : Equiv.Perm (Fin 55) := (pm X)⁻¹

theorem mulP_PV {X Y : ℕ} (hX : PV X) (hY : PV Y) : PV (mulP X Y) :=
  ⟨mulP_lt X Y, fun i hi => by rw [mulP_fld X Y hi]; exact hY.2.1 _ (hX.2.1 i hi),
    fun i hi j hj e => by
      rw [mulP_fld X Y hi, mulP_fld X Y hj] at e
      exact hX.2.2 i hi j hj (hY.2.2 _ (hX.2.1 i hi) _ (hX.2.1 j hj) e)⟩

theorem pm_mul {X Y : ℕ} (hX : PV X) (hY : PV Y) : pm (mulP X Y) = pm Y * pm X := by
  refine Equiv.ext fun i => Fin.ext ?_
  rw [pm_val (mulP_PV hX hY), Equiv.Perm.mul_apply, pm_val hY, pm_val hX, mulP_fld X Y i.2]

theorem mP_mul {X Y : ℕ} (hX : PV X) (hY : PV Y) : mP (mulP X Y) = mP X * mP Y := by
  unfold mP
  rw [pm_mul hX hY, mul_inv_rev]

theorem pm_inj {A B : ℕ} (hA : PV A) (hB : PV B) (h : pm A = pm B) : A = B := by
  refine eq_of_fld hA.1 hB.1 fun i hi => ?_
  have e : ((pm A ⟨i, hi⟩ : Fin 55) : ℕ) = pm B ⟨i, hi⟩ := by rw [h]
  rwa [pm_val hA, pm_val hB] at e

theorem mP_inj {A B : ℕ} (hA : PV A) (hB : PV B) (h : mP A = mP B) : A = B :=
  pm_inj hA hB (inv_injective h)

theorem ONEP_eq : ONEP = pack (fun i => i) 55 := by rfl

theorem fld_one {i : ℕ} (hi : i < 55) : fld ONEP i = i := by
  rw [ONEP_eq]
  exact (pack_spec (fun i => i) 55 fun i hi => by omega).2 i hi

theorem one_PV : PV ONEP :=
  ⟨by rw [ONEP_eq]; exact (pack_spec (fun i => i) 55 fun i hi => by omega).1,
    fun i hi => by rw [fld_one hi]; exact hi,
    fun i hi j hj e => by rwa [fld_one hi, fld_one hj] at e⟩

theorem pm_one : pm ONEP = 1 :=
  Equiv.ext fun i => Fin.ext (by rw [pm_val one_PV, fld_one i.2]; rfl)

theorem mP_one : mP ONEP = 1 := by
  unfold mP
  rw [pm_one, inv_one]

@[expose] def Cst (X : ℕ) : Prop := ∀ i < 55, fld X i = fld X 0

theorem cst_zero : Cst 0 := fun i _ => by
  simp [fld_eq]

theorem cst_mul_left {X : ℕ} (Y : ℕ) (h : Cst X) : Cst (mulP X Y) := fun i hi => by
  rw [mulP_fld X Y hi, mulP_fld X Y (by norm_num), h i hi]

theorem cst_mul_right {X Y : ℕ} (hX : PV X) (h : Cst Y) : Cst (mulP X Y) := fun i hi => by
  rw [mulP_fld X Y hi, mulP_fld X Y (by norm_num), h _ (hX.2.1 i hi), h _ (hX.2.1 0 (by norm_num))]

theorem not_cst {X : ℕ} (h : PV X) : ¬Cst X := fun hc =>
  absurd (h.2.2 1 (by norm_num) 0 (by norm_num) (hc 1 (by norm_num))) (by norm_num)

theorem mulP_zero_right (X : ℕ) : mulP X 0 = 0 :=
  eq_of_fld (mulP_lt X 0) (by norm_num) fun i hi => by
    rw [mulP_fld X 0 hi]
    simp [fld_eq]

end CFSG.Certificates.DSP

end
