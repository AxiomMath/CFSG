module

public import CFSG.Certificates.Kernel.LyOmega.Defs
public import Certificates.Data.Kernel.LyOmega.Base
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Std.Tactic.BVDecide.Normalize.BitVec
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.KS.LyOm.Pack

open CFSG.KC.LyOm CFSG.KC.LL CFSG.KS.LyOm

@[expose] noncomputable def packR (f o : ℕ → ℕ) (n : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun t acc => Nat.lor acc (Nat.shiftLeft (f t) (o t))) n

theorem packR_tb (f o : ℕ → ℕ) (b : ℕ) : ∀ n, (packR f o n).testBit b = true ↔
    ∃ t < n, o t ≤ b ∧ (f t).testBit (b - o t) = true
  | 0 => by simp [packR]
  | n + 1 => by
    have e : packR f o (n + 1) = Nat.lor (packR f o n) (Nat.shiftLeft (f n) (o n)) := rfl
    rw [e, Nat.lor_eq, Nat.testBit_or, Bool.or_eq_true, packR_tb f o b n]
    change _ ∨ (f n <<< o n).testBit b = true ↔ _
    rw [Nat.testBit_shiftLeft]
    constructor
    · rintro (⟨t, ht, h⟩ | h)
      · exact ⟨t, by omega, h⟩
      · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        exact ⟨n, by omega, h⟩
    · rintro ⟨t, ht, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | rfl
      · exact Or.inl ⟨t, ht, h⟩
      · right
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        exact h

theorem packR_lane_tb {w n : ℕ} {f π : ℕ → ℕ} (hf : ∀ t < n, f t < 2 ^ w) (L q : ℕ) (hq : q < w) :
    (packR f (fun t => w * π t) n).testBit (w * L + q) = true ↔
      ∃ t < n, π t = L ∧ (f t).testBit q = true := by
  rw [packR_tb]
  constructor
  · rintro ⟨t, ht, hle, hb⟩
    rcases lt_trichotomy (π t) L with h | h | h
    · exfalso
      have h1 : w ≤ w * L + q - w * π t := by
        have : w * (π t + 1) ≤ w * L := Nat.mul_le_mul_left _ h
        rw [Nat.mul_succ] at this
        omega
      have := Nat.testBit_lt_two_pow (lt_of_lt_of_le (hf t ht) (Nat.pow_le_pow_right (by omega) h1))
      rw [this] at hb
      exact absurd hb (by simp)
    · refine ⟨t, ht, h, ?_⟩
      rw [h] at hb
      simpa using hb
    · exfalso
      have : w * (L + 1) ≤ w * π t := Nat.mul_le_mul_left _ h
      rw [Nat.mul_succ] at this
      omega
  · rintro ⟨t, ht, rfl, hb⟩
    exact ⟨t, ht, by omega, by simpa using hb⟩

theorem lane_eq_of_tb {X Y w : ℕ} (hY : Y < 2 ^ w)
    (h : ∀ q < w, X.testBit q = Y.testBit q) : X % 2 ^ w = Y := by
  apply Nat.eq_of_testBit_eq
  intro q
  rw [Nat.testBit_mod_two_pow]
  by_cases hq : q < w
  · simp [hq, h q hq]
  · simp only [hq, decide_false, Bool.false_and]
    exact (Nat.testBit_lt_two_pow (lt_of_lt_of_le hY (Nat.pow_le_pow_right (by omega) (by omega)))).symm

theorem div_tb (X a q : ℕ) : (X / 2 ^ a).testBit q = X.testBit (a + q) := by
  rw [Nat.testBit_div_two_pow, add_comm]

theorem packR_lane {w n : ℕ} {f π : ℕ → ℕ} (hf : ∀ t < n, f t < 2 ^ w)
    (hπ : ∀ t < n, ∀ t' < n, π t = π t' → t = t') {t : ℕ} (ht : t < n) :
    packR f (fun t => w * π t) n / 2 ^ (w * π t) % 2 ^ w = f t := by
  refine lane_eq_of_tb (hf t ht) fun q hq => ?_
  rw [div_tb]
  apply Bool.eq_iff_iff.2
  rw [packR_lane_tb hf _ _ hq]
  constructor
  · rintro ⟨t', ht', e, hb⟩
    rw [hπ t' ht' t ht e] at hb
    exact hb
  · intro hb
    exact ⟨t, ht, rfl, hb⟩

theorem packR_lane_zero {w n : ℕ} {f π : ℕ → ℕ} (hf : ∀ t < n, f t < 2 ^ w) {L : ℕ}
    (hL : ∀ t < n, π t ≠ L) : packR f (fun t => w * π t) n / 2 ^ (w * L) % 2 ^ w = 0 := by
  refine lane_eq_of_tb (by positivity) fun q hq => ?_
  rw [div_tb, Nat.zero_testBit]
  apply Bool.eq_false_iff.2
  intro hb
  obtain ⟨t, ht, e, -⟩ := (packR_lane_tb hf _ _ hq).1 hb
  exact hL t ht e

theorem packR_lt {w n m : ℕ} {f π : ℕ → ℕ} (hf : ∀ t < n, f t < 2 ^ w) (hπ : ∀ t < n, π t < m) :
    packR f (fun t => w * π t) n < 2 ^ (w * m) := by
  apply Nat.lt_pow_two_of_testBit
  intro b hb
  apply Bool.eq_false_iff.2
  intro h
  rw [packR_tb] at h
  obtain ⟨t, ht, hle, hbit⟩ := h
  have h1 : w * (π t + 1) ≤ w * m := Nat.mul_le_mul_left _ (hπ t ht)
  rw [Nat.mul_succ] at h1
  have h2 : w ≤ b - w * π t := by omega
  rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (hf t ht) (Nat.pow_le_pow_right (by omega) h2))] at hbit
  exact absurd hbit (by simp)

theorem fldW_eq' (r o w : ℕ) : fldW r o w = r / 2 ^ o % 2 ^ w := by
  change (r >>> o) &&& ((1 <<< w) - 1) = _
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, one_mul]
  exact Nat.and_two_pow_sub_one_eq_mod _ _

theorem sEnt_lt (X i j : ℕ) : sEnt X i j < 2 ^ 11 := by
  unfold sEnt
  rw [fldW_eq']
  exact Nat.mod_lt _ (by positivity)

theorem sEnt_eq (X i j : ℕ) : sEnt X i j = X / 2 ^ (77 * i + 11 * j) % 2 ^ 11 := by
  unfold sEnt
  rw [fldW_eq']
  rfl

theorem sTr_eq (X : ℕ) : sTr X = packR (fun t => sEnt X (t / 7) (t % 7))
    (fun t => 11 * (7 * (t % 7) + t / 7)) 49 := by
  unfold sTr packR
  congr 1

theorem sTr_sound {X : ℕ} (hX : LCanon 11 7 7 X) :
    LCanon 11 7 7 (sTr X) ∧ smM (sTr X) = (smM X).transpose := by
  have hf : ∀ t < 49, sEnt X (t / 7) (t % 7) < 2 ^ 11 := fun t _ => sEnt_lt _ _ _
  have hπ : ∀ t < 49, ∀ t' < 49, 7 * (t % 7) + t / 7 = 7 * (t' % 7) + t' / 7 → t = t' := by
    intro t ht t' ht' e
    omega
  have hlane : ∀ i < 7, ∀ j < 7, sTr X / 2 ^ (77 * i + 11 * j) % 2 ^ 11 =
      X / 2 ^ (77 * j + 11 * i) % 2 ^ 11 := by
    intro i hi j hj
    have e1 : 77 * i + 11 * j = 11 * (7 * ((7 * j + i) % 7) + (7 * j + i) / 7) := by omega
    rw [sTr_eq, e1, packR_lane hf hπ (by omega), sEnt_eq]
    congr 3 <;> omega
  refine ⟨⟨?_, fun i hi j hj => ?_⟩, ?_⟩
  · rw [sTr_eq, show 11 * 7 * 7 = 11 * 49 by norm_num]
    exact packR_lt (π := fun t => 7 * (t % 7) + t / 7) hf (fun t ht => by omega)
  · have e : 11 * 7 * i + 11 * j = 77 * i + 11 * j := by ring
    rw [e, hlane i hi j hj]
    have := hX.2 j hj i hi
    have e2 : 11 * 7 * j + 11 * i = 77 * j + 11 * i := by ring
    rwa [e2] at this
  · funext i j
    simp only [smM, ent, Matrix.transpose_apply]
    rw [hlane i i.2 j j.2]

theorem toBig_eq (X : ℕ) : toBig X = packR (fun t => sEnt X (t / 7) (t % 7))
    (fun t => 12 * (111 * (t / 7) + t % 7)) 49 := by
  unfold toBig packR
  congr 1

@[expose] def padM (M : Matrix (Fin 7) (Fin 7) (ZMod 5)) : Matrix (Fin 111) (Fin 111) (ZMod 5) :=
  fun i j => if h : i.val < 7 ∧ j.val < 7 then M ⟨i.val, h.1⟩ ⟨j.val, h.2⟩ else 0

theorem toBig_sound {X : ℕ} (hX : LCanon 11 7 7 X) :
    LCanon 12 111 111 (toBig X) ∧ bigM (toBig X) = padM (smM X) := by
  have hf : ∀ t < 49, sEnt X (t / 7) (t % 7) < 2 ^ 12 :=
    fun t _ => lt_trans (sEnt_lt _ _ _) (by norm_num)
  have hπ : ∀ t < 49, ∀ t' < 49, 111 * (t / 7) + t % 7 = 111 * (t' / 7) + t' % 7 → t = t' := by
    intro t ht t' ht' e
    omega
  have hin : ∀ i < 7, ∀ j < 7, toBig X / 2 ^ (1332 * i + 12 * j) % 2 ^ 12 =
      X / 2 ^ (77 * i + 11 * j) % 2 ^ 11 := by
    intro i hi j hj
    have e1 : 1332 * i + 12 * j = 12 * (111 * ((7 * i + j) / 7) + (7 * i + j) % 7) := by omega
    rw [toBig_eq, e1, packR_lane hf hπ (by omega), sEnt_eq]
    congr 3 <;> omega
  have hout : ∀ i < 111, ∀ j < 111, ¬ (i < 7 ∧ j < 7) →
      toBig X / 2 ^ (1332 * i + 12 * j) % 2 ^ 12 = 0 := by
    intro i hi j hj hn
    have e1 : 1332 * i + 12 * j = 12 * (111 * i + j) := by ring
    rw [toBig_eq, e1]
    exact packR_lane_zero hf fun t ht e => hn (by omega)
  refine ⟨⟨?_, fun i hi j hj => ?_⟩, ?_⟩
  · rw [toBig_eq, show 12 * 111 * 111 = 12 * 12321 by norm_num]
    exact packR_lt (π := fun t => 111 * (t / 7) + t % 7) hf (fun t ht => by omega)
  · have e : 12 * 111 * i + 12 * j = 1332 * i + 12 * j := by ring
    rw [e]
    by_cases h : i < 7 ∧ j < 7
    · rw [hin i h.1 j h.2]
      have := hX.2 i h.1 j h.2
      have e2 : 11 * 7 * i + 11 * j = 77 * i + 11 * j := by ring
      rwa [e2] at this
    · rw [hout i hi j hj h]
      norm_num
  · funext i j
    simp only [bigM, ent, padM]
    by_cases h : i.val < 7 ∧ j.val < 7
    · rw [dif_pos h, hin i.val h.1 j.val h.2]
      rfl
    · rw [dif_neg h, hout i.val i.2 j.val j.2 h]
      rfl

end CFSG.KS.LyOm.Pack

end
