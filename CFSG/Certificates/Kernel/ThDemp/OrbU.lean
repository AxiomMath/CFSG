
module

public import CFSG.Certificates.Kernel.ThDemp.OrbPtsBase
import Mathlib.Tactic.IntervalCases

public section

namespace CFSG.Certificates.ThDemp.USp

open MulAction CFSG.KC.Th CFSG.KC.Th.BigS CFSG.KC.Th.Spec CFSG.KC.ThDemp CFSG.KC.Loop
  CFSG.Certificates.ThDemp.Act CFSG.Certificates.ThDemp.Lanes CFSG.Certificates.ThDemp.Batches
  CFSG.Certificates.ThDemp.Key CFSG.Certificates.ThDemp.Rows

set_option exponentiation.threshold 2000

variable {D : DempData}

theorem stackN_succ (s m : ℕ) (F : ℕ → ℕ) : stackN s (m + 1) F = stackN s m F ||| F m <<< (s * m) :=
  rfl

theorem stackN_congr (s : ℕ) {F G : ℕ → ℕ} : ∀ m, (∀ k < m, F k = G k) → stackN s m F = stackN s m G
  | 0, _ => rfl
  | m + 1, h => by
    rw [stackN_succ, stackN_succ, stackN_congr s m (fun k hk => h k (by omega)), h m (by omega)]

theorem row_stackN {F : ℕ → ℕ} {m : ℕ} (hF : ∀ k < m, F k < 2 ^ 248) {k : ℕ} (hk : k < m) :
    (stackN 256 m F >>> (256 * k)) &&& (2 ^ 248 - 1) = F k := by
  set F' : ℕ → ℕ := fun k => if k < m then F k else 0
  have hF' : ∀ k, F' k < 2 ^ 256 := fun k => by
    simp only [F']
    split_ifs with h
    · exact Nat.lt_of_lt_of_le (hF k h) (Nat.pow_le_pow_right (by omega) (by omega))
    · exact Nat.two_pow_pos _
  rw [stackN_congr 256 m (G := F') (fun k hk => by simp [F', hk])]
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one,
    testBit_stackN_s (by omega) hF']
  by_cases hj : j < 248
  · have e1 : (256 * k + j) / 256 = k := by omega
    have e2 : (256 * k + j) % 256 = j := by omega
    simp [e1, e2, hk, hj, F']
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (hF k hk) (Nat.pow_le_pow_right (by omega)
      (by omega)))]
    simp [hj]

theorem rowsOf_U0 (hbv : ∀ l < 5, D.bvL l < 2 ^ 248) :
    rowsOf (2 ^ 248 - 1) (U0 D) = [D.bvL 0, D.bvL 1, D.bvL 2, D.bvL 3, D.bvL 4] := by
  have h := fun k (hk : k < 5) => row_stackN (F := D.bvL) (m := 5) hbv hk
  have h0 : Nat.land (U0 D) (2 ^ 248 - 1) = D.bvL 0 := by
    have := h 0 (by omega)
    simp only [Nat.mul_zero, Nat.shiftRight_zero] at this
    exact this
  have h1 : Nat.land (Nat.shiftRight (U0 D) 256) (2 ^ 248 - 1) = D.bvL 1 := h 1 (by omega)
  have h2 : Nat.land (Nat.shiftRight (U0 D) 512) (2 ^ 248 - 1) = D.bvL 2 := h 2 (by omega)
  have h3 : Nat.land (Nat.shiftRight (U0 D) 768) (2 ^ 248 - 1) = D.bvL 3 := h 3 (by omega)
  have h4 : Nat.land (Nat.shiftRight (U0 D) 1024) (2 ^ 248 - 1) = D.bvL 4 := h 4 (by omega)
  change [Nat.land (U0 D) _, Nat.land (Nat.shiftRight (U0 D) 256) _, Nat.land (Nat.shiftRight (U0 D) 512) _,
    Nat.land (Nat.shiftRight (U0 D) 768) _, Nat.land (Nat.shiftRight (U0 D) 1024) _] = _
  rw [h0, h1, h2, h3, h4]

@[expose] noncomputable def uVecN (D : DempData) (c n : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun k acc => Nat.xor acc (Nat.mul (bitsN c k 1) (D.bvL k))) n

theorem uVec_eq (c : ℕ) : uVec D c = uVecN D c 5 := rfl

theorem uVecN_succ (c n : ℕ) : uVecN D c (n + 1) = uVecN D c n ^^^ bitsN c n 1 * D.bvL n := rfl

theorem uVecN_congr {c c' : ℕ} : ∀ n, (∀ k < n, bitsN c k 1 = bitsN c' k 1) →
    uVecN D c n = uVecN D c' n
  | 0, _ => rfl
  | n + 1, h => by
    rw [uVecN_succ, uVecN_succ, uVecN_congr n (fun k hk => h k (by omega)), h n (by omega)]

theorem bitsN_one (c k : ℕ) : bitsN c k 1 = c / 2 ^ k % 2 := by
  rw [bitsN_eq, Nat.shiftRight_eq_div_pow, pow_one]

theorem bitsN_one_lt (c k : ℕ) : bitsN c k 1 < 2 := by
  rw [bitsN_one]
  exact Nat.mod_lt _ (by omega)

theorem pkVec_bit {t : ℕ} (ht : t < 2) (b : ℕ) : pkVec (t * b) = (t : ZMod 2) • pkVec b := by
  rcases (by omega : t = 0 ∨ t = 1) with rfl | rfl
  · rw [Nat.zero_mul, pkVec_zero, Nat.cast_zero, zero_smul]
  · rw [Nat.one_mul, Nat.cast_one, one_smul]

@[expose] noncomputable def Sn (D : DempData) (n : ℕ) : Submodule (ZMod 2) (Fin 248 → ZMod 2) :=
  Submodule.span (ZMod 2) {v | ∃ k < n, v = pkVec (D.bvL k)}

theorem Sn_succ (n : ℕ) : Sn D (n + 1) = Sn D n ⊔ (ZMod 2) ∙ pkVec (D.bvL n) := by
  rw [Sn, Sn, sup_comm, ← Submodule.span_insert]
  congr 1
  ext v
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff]
  constructor
  · rintro ⟨k, hk, rfl⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · exact Or.inr ⟨k, hk, rfl⟩
    · exact Or.inl rfl
  · rintro (rfl | ⟨k, hk, rfl⟩)
    · exact ⟨n, by omega, rfl⟩
    · exact ⟨k, by omega, rfl⟩

theorem bits_add_low {c' t n k : ℕ} (hk : k < n) : bitsN (c' + t * 2 ^ n) k 1 = bitsN c' k 1 := by
  rw [bitsN_one, bitsN_one]
  have e : t * 2 ^ n = 2 ^ k * (2 * (t * 2 ^ (n - k - 1))) := by
    rw [← mul_assoc, ← mul_assoc, mul_comm (2 ^ k * 2) t, mul_assoc t, ← pow_succ, ← pow_add]
    congr 2
    omega
  rw [e, Nat.add_mul_div_left _ _ (Nat.two_pow_pos k), Nat.add_mul_mod_self_left]

theorem bits_add_top {c' t n : ℕ} (hc : c' < 2 ^ n) (ht : t < 2) : bitsN (c' + t * 2 ^ n) n 1 = t := by
  rw [bitsN_one, mul_comm, Nat.add_mul_div_left _ _ (Nat.two_pow_pos n), Nat.div_eq_of_lt hc,
    Nat.zero_add, Nat.mod_eq_of_lt ht]

theorem exists_uVecN : ∀ n, ∀ w ∈ Sn D n, ∃ c < 2 ^ n, w = pkVec (uVecN D c n)
  | 0, w, hw => by
    have : Sn D 0 = ⊥ := by
      rw [Sn, Submodule.span_eq_bot]
      rintro v ⟨k, hk, -⟩
      omega
    rw [this, Submodule.mem_bot] at hw
    exact ⟨0, by norm_num, by rw [hw]; exact pkVec_zero.symm⟩
  | n + 1, w, hw => by
    rw [Sn_succ, Submodule.mem_sup] at hw
    obtain ⟨w', hw', y, hy, rfl⟩ := hw
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hy
    obtain ⟨c', hc', e⟩ := exists_uVecN n w' hw'
    have ht : t.val < 2 := ZMod.val_lt t
    refine ⟨c' + t.val * 2 ^ n, ?_, ?_⟩
    · rw [pow_succ]
      have : t.val * 2 ^ n ≤ 1 * 2 ^ n := Nat.mul_le_mul_right _ (by omega)
      omega
    · rw [uVecN_succ, pkVec_xor, uVecN_congr n (fun k hk => bits_add_low hk), ← e,
        bits_add_top hc' ht, pkVec_bit ht, ZMod.natCast_zmod_val]

theorem exists_uVec (hbv : ∀ l < 5, D.bvL l < 2 ^ 248) {w : Fin 248 → ZMod 2}
    (hw : w ∈ (sp (U0 D) : Submodule (ZMod 2) (Fin 248 → ZMod 2))) :
    ∃ c < 32, w = pkVec (uVec D c) := by
  have e : (sp (U0 D) : Submodule (ZMod 2) (Fin 248 → ZMod 2)) = Sn D 5 := by
    change spanL _ = _
    rw [spanL, rowsOf_U0 hbv, Sn]
    congr 1
    ext v
    simp only [List.mem_cons, List.not_mem_nil, or_false, Set.mem_setOf_eq]
    constructor
    · rintro ⟨b, hb, rfl⟩
      rcases hb with rfl | rfl | rfl | rfl | rfl
      · exact ⟨0, by omega, rfl⟩
      · exact ⟨1, by omega, rfl⟩
      · exact ⟨2, by omega, rfl⟩
      · exact ⟨3, by omega, rfl⟩
      · exact ⟨4, by omega, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      refine ⟨D.bvL k, ?_, rfl⟩
      interval_cases k <;> simp
  rw [e] at hw
  obtain ⟨c, hc, h⟩ := exists_uVecN 5 w hw
  exact ⟨c, by simpa using hc, h⟩

theorem uVecN_lt (hbv : ∀ l < 5, D.bvL l < 2 ^ 248) (c : ℕ) : ∀ n ≤ 5, uVecN D c n < 2 ^ 248
  | 0, _ => Nat.two_pow_pos _
  | n + 1, hn => by
    rw [uVecN_succ]
    refine Nat.xor_lt_two_pow (uVecN_lt hbv c n (by omega)) ?_
    rcases (by have := bitsN_one_lt c n; omega : bitsN c n 1 = 0 ∨ bitsN c n 1 = 1) with h | h
    · rw [h, Nat.zero_mul]
      exact Nat.two_pow_pos _
    · rw [h, Nat.one_mul]
      exact hbv n (by omega)

theorem uVec_lt (hbv : ∀ l < 5, D.bvL l < 2 ^ 248) (c : ℕ) : uVec D c < 2 ^ 248 :=
  uVecN_lt hbv c 5 le_rfl

theorem uVecN_mem : ∀ (c n : ℕ), pkVec (uVecN D c n) ∈ Sn D n
  | c, 0 => by
    change pkVec 0 ∈ _
    rw [pkVec_zero]
    exact Submodule.zero_mem _
  | c, n + 1 => by
    rw [uVecN_succ, pkVec_xor, pkVec_bit (bitsN_one_lt c n), Sn_succ]
    exact Submodule.add_mem_sup (uVecN_mem c n) (Submodule.smul_mem _ _
      (Submodule.mem_span_singleton_self _))

theorem uVec_mem (hbv : ∀ l < 5, D.bvL l < 2 ^ 248) (c : ℕ) :
    pkVec (uVec D c) ∈ (sp (U0 D) : Submodule (ZMod 2) (Fin 248 → ZMod 2)) := by
  have e : (sp (U0 D) : Submodule (ZMod 2) (Fin 248 → ZMod 2)) = Sn D 5 := by
    change spanL _ = _
    rw [spanL, rowsOf_U0 hbv, Sn]
    congr 1
    ext v
    simp only [List.mem_cons, List.not_mem_nil, or_false, Set.mem_setOf_eq]
    constructor
    · rintro ⟨b, hb, rfl⟩
      rcases hb with rfl | rfl | rfl | rfl | rfl
      · exact ⟨0, by omega, rfl⟩
      · exact ⟨1, by omega, rfl⟩
      · exact ⟨2, by omega, rfl⟩
      · exact ⟨3, by omega, rfl⟩
      · exact ⟨4, by omega, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      refine ⟨D.bvL k, ?_, rfl⟩
      interval_cases k <;> simp
  rw [e]
  exact uVecN_mem c 5

theorem rowAt_eq (M c : ℕ) (hrm : D.rm = 2 ^ 248 - 1) :
    rowAt D M c = (M >>> (256 * c)) &&& (2 ^ 248 - 1) := by
  unfold rowAt
  rw [hrm]
  rfl

theorem rowAt_uAll (hrm : D.rm = 2 ^ 248 - 1) (hbv : ∀ l < 5, D.bvL l < 2 ^ 248) {c : ℕ}
    (hc : c < 32) : rowAt D (uAll D) c = uVec D c := by
  rw [rowAt_eq _ _ hrm]
  exact row_stackN (fun k _ => uVec_lt hbv k) hc

theorem rowAt_mulB (hrm : D.rm = 2 ^ 248 - 1) (A X : ℕ) {c : ℕ} (hc : c < 32) :
    rowAt D (mulB (cR 32) D.rm A X) c = vecB (2 ^ 248 - 1) (rowAt D A c) X := by
  rw [rowAt_eq _ _ hrm, rowAt_eq _ _ hrm, hrm, cR_eq]
  exact row_mulB hc A X

theorem rowAt_xor (hrm : D.rm = 2 ^ 248 - 1) (A B c : ℕ) :
    rowAt D (A ^^^ B) c = rowAt D A c ^^^ rowAt D B c := by
  rw [rowAt_eq _ _ hrm, rowAt_eq _ _ hrm, rowAt_eq _ _ hrm]
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_xor]
  cases A.testBit (256 * c + j) <;> cases B.testBit (256 * c + j) <;>
    cases (2 ^ 248 - 1 : ℕ).testBit j <;> rfl

theorem rowAt_zero (c : ℕ) : rowAt D 0 c = 0 := by
  unfold rowAt
  simp

theorem eqRows_eq (A B : ℕ) :
    eqRows D A B = ((Finset.range 32).filter (fun c => rowAt D A c = rowAt D B c)).card := by
  unfold eqRows
  rw [Unfold.card_filter_of_sumBelow (by norm_num)]
  congr 1

end CFSG.Certificates.ThDemp.USp

end
