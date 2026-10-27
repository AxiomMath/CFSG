module

public import Certificates.Data.Kernel.Misc.Sp4Cen
public import CFSG.Certificates.Kernel.Misc.GL4EltSound
public import CFSG.Certificates.Kernel.F4M3BSound
import CFSG.Certificates.Kernel.LocalQTPermSound
public import CFSG.Certificates.Kernel.Misc.KGrpSound

public section

namespace CFSG.KC.Misc.Sp4Cen

open Matrix CFSG.KD.Sp4Cen CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc.GL4
open Certificates.A5GL42 (Mat4 ofCode)

theorem m33825 : ∀ k < 32, Nat.testBit 33825 k = decide (k = 0 ∨ k = 5 ∨ k = 10 ∨ k = 15) := by
  decide

theorem m2114 : ∀ k < 32, Nat.testBit 2114 k = decide (k = 1 ∨ k = 6 ∨ k = 11) := by decide

theorem m132 : ∀ k < 32, Nat.testBit 132 k = decide (k = 2 ∨ k = 7) := by decide

theorem m8 : ∀ k < 32, Nat.testBit 8 k = decide (k = 3) := by decide

theorem m16912 : ∀ k < 32, Nat.testBit 16912 k = decide (k = 4 ∨ k = 9 ∨ k = 14) := by decide

theorem m8448 : ∀ k < 32, Nat.testBit 8448 k = decide (k = 8 ∨ k = 13) := by decide

theorem m4096 : ∀ k < 32, Nat.testBit 4096 k = decide (k = 12) := by decide

theorem trF_bit (a : ℕ) {i j : ℕ} (hi : i < 4) (hj : j < 4) :
    (trF a).testBit (4 * i + j) = a.testBit (4 * j + i) := by
  interval_cases i <;> interval_cases j <;>
    simp [trF, Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftRight,
      m33825, m2114, m132, m8, m16912, m8448, m4096, -Nat.testBit_zero]

theorem ofCode_trF (a : ℕ) : ofCode (trF a) = (ofCode a)ᵀ := by
  ext i j
  simp only [ofCode, Matrix.of_apply, Matrix.transpose_apply, trF_bit a i.2 j.2]

theorem ofCode_formF (w g : ℕ) : ofCode (formF w g) = (ofCode g)ᵀ * ofCode w * ofCode g := by
  rw [formF, mul4F_ofCode, mul4F_ofCode, ofCode_trF, Matrix.mul_assoc]

theorem landE (a b : ℕ) : Nat.land a b = a &&& b := rfl

theorem lorE (a b : ℕ) : Nat.lor a b = a ||| b := rfl

theorem shlE (a b : ℕ) : Nat.shiftLeft a b = a <<< b := rfl

theorem subE (a b : ℕ) : Nat.sub a b = a - b := rfl

theorem powE (a b : ℕ) : Nat.pow a b = a ^ b := rfl

theorem indK_bit (E : ℕ → ℕ) : ∀ n c, (indK E n).testBit c = true ↔ ∃ k < n, E k = c
  | 0, c => by
    change Nat.testBit 0 c = true ↔ _
    simp
  | n + 1, c => by
    have e : indK E (n + 1) = Nat.lor (indK E n) (Nat.shiftLeft 1 (E n)) := rfl
    rw [e, lorE, shlE, Nat.testBit_or, Bool.or_eq_true, indK_bit E n c, Nat.shiftLeft_eq,
      Nat.one_mul, Nat.testBit_two_pow, decide_eq_true_iff]
    constructor
    · rintro (⟨k, hk, rfl⟩ | rfl)
      · exact ⟨k, by omega, rfl⟩
      · exact ⟨n, by omega, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
      · exact Or.inl ⟨k, hk, rfl⟩
      · exact Or.inr rfl

theorem pln16_bit (b c : ℕ) :
    (CFSG.KC.F4M3B.pln b 16).testBit c = (decide (c < 65536) && c.testBit b) := by
  rw [CFSG.KC.F4M3B.pln_bit]
  norm_num

theorem entP_bit {c i j : ℕ} (hc : c < 65536) (hi : i < 4) (hj : j < 4) :
    (entP (fun b => CFSG.KC.F4M3B.pln b 16) i j).testBit c = (mul4F c c).testBit (4 * i + j) := by
  rw [mul4F_bit c c hi hj]
  have e4 : 4 * 1 + j = 4 + j := by omega
  have e8 : 4 * 2 + j = 8 + j := by omega
  have e12 : 4 * 3 + j = 12 + j := by omega
  have e0 : 4 * 0 + j = j := by omega
  have f0 : 4 * i + 0 = 4 * i := by omega
  rw [e4, e8, e12, e0, f0]
  change ((((CFSG.KC.F4M3B.pln (4 * i) 16 &&& CFSG.KC.F4M3B.pln j 16) ^^^
      (CFSG.KC.F4M3B.pln (4 * i + 1) 16 &&& CFSG.KC.F4M3B.pln (4 + j) 16)) ^^^
      ((CFSG.KC.F4M3B.pln (4 * i + 2) 16 &&& CFSG.KC.F4M3B.pln (8 + j) 16) ^^^
      (CFSG.KC.F4M3B.pln (4 * i + 3) 16 &&& CFSG.KC.F4M3B.pln (12 + j) 16)))).testBit c = _
  simp only [Nat.testBit_xor, Nat.testBit_and, pln16_bit, decide_eq_true hc, Bool.true_and,
    Bool.xor_assoc]

theorem id4_bit : ∀ q < 16, id4.testBit q = decide (q / 4 = q % 4) := by decide

theorem sqAcc_bit {c T : ℕ} (hc : c < 65536) (hT : T.testBit c = true) : ∀ n ≤ 16,
    (sqAcc (fun b => CFSG.KC.F4M3B.pln b 16) T n).testBit c = true ↔
      ∀ q < n, (mul4F c c).testBit q = id4.testBit q
  | 0, _ => by
    change T.testBit c = true ↔ _
    simp only [hT, true_iff]
    intro q hq
    omega
  | n + 1, hn => by
    have ih := sqAcc_bit hc hT n (by omega)
    have hq4 : n / 4 < 4 := by omega
    have hq4' : n % 4 < 4 := Nat.mod_lt _ (by norm_num)
    have hq : 4 * (n / 4) + n % 4 = n := Nat.div_add_mod n 4
    have he := entP_bit hc hq4 hq4'
    rw [hq] at he
    have hstep : ∀ b : Bool, (Bool.rec (motive := fun _ => ℕ)
        (Nat.xor T (entP (fun b => CFSG.KC.F4M3B.pln b 16) (n / 4) (n % 4)))
        (entP (fun b => CFSG.KC.F4M3B.pln b 16) (n / 4) (n % 4)) b).testBit c =
        (b == (mul4F c c).testBit n) := by
      intro b
      cases b
      · change (T ^^^ entP (fun b => CFSG.KC.F4M3B.pln b 16) (n / 4) (n % 4)).testBit c = _
        rw [Nat.testBit_xor, hT, he]
        cases (mul4F c c).testBit n <;> rfl
      · change (entP (fun b => CFSG.KC.F4M3B.pln b 16) (n / 4) (n % 4)).testBit c = _
        rw [he]
        cases (mul4F c c).testBit n <;> rfl
    have e : (sqAcc (fun b => CFSG.KC.F4M3B.pln b 16) T (n + 1)).testBit c =
        ((sqAcc (fun b => CFSG.KC.F4M3B.pln b 16) T n).testBit c &&
          (Bool.rec (motive := fun _ => ℕ)
            (Nat.xor T (entP (fun b => CFSG.KC.F4M3B.pln b 16) (n / 4) (n % 4)))
            (entP (fun b => CFSG.KC.F4M3B.pln b 16) (n / 4) (n % 4))
            (Nat.beq (n / 4) (n % 4))).testBit c) :=
      Nat.testBit_and _ _ _
    rw [e, hstep, Bool.and_eq_true, ih]
    have hb : Nat.beq (n / 4) (n % 4) = decide (n / 4 = n % 4) := by
      by_cases h : n / 4 = n % 4
      · rw [h, Nat.beq_refl, decide_eq_true rfl]
      · rw [Bool.eq_false_iff.mpr (fun h' => h (Nat.eq_of_beq_eq_true h')), decide_eq_false h]
    rw [hb]
    constructor
    · rintro ⟨h1, h2⟩ q hq
      rcases Nat.lt_succ_iff_lt_or_eq.mp hq with hq | rfl
      · exact h1 q hq
      · rw [id4_bit q (by omega)]
        revert h2
        cases (mul4F c c).testBit q <;> cases decide (q / 4 = q % 4) <;> simp
    · intro h
      refine ⟨fun q hq => h q (by omega), ?_⟩
      have := h n (by omega)
      rw [id4_bit n (by omega)] at this
      rw [this]
      cases decide (n / 4 = n % 4) <;> rfl

theorem ones_bit' {m c : ℕ} (hc : c < m) : (Nat.sub (Nat.pow 2 m) 1).testBit c = true := by
  rw [subE, powE, Nat.testBit_two_pow_sub_one, decide_eq_true_iff]
  exact hc

theorem ones_bit {c : ℕ} (hc : c < 65536) :
    (Nat.sub (Nat.pow 2 (Nat.pow 2 16)) 1).testBit c = true :=
  ones_bit' (m := Nat.pow 2 16) (lt_of_lt_of_le hc (by rw [powE]; norm_num))

theorem id4_lt : id4 < 65536 := by decide

theorem sqPlane_bit {c : ℕ} (hc : c < 65536) : sqPlane.testBit c = true ↔ mul4F c c = id4 := by
  rw [sqPlane, sqAcc_bit hc (ones_bit hc) 16 le_rfl]
  constructor
  · intro h
    refine Nat.eq_of_testBit_eq fun q => ?_
    by_cases hq : q < 16
    · exact h q hq
    · rw [testBit_ge16 (mul4F_lt c c) (by omega), testBit_ge16 id4_lt (by omega)]
  · intro h q _
    rw [h]

theorem invK_sound {RI : ℕ → ℕ} (h : invK RI = true) :
    (∀ k < 315, xOf RI k < xOf RI (k + 1)) ∧
      ∀ c < 65536, mul4F c c = id4 ↔ ∃ k < 316, xOf RI k = c := by
  rw [invK, andB_iff, allN_iff] at h
  refine ⟨fun k hk => Nat.le_of_ble_eq_true (h.1 k hk), fun c hc => ?_⟩
  rw [← sqPlane_bit hc, Nat.eq_of_beq_eq_true h.2, indK_bit]

open Certificates.GL4 (GL4) in
theorem f16_lt (r i : ℕ) : f16 r i < 65536 := by
  change Nat.land _ 65535 < 65536
  rw [landE]
  exact lt_of_le_of_lt Nat.and_le_right (by norm_num)

open Certificates.GL4 (GL4) in
theorem invW_sound {g gi : ℕ} (hg : g < 65536) (hgi : gi < 65536) (h : invW g gi = true) :
    ∃ u : GL4, enc4 u = g ∧ enc4 u⁻¹ = gi := by
  rw [invW, andB_iff] at h
  have h1 := Nat.eq_of_beq_eq_true h.1
  have h2 := Nat.eq_of_beq_eq_true h.2
  let u : GL4 := ⟨ofCode g, ofCode gi, by rw [← mul4F_ofCode, h1, ofCode_id4],
    by rw [← mul4F_ofCode, h2, ofCode_id4]⟩
  exact ⟨u, code4_ofCode hg, code4_ofCode hgi⟩

open Certificates.GL4 (GL4) in
theorem relB_iff (u v : GL4) (n : ℕ) : relB (enc4 u) (enc4 v) n = true ↔ (u * v) ^ n = 1 := by
  rw [relB, ← gl4_enc.enc_mul, pow4F_enc]
  constructor
  · intro h
    exact enc4_eq_id4.1 (Nat.eq_of_beq_eq_true h)
  · intro h
    rw [enc4_eq_id4.2 h]
    exact Nat.beq_refl _

open Certificates.GL4 (GL4) in
theorem conjF_enc (g x : GL4) : conjF (enc4 g) (enc4 x) (enc4 g⁻¹) = enc4 (g * x * g⁻¹) := by
  rw [conjF, ← gl4_enc.enc_mul, ← gl4_enc.enc_mul]

open Certificates.GL4 (GL4) in
theorem ofCode_formF_enc (w : ℕ) (g : GL4) :
    ofCode (formF w (enc4 g)) = (g : Mat4)ᵀ * ofCode w * (g : Mat4) := by
  rw [ofCode_formF, ← coe_eq_of_enc4 rfl]

theorem wordE_mem {H : Subgroup (GL (Fin 4) (ZMod 2))} {L : ℕ → ℕ}
    (hL : ∀ i, ∃ g ∈ H, enc4 g = L i) :
    ∀ fuel acc w, (∃ g ∈ H, enc4 g = acc) → ∃ g ∈ H, enc4 g = wordE L fuel acc w
  | 0, _, _, h => h
  | fuel + 1, acc, w, ⟨g, hg, e⟩ => by
    have hs : wordE L (fuel + 1) acc w = Bool.rec (motive := fun _ => ℕ)
        (wordE L fuel (mul4F acc (L (Nat.pred (Nat.land w 7)))) (Nat.shiftRight w 3)) acc
        (Nat.beq (Nat.land w 7) 0) := rfl
    rw [hs]
    cases Nat.beq (Nat.land w 7) 0
    · obtain ⟨x, hx, ex⟩ := hL (Nat.pred (Nat.land w 7))
      refine wordE_mem hL fuel _ _ ⟨g * x, H.mul_mem hg hx, ?_⟩
      rw [← e, ← ex]
      exact gl4_enc.enc_mul g x
    · exact ⟨g, hg, e⟩

end CFSG.KC.Misc.Sp4Cen

end
