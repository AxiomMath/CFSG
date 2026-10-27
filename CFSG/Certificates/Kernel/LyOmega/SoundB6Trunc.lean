module

public import CFSG.Certificates.Kernel.LyOmega.Defs
public import CFSG.Certificates.Kernel.Spor.OrdSound
import all CFSG.Certificates.Kernel.Spor.OrdSound
public import Certificates.Data.Kernel.LyOmega.Small

public section
namespace CFSG.KS.LyOm.SB6T
open CFSG.KC.LyOm CFSG.KC.Ord CFSG.KC.LL CFSG.KS.LyOm CFSG.KC.Loop CFSG.KS.Ord

private theorem lor_split {w a h' y H' : ℕ} (ha : a < 2 ^ w) (hh : h' < 2 ^ w) :
    (2 ^ w * y + a) ||| (2 ^ w * H' + h') = 2 ^ w * (y ||| H') + (a ||| h') := by
  apply Nat.eq_of_testBit_eq
  intro i
  have hlt : a ||| h' < 2 ^ w := Nat.or_lt_two_pow ha hh
  rw [Nat.testBit_or, Nat.testBit_two_pow_mul_add _ ha, Nat.testBit_two_pow_mul_add _ hh,
    Nat.testBit_two_pow_mul_add _ hlt]
  split_ifs <;> simp

private theorem land_split {w a h' y H' : ℕ} (ha : a < 2 ^ w) (hh : h' < 2 ^ w) :
    (2 ^ w * y + a) &&& (2 ^ w * H' + h') = 2 ^ w * (y &&& H') + (a &&& h') := by
  apply Nat.eq_of_testBit_eq
  intro i
  have hlt : a &&& h' < 2 ^ w := Nat.lt_of_le_of_lt Nat.and_le_left ha
  rw [Nat.testBit_and, Nat.testBit_two_pow_mul_add _ ha, Nat.testBit_two_pow_mul_add _ hh,
    Nat.testBit_two_pow_mul_add _ hlt]
  split_ifs <;> simp

private noncomputable def Ln (w n : ℕ) : ℕ := ∑ t ∈ Finset.range n, 2 ^ (w * t)

private noncomputable def Hn (w n : ℕ) : ℕ := Ln w n * 2 ^ (w - 1)

private theorem Ln_zero (w : ℕ) : Ln w 0 = 0 := by simp [Ln]

private theorem Ln_succ (w n : ℕ) : Ln w (n + 1) = 1 + 2 ^ w * Ln w n := by
  unfold Ln
  rw [Finset.sum_range_succ', Finset.mul_sum]
  simp only [Nat.mul_zero, pow_zero]
  rw [Nat.add_comm]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Nat.mul_succ, pow_add, Nat.mul_comm]

private noncomputable def mm (w c L H x : ℕ) : ℕ := (((x ||| H) - c * L) &&& H) >>> (w - 1)

private theorem csub_eq (w L H c x : ℕ) : csub w L H c x = x - mm w c L H x * c := rfl

private noncomputable def flag (w c a : ℕ) : ℕ := (((a ||| 2 ^ (w - 1)) - c) &&& 2 ^ (w - 1)) >>> (w - 1)

private theorem and_h {w u : ℕ} (hw : 0 < w) (hu : u < 2 ^ w) :
    u &&& 2 ^ (w - 1) = if 2 ^ (w - 1) ≤ u then 2 ^ (w - 1) else 0 :=
  and_top (by rw [← two_pow_pred hw]; exact hu)

private theorem flag_eq {w c a : ℕ} (hw : 0 < w) (ha : a < 2 ^ w) :
    flag w c a = if 2 ^ (w - 1) ≤ (a ||| 2 ^ (w - 1)) - c then 1 else 0 := by
  have hh : 2 ^ (w - 1) < 2 ^ w := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hlt : (a ||| 2 ^ (w - 1)) - c < 2 ^ w :=
    Nat.lt_of_le_of_lt (Nat.sub_le _ _) (Nat.or_lt_two_pow ha hh)
  unfold flag
  rw [and_h hw hlt, Nat.shiftRight_eq_div_pow]
  split_ifs
  · exact Nat.div_self (Nat.two_pow_pos _)
  · simp

private theorem flag_mul_le {w c a : ℕ} (hw : 0 < w) (hc : c ≤ 2 ^ (w - 1)) (ha : a < 2 ^ w) :
    flag w c a * c ≤ a := by
  rw [flag_eq hw ha]
  split_ifs with h
  · by_cases hah : 2 ^ (w - 1) ≤ a
    · omega
    · rw [or_top (by omega)] at h
      omega
  · simp

private theorem Dstep {w c n a y : ℕ} (hw : 0 < w) (hc : c ≤ 2 ^ (w - 1)) (ha : a < 2 ^ w) :
    (((2 ^ w * y + a) ||| Hn w (n + 1)) - c * Ln w (n + 1)) &&& Hn w (n + 1) =
      2 ^ w * (((y ||| Hn w n) - c * Ln w n) &&& Hn w n) +
        (((a ||| 2 ^ (w - 1)) - c) &&& 2 ^ (w - 1)) := by
  have hh : 2 ^ (w - 1) < 2 ^ w := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have eH : Hn w (n + 1) = 2 ^ w * Hn w n + 2 ^ (w - 1) := by
    unfold Hn; rw [Ln_succ]; ring
  have eL : c * Ln w (n + 1) = 2 ^ w * (c * Ln w n) + c := by
    rw [Ln_succ]; ring
  rw [eH, eL, lor_split ha hh]
  have hA : c ≤ a ||| 2 ^ (w - 1) := Nat.le_trans hc Nat.right_le_or
  have hY : c * Ln w n ≤ y ||| Hn w n := by
    refine Nat.le_trans ?_ Nat.right_le_or
    unfold Hn
    rw [Nat.mul_comm c]
    exact Nat.mul_le_mul_left _ hc
  have e3 : (2 ^ w * (y ||| Hn w n) + (a ||| 2 ^ (w - 1))) - (2 ^ w * (c * Ln w n) + c) =
      2 ^ w * ((y ||| Hn w n) - c * Ln w n) + ((a ||| 2 ^ (w - 1)) - c) := by
    rw [Nat.mul_sub]
    have := Nat.mul_le_mul_left (2 ^ w) hY
    omega
  rw [e3]
  have hu : (a ||| 2 ^ (w - 1)) - c < 2 ^ w :=
    Nat.lt_of_le_of_lt (Nat.sub_le _ _) (Nat.or_lt_two_pow ha hh)
  exact land_split hu hh

private theorem D_dvd {w c : ℕ} (hw : 0 < w) (hc : c ≤ 2 ^ (w - 1)) : ∀ n y,
    2 ^ (w - 1) ∣ (((y ||| Hn w n) - c * Ln w n) &&& Hn w n)
  | 0, y => by simp [Hn, Ln_zero]
  | n + 1, y => by
    have hP : 0 < 2 ^ w := Nat.two_pow_pos w
    have h := Dstep (w := w) (c := c) (n := n) (a := y % 2 ^ w) (y := y / 2 ^ w) hw hc
      (Nat.mod_lt _ hP)
    rw [Nat.div_add_mod] at h
    rw [h]
    refine Nat.dvd_add (Dvd.dvd.mul_right ⟨2, by rw [two_pow_pred hw]; ring⟩ _) ?_
    have hh : 2 ^ (w - 1) < 2 ^ w := Nat.pow_lt_pow_right (by norm_num) (by omega)
    have hu : (y % 2 ^ w ||| 2 ^ (w - 1)) - c < 2 ^ w :=
      Nat.lt_of_le_of_lt (Nat.sub_le _ _) (Nat.or_lt_two_pow (Nat.mod_lt _ hP) hh)
    rw [and_h hw hu]
    split_ifs <;> simp

private theorem mm_succ {w c n a y : ℕ} (hw : 0 < w) (hc : c ≤ 2 ^ (w - 1)) (ha : a < 2 ^ w) :
    mm w c (Ln w (n + 1)) (Hn w (n + 1)) (2 ^ w * y + a) =
      2 ^ w * mm w c (Ln w n) (Hn w n) y + flag w c a := by
  have hh : 2 ^ (w - 1) < 2 ^ w := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hpos : 0 < 2 ^ (w - 1) := Nat.two_pow_pos _
  unfold mm
  rw [Dstep hw hc ha]
  obtain ⟨D1, hD1⟩ := D_dvd hw hc n y
  have hu : (a ||| 2 ^ (w - 1)) - c < 2 ^ w :=
    Nat.lt_of_le_of_lt (Nat.sub_le _ _) (Nat.or_lt_two_pow ha hh)
  have he : (((a ||| 2 ^ (w - 1)) - c) &&& 2 ^ (w - 1)) = 2 ^ (w - 1) * flag w c a := by
    rw [flag_eq hw ha, and_h hw hu]
    split_ifs <;> simp
  rw [hD1, he, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
  have e : 2 ^ w * (2 ^ (w - 1) * D1) + 2 ^ (w - 1) * flag w c a =
      2 ^ (w - 1) * (2 ^ w * D1 + flag w c a) := by ring
  rw [e, Nat.mul_div_cancel_left _ hpos, Nat.mul_div_cancel_left _ hpos]

private theorem mm_mul_le {w c : ℕ} (hw : 0 < w) (hc : c ≤ 2 ^ (w - 1)) : ∀ n x,
    mm w c (Ln w n) (Hn w n) x * c ≤ x
  | 0, x => by simp [mm, Hn, Ln_zero]
  | n + 1, x => by
    obtain ⟨y, a, ha, rfl⟩ : ∃ y a, a < 2 ^ w ∧ x = 2 ^ w * y + a :=
      ⟨x / 2 ^ w, x % 2 ^ w, Nat.mod_lt _ (Nat.two_pow_pos w), (Nat.div_add_mod _ _).symm⟩
    rw [mm_succ hw hc ha]
    have h1 := mm_mul_le hw hc n y
    have h2 := flag_mul_le hw hc ha
    have e : (2 ^ w * mm w c (Ln w n) (Hn w n) y + flag w c a) * c =
        2 ^ w * (mm w c (Ln w n) (Hn w n) y * c) + flag w c a * c := by ring
    rw [e]
    have := Nat.mul_le_mul_left (2 ^ w) h1
    omega

private theorem csub_succ {w c n a y : ℕ} (hw : 0 < w) (hc : c ≤ 2 ^ (w - 1)) (ha : a < 2 ^ w) :
    csub w (Ln w (n + 1)) (Hn w (n + 1)) c (2 ^ w * y + a) =
      2 ^ w * csub w (Ln w n) (Hn w n) c y + (a - flag w c a * c) := by
  rw [csub_eq, csub_eq, mm_succ hw hc ha]
  have h1 := mm_mul_le hw hc n y
  have h2 := flag_mul_le hw hc ha
  have e : (2 ^ w * mm w c (Ln w n) (Hn w n) y + flag w c a) * c =
      2 ^ w * (mm w c (Ln w n) (Hn w n) y * c) + flag w c a * c := by ring
  rw [e, Nat.mul_sub]
  have := Nat.mul_le_mul_left (2 ^ w) h1
  omega

private theorem mod_split {P Q a y : ℕ} (hP : 0 < P) (ha : a < P) :
    (P * y + a) % (P * Q) = P * (y % Q) + a := by
  rw [Nat.mod_mul]
  have h1 : (P * y + a) % P = a := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt ha]
  have h2 : (P * y + a) / P = y := by
    rw [Nat.mul_add_div hP, Nat.div_eq_of_lt ha, Nat.add_zero]
  rw [h1, h2, Nat.add_comm]

private theorem csub_mod {w c : ℕ} (hw : 0 < w) (hc : c ≤ 2 ^ (w - 1)) : ∀ k n, k ≤ n → ∀ x,
    csub w (Ln w n) (Hn w n) c x % 2 ^ (w * k) = csub w (Ln w n) (Hn w n) c (x % 2 ^ (w * k))
  | 0, n, _, x => by simp only [Nat.mul_zero, pow_zero, Nat.mod_one]; simp [csub]
  | k + 1, n, hk, x => by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    obtain ⟨y, a, ha, rfl⟩ : ∃ y a, a < 2 ^ w ∧ x = 2 ^ w * y + a :=
      ⟨x / 2 ^ w, x % 2 ^ w, Nat.mod_lt _ (Nat.two_pow_pos w), (Nat.div_add_mod _ _).symm⟩
    have hP := Nat.two_pow_pos w
    have e : 2 ^ (w * (k + 1)) = 2 ^ w * 2 ^ (w * k) := by
      rw [Nat.mul_succ, pow_add, Nat.mul_comm]
    have hg : a - flag w c a * c < 2 ^ w := Nat.lt_of_le_of_lt (Nat.sub_le _ _) ha
    rw [e, mod_split hP ha, csub_succ hw hc ha, csub_succ hw hc ha, mod_split hP hg,
      csub_mod hw hc k m (by omega) y]

private theorem redP_mod {w p T : ℕ} (hw : 0 < w) (hT : p * 2 ^ T ≤ 2 ^ (w - 1)) {k n : ℕ}
    (hk : k ≤ n) (x : ℕ) :
    redP w (Ln w n) (Hn w n) p T x % 2 ^ (w * k) =
      redP w (Ln w n) (Hn w n) p T (x % 2 ^ (w * k)) := by
  unfold redP
  generalize Nat.succ T = M
  induction M with
  | zero => rfl
  | succ M ih =>
    have hc : Nat.shiftLeft p (Nat.sub T M) ≤ 2 ^ (w - 1) := by
      show p <<< (T - M) ≤ _
      rw [Nat.shiftLeft_eq]
      exact Nat.le_trans (Nat.mul_le_mul_left p (Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _))) hT
    rw [Nat.rec_add_one, Nat.rec_add_one, csub_mod hw hc k n hk, ih]

private theorem rec_add_modEq {M : ℕ} (f f' : ℕ → ℕ) : ∀ g a a', a ≡ a' [MOD M] →
    (∀ i < g, f i ≡ f' i [MOD M]) →
    Nat.rec (motive := fun _ => ℕ) a (fun i acc => Nat.add acc (f i)) g ≡
      Nat.rec (motive := fun _ => ℕ) a' (fun i acc => Nat.add acc (f' i)) g [MOD M]
  | 0, a, a', h, _ => h
  | g + 1, a, a', h, hf =>
    Nat.ModEq.add (rec_add_modEq f f' g a a' h (fun i hi => hf i (by omega))) (hf g (by omega))

private theorem strictN_eq' (y : ℕ) (k : ℕ → ℕ) : strictN y k = k y := by cases y <;> rfl

private theorem rowsMulU_modEq {w S g m CMh RM X X' B M : ℕ}
    (hA : ∀ k < g * m, (X >>> (w * k)) &&& CMh ≡ (X' >>> (w * k)) &&& CMh [MOD M]) :
    rowsMulU w S g m CMh RM X B ≡ rowsMulU w S g m CMh RM X' B [MOD M] := by
  unfold rowsMulU
  simp only [strictN_eq']
  induction m with
  | zero => exact Nat.ModEq.refl _
  | succ m ih =>
    have ih' := ih (fun k hk => hA k (by rw [Nat.mul_succ]; omega))
    refine rec_add_modEq (fun i => Nat.mul (Nat.land (Nat.shiftRight X (Nat.mul w (Nat.add (Nat.mul g m) i))) CMh) (Nat.land (Nat.shiftRight (rowsOf S (Nat.mul g m) g B) (Nat.mul S i)) RM))
      (fun i => Nat.mul (Nat.land (Nat.shiftRight X' (Nat.mul w (Nat.add (Nat.mul g m) i))) CMh) (Nat.land (Nat.shiftRight (rowsOf S (Nat.mul g m) g B) (Nat.mul S i)) RM)) g _ _ ih' (fun i hi => ?_)
    exact Nat.ModEq.mul (hA (g * m + i) (by rw [Nat.mul_succ]; omega)) (Nat.ModEq.refl _)

private theorem bAnd_true' {a b : Bool} (h : Bool.rec (motive := fun _ => Bool) false b a = true) :
    a = true ∧ b = true := by
  cases a <;> simp_all

private theorem cm_bit (n : ℕ) :
    (2047 * ∑ r ∈ Finset.range n, 2 ^ (539 * r)) < 2 ^ (539 * n) ∧
    ∀ i, (2047 * ∑ r ∈ Finset.range n, 2 ^ (539 * r)).testBit i = true → i % 539 < 11 := by
  induction n with
  | zero => refine ⟨by simp, fun i h => ?_⟩; simp at h
  | succ n ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have e : 2047 * ∑ r ∈ Finset.range (n + 1), 2 ^ (539 * r) =
        2 ^ (539 * n) * 2047 + 2047 * ∑ r ∈ Finset.range n, 2 ^ (539 * r) := by
      rw [Finset.sum_range_succ]; ring
    rw [e]
    have hp : 0 < 2 ^ (539 * n) := Nat.two_pow_pos _
    have e2 : 2 ^ (539 * (n + 1)) = 2 ^ (539 * n) * 2 ^ 539 := by
      rw [Nat.mul_succ, pow_add]
    refine ⟨?_, fun i h => ?_⟩
    · rw [e2]
      have : (2 : ℕ) ^ 539 ≥ 2048 := by
        have : (2 : ℕ) ^ 11 ≤ 2 ^ 539 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
        omega
      have h3 := Nat.mul_le_mul_left (2 ^ (539 * n)) this
      omega
    · rw [Nat.testBit_two_pow_mul_add _ ih1] at h
      split_ifs at h with hi
      · exact ih2 i h
      · by_contra hcon
        have h4 : i - 539 * n < 11 := by
          by_contra h5
          have : (2047 : ℕ) < 2 ^ (i - 539 * n) :=
            Nat.lt_of_lt_of_le (by norm_num : (2047 : ℕ) < 2 ^ 11)
              (Nat.pow_le_pow_right (by norm_num) (by omega))
          rw [Nat.testBit_lt_two_pow this] at h
          exact absurd h (by simp)
        omega

private theorem colmask_mod {c k : ℕ} (hc : c ≤ 64) (hk : k < 49) (X : ℕ) :
    (X >>> (11 * k)) &&& (2047 * rep1 539 64) ≡
      ((X % 2 ^ (539 * c)) >>> (11 * k)) &&& (2047 * rep1 539 64) [MOD 2 ^ (539 * c)] := by
  unfold Nat.ModEq
  apply Nat.eq_of_testBit_eq
  intro i
  rw [rep1_eq (Or.inl (by norm_num))]
  rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
  by_cases hi : i < 539 * c
  · simp only [hi, decide_true, Bool.true_and, Nat.testBit_and, Nat.testBit_shiftRight]
    by_cases hb : (2047 * ∑ r ∈ Finset.range 64, 2 ^ (539 * r)).testBit i = true
    · have h1 := (cm_bit 64).2 i hb
      have h2 : 11 * k + i < 539 * c := by omega
      rw [Nat.testBit_mod_two_pow]
      simp [h2]
    · simp only [Bool.not_eq_true] at hb
      simp [hb]
  · simp [hi]

private noncomputable def RMc : ℕ := Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 539)) (nat_lit 1)

private theorem sBlk_eq (C : SConsts) (X K : ℕ) :
    sBlk C X K = redP 11 C.Lb C.Hb 5 7 (rowsMulU 11 539 7 7 C.CMb RMc X K) := rfl

theorem sBlk_trunc {C : SConsts} (hC : sConstsOK C = true) {c X K : ℕ} (hc : c ≤ 64) :
    sBlk C X K % 2 ^ (539 * c) = sBlk C (X % 2 ^ (539 * c)) K % 2 ^ (539 * c) := by
  unfold sConstsOK at hC
  obtain ⟨hLb, hC⟩ := bAnd_true' hC
  obtain ⟨hHb, hC⟩ := bAnd_true' hC
  obtain ⟨hCMb, -⟩ := bAnd_true' hC
  have e1 : C.Lb = Ln 11 3136 := by
    rw [Nat.eq_of_beq_eq_true hLb, rep1_eq (Or.inl (by norm_num))]; rfl
  have e2 : C.Hb = Hn 11 3136 := by
    rw [Nat.eq_of_beq_eq_true hHb, e1]
    unfold Hn
    generalize Ln 11 3136 = L
    exact Nat.shiftLeft_eq L 10
  have e3 : C.CMb = 2047 * rep1 539 64 := Nat.eq_of_beq_eq_true hCMb
  have hQ : 11 * (49 * c) = 539 * c := by ring
  have hk : 49 * c ≤ 3136 := by omega
  have hT : (5 : ℕ) * 2 ^ 7 ≤ 2 ^ (11 - 1) := by norm_num
  have hU : rowsMulU 11 539 7 7 C.CMb RMc X K ≡
      rowsMulU 11 539 7 7 C.CMb RMc (X % 2 ^ (539 * c)) K [MOD 2 ^ (539 * c)] := by
    refine rowsMulU_modEq (fun k hk' => ?_)
    rw [e3]
    exact colmask_mod hc (by omega) X
  have h1 := redP_mod (w := 11) (p := 5) (T := 7) (by norm_num) hT (n := 3136) hk
    (rowsMulU 11 539 7 7 C.CMb RMc X K)
  have h2 := redP_mod (w := 11) (p := 5) (T := 7) (by norm_num) hT (n := 3136) hk
    (rowsMulU 11 539 7 7 C.CMb RMc (X % 2 ^ (539 * c)) K)
  rw [hQ] at h1 h2
  rw [sBlk_eq, sBlk_eq, e1, e2, h1, h2]
  congr 1

end CFSG.KS.LyOm.SB6T
end
