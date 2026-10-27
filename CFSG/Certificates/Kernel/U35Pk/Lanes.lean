module

public import CFSG.RankThree.PartOne.HNB.F25
public import Mathlib.Tactic.Basify
public import Std.Tactic.BVDecide.Normalize.BitVec

public section

namespace CFSG.Certificates.U35Pk

open CFSG.RankThree.PartOne.HNB Matrix

set_option exponentiation.threshold 2100

theorem land_split (x m L w : ℕ) (hm : m < 2 ^ w) :
    x &&& (m + 2 ^ w * L) = (x % 2 ^ w &&& m) + 2 ^ w * (x / 2 ^ w &&& L) := by
  apply Nat.eq_of_testBit_eq
  intro j
  have h1 : x % 2 ^ w &&& m < 2 ^ w := Nat.and_lt_two_pow _ hm
  rw [Nat.add_comm (x % 2 ^ w &&& m), Nat.testBit_two_pow_mul_add _ h1, Nat.testBit_and,
    Nat.add_comm m, Nat.testBit_two_pow_mul_add _ hm]
  by_cases hj : j < w
  · simp only [hj, if_true, Nat.testBit_and, Nat.testBit_mod_two_pow, decide_true, Bool.true_and]
  · simp only [hj, if_false, Nat.testBit_and, ← Nat.shiftRight_eq_div_pow, Nat.testBit_shiftRight]
    congr 2
    omega

theorem land_shift_mask (x p w : ℕ) : x &&& 2 ^ p * (2 ^ w - 1) = 2 ^ p * (x / 2 ^ p % 2 ^ w) := by
  have h := land_split x 0 (2 ^ w - 1) p (Nat.two_pow_pos p)
  rw [Nat.zero_add] at h
  rw [h, Nat.and_zero, Nat.zero_add, Nat.and_two_pow_sub_one_eq_mod]

theorem add_two_pow_mul_lt {L v p w : ℕ} (hL : L < 2 ^ p) (hv : v < 2 ^ w) :
    L + 2 ^ p * v < 2 ^ (p + w) := by
  rw [Nat.pow_add]
  have : 2 ^ p * v + 2 ^ p ≤ 2 ^ p * 2 ^ w := by
    rw [← Nat.mul_succ]
    exact Nat.mul_le_mul_left _ hv
  omega

theorem split_div {L H p : ℕ} (hL : L < 2 ^ p) : (L + 2 ^ p * H) / 2 ^ p = H := by
  rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos p), Nat.div_eq_of_lt hL, Nat.zero_add]

theorem split_mod {L H p : ℕ} (hL : L < 2 ^ p) : (L + 2 ^ p * H) % 2 ^ p = L := by
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hL]

@[expose] def ev : (ℕ → ℕ) → ℕ → ℕ
  | _, 0 => 0
  | W, n + 1 => W 0 + 2 ^ 18 * ev (fun m => W (m + 1)) n

theorem ev_zero (W : ℕ → ℕ) : ev W 0 = 0 := rfl

theorem ev_succ (W : ℕ → ℕ) (n : ℕ) : ev W (n + 1) = W 0 + 2 ^ 18 * ev (fun m => W (m + 1)) n :=
  rfl

theorem ev_lt : ∀ {n : ℕ} {W : ℕ → ℕ}, (∀ m < n, W m < 2 ^ 18) → ev W n < 2 ^ (18 * n)
  | 0, _, _ => by simp [ev]
  | n + 1, W, h => by
    have e : 18 * (n + 1) = 18 + 18 * n := by ring
    rw [ev_succ, e]
    exact add_two_pow_mul_lt (h 0 (by omega)) (ev_lt fun m hm => h (m + 1) (by omega))

theorem ev_inj : ∀ {n : ℕ} {W V : ℕ → ℕ}, (∀ m < n, W m < 2 ^ 18) → (∀ m < n, V m < 2 ^ 18) →
    ev W n = ev V n → ∀ m < n, W m = V m
  | 0, _, _, _, _, _ => fun m hm => absurd hm (Nat.not_lt_zero m)
  | n + 1, W, V, hW, hV, h => by
    rw [ev_succ, ev_succ] at h
    have h0 : W 0 = V 0 := by
      have := congrArg (· % 2 ^ 18) h
      simpa only [split_mod (hW 0 (by omega)), split_mod (hV 0 (by omega))] using this
    have h1 := congrArg (· / 2 ^ 18) h
    simp only [split_div (hW 0 (by omega)), split_div (hV 0 (by omega))] at h1
    intro m hm
    rcases m with _ | m
    · exact h0
    · exact ev_inj (fun m hm => hW (m + 1) (by omega)) (fun m hm => hV (m + 1) (by omega)) h1 m
        (by omega)

theorem ev_add : ∀ {n : ℕ} (W V : ℕ → ℕ), ev (fun m => W m + V m) n = ev W n + ev V n
  | 0, _, _ => rfl
  | n + 1, W, V => by
    rw [ev_succ, ev_succ, ev_succ, ev_add (fun m => W (m + 1)) (fun m => V (m + 1))]
    ring

theorem ev_mul : ∀ {n : ℕ} (c : ℕ) (W : ℕ → ℕ), ev (fun m => c * W m) n = c * ev W n
  | 0, _, _ => by simp [ev]
  | n + 1, c, W => by
    rw [ev_succ, ev_succ, ev_mul c (fun m => W (m + 1))]
    ring

theorem ev_div_land : ∀ {n : ℕ} {W : ℕ → ℕ}, (∀ m < n, W m < 2 ^ 18) →
    (ev W n / 2 ^ 10 &&& ev (fun _ => 255) n) = ev (fun m => W m / 2 ^ 10) n
  | 0, _, _ => by simp [ev]
  | n + 1, W, hW => by
    have hW0 := hW 0 (by omega)
    set E := ev (fun m => W (m + 1)) n
    have e0 : 2 ^ 18 * E = 2 ^ 10 * (2 ^ 8 * E) := by ring
    have e1 : (W 0 + 2 ^ 18 * E) / 2 ^ 10 = W 0 / 2 ^ 10 + 2 ^ 8 * E := by
      rw [e0, Nat.add_mul_div_left _ _ (by norm_num)]
    have hq : W 0 / 2 ^ 10 < 2 ^ 8 := by omega
    rw [ev_succ, ev_succ, ev_succ, e1, land_split _ _ _ 18 (by norm_num)]
    have e255 : (255 : ℕ) = 2 ^ 8 - 1 := by norm_num
    have e18 : (2 : ℕ) ^ 18 = 2 ^ 8 * 2 ^ 10 := by norm_num
    have e2 : (W 0 / 2 ^ 10 + 2 ^ 8 * E) % 2 ^ 18 &&& 255 = W 0 / 2 ^ 10 := by
      rw [e255, Nat.and_two_pow_sub_one_eq_mod, e18, Nat.mod_mul_right_mod, split_mod hq]
    have e3 : (W 0 / 2 ^ 10 + 2 ^ 8 * E) / 2 ^ 18 = E / 2 ^ 10 := by
      rw [e18, ← Nat.div_div_eq_div_mul, split_div hq]
    rw [e2, e3, ev_div_land fun m hm => hW (m + 1) (by omega)]

@[expose] def re (x : F25) : ℕ := (x : ZMod 5 × ZMod 5).1.val

@[expose] def im (x : F25) : ℕ := (x : ZMod 5 × ZMod 5).2.val

theorem re_lt (x : F25) : re x < 5 := ZMod.val_lt _

theorem im_lt (x : F25) : im x < 5 := ZMod.val_lt _

theorem ext_re_im {x y : F25} (h1 : re x = re y) (h2 : im x = im y) : x = y :=
  Prod.ext (ZMod.val_injective _ h1) (ZMod.val_injective _ h2)

@[expose] def lanesB (F : Fin 3 → Fin 3 → ℕ) (m : ℕ) : ℕ :=
  [F 2 0, F 2 1, F 2 2, F 1 0, F 1 1, F 1 2, F 0 0, F 0 1, F 0 2].getD m 0

@[expose] def packB (F : Fin 3 → Fin 3 → ℕ) : ℕ := ev (lanesB F) 9

@[expose] def lanesA (F : Fin 3 → Fin 3 → ℕ) (m : ℕ) : ℕ :=
  [F 0 0, 0, 0, F 0 1, 0, 0, F 0 2, 0, 0, 0, 0, 0, 0, 0, 0,
    F 1 0, 0, 0, F 1 1, 0, 0, F 1 2, 0, 0, 0, 0, 0, 0, 0, 0,
    F 2 0, 0, 0, F 2 1, 0, 0, F 2 2].getD m 0

@[expose] def packA (F : Fin 3 → Fin 3 → ℕ) : ℕ := ev (lanesA F) 37

@[expose] def encB (X : Matrix (Fin 3) (Fin 3) F25) : ℕ :=
  packB (fun r j => re (X r j)) + 2 ^ 1024 * packB (fun r j => im (X r j))

@[expose] def encA (X : Matrix (Fin 3) (Fin 3) F25) : ℕ :=
  packA (fun r j => re (X r j)) + 2 ^ 1024 * packA (fun r j => im (X r j))

theorem packB_eq (F : Fin 3 → Fin 3 → ℕ) :
    packB F = 2 ^ 108 * (F 0 0 + 2 ^ 18 * F 0 1 + 2 ^ 36 * F 0 2) +
      2 ^ 54 * (F 1 0 + 2 ^ 18 * F 1 1 + 2 ^ 36 * F 1 2) + (F 2 0 + 2 ^ 18 * F 2 1 + 2 ^ 36 * F 2 2) := by
  simp only [packB, ev, lanesB, List.getD_cons_succ, List.getD_cons_zero]
  ring

theorem lanesB_lt {F : Fin 3 → Fin 3 → ℕ} {b : ℕ} (hF : ∀ r j, F r j < b) (hb : 0 < b) (m : ℕ) :
    lanesB F m < b := by
  unfold lanesB
  rcases m with _ | _ | _ | _ | _ | _ | _ | _ | _ | m <;> simp [hF, hb]

theorem packB_lt {F : Fin 3 → Fin 3 → ℕ} (hF : ∀ r j, F r j < 2 ^ 18) : packB F < 2 ^ 162 :=
  ev_lt fun m _ => lanesB_lt hF (by norm_num) m

theorem packB_inj {F G : Fin 3 → Fin 3 → ℕ} (hF : ∀ r j, F r j < 2 ^ 18) (hG : ∀ r j, G r j < 2 ^ 18)
    (h : packB F = packB G) : F = G := by
  have e := ev_inj (fun m _ => lanesB_lt hF (by norm_num) m) (fun m _ => lanesB_lt hG (by norm_num) m) h
  funext r j
  fin_cases r <;> fin_cases j
  · exact e 6 (by norm_num)
  · exact e 7 (by norm_num)
  · exact e 8 (by norm_num)
  · exact e 3 (by norm_num)
  · exact e 4 (by norm_num)
  · exact e 5 (by norm_num)
  · exact e 0 (by norm_num)
  · exact e 1 (by norm_num)
  · exact e 2 (by norm_num)

theorem lt18_of_lt5 {x : ℕ} (h : x < 5) : x < 2 ^ 18 := by omega

theorem encB_split (X : Matrix (Fin 3) (Fin 3) F25) :
    encB X % 2 ^ 1024 = packB (fun r j => re (X r j)) ∧
      encB X / 2 ^ 1024 = packB (fun r j => im (X r j)) := by
  have h : packB (fun r j => re (X r j)) < 2 ^ 1024 :=
    lt_trans (packB_lt fun r j => lt18_of_lt5 (re_lt _)) (by norm_num)
  exact ⟨split_mod h, split_div h⟩

theorem encB_inj {X Y : Matrix (Fin 3) (Fin 3) F25} (h : encB X = encB Y) : X = Y := by
  have h1 := packB_inj (fun r j => lt18_of_lt5 (re_lt (X r j))) (fun r j => lt18_of_lt5 (re_lt (Y r j)))
    (by rw [← (encB_split X).1, ← (encB_split Y).1, h])
  have h2 := packB_inj (fun r j => lt18_of_lt5 (im_lt (X r j))) (fun r j => lt18_of_lt5 (im_lt (Y r j)))
    (by rw [← (encB_split X).2, ← (encB_split Y).2, h])
  ext r j
  exact ext_re_im (congrFun (congrFun h1 r) j) (congrFun (congrFun h2 r) j)

end CFSG.Certificates.U35Pk
