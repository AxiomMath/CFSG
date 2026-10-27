module

public import Certificates.Data.Kernel.TwoNodeSmall.PosBK
import Mathlib.Tactic.IntervalCases
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.TwoNodeSmall.LaneSound

open CFSG.TwoNodeSmall CFSG.TwoNodeSmall.WitK CFSG.TwoNodeSmall.ExclK CFSG.TwoNodeSmall.PosBK

@[expose] def enc : List Nat → Nat
  | [] => 0
  | x :: l => x + 65536 * enc l

theorem enc_nil : enc [] = 0 := rfl

theorem enc_cons (x : Nat) (l : List Nat) : enc (x :: l) = x + 65536 * enc l := rfl

theorem enc_append (l m : List Nat) : enc (l ++ m) = enc l + 65536 ^ l.length * enc m := by
  induction l with
  | nil => simp [enc]
  | cons x l ih =>
    simp only [List.cons_append, enc_cons, ih, List.length_cons, pow_succ]
    ring

theorem enc_map_add (l : List Nat) (x y : Nat → Nat) (k : Nat) :
    enc (l.map fun i => x i + k * y i) = enc (l.map x) + k * enc (l.map y) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [List.map_cons, enc_cons, ih]
    ring

theorem enc_map_mul (l : List Nat) (x : Nat → Nat) (k : Nat) :
    enc (l.map fun i => k * x i) = k * enc (l.map x) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [List.map_cons, enc_cons, ih]
    ring

theorem enc_map_mod_div (l : List Nat) (x : Nat → Nat) :
    enc (l.map x) = enc (l.map fun i => x i % 3) + 3 * enc (l.map fun i => x i / 3) := by
  rw [← enc_map_add]
  congr 1
  apply List.map_congr_left
  intro i _
  omega

theorem enc_map_congr {l : List Nat} {x y : Nat → Nat} (h : ∀ i ∈ l, x i = y i) :
    enc (l.map x) = enc (l.map y) := by
  rw [List.map_congr_left h]

theorem enc_map_inj (l : List Nat) (x y : Nat → Nat) (hx : ∀ i, x i < 65536)
    (hy : ∀ i, y i < 65536) : enc (l.map x) = enc (l.map y) ↔ ∀ i ∈ l, x i = y i := by
  induction l with
  | nil => simp [enc]
  | cons i l ih =>
    simp only [List.map_cons, enc_cons, List.mem_cons, forall_eq_or_imp, ← ih]
    have := hx i
    have := hy i
    omega

theorem ones_mul (c : Nat) (l : List Nat) : Nat.mul c (ones l.length) = enc (l.map fun _ => c) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    change c * (ones l.length * 65536 + 1) = _
    simp only [List.map_cons, enc_cons, ← ih]
    change _ = c + 65536 * (c * ones l.length)
    ring

theorem land_lane {A B C E : Nat} (hA : A < 65536) (hC : C < 65536) :
    (A + 65536 * B) &&& (C + 65536 * E) = (A &&& C) + 65536 * (B &&& E) := by
  have h16 : (65536 : Nat) = 2 ^ 16 := rfl
  rw [h16] at hA hC ⊢
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.add_comm A, Nat.add_comm C, Nat.add_comm (A &&& C),
    Nat.testBit_two_pow_mul_add _ hA, Nat.testBit_two_pow_mul_add _ hC,
    Nat.testBit_two_pow_mul_add _ (Nat.and_lt_two_pow _ hC), Nat.testBit_and, Nat.testBit_and]
  split <;> rfl

theorem land_small (q r c : Nat) (hc : c = 3 ∨ c = 7) (hq : q ≤ c) :
    (q + 2048 * r) &&& c = q := by
  have e3 : (3 : Nat) = 2 ^ 2 - 1 := rfl
  have e7 : (7 : Nat) = 2 ^ 3 - 1 := rfl
  rcases hc with rfl | rfl
  · rw [e3, Nat.and_two_pow_sub_one_eq_mod]
    omega
  · rw [e7, Nat.and_two_pow_sub_one_eq_mod]
    omega

theorem red_core (c : Nat) (hc : c = 3 ∨ c = 7) (l : List Nat) (x : Nat → Nat)
    (hx : ∀ i, x i ≤ 11) :
    ((enc (l.map x) * 11) >>> 5) &&& enc (l.map fun _ => c) = enc (l.map fun i => x i / 3) := by
  induction l with
  | nil => simp [enc]
  | cons i l ih =>
    simp only [List.map_cons, enc_cons]
    have hi := hx i
    have hc' : c < 65536 := by omega
    have h1 : ((x i + 65536 * enc (l.map x)) * 11) >>> 5 =
        (x i / 3 + 2048 * (enc (l.map x) * 11 % 32)) + 65536 * ((enc (l.map x) * 11) >>> 5) := by
      have e : (2 : Nat) ^ 5 = 32 := rfl
      rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, e]
      omega
    have hA : x i / 3 + 2048 * (enc (l.map x) * 11 % 32) < 65536 := by omega
    rw [h1, land_lane hA hc', ih, land_small _ _ c hc (by omega)]

@[expose] noncomputable def rdc (c D x : Nat) : Nat :=
  Nat.sub x (Nat.mul 3 (Nat.land (Nat.shiftRight (Nat.mul x 11) 5) (Nat.mul c (ones D))))

theorem redF_eq (D x : Nat) : ExclK.red (fdB 3 D) x = rdc 7 D x := rfl

theorem redW_eq (D x : Nat) : WitK.red (Nat.mul 3 (ones D)) x = rdc 3 D x := rfl

theorem rdc_enc (c : Nat) (hc : c = 3 ∨ c = 7) (l : List Nat) (x : Nat → Nat)
    (hx : ∀ i, x i ≤ 11) : rdc c l.length (enc (l.map x)) = enc (l.map fun i => x i % 3) := by
  unfold rdc
  rw [ones_mul]
  change enc (l.map x) - 3 * (((enc (l.map x) * 11) >>> 5) &&& enc (l.map fun _ => c)) = _
  rw [red_core c hc l x hx, enc_map_mod_div l x]
  omega

@[expose] def fw (D : Nat) (x : Nat → Nat) : Nat := enc ((List.range D).map x)

@[expose] def rv (D : Nat) (x : Nat → Nat) : Nat := enc ((List.range D).reverse.map x)

theorem fw_zero (x : Nat → Nat) : fw 0 x = 0 := rfl

theorem rv_zero (x : Nat → Nat) : rv 0 x = 0 := rfl

theorem fw_succ_last (D : Nat) (x : Nat → Nat) : fw (D + 1) x = fw D x + 65536 ^ D * x D := by
  simp only [fw, List.range_succ, List.map_append, enc_append, List.length_map, List.length_range,
    List.map_cons, List.map_nil, enc_cons, enc_nil]
  ring

theorem rv_succ_last (D : Nat) (x : Nat → Nat) : rv (D + 1) x = x D + 65536 * rv D x := by
  simp only [rv, List.range_succ, List.reverse_append, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.cons_append, List.map_cons, enc_cons]

theorem fw_succ_first (D : Nat) (x : Nat → Nat) :
    fw (D + 1) x = x 0 + 65536 * fw D (fun i => x (i + 1)) := by
  simp only [fw, List.range_succ_eq_map, List.map_cons, List.map_map, enc_cons]
  rfl

theorem rv_succ_first (D : Nat) (x : Nat → Nat) :
    rv (D + 1) x = rv D (fun i => x (i + 1)) + 65536 ^ D * x 0 := by
  simp only [rv, List.range_succ_eq_map, List.reverse_cons, List.map_append, enc_append,
    List.length_map, List.length_reverse, List.length_range, List.map_cons, List.map_nil, enc_cons,
    enc_nil, List.map_reverse, List.map_map]
  rfl

theorem getD_succ (v : Vec) (i : Nat) : v.getD (i + 1) 0 = v.tail.getD i 0 := by
  cases v <;> simp

theorem headD_eq (v : Vec) : v.headD 0 = v.getD 0 0 := by
  cases v <;> simp

@[expose] def ln (v : Vec) (i : Nat) : Nat := v.getD i 0 % 3

theorem pk_eq (D : Nat) (v : Vec) : pk D v = fw D (ln v) := by
  induction D generalizing v with
  | zero => rfl
  | succ D ih =>
    rw [fw_succ_first]
    change Nat.add (Nat.mod (v.headD 0) 3) (Nat.mul 65536 (pk D v.tail)) = _
    rw [ih]
    simp only [ln, getD_succ, headD_eq]
    rfl

theorem pkr_go (D : Nat) : ∀ (v : Vec) (acc : Nat),
    (Nat.rec (motive := fun _ => Vec → Nat → Nat) (fun _ acc => acc)
      (fun _ ih v acc => ih v.tail (Nat.add (Nat.mul acc 65536) (Nat.mod (v.headD 0) 3))) D v acc :
      Nat) = acc * 65536 ^ D + rv D (ln v) := by
  induction D with
  | zero => intro v acc; simp [rv, enc]
  | succ D ih =>
    intro v acc
    change (Nat.rec (motive := fun _ => Vec → Nat → Nat) (fun _ acc => acc)
      (fun _ ih v acc => ih v.tail (Nat.add (Nat.mul acc 65536) (Nat.mod (v.headD 0) 3))) D v.tail
      (Nat.add (Nat.mul acc 65536) (Nat.mod (v.headD 0) 3)) : Nat) = _
    rw [ih, rv_succ_first]
    have e : (fun i => ln v (i + 1)) = ln v.tail := by
      funext i
      simp only [ln, getD_succ]
    rw [e]
    have e2 : (v.getD 0 0).mod 3 = v.getD 0 0 % 3 := rfl
    simp only [ln, Nat.add_eq, Nat.mul_eq, headD_eq, e2, pow_succ]
    ring

theorem pkr_eq (D : Nat) (f : Vec) : pkr D f = rv D (ln f) := by
  have h := pkr_go D f 0
  rw [Nat.zero_mul, Nat.zero_add] at h
  exact h

theorem pkP_eq (D : Nat) (v : Vec) : pkP 3 D v = pk D v := rfl

theorem pkrP_eq (D : Nat) (f : Vec) : pkrP 3 D f = pkr D f := rfl

theorem ln_le (v : Vec) (i : Nat) : ln v i ≤ 2 := by
  unfold ln
  omega

theorem fw_bound (D : Nat) (x : Nat → Nat) (hx : ∀ i, x i ≤ 2) :
    fw D x * 65535 + 2 ≤ 2 * 65536 ^ D := by
  induction D with
  | zero => simp [fw_zero]
  | succ D ih =>
    rw [fw_succ_last, pow_succ]
    have h1 : 65536 ^ D * x D ≤ 65536 ^ D * 2 := Nat.mul_le_mul_left _ (hx D)
    generalize 65536 ^ D * x D = Q at h1 ⊢
    generalize 65536 ^ D = P at h1 ih ⊢
    linarith

theorem fw_bound' (D : Nat) (x : Nat → Nat) (hx : ∀ i, x i ≤ 2) :
    fw D x * 65536 ≤ 3 * 65536 ^ D := by
  have := fw_bound D x hx
  generalize 65536 ^ D = P at this ⊢
  linarith

theorem conv (a b : Nat → Nat) (ha : ∀ i, a i ≤ 2) (hb : ∀ i, b i ≤ 2) (D : Nat) :
    ∃ L H, 65536 * (rv D a * fw D b) =
      L + ((List.range D).map fun i => a i * b i).sum * 65536 ^ D + H * 65536 ^ (D + 1) ∧
      L * 65536 ≤ 6 * D * 65536 ^ D := by
  induction D with
  | zero => exact ⟨0, 0, by simp [rv_zero], by simp⟩
  | succ D ih =>
    obtain ⟨L, H, hE, hL⟩ := ih
    refine ⟨65536 * a D * fw D b + 65536 * L, H + b D * rv D a, ?_, ?_⟩
    · rw [rv_succ_last, fw_succ_last, List.range_succ, List.map_append, List.sum_append]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
      calc 65536 * ((a D + 65536 * rv D a) * (fw D b + 65536 ^ D * b D))
          = 65536 * a D * fw D b + a D * b D * 65536 ^ (D + 1) +
              65536 * (65536 * (rv D a * fw D b)) + b D * rv D a * 65536 ^ (D + 2) := by ring
        _ = _ := by rw [hE]; ring
    · have h1 := fw_bound' D b hb
      have h2 : a D * (fw D b * 65536) ≤ 2 * (3 * 65536 ^ D) := Nat.mul_le_mul (ha D) h1
      rw [pow_succ]
      nlinarith

theorem lane_extract {P L S H D : Nat} (hD : 1 ≤ D) (hX : 6 * D < 65536) (hS : S < 65536)
    (hE : 65536 * P = L + S * 65536 ^ D + H * 65536 ^ (D + 1))
    (hL : L * 65536 ≤ 6 * D * 65536 ^ D) : P / 65536 ^ (D - 1) % 65536 = S := by
  obtain ⟨m, rfl⟩ : ∃ m, D = m + 1 := ⟨D - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  have hpos : 0 < 65536 ^ (m + 1) := by positivity
  have hL' : L < 65536 ^ (m + 1) := by
    have h3 : 6 * (m + 1) * 65536 ^ (m + 1) < 65536 ^ (m + 1) * 65536 := by
      rw [Nat.mul_comm (65536 ^ (m + 1))]
      exact Nat.mul_lt_mul_of_pos_right hX hpos
    exact Nat.lt_of_mul_lt_mul_right (Nat.lt_of_le_of_lt hL h3)
  have h1 : P / 65536 ^ m = 65536 * P / 65536 ^ (m + 1) := by
    rw [pow_succ, Nat.mul_comm (65536 ^ m) 65536, Nat.mul_div_mul_left _ _ (by norm_num)]
  have h2 : L + S * 65536 ^ (m + 1) + H * 65536 ^ (m + 1 + 1) =
      L + (S + H * 65536) * 65536 ^ (m + 1) := by ring
  rw [h1, hE, h2, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hL', Nat.zero_add,
    Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hS]

theorem sum_le (D : Nat) (a b : Nat → Nat) (ha : ∀ i, a i ≤ 2) (hb : ∀ i, b i ≤ 2) :
    ((List.range D).map fun i => a i * b i).sum ≤ 4 * D := by
  induction D with
  | zero => simp
  | succ D ih =>
    rw [List.range_succ, List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    have := Nat.mul_le_mul (ha D) (hb D)
    omega

theorem dot_rv_fw (D : Nat) (hD : D ≤ 10) (a b : Nat → Nat) (ha : ∀ i, a i ≤ 2)
    (hb : ∀ i, b i ≤ 2) :
    Nat.land (Nat.shiftRight (Nat.mul (rv D a) (fw D b)) (Nat.mul 16 (Nat.sub D 1))) 65535 =
      ((List.range D).map fun i => a i * b i).sum := by
  rcases Nat.eq_zero_or_pos D with rfl | hD1
  · simp [rv, fw, enc]
  obtain ⟨L, H, hE, hL⟩ := conv a b ha hb D
  have hS := sum_le D a b ha hb
  change (rv D a * fw D b) >>> (16 * (D - 1)) &&& 2 ^ 16 - 1 = _
  have e : (2 : Nat) ^ 16 = 65536 := rfl
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, pow_mul, e]
  exact lane_extract hD1 (by omega) (by omega) hE hL

theorem foldl_add (l : List Nat) (acc : Nat) : l.foldl (· + ·) acc = acc + l.sum := by
  induction l generalizing acc with
  | nil => simp
  | cons x l ih =>
    rw [List.foldl_cons, ih, List.sum_cons]
    omega

theorem sum_mod3 (l : List Nat) (f v : Vec) :
    ((l.map fun i => ln f i * ln v i).sum) % 3 = ((l.map fun i => f.getD i 0 * v.getD i 0).sum) % 3 := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [Nat.add_mod, ih, Nat.add_mod (f.getD i 0 * v.getD i 0)]
    congr 2
    simp only [ln]
    rw [← Nat.mul_mod]

theorem dotv_eq {P : Pt} (hp : P.p = 3) (f v : Vec) :
    P.dotv f v = ((List.range P.D).map fun i => ln f i * ln v i).sum % 3 := by
  rw [Pt.dotv, foldl_add, Nat.zero_add, hp, sum_mod3]

theorem dotv_comm (P : Pt) (f v : Vec) : P.dotv f v = P.dotv v f := by
  unfold Pt.dotv
  congr 3
  funext i
  exact Nat.mul_comm _ _

theorem dotv_lt {P : Pt} (hp : P.p = 3) (f v : Vec) : P.dotv f v < 3 := by
  rw [Pt.dotv, hp]
  exact Nat.mod_lt _ (by norm_num)

theorem dotK_pk {P : Pt} (hp : P.p = 3) (hD : P.D ≤ 10) (f v : Vec) :
    ExclK.dotK (fdB 3 P.D) (pkr P.D f) (pk P.D v) = P.dotv f v := by
  rw [dotv_eq hp, pkr_eq, pk_eq]
  change Nat.mod (Nat.land (Nat.shiftRight (Nat.mul (rv P.D (ln f)) (fw P.D (ln v)))
    (Nat.mul 16 (Nat.sub P.D 1))) 65535) 3 = _
  rw [dot_rv_fw P.D hD _ _ (ln_le f) (ln_le v)]
  rfl

theorem dotKW_pk {P : Pt} (hp : P.p = 3) (hD : P.D ≤ 10) (f v : Vec) :
    WitK.dotK (Nat.mul 16 (Nat.sub P.D 1)) (pkr P.D f) (pk P.D v) = P.dotv f v :=
  dotK_pk hp hD f v

theorem reflOK_pk {P : Pt} (hp : P.p = 3) (hD : P.D ≤ 10) (h f : Vec) :
    reflOK (fdB 3 P.D) (pk P.D h, pkr P.D f) = true ↔ P.dotv f h = 2 := by
  unfold reflOK
  rw [dotK_pk hp hD, Nat.beq_eq]

theorem red_fw (c : Nat) (hc : c = 3 ∨ c = 7) (D : Nat) (x : Nat → Nat) (hx : ∀ i, x i ≤ 11) :
    rdc c D (fw D x) = fw D (fun i => x i % 3) := by
  have h := rdc_enc c hc (List.range D) x hx
  rw [List.length_range] at h
  exact h

theorem red_rv (c : Nat) (hc : c = 3 ∨ c = 7) (D : Nat) (x : Nat → Nat) (hx : ∀ i, x i ≤ 11) :
    rdc c D (rv D x) = rv D (fun i => x i % 3) := by
  have h := rdc_enc c hc (List.range D).reverse x hx
  rw [List.length_reverse, List.length_range] at h
  exact h

theorem red_fw_add (c : Nat) (hc : c = 3 ∨ c = 7) (D k : Nat) (hk : k ≤ 2) (v w : Vec) :
    rdc c D (Nat.add (pk D v) (Nat.mul k (pk D w))) = fw D (fun i => (ln v i + k * ln w i) % 3) := by
  rw [pk_eq, pk_eq]
  change rdc c D (enc ((List.range D).map (ln v)) + k * enc ((List.range D).map (ln w))) = _
  rw [← enc_map_add]
  refine red_fw c hc D (fun i => ln v i + k * ln w i) (fun i => ?_)
  have := ln_le v i
  have := Nat.mul_le_mul hk (ln_le w i)
  omega

theorem red_rv_add (c : Nat) (hc : c = 3 ∨ c = 7) (D k : Nat) (hk : k ≤ 2) (v w : Vec) :
    rdc c D (Nat.add (pkr D v) (Nat.mul k (pkr D w))) = rv D (fun i => (ln v i + k * ln w i) % 3) := by
  rw [pkr_eq, pkr_eq]
  change rdc c D (enc ((List.range D).reverse.map (ln v)) +
    k * enc ((List.range D).reverse.map (ln w))) = _
  rw [← enc_map_add]
  refine red_rv c hc D (fun i => ln v i + k * ln w i) (fun i => ?_)
  have := ln_le v i
  have := Nat.mul_le_mul hk (ln_le w i)
  omega

theorem applyRefl_getD (P : Pt) (r : Refl) (v : Vec) {i : Nat} (hi : i < P.D) :
    (P.applyRefl r v).getD i 0 =
      (v.getD i 0 + (P.p - (P.dotv r.f v * r.h.getD i 0) % P.p)) % P.p := by
  simp [Pt.applyRefl, List.getD_eq_getElem?_getD, hi]

theorem lane_app (c v h : Nat) (hc : c < 3) :
    (v % 3 + (3 - c) % 3 * (h % 3)) % 3 = ((v + (3 - c * h % 3)) % 3) % 3 := by
  rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2) with rfl | rfl | rfl <;> omega

theorem pk_applyRefl {P : Pt} (hp : P.p = 3) (f h v : Vec) :
    pk P.D (P.applyRefl ⟨f, h⟩ v) =
      fw P.D (fun i => (ln v i + (3 - P.dotv f v) % 3 * ln h i) % 3) := by
  rw [pk_eq]
  unfold fw
  apply enc_map_congr
  intro i hi
  rw [List.mem_range] at hi
  simp only [ln]
  rw [applyRefl_getD P _ v hi, hp, lane_app _ _ _ (dotv_lt hp f v)]

theorem pkr_applyRefl {P : Pt} (hp : P.p = 3) (f h v : Vec) :
    pkr P.D (P.applyRefl ⟨f, h⟩ v) =
      rv P.D (fun i => (ln v i + (3 - P.dotv f v) % 3 * ln h i) % 3) := by
  rw [pkr_eq]
  unfold rv
  apply enc_map_congr
  intro i hi
  rw [List.mem_reverse, List.mem_range] at hi
  simp only [ln]
  rw [applyRefl_getD P _ v hi, hp, lane_app _ _ _ (dotv_lt hp f v)]

theorem k_le (c : Nat) : (3 - c) % 3 ≤ 2 := by omega

theorem appK_pk {P : Pt} (hp : P.p = 3) (hD : P.D ≤ 10) (h f v : Vec) :
    ExclK.appK (fdB 3 P.D) (pk P.D h, pkr P.D f) (pk P.D v) = pk P.D (P.applyRefl ⟨f, h⟩ v) := by
  unfold ExclK.appK negK
  rw [dotK_pk hp hD, redF_eq, pk_applyRefl hp]
  exact red_fw_add 7 (Or.inr rfl) P.D _ (k_le _) v h

theorem appKW_pk {P : Pt} (hp : P.p = 3) (hD : P.D ≤ 10) (h f v : Vec) :
    WitK.appK (Nat.mul 3 (ones P.D)) (Nat.mul 16 (Nat.sub P.D 1)) (pk P.D h, pkr P.D f) (pk P.D v) =
      pk P.D (P.applyRefl ⟨f, h⟩ v) := by
  unfold WitK.appK
  rw [dotKW_pk hp hD, redW_eq, pk_applyRefl hp]
  exact red_fw_add 3 (Or.inl rfl) P.D _ (k_le _) v h

theorem conjFW_pkr {P : Pt} (hp : P.p = 3) (hD : P.D ≤ 10) (gh gf rf : Vec) :
    WitK.red (Nat.mul 3 (ones P.D)) (Nat.add (pkr P.D rf) (Nat.mul (Nat.mod (Nat.sub 3
      (WitK.dotK (Nat.mul 16 (Nat.sub P.D 1)) (pkr P.D rf) (pk P.D gh))) 3) (pkr P.D gf))) =
      pkr P.D (P.applyRefl ⟨gh, gf⟩ rf) := by
  rw [dotKW_pk hp hD, redW_eq, pkr_applyRefl hp, dotv_comm P gh rf]
  exact red_rv_add 3 (Or.inl rfl) P.D _ (k_le _) rf gf

theorem conjK_pk {P : Pt} (hp : P.p = 3) (hD : P.D ≤ 10) (gh gf rh rf : Vec) :
    ExclK.conjK (fdB 3 P.D) (pk P.D gh, pkr P.D gf) (pk P.D rh, pkr P.D rf) =
      (pk P.D (P.applyRefl ⟨gf, gh⟩ rh), pkr P.D (P.applyRefl ⟨gh, gf⟩ rf)) := by
  unfold ExclK.conjK
  rw [appK_pk hp hD]
  congr 1
  unfold negK
  rw [dotK_pk hp hD, redF_eq, pkr_applyRefl hp, dotv_comm P gh rf]
  exact red_rv_add 7 (Or.inr rfl) P.D _ (k_le _) rf gf

theorem smulK_pk {P : Pt} (hp : P.p = 3) (l : Nat) (hl : l < 3) (v : Vec) :
    smulK (fdB 3 P.D) l (pk P.D v) = pk P.D ((List.range P.D).map fun i => l * v.getD i 0 % 3) := by
  have _ := hp
  unfold smulK
  rw [redF_eq, pk_eq, pk_eq]
  have e : Nat.mul l (fw P.D (ln v)) = fw P.D (fun i => l * ln v i) := by
    unfold fw
    rw [enc_map_mul]
    rfl
  rw [e, red_fw 7 (Or.inr rfl) P.D _ (fun i => by
    have := Nat.mul_le_mul (by omega : l ≤ 2) (ln_le v i); omega)]
  unfold fw
  apply enc_map_congr
  intro i hi
  rw [List.mem_range] at hi
  simp [ln, List.getD_eq_getElem?_getD, hi, Nat.mul_mod]

@[expose] def negV (D : Nat) (v : Vec) : Vec := (List.range D).map fun i => (3 - v.getD i 0 % 3) % 3

theorem sub_enc (l : List Nat) (x : Nat → Nat) (hx : ∀ i, x i ≤ 3) :
    Nat.sub (Nat.mul 3 (ones l.length)) (enc (l.map x)) = enc (l.map fun i => 3 - x i) := by
  rw [ones_mul]
  have e : enc (l.map fun _ => 3) = enc (l.map fun i => 3 - x i) + 1 * enc (l.map x) := by
    rw [← enc_map_add]
    apply enc_map_congr
    intro i _
    have := hx i
    omega
  change enc (l.map fun _ => 3) - enc (l.map x) = _
  omega

theorem negV_ln (D : Nat) (v : Vec) {i : Nat} (hi : i < D) : ln (negV D v) i = (3 - ln v i) % 3 := by
  simp [ln, negV, List.getD_eq_getElem?_getD, hi]

theorem neg_pk (D : Nat) (v : Vec) :
    ExclK.red (fdB 3 D) (Nat.sub (Nat.mul 3 (ones D)) (pk D v)) = pk D (negV D v) := by
  rw [redF_eq, pk_eq, pk_eq]
  have h := sub_enc (List.range D) (ln v) (fun i => by have := ln_le v i; omega)
  rw [List.length_range] at h
  unfold fw
  rw [h]
  have h2 := rdc_enc 7 (Or.inr rfl) (List.range D) (fun i => 3 - ln v i) (fun i => by omega)
  rw [List.length_range] at h2
  rw [h2]
  apply enc_map_congr
  intro i hi
  rw [List.mem_range] at hi
  rw [negV_ln D v hi]

theorem neg_pkr (D : Nat) (v : Vec) :
    ExclK.red (fdB 3 D) (Nat.sub (Nat.mul 3 (ones D)) (pkr D v)) = pkr D (negV D v) := by
  rw [redF_eq, pkr_eq, pkr_eq]
  have h := sub_enc (List.range D).reverse (ln v) (fun i => by have := ln_le v i; omega)
  rw [List.length_reverse, List.length_range] at h
  unfold rv
  rw [h]
  have h2 := rdc_enc 7 (Or.inr rfl) (List.range D).reverse (fun i => 3 - ln v i) (fun i => by omega)
  rw [List.length_reverse, List.length_range] at h2
  rw [h2]
  apply enc_map_congr
  intro i hi
  rw [List.mem_reverse, List.mem_range] at hi
  rw [negV_ln D v hi]

theorem fw_eq_zero (D : Nat) (x : Nat → Nat) (hx : ∀ j < D, x j = 0) : fw D x = 0 := by
  induction D with
  | zero => rfl
  | succ D ih =>
    rw [fw_succ_last, ih (fun j hj => hx j (by omega)), hx D (by omega)]
    rfl

theorem fw_unit (D i : Nat) (hi : i < D) : fw D (fun j => if j = i then 1 else 0) = 65536 ^ i := by
  induction D with
  | zero => omega
  | succ D ih =>
    rw [fw_succ_last]
    rcases Nat.lt_or_ge i D with h | h
    · rw [ih h, if_neg (by omega), Nat.mul_zero, Nat.add_zero]
    · obtain rfl : i = D := by omega
      rw [fw_eq_zero i _ (fun j hj => if_neg (by omega)), if_pos rfl]
      ring

theorem shiftLeft_unit (P : Pt) {i : Nat} (hi : i < P.D) :
    Nat.shiftLeft 1 (Nat.mul 16 i) = pk P.D (P.unit i) := by
  change 1 <<< (16 * i) = _
  have e : (2 : Nat) ^ 16 = 65536 := rfl
  rw [pk_eq, Nat.shiftLeft_eq, Nat.one_mul, pow_mul, e, ← fw_unit P.D i hi]
  unfold fw
  apply enc_map_congr
  intro j hj
  rw [List.mem_range] at hj
  simp only [ln, Pt.unit, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj,
    Option.map_some, Option.getD_some]
  split <;> rfl

theorem ln_lt (v : Vec) (i : Nat) : ln v i < 65536 := by
  have := ln_le v i
  omega

theorem pk_inj {P : Pt} (hp : P.p = 3) (v w : Vec) : pk P.D v = pk P.D w ↔ P.vecEq v w = true := by
  rw [pk_eq, pk_eq]
  unfold fw
  rw [enc_map_inj _ _ _ (ln_lt v) (ln_lt w), Pt.vecEq, List.all_eq_true]
  simp only [Pt.ent, hp, ln, beq_iff_eq]

theorem pkr_inj {P : Pt} (hp : P.p = 3) (v w : Vec) :
    pkr P.D v = pkr P.D w ↔ P.vecEq v w = true := by
  rw [pkr_eq, pkr_eq]
  unfold rv
  rw [enc_map_inj _ _ _ (ln_lt v) (ln_lt w), Pt.vecEq, List.all_eq_true]
  simp only [List.mem_reverse, Pt.ent, hp, ln, beq_iff_eq]

theorem fw_boundB (D B : Nat) (x : Nat → Nat) (hx : ∀ i, x i ≤ B) :
    fw D x * 65535 + B ≤ B * 65536 ^ D := by
  induction D with
  | zero => simp [fw_zero]
  | succ D ih =>
    rw [fw_succ_last, pow_succ]
    have h1 : 65536 ^ D * x D ≤ 65536 ^ D * B := Nat.mul_le_mul_left _ (hx D)
    have e : B * (65536 ^ D * 65536) = 65536 * (65536 ^ D * B) := by ring
    rw [e]
    rw [Nat.mul_comm B] at ih
    generalize 65536 ^ D * x D = Q at h1 ⊢
    generalize 65536 ^ D * B = R at h1 ih ⊢
    linarith

theorem convB (a b : Nat → Nat) (B : Nat) (hb : ∀ i, b i ≤ B) (D : Nat) :
    ∃ L H, 65536 * (rv D a * fw D b) =
      L + ((List.range D).map fun i => a i * b i).sum * 65536 ^ D + H * 65536 ^ (D + 1) ∧
      L * 65535 ≤ B * ((List.range D).map a).sum * 65536 ^ D := by
  induction D with
  | zero => exact ⟨0, 0, by simp [rv_zero], by simp⟩
  | succ D ih =>
    obtain ⟨L, H, hE, hL⟩ := ih
    refine ⟨65536 * a D * fw D b + 65536 * L, H + b D * rv D a, ?_, ?_⟩
    · rw [rv_succ_last, fw_succ_last, List.range_succ, List.map_append, List.sum_append]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
      calc 65536 * ((a D + 65536 * rv D a) * (fw D b + 65536 ^ D * b D))
          = 65536 * a D * fw D b + a D * b D * 65536 ^ (D + 1) +
              65536 * (65536 * (rv D a * fw D b)) + b D * rv D a * 65536 ^ (D + 2) := by ring
        _ = _ := by rw [hE]; ring
    · have h1 : fw D b * 65535 ≤ B * 65536 ^ D := by
        exact Nat.le_of_add_right_le (fw_boundB D B b hb)
      have h2 : a D * (fw D b * 65535) ≤ a D * (B * 65536 ^ D) := Nat.mul_le_mul_left _ h1
      rw [List.range_succ, List.map_append, List.sum_append, pow_succ]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
      calc (65536 * a D * fw D b + 65536 * L) * 65535
          = 65536 * (a D * (fw D b * 65535)) + 65536 * (L * 65535) := by ring
        _ ≤ 65536 * (a D * (B * 65536 ^ D)) +
              65536 * (B * ((List.range D).map a).sum * 65536 ^ D) :=
            Nat.add_le_add (Nat.mul_le_mul_left _ h2) (Nat.mul_le_mul_left _ hL)
        _ = _ := by ring

theorem lane_extract0 {P L S H D : Nat} (hD : 1 ≤ D) (hS : S < 65536)
    (hE : 65536 * P = L + S * 65536 ^ D + H * 65536 ^ (D + 1)) (hL' : L < 65536 ^ D) :
    P / 65536 ^ (D - 1) % 65536 = S := by
  obtain ⟨m, rfl⟩ : ∃ m, D = m + 1 := ⟨D - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  have hpos : 0 < 65536 ^ (m + 1) := by positivity
  have h1 : P / 65536 ^ m = 65536 * P / 65536 ^ (m + 1) := by
    rw [pow_succ, Nat.mul_comm (65536 ^ m) 65536, Nat.mul_div_mul_left _ _ (by norm_num)]
  have h2 : L + S * 65536 ^ (m + 1) + H * 65536 ^ (m + 1 + 1) =
      L + (S + H * 65536) * 65536 ^ (m + 1) := by ring
  rw [h1, hE, h2, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hL', Nat.zero_add,
    Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hS]

theorem lane_rv_fw (D B : Nat) (a b : Nat → Nat) (hb : ∀ i, b i ≤ B)
    (hBS : B * ((List.range D).map a).sum < 65535)
    (hS : ((List.range D).map fun i => a i * b i).sum < 65536) :
    Nat.land (Nat.shiftRight (Nat.mul (rv D a) (fw D b)) (Nat.mul 16 (Nat.sub D 1))) 65535 =
      ((List.range D).map fun i => a i * b i).sum := by
  rcases Nat.eq_zero_or_pos D with rfl | hD1
  · simp [rv, fw, enc]
  obtain ⟨L, H, hE, hL⟩ := convB a b B hb D
  have hpos : 0 < 65536 ^ D := by positivity
  have h3 : B * ((List.range D).map a).sum * 65536 ^ D < 65535 * 65536 ^ D :=
    Nat.mul_lt_mul_of_pos_right hBS hpos
  have h4 : 65535 * L < 65535 * 65536 ^ D := by
    rw [Nat.mul_comm]
    exact Nat.lt_of_le_of_lt hL h3
  have hL' : L < 65536 ^ D := Nat.lt_of_mul_lt_mul_left h4
  change (rv D a * fw D b) >>> (16 * (D - 1)) &&& 2 ^ 16 - 1 = _
  have e : (2 : Nat) ^ 16 = 65536 := rfl
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, pow_mul, e]
  exact lane_extract0 hD1 hS hE hL'

theorem sum_le_const (D B : Nat) (a : Nat → Nat) (ha : ∀ i, a i ≤ B) :
    ((List.range D).map a).sum ≤ B * D := by
  induction D with
  | zero => simp
  | succ D ih =>
    rw [List.range_succ, List.map_append, List.sum_append, Nat.mul_succ]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    have := ha D
    omega

theorem sum_mul_le (D B : Nat) (a b : Nat → Nat) (hb : ∀ i, b i ≤ B) :
    ((List.range D).map fun i => a i * b i).sum ≤ B * ((List.range D).map a).sum := by
  induction D with
  | zero => simp
  | succ D ih =>
    rw [List.range_succ, List.map_append, List.sum_append, List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    have := Nat.mul_le_mul_left (a D) (hb D)
    rw [Nat.mul_add, Nat.mul_comm B (a D)]
    omega

theorem yK_eq (D : Nat) : yK D = rv D (fun i => 3 ^ i) := by
  induction D with
  | zero => rfl
  | succ D ih =>
    rw [rv_succ_last]
    change Nat.add (Nat.mul (yK D) 65536) (Nat.pow 3 D) = _
    rw [ih]
    change rv D (fun i => 3 ^ i) * 65536 + 3 ^ D = _
    ring

theorem pow3_sum (D : Nat) : 2 * ((List.range D).map fun i => 3 ^ i).sum + 1 = 3 ^ D := by
  induction D with
  | zero => rfl
  | succ D ih =>
    rw [List.range_succ, List.map_append, List.sum_append, pow_succ]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    omega

theorem foldr_code (p : Nat) (g : Nat → Nat) (D init : Nat) :
    (List.range D).foldr (fun j acc => g j + p * acc) init =
      ((List.range D).map fun i => p ^ i * g i).sum + p ^ D * init := by
  induction D generalizing init with
  | zero => simp
  | succ D ih =>
    rw [List.range_succ, List.foldr_append, List.foldr_cons, List.foldr_nil, ih, List.map_append,
      List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, pow_succ]
    ring

theorem code_eq {P : Pt} (hp : P.p = 3) (v : Vec) :
    P.code v = ((List.range P.D).map fun i => 3 ^ i * ln v i).sum := by
  rw [Pt.code, foldr_code]
  simp only [Pt.ent, hp, ln, Nat.mul_zero, Nat.add_zero]

theorem codeK_pk {P : Pt} (hp : P.p = 3) (hD : P.D ≤ 10) (v : Vec) :
    codeK (yK P.D) (Nat.mul 16 (Nat.sub P.D 1)) (pk P.D v) = P.code v := by
  rw [code_eq hp, yK_eq, pk_eq]
  have e : Nat.mul (fw P.D (ln v)) (rv P.D fun i => 3 ^ i) =
      Nat.mul (rv P.D fun i => 3 ^ i) (fw P.D (ln v)) := Nat.mul_comm _ _
  change Nat.land (Nat.shiftRight (Nat.mul (fw P.D (ln v)) (rv P.D fun i => 3 ^ i))
    (Nat.mul 16 (Nat.sub P.D 1))) 65535 = _
  have h3 : 3 ^ P.D ≤ 59049 := le_trans (Nat.pow_le_pow_right (by norm_num) hD) (by norm_num)
  have hg := pow3_sum P.D
  have hS := sum_mul_le P.D 2 (fun i => 3 ^ i) (ln v) (ln_le v)
  rw [e, lane_rv_fw P.D 2 _ _ (ln_le v) (by omega) (by omega)]

theorem fdB_of_ne {p : Nat} (D : Nat) (hp : p ≠ 3) : fdB p D = fdOf p D := by
  have h : Nat.beq p 3 = false := by
    cases h' : Nat.beq p 3
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true h') hp
  unfold fdB
  rw [h]
  rfl

@[expose] def lnp (p : Nat) (v : Vec) (i : Nat) : Nat := v.getD i 0 % p

theorem lnp_le {p : Nat} (hp : 0 < p) (v : Vec) (i : Nat) : lnp p v i ≤ p - 1 := by
  unfold lnp
  have := Nat.mod_lt (v.getD i 0) hp
  omega

theorem pkP_fw (p D : Nat) (v : Vec) : pkP p D v = fw D (lnp p v) := by
  induction D generalizing v with
  | zero => rfl
  | succ D ih =>
    rw [fw_succ_first]
    change Nat.add (Nat.mod (v.headD 0) p) (Nat.mul 65536 (pkP p D v.tail)) = _
    rw [ih]
    simp only [lnp, getD_succ, headD_eq]
    rfl

theorem pkrP_go (p D : Nat) : ∀ (v : Vec) (acc : Nat),
    (Nat.rec (motive := fun _ => Vec → Nat → Nat) (fun _ acc => acc)
      (fun _ ih v acc => ih v.tail (Nat.add (Nat.mul acc 65536) (Nat.mod (v.headD 0) p))) D v acc :
      Nat) = acc * 65536 ^ D + rv D (lnp p v) := by
  induction D with
  | zero => intro v acc; simp [rv, enc]
  | succ D ih =>
    intro v acc
    change (Nat.rec (motive := fun _ => Vec → Nat → Nat) (fun _ acc => acc)
      (fun _ ih v acc => ih v.tail (Nat.add (Nat.mul acc 65536) (Nat.mod (v.headD 0) p))) D v.tail
      (Nat.add (Nat.mul acc 65536) (Nat.mod (v.headD 0) p)) : Nat) = _
    rw [ih, rv_succ_first]
    have e : (fun i => lnp p v (i + 1)) = lnp p v.tail := by
      funext i
      simp only [lnp, getD_succ]
    rw [e]
    have e2 : (v.getD 0 0).mod p = v.getD 0 0 % p := rfl
    simp only [lnp, Nat.add_eq, Nat.mul_eq, headD_eq, e2, pow_succ]
    ring

theorem pkrP_rv (p D : Nat) (f : Vec) : pkrP p D f = rv D (lnp p f) := by
  have h := pkrP_go p D f 0
  rw [Nat.zero_mul, Nat.zero_add] at h
  exact h

theorem sum_modP (p : Nat) (l : List Nat) (f v : Vec) :
    ((l.map fun i => lnp p f i * lnp p v i).sum) % p =
      ((l.map fun i => f.getD i 0 * v.getD i 0).sum) % p := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [Nat.add_mod, ih, Nat.add_mod (f.getD i 0 * v.getD i 0)]
    congr 2
    simp only [lnp]
    rw [← Nat.mul_mod]

theorem dotv_eqP {P : Pt} {p : Nat} (hp : P.p = p) (f v : Vec) :
    P.dotv f v = ((List.range P.D).map fun i => lnp p f i * lnp p v i).sum % p := by
  rw [Pt.dotv, foldl_add, Nat.zero_add, hp, sum_modP]

theorem dotv_ltP {P : Pt} {p : Nat} (hp : P.p = p) (hp0 : 0 < p) (f v : Vec) : P.dotv f v < p := by
  rw [Pt.dotv, hp]
  exact Nat.mod_lt _ hp0

theorem dotKP_pk {P : Pt} {p : Nat} (hp : P.p = p) (hp0 : 0 < p) (hp7 : p ≤ 7) (hD : P.D ≤ 10)
    (f v : Vec) : ExclK.dotK (fdOf p P.D) (pkrP p P.D f) (pkP p P.D v) = P.dotv f v := by
  rw [dotv_eqP hp, pkrP_rv, pkP_fw]
  change Nat.mod (Nat.land (Nat.shiftRight (Nat.mul (rv P.D (lnp p f)) (fw P.D (lnp p v)))
    (Nat.mul 16 (Nat.sub P.D 1))) 65535) p = _
  have hSa := sum_le_const P.D (p - 1) (lnp p f) (lnp_le hp0 f)
  have hS := sum_mul_le P.D (p - 1) (lnp p f) (lnp p v) (lnp_le hp0 v)
  have h1 : (p - 1) * P.D ≤ 6 * 10 := Nat.mul_le_mul (by omega) hD
  have h2 : (p - 1) * ((List.range P.D).map (lnp p f)).sum ≤ 6 * 60 :=
    Nat.mul_le_mul (by omega) (by omega)
  rw [lane_rv_fw P.D (p - 1) _ _ (lnp_le hp0 v) (by omega) (by omega)]
  rfl

theorem reflOKP_pk {P : Pt} {p : Nat} (hp : P.p = p) (hp0 : 0 < p) (hp7 : p ≤ 7) (hD : P.D ≤ 10)
    (h f : Vec) : reflOK (fdOf p P.D) (pkP p P.D h, pkrP p P.D f) = true ↔ P.dotv f h = 2 := by
  unfold reflOK
  rw [dotKP_pk hp hp0 hp7 hD, Nat.beq_eq]

@[expose] noncomputable def rdcM (p M k D x : Nat) : Nat :=
  Nat.sub x (Nat.mul p (Nat.land (Nat.shiftRight (Nat.mul x M) k) (Nat.mul 7 (ones D))))

theorem redF5_eq (D x : Nat) : ExclK.red (fdOf 5 D) x = rdcM 5 13 6 D x := rfl

theorem redF7_eq (D x : Nat) : ExclK.red (fdOf 7 D) x = rdcM 7 37 8 D x := rfl

theorem land7 (q r : Nat) (hq : q ≤ 7) : (q + 8 * r) &&& 7 = q := by
  have e7 : (7 : Nat) = 2 ^ 3 - 1 := rfl
  rw [e7, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem red_coreM (p M k : Nat) (hpMk : (p = 7 ∧ M = 37 ∧ k = 8) ∨ (p = 5 ∧ M = 13 ∧ k = 6))
    (l : List Nat) (x : Nat → Nat) (hx : ∀ i, x i ≤ p * (p - 1)) :
    ((enc (l.map x) * M) >>> k) &&& enc (l.map fun _ => 7) = enc (l.map fun i => x i / p) := by
  induction l with
  | nil => simp [enc]
  | cons i l ih =>
    simp only [List.map_cons, enc_cons]
    have hi := hx i
    have h1 : ∃ r, ((x i + 65536 * enc (l.map x)) * M) >>> k =
        (x i / p + 8 * r) + 65536 * ((enc (l.map x) * M) >>> k) ∧
        x i / p + 8 * r < 65536 ∧ x i / p ≤ 7 := by
      rcases hpMk with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
      · refine ⟨32 * (enc (l.map x) * 37 % 256), ?_, by omega, by omega⟩
        have e : (2 : Nat) ^ 8 = 256 := rfl
        rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, e]
        omega
      · refine ⟨128 * (enc (l.map x) * 13 % 64), ?_, by omega, by omega⟩
        have e : (2 : Nat) ^ 6 = 64 := rfl
        rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, e]
        omega
    obtain ⟨r, hr, hA, h7⟩ := h1
    rw [hr, land_lane hA (by norm_num), ih, land7 _ _ h7]

theorem enc_map_mod_divP (p : Nat) (l : List Nat) (x : Nat → Nat) :
    enc (l.map x) = enc (l.map fun i => x i % p) + p * enc (l.map fun i => x i / p) := by
  rw [← enc_map_add]
  congr 1
  apply List.map_congr_left
  intro i _
  exact (Nat.mod_add_div (x i) p).symm

theorem rdcM_enc (p M k : Nat) (hpMk : (p = 7 ∧ M = 37 ∧ k = 8) ∨ (p = 5 ∧ M = 13 ∧ k = 6))
    (l : List Nat) (x : Nat → Nat) (hx : ∀ i, x i ≤ p * (p - 1)) :
    rdcM p M k l.length (enc (l.map x)) = enc (l.map fun i => x i % p) := by
  unfold rdcM
  rw [ones_mul]
  change enc (l.map x) - p * (((enc (l.map x) * M) >>> k) &&& enc (l.map fun _ => 7)) = _
  rw [red_coreM p M k hpMk l x hx, enc_map_mod_divP p l x]
  omega

theorem redP_enc {p : Nat} (hp : p = 5 ∨ p = 7) (l : List Nat) (x : Nat → Nat)
    (hx : ∀ i, x i ≤ p * (p - 1)) :
    ExclK.red (fdOf p l.length) (enc (l.map x)) = enc (l.map fun i => x i % p) := by
  rcases hp with rfl | rfl
  · rw [redF5_eq]
    exact rdcM_enc 5 13 6 (Or.inr ⟨rfl, rfl, rfl⟩) l x hx
  · rw [redF7_eq]
    exact rdcM_enc 7 37 8 (Or.inl ⟨rfl, rfl, rfl⟩) l x hx

theorem red_fwP {p : Nat} (hp : p = 5 ∨ p = 7) (D : Nat) (x : Nat → Nat)
    (hx : ∀ i, x i ≤ p * (p - 1)) : ExclK.red (fdOf p D) (fw D x) = fw D (fun i => x i % p) := by
  have h := redP_enc hp (List.range D) x hx
  rw [List.length_range] at h
  exact h

theorem red_rvP {p : Nat} (hp : p = 5 ∨ p = 7) (D : Nat) (x : Nat → Nat)
    (hx : ∀ i, x i ≤ p * (p - 1)) : ExclK.red (fdOf p D) (rv D x) = rv D (fun i => x i % p) := by
  have h := redP_enc hp (List.range D).reverse x hx
  rw [List.length_reverse, List.length_range] at h
  exact h

theorem lane_addP {p : Nat} (hp : p = 5 ∨ p = 7) (k : Nat) (hk : k ≤ p - 1) (v w : Vec) (i : Nat) :
    lnp p v i + k * lnp p w i ≤ p * (p - 1) := by
  have h1 := lnp_le (p := p) (by omega) v i
  have h2 := Nat.mul_le_mul hk (lnp_le (p := p) (by omega) w i)
  rcases hp with rfl | rfl <;> omega

theorem red_fw_addP {p : Nat} (hp : p = 5 ∨ p = 7) (D k : Nat) (hk : k ≤ p - 1) (v w : Vec) :
    ExclK.red (fdOf p D) (Nat.add (pkP p D v) (Nat.mul k (pkP p D w))) =
      fw D (fun i => (lnp p v i + k * lnp p w i) % p) := by
  rw [pkP_fw, pkP_fw]
  change ExclK.red (fdOf p D) (enc ((List.range D).map (lnp p v)) +
    k * enc ((List.range D).map (lnp p w))) = _
  rw [← enc_map_add]
  exact red_fwP hp D (fun i => lnp p v i + k * lnp p w i) (lane_addP hp k hk v w)

theorem red_rv_addP {p : Nat} (hp : p = 5 ∨ p = 7) (D k : Nat) (hk : k ≤ p - 1) (v w : Vec) :
    ExclK.red (fdOf p D) (Nat.add (pkrP p D v) (Nat.mul k (pkrP p D w))) =
      rv D (fun i => (lnp p v i + k * lnp p w i) % p) := by
  rw [pkrP_rv, pkrP_rv]
  change ExclK.red (fdOf p D) (enc ((List.range D).reverse.map (lnp p v)) +
    k * enc ((List.range D).reverse.map (lnp p w))) = _
  rw [← enc_map_add]
  exact red_rvP hp D (fun i => lnp p v i + k * lnp p w i) (lane_addP hp k hk v w)

theorem lane_appP {p : Nat} (hp : p = 5 ∨ p = 7) (c v h : Nat) (hc : c < p) :
    (v % p + (p - c) % p * (h % p)) % p = ((v + (p - c * h % p)) % p) % p := by
  rcases hp with rfl | rfl <;> interval_cases c <;> omega

theorem pkP_applyRefl {P : Pt} {p : Nat} (hp : P.p = p) (hp57 : p = 5 ∨ p = 7) (f h v : Vec) :
    pkP p P.D (P.applyRefl ⟨f, h⟩ v) =
      fw P.D (fun i => (lnp p v i + (p - P.dotv f v) % p * lnp p h i) % p) := by
  rw [pkP_fw]
  unfold fw
  apply enc_map_congr
  intro i hi
  rw [List.mem_range] at hi
  simp only [lnp]
  rw [applyRefl_getD P _ v hi, hp, lane_appP hp57 _ _ _ (dotv_ltP hp (by omega) f v)]

theorem pkrP_applyRefl {P : Pt} {p : Nat} (hp : P.p = p) (hp57 : p = 5 ∨ p = 7) (f h v : Vec) :
    pkrP p P.D (P.applyRefl ⟨f, h⟩ v) =
      rv P.D (fun i => (lnp p v i + (p - P.dotv f v) % p * lnp p h i) % p) := by
  rw [pkrP_rv]
  unfold rv
  apply enc_map_congr
  intro i hi
  rw [List.mem_reverse, List.mem_range] at hi
  simp only [lnp]
  rw [applyRefl_getD P _ v hi, hp, lane_appP hp57 _ _ _ (dotv_ltP hp (by omega) f v)]

theorem kP_le {p : Nat} (hp : 0 < p) (c : Nat) : (p - c) % p ≤ p - 1 := by
  have := Nat.mod_lt (p - c) hp
  omega

theorem appKP_pk {P : Pt} {p : Nat} (hp : P.p = p) (hp57 : p = 5 ∨ p = 7) (hD : P.D ≤ 10)
    (h f v : Vec) :
    ExclK.appK (fdOf p P.D) (pkP p P.D h, pkrP p P.D f) (pkP p P.D v) =
      pkP p P.D (P.applyRefl ⟨f, h⟩ v) := by
  have hp0 : 0 < p := by omega
  unfold ExclK.appK negK
  rw [dotKP_pk hp hp0 (by omega) hD, pkP_applyRefl hp hp57]
  exact red_fw_addP hp57 P.D _ (kP_le hp0 _) v h

theorem conjKP_pk {P : Pt} {p : Nat} (hp : P.p = p) (hp57 : p = 5 ∨ p = 7) (hD : P.D ≤ 10)
    (gh gf rh rf : Vec) :
    ExclK.conjK (fdOf p P.D) (pkP p P.D gh, pkrP p P.D gf) (pkP p P.D rh, pkrP p P.D rf) =
      (pkP p P.D (P.applyRefl ⟨gf, gh⟩ rh), pkrP p P.D (P.applyRefl ⟨gh, gf⟩ rf)) := by
  have hp0 : 0 < p := by omega
  unfold ExclK.conjK
  rw [appKP_pk hp hp57 hD]
  congr 1
  unfold negK
  rw [dotKP_pk hp hp0 (by omega) hD, pkrP_applyRefl hp hp57, dotv_comm P gh rf]
  exact red_rv_addP hp57 P.D _ (kP_le hp0 _) rf gf

theorem smulKP_pk {p : Nat} (hp : p = 5 ∨ p = 7) (D l : Nat) (hl : l < p) (v : Vec) :
    smulK (fdOf p D) l (pkP p D v) = pkP p D ((List.range D).map fun i => l * v.getD i 0 % p) := by
  unfold smulK
  rw [pkP_fw, pkP_fw]
  have e : Nat.mul l (fw D (lnp p v)) = fw D (fun i => l * lnp p v i) := by
    unfold fw
    rw [enc_map_mul]
    rfl
  rw [e, red_fwP hp D _ (fun i => by
    have h0 := lane_addP hp l (by omega) v v i
    omega)]
  unfold fw
  apply enc_map_congr
  intro i hi
  rw [List.mem_range] at hi
  simp [lnp, List.getD_eq_getElem?_getD, hi, Nat.mul_mod]

theorem shiftLeft_unitP (P : Pt) {p : Nat} (hp : 2 ≤ p) {i : Nat} (hi : i < P.D) :
    Nat.shiftLeft 1 (Nat.mul 16 i) = pkP p P.D (P.unit i) := by
  change 1 <<< (16 * i) = _
  have e : (2 : Nat) ^ 16 = 65536 := rfl
  rw [pkP_fw, Nat.shiftLeft_eq, Nat.one_mul, pow_mul, e, ← fw_unit P.D i hi]
  unfold fw
  apply enc_map_congr
  intro j hj
  rw [List.mem_range] at hj
  simp only [lnp, Pt.unit, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj,
    Option.map_some, Option.getD_some]
  split
  · exact (Nat.mod_eq_of_lt (by omega)).symm
  · exact (Nat.zero_mod p).symm

theorem lnp_lt {p : Nat} (hp0 : 0 < p) (hp : p ≤ 65536) (v : Vec) (i : Nat) : lnp p v i < 65536 := by
  have := lnp_le hp0 v i
  omega

theorem pkP_inj {P : Pt} {p : Nat} (hp : P.p = p) (hp0 : 0 < p) (hp1 : p ≤ 65536) (v w : Vec) :
    pkP p P.D v = pkP p P.D w ↔ P.vecEq v w = true := by
  rw [pkP_fw, pkP_fw]
  unfold fw
  rw [enc_map_inj _ _ _ (lnp_lt hp0 hp1 v) (lnp_lt hp0 hp1 w), Pt.vecEq, List.all_eq_true]
  simp only [Pt.ent, hp, lnp, beq_iff_eq]

theorem pkrP_inj {P : Pt} {p : Nat} (hp : P.p = p) (hp0 : 0 < p) (hp1 : p ≤ 65536) (v w : Vec) :
    pkrP p P.D v = pkrP p P.D w ↔ P.vecEq v w = true := by
  rw [pkrP_rv, pkrP_rv]
  unfold rv
  rw [enc_map_inj _ _ _ (lnp_lt hp0 hp1 v) (lnp_lt hp0 hp1 w), Pt.vecEq, List.all_eq_true]
  simp only [List.mem_reverse, Pt.ent, hp, lnp, beq_iff_eq]

end CFSG.TwoNodeSmall.LaneSound

end
