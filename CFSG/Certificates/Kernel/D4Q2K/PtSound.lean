module

public import Certificates.Data.Kernel.D4Q2K.Defs
public import Certificates.Data.CFSGNative.D4Q2.Check

public section

namespace CFSG.KC.D4Q2K

open CFSG.ClassicalInvolution.PhanDn.D4Q2

theorem pf_tb_land (x y i : Nat) : (Nat.land x y).testBit i = (x.testBit i && y.testBit i) :=
  Nat.testBit_and x y i

theorem pf_tb_lor (x y i : Nat) : (Nat.lor x y).testBit i = (x.testBit i || y.testBit i) :=
  Nat.testBit_or x y i

theorem pf_tb_xor (x y i : Nat) : (Nat.xor x y).testBit i = (x.testBit i ^^ y.testBit i) :=
  Nat.testBit_xor x y i

theorem pf_tb_subpow (n v : Nat) :
    (Nat.sub (Nat.pow (nat_lit 2) n) (nat_lit 1)).testBit v = decide (v < n) :=
  Nat.testBit_two_pow_sub_one n v

theorem pf_tb_allPl (v : Nat) : allPl.testBit v = decide (v < 65536) := by
  unfold allPl
  exact pf_tb_subpow (nat_lit 65536) v


theorem pf_tb_notP (x v : Nat) : (notP x).testBit v = (decide (v < 65536) ^^ x.testBit v) := by
  unfold notP
  rw [pf_tb_xor, pf_tb_allPl]

def pf_B (b : Nat) : Nat := (2 ^ (2 ^ b) - 1) <<< (2 ^ b)

def pf_Q (b j : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (pf_B b) (fun i acc => acc ||| (acc <<< (2 ^ (b + 1) * 2 ^ i))) j

theorem pf_tb_lt (v b : Nat) (hv : v < 2 ^ (b + 1)) : v.testBit b = decide (2 ^ b ≤ v) := by
  have hP : 0 < 2 ^ b := Nat.two_pow_pos b
  have h2 : 2 ^ (b + 1) = 2 * 2 ^ b := by rw [Nat.pow_succ, Nat.mul_comm]
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have hlt : v / 2 ^ b < 2 := (Nat.div_lt_iff_lt_mul hP).2 (by omega)
  by_cases h : 2 ^ b ≤ v
  · have : 1 ≤ v / 2 ^ b := (Nat.le_div_iff_mul_le hP).2 (by omega)
    simp only [h, decide_true]
    apply decide_eq_true
    omega
  · have : v / 2 ^ b = 0 := Nat.div_eq_of_lt (by omega)
    simp [h, this]

theorem pf_tb_period (x b m : Nat) : (x + 2 ^ (b + 1) * m).testBit b = x.testBit b := by
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq]
  have : 2 ^ (b + 1) * m = 2 ^ b * (2 * m) := by rw [Nat.pow_succ, Nat.mul_assoc]
  rw [this, Nat.add_mul_div_left _ _ (Nat.two_pow_pos b), Nat.add_mul_mod_self_left]

theorem pf_tb_B (b v : Nat) : (pf_B b).testBit v = (decide (v < 2 ^ (b + 1)) && v.testBit b) := by
  unfold pf_B
  have h2 : 2 ^ (b + 1) = 2 * 2 ^ b := by rw [Nat.pow_succ, Nat.mul_comm]
  rw [Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
  by_cases hv : v < 2 ^ (b + 1)
  · rw [pf_tb_lt v b hv]
    by_cases h : 2 ^ b ≤ v <;> simp [h, hv] <;> omega
  · have : ¬ v - 2 ^ b < 2 ^ b := by omega
    simp [hv, this]

theorem pf_tb_Q (b j v : Nat) :
    (pf_Q b j).testBit v = (decide (v < 2 ^ (b + 1) * 2 ^ j) && v.testBit b) := by
  induction j generalizing v with
  | zero =>
    change (pf_B b).testBit v = _
    rw [pf_tb_B, Nat.pow_zero, Nat.mul_one]
  | succ j ih =>
    change (pf_Q b j ||| (pf_Q b j <<< (2 ^ (b + 1) * 2 ^ j))).testBit v = _
    rw [Nat.testBit_or, Nat.testBit_shiftLeft, ih, ih]
    have h2 : 2 ^ (b + 1) * 2 ^ (j + 1) = 2 * (2 ^ (b + 1) * 2 ^ j) := by
      rw [Nat.pow_succ 2 j]
      rw [Nat.mul_comm (2 ^ j) 2, ← Nat.mul_assoc, Nat.mul_comm _ 2, Nat.mul_assoc]
    rw [h2]
    generalize hs : 2 ^ (b + 1) * 2 ^ j = s
    by_cases hv : v < s
    · have h1 : ¬ v ≥ s := by omega
      have h2 : v < 2 * s := by omega
      simp [hv, h1, h2]
    · have hb : v.testBit b = (v - s).testBit b := by
        have := pf_tb_period (v - s) b (2 ^ j)
        rw [hs] at this
        have e : v - s + s = v := by omega
        rw [e] at this
        exact this
      rw [← hb]
      have e : decide (v - s < s) = decide (v < 2 * s) := by
        simp only [decide_eq_decide]
        omega
      have h1 : v ≥ s := by omega
      simp [hv, h1, e]

theorem pf_bitPl_Q : ∀ b, b < 16 → bitPl b = pf_Q b (15 - b) := by decide +kernel

theorem pf_tb_bitPl {b : Nat} (hb : b < 16) (v : Nat) :
    (bitPl b).testBit v = (decide (v < 65536) && v.testBit b) := by
  rw [pf_bitPl_Q b hb, pf_tb_Q]
  have : 2 ^ (b + 1) * 2 ^ (15 - b) = 65536 := by
    rw [← Nat.pow_add]
    have : b + 1 + (15 - b) = 16 := by omega
    rw [this]
  rw [this]

theorem pf_tb_lo {k : Nat} (hk : k < 8) (v : Nat) :
    (lo k).testBit v = (decide (v < 65536) && v.testBit (2 * k)) :=
  pf_tb_bitPl (b := 2 * k) (by omega) v

theorem pf_tb_hi {k : Nat} (hk : k < 8) (v : Nat) :
    (hi k).testBit v = (decide (v < 65536) && v.testBit (2 * k + 1)) :=
  pf_tb_bitPl (b := 2 * k + 1) (by omega) v

theorem pf_tb_m0 (x0 x1 y0 y1 v : Nat) : (m0 x0 x1 y0 y1).testBit v =
    ((x0.testBit v && y0.testBit v) ^^ (x1.testBit v && y1.testBit v)) := by
  unfold m0
  rw [pf_tb_xor, pf_tb_land, pf_tb_land]

theorem pf_tb_m1 (x0 x1 y0 y1 v : Nat) : (m1 x0 x1 y0 y1).testBit v =
    (((x0.testBit v && y1.testBit v) ^^ (x1.testBit v && y0.testBit v)) ^^
      (x1.testBit v && y1.testBit v)) := by
  unfold m1
  rw [pf_tb_xor, pf_tb_xor, pf_tb_land, pf_tb_land, pf_tb_land]

theorem pf_tb_nz {k : Nat} (hk : k < 8) (v : Nat) :
    (nz k).testBit v = (decide (v < 65536) && (v.testBit (2 * k) || v.testBit (2 * k + 1))) := by
  unfold nz
  rw [pf_tb_lor, pf_tb_lo hk, pf_tb_hi hk]
  cases decide (v < 65536) <;> simp

theorem pf_tb_one {k : Nat} (hk : k < 8) (v : Nat) :
    (one k).testBit v = (decide (v < 65536) && (v.testBit (2 * k) && !v.testBit (2 * k + 1))) := by
  unfold one
  rw [pf_tb_land, pf_tb_notP, pf_tb_lo hk, pf_tb_hi hk]
  cases decide (v < 65536) <;> simp

def pf_C (a b : Bool) : Nat := a.toNat + 2 * b.toNat

theorem pf_mod4 (w : Nat) : w % 4 = pf_C (w.testBit 0) (w.testBit 1) := by
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq]
  unfold pf_C
  by_cases h1 : w % 2 = 1 <;> by_cases h2 : w / 2 % 2 = 1 <;> simp [h1, h2] <;> omega

theorem pf_cd (v k : Nat) : cd v k = pf_C (v.testBit (2 * k)) (v.testBit (2 * k + 1)) := by
  unfold cd
  rw [pf_mod4, Nat.testBit_shiftRight, Nat.testBit_shiftRight, Nat.add_zero]

theorem pf_mul4C (a b c d : Bool) : mul4 (pf_C a b) (pf_C c d) =
    pf_C ((a && c) ^^ (b && d)) (((a && d) ^^ (b && c)) ^^ (b && d)) := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide

theorem pf_xorC (a b c d : Bool) : pf_C a b ^^^ pf_C c d = pf_C (a ^^ c) (b ^^ d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide

theorem pf_normC4 (a b : Bool) : mul4 (pf_C a b) (frob4 (pf_C a b)) = pf_C (a || b) false := by
  cases a <;> cases b <;> decide

theorem pf_C_eq0 (a b : Bool) : (pf_C a b == 0) = (!a && !b) := by
  cases a <;> cases b <;> decide

theorem pf_C_ne0 (a b : Bool) : (pf_C a b != 0) = (a || b) := by
  cases a <;> cases b <;> decide

theorem pf_C_eq1 (a b : Bool) : (pf_C a b == 1) = (a && !b) := by
  cases a <;> cases b <;> decide

theorem pf_zUp_succ (k : Nat) : zUp (k + 1) = Nat.land (zUp k) (notP (nz k)) := rfl

theorem pf_zUp_zero : zUp 0 = allPl := rfl

theorem pf_quadC {v : Nat} (hv : v < 65536) :
    quadC v = pf_C (quadLo.testBit v) (quadHi.testBit v) := by
  unfold quadC
  simp only [pf_cd, pf_mul4C, pf_xorC]
  unfold quadLo quadHi
  simp only [pf_tb_xor, pf_tb_m0, pf_tb_m1, Nat.zero_testBit, Nat.add_eq]
  simp (disch := omega) only [pf_tb_lo, pf_tb_hi]
  simp [hv]

theorem pf_tb_hermPl (v : Nat) : hermPl.testBit v = (false ^^ (nz 0).testBit v ^^ (nz 1).testBit v ^^
    (nz 2).testBit v ^^ (nz 3).testBit v ^^ (nz 4).testBit v ^^ (nz 5).testBit v ^^
    (nz 6).testBit v ^^ (nz 7).testBit v) := by
  unfold hermPl
  simp only [pf_tb_xor, Nat.zero_testBit]

theorem pf_hermC {v : Nat} (hv : v < 65536) : hermC v v = pf_C (hermPl.testBit v) false := by
  unfold hermC
  simp only [pf_cd, pf_normC4, pf_xorC]
  rw [pf_tb_hermPl]
  simp (disch := omega) only [pf_tb_nz]
  simp [hv]

theorem pf_range8 : List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] := rfl

theorem pf_normC {v : Nat} (hv : v < 65536) : normC v = normPl.testBit v := by
  unfold normC
  rw [pf_range8]
  simp only [List.find?_cons, List.find?_nil, pf_cd, pf_C_ne0, pf_C_eq1]
  unfold normPl
  simp only [pf_zUp_succ, pf_zUp_zero, pf_tb_lor, pf_tb_land, pf_tb_notP, pf_tb_allPl,
    Nat.zero_testBit, hv, decide_true]
  simp (disch := omega) only [pf_tb_nz, pf_tb_one]
  simp only [hv, decide_true, Bool.true_and, Bool.true_xor, Bool.false_or, Bool.true_and]
  simp only [Nat.reduceMul, Nat.reduceAdd]
  cases h0 : v.testBit 0 <;> cases h1 : v.testBit 1 <;> simp [*] <;>
    cases h2 : v.testBit 2 <;> cases h3 : v.testBit 3 <;> simp [*] <;>
    cases h4 : v.testBit 4 <;> cases h5 : v.testBit 5 <;> simp [*] <;>
    cases h6 : v.testBit 6 <;> cases h7 : v.testBit 7 <;> simp [*] <;>
    cases h8 : v.testBit 8 <;> cases h9 : v.testBit 9 <;> simp [*] <;>
    cases h10 : v.testBit 10 <;> cases h11 : v.testBit 11 <;> simp [*] <;>
    cases h12 : v.testBit 12 <;> cases h13 : v.testBit 13 <;> simp [*] <;>
    cases h14 : v.testBit 14 <;> cases h15 : v.testBit 15 <;> simp [*]

theorem pf_tb_ptPl_lo {v : Nat} (hv : v < 65536) :
    ptPl.testBit v = (normC v && quadC v == 0 && hermC v v != 0) := by
  rw [pf_normC hv, pf_quadC hv, pf_hermC hv, pf_C_eq0, pf_C_ne0]
  unfold ptPl
  simp only [pf_tb_land, pf_tb_notP, hv, decide_true]
  cases normPl.testBit v <;> cases quadLo.testBit v <;> cases quadHi.testBit v <;>
    cases hermPl.testBit v <;> rfl

theorem pf_tb_ptPl_hi {v : Nat} (hv : ¬ v < 65536) : ptPl.testBit v = false := by
  unfold ptPl
  simp only [pf_tb_land, pf_tb_hermPl]
  simp (disch := omega) only [pf_tb_nz]
  simp [hv]

theorem pf_tb_plOf (L : List Nat) (v : Nat) : (plOf L).testBit v = decide (v ∈ L) := by
  induction L with
  | nil => exact Nat.zero_testBit v
  | cons p t ih =>
    change ((1 <<< p) ||| plOf t).testBit v = _
    rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow, ih]
    simp [List.mem_cons, eq_comm]

theorem pf_incFrom (L : List Nat) (c : Nat) (h : incFrom L c = true) :
    (∀ x ∈ L, x < 65536 ∧ c ≤ x) ∧ L.Pairwise (· < ·) := by
  induction L generalizing c with
  | nil => simp
  | cons p t ih =>
    change (Nat.ble c p && (Nat.blt p 65536 && incFrom t (p + 1))) = true at h
    simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at h
    obtain ⟨h1, h2, h3⟩ := h
    obtain ⟨ih1, ih2⟩ := ih (p + 1) h3
    refine ⟨?_, List.pairwise_cons.2 ⟨fun x hx => by have := ih1 x hx; omega, ih2⟩⟩
    intro x hx
    rcases List.mem_cons.1 hx with hx | hx
    · omega
    · have := ih1 x hx
      omega

theorem pf_sorted_eq : ∀ {l1 l2 : List Nat}, l1.Pairwise (· < ·) → l2.Pairwise (· < ·) →
    (∀ x, x ∈ l1 ↔ x ∈ l2) → l1 = l2 := by
  intro l1
  induction l1 with
  | nil =>
    intro l2 _ _ h
    cases l2 with
    | nil => rfl
    | cons b t => exact absurd ((h b).2 (by simp)) (by simp)
  | cons a t ih =>
    intro l2 h1 h2 h
    cases l2 with
    | nil => exact absurd ((h a).1 (by simp)) (by simp)
    | cons b u =>
      rw [List.pairwise_cons] at h1 h2
      have hab : a = b := by
        have ha := (h a).1 (by simp)
        have hb := (h b).2 (by simp)
        rcases List.mem_cons.1 ha with e | ha'
        · exact e
        · rcases List.mem_cons.1 hb with e | hb'
          · exact e.symm
          · have := h2.1 a ha'
            have := h1.1 b hb'
            omega
      subst hab
      rw [ih h1.2 h2.2 (fun x => ?_)]
      constructor
      · intro hx
        rcases List.mem_cons.1 ((h x).1 (List.mem_cons_of_mem _ hx)) with e | e
        · have := h1.1 x hx
          omega
        · exact e
      · intro hx
        rcases List.mem_cons.1 ((h x).2 (List.mem_cons_of_mem _ hx)) with e | e
        · have := h2.1 x hx
          omega
        · exact e

theorem ptK_sound {L : List Nat} (h : ptK L = true) : ptCodes () = L.toArray := by
  change (incFrom L 0 && Nat.beq (plOf L) ptPl) = true at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  have hp : plOf L = ptPl := Nat.eq_of_beq_eq_true h2
  obtain ⟨hb, hs⟩ := pf_incFrom L 0 h1
  rw [← Array.toList_inj, List.toList_toArray]
  unfold ptCodes
  rw [Array.toList_filter, Array.toList_range]
  refine (pf_sorted_eq hs (List.pairwise_lt_range.filter _) (fun x => ?_)).symm
  rw [List.mem_filter, List.mem_range]
  have hx : x ∈ L ↔ ptPl.testBit x = true := by
    rw [← hp, pf_tb_plOf, decide_eq_true_iff]
  rw [hx]
  by_cases h : x < 65536
  · rw [pf_tb_ptPl_lo h]
    simp [h]
  · rw [pf_tb_ptPl_hi h]
    simp [h]

theorem lenL_eq (l : List Nat) : lenL l = l.length := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    change Nat.succ (lenL l) = (x :: l).length
    rw [ih, List.length_cons]

theorem sizeCheck_of {L : List Nat} {F : Array (Array Nat)} (h : ptK L = true)
    (hL : L.length = 2240) (hF : F.size = 4480) : sizeCheck (mkTabs (ptCodes ()) F) = true := by
  change ((ptCodes ()).size == 2240 && F.size == 4480) = true
  rw [ptK_sound h, List.size_toArray, hL, hF]
  rfl

theorem pf_strictB (y : Nat) (k : Nat → Bool) : Enum.strictB y k = k y := by
  cases y <;> rfl

theorem pf_tb_shr (x i j : Nat) : (Nat.shiftRight x i).testBit j = x.testBit (i + j) :=
  Nat.testBit_shiftRight x

theorem pf_tb_shl (x i j : Nat) :
    (Nat.shiftLeft x i).testBit j = (decide (j ≥ i) && x.testBit (j - i)) :=
  Nat.testBit_shiftLeft x

theorem pf_tb_65535 (j : Nat) : (65535 : Nat).testBit j = decide (j < 16) :=
  Nat.testBit_two_pow_sub_one 16 j

theorem pf_tb_ptAt (T i j : Nat) :
    (ptAt T i).testBit j = (decide (j < 16) && T.testBit (16 * i + j)) := by
  unfold ptAt
  rw [pf_tb_land, pf_tb_shr, pf_tb_65535, Bool.and_comm]
  rfl

theorem pf_tb_hi16 {p j : Nat} (hp : p < 65536) (hj : 16 ≤ j) : p.testBit j = false := by
  apply Nat.testBit_lt_two_pow
  have : 2 ^ 16 ≤ 2 ^ j := Nat.pow_le_pow_right (by decide) hj
  exact Nat.lt_of_lt_of_le hp this

theorem pf_ptAt_cons0 {p : Nat} (X : Nat) (hp : p < 65536) :
    ptAt (Nat.lor p (Nat.shiftLeft X 16)) 0 = p := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [pf_tb_ptAt, pf_tb_lor, pf_tb_shl, Nat.mul_zero, Nat.zero_add]
  by_cases hj : j < 16
  · have : ¬ j ≥ 16 := by omega
    simp [hj, this]
  · rw [pf_tb_hi16 hp (by omega)]
    simp [hj]

theorem pf_ptAt_consS {p : Nat} (X i : Nat) (hp : p < 65536) :
    ptAt (Nat.lor p (Nat.shiftLeft X 16)) (i + 1) = ptAt X i := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [pf_tb_ptAt, pf_tb_ptAt, pf_tb_lor, pf_tb_shl, pf_tb_hi16 hp (by omega)]
  have e : 16 * (i + 1) + j - 16 = 16 * i + j := by omega
  have h16 : 16 * (i + 1) + j ≥ 16 := by omega
  rw [e]
  simp [h16]

theorem pf_ptAt : ∀ (L : List Nat), (∀ x ∈ L, x < 65536) → ∀ i, ptAt (packL L) i = L[i]!
  | [], _, i => by
    rw [List.getElem!_nil]
    apply Nat.eq_of_testBit_eq
    intro j
    rw [pf_tb_ptAt]
    have : packL [] = 0 := rfl
    rw [this, Nat.zero_testBit, Bool.and_false]
    exact (Nat.zero_testBit j).symm
  | p :: t, h, 0 => by
    rw [List.getElem!_cons_zero]
    exact pf_ptAt_cons0 (packL t) (h p (by simp))
  | p :: t, h, i + 1 => by
    rw [List.getElem!_cons_succ]
    have e := pf_ptAt_consS (packL t) i (h p (by simp))
    change ptAt (Nat.lor p (Nat.shiftLeft (packL t) 16)) (i + 1) = _
    rw [e]
    exact pf_ptAt t (fun x hx => h x (by simp [hx])) i

theorem pf_cd_lt (v k : Nat) : cd v k < 4 := Nat.mod_lt _ (by decide)

theorem pf_cdK (v k : Nat) : cdK v k = cd v k := Nat.and_two_pow_sub_one_eq_mod _ 2

theorem pf_mulK4 : ∀ a, a < 4 → ∀ b, b < 4 → mulK a b = mul4 a b := by decide +kernel

theorem pf_frobK4 : ∀ a, a < 4 → frobK a = frob4 a ∧ frob4 a < 4 := by decide +kernel

theorem pf_mulK_cc (u k v l : Nat) : mulK (cd u k) (cd v l) = mul4 (cd u k) (cd v l) :=
  pf_mulK4 _ (pf_cd_lt u k) _ (pf_cd_lt v l)

theorem pf_mulK_cf (u k v l : Nat) :
    mulK (cd u k) (frobK (cd v l)) = mul4 (cd u k) (frob4 (cd v l)) := by
  rw [(pf_frobK4 _ (pf_cd_lt v l)).1]
  exact pf_mulK4 _ (pf_cd_lt u k) _ (pf_frobK4 _ (pf_cd_lt v l)).2

theorem pf_xor_eq (x y : Nat) : Nat.xor x y = x ^^^ y := rfl

theorem pf_polarK (u v : Nat) : polarK u v = polarC u v := by
  unfold polarK polarC
  simp only [pf_cdK, Nat.add_eq, Nat.reduceAdd, pf_mulK_cc, pf_xor_eq]
  change 0 ^^^ _ ^^^ _ ^^^ _ ^^^ _ = _
  simp only [Nat.zero_xor, Nat.xor_assoc]

theorem pf_hermK (u v : Nat) : hermK u v = hermC u v := by
  unfold hermK hermC
  simp only [pf_cdK, pf_mulK_cf, pf_xor_eq]
  change 0 ^^^ _ ^^^ _ ^^^ _ ^^^ _ ^^^ _ ^^^ _ ^^^ _ ^^^ _ = _
  simp only [Nat.zero_xor, Nat.xor_assoc]

theorem pf_adjK {u v : Nat} (h : adjK u v = true) : ptAdjC u v = true := by
  unfold adjK at h
  rw [pf_polarK, pf_hermK] at h
  change (!(Nat.beq u v) && (Nat.beq (polarC u v) 0 && Nat.beq (hermC u v) 0)) = true at h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨h1, h2, h3⟩ := h
  have e1 : u ≠ v := Nat.ne_of_beq_eq_false h1
  have e2 : polarC u v = 0 := Nat.eq_of_beq_eq_true h2
  have e3 : hermC u v = 0 := Nat.eq_of_beq_eq_true h3
  unfold ptAdjC
  simp [e1, e2, e3]

theorem pf_frame {L : List Nat} (hL : ∀ x ∈ L, x < 65536) (fr : Array Nat)
    (h : frameOK (packL L) fr.toList = true) :
    (fr.size == 4 && fr.all (· < 2240) && ptAdjC L.toArray[fr[0]!]! L.toArray[fr[1]!]! &&
      ptAdjC L.toArray[fr[0]!]! L.toArray[fr[2]!]! && ptAdjC L.toArray[fr[0]!]! L.toArray[fr[3]!]! &&
      ptAdjC L.toArray[fr[1]!]! L.toArray[fr[2]!]! && ptAdjC L.toArray[fr[1]!]! L.toArray[fr[3]!]! &&
      ptAdjC L.toArray[fr[2]!]! L.toArray[fr[3]!]!) = true := by
  rw [← Array.all_toList, ← Array.length_toList]
  simp only [← Array.getElem!_toList]
  generalize fr.toList = l at h ⊢
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, t⟩⟩⟩⟩⟩
  · cases h
  · cases h
  · cases h
  · cases h
  · change (Nat.blt a 2240 && (Nat.blt b 2240 && (Nat.blt c 2240 && (Nat.blt d 2240 &&
      (adjK (ptAt (packL L) a) (ptAt (packL L) b) && (adjK (ptAt (packL L) a) (ptAt (packL L) c) &&
      (adjK (ptAt (packL L) a) (ptAt (packL L) d) && (adjK (ptAt (packL L) b) (ptAt (packL L) c) &&
      (adjK (ptAt (packL L) b) (ptAt (packL L) d) &&
        adjK (ptAt (packL L) c) (ptAt (packL L) d)))))))))) = true at h
    simp only [Bool.and_eq_true, Nat.blt_eq, pf_ptAt L hL] at h
    obtain ⟨ha, hb, hc, hd, h01, h02, h03, h12, h13, h23⟩ := h
    simp only [List.getElem!_cons_zero, List.getElem!_cons_succ, List.length_cons,
      List.length_nil, List.all_cons, List.all_nil, ha, hb, hc, hd, decide_true, Bool.and_true,
      Nat.reduceAdd, beq_self_eq_true, pf_adjK h01, pf_adjK h02, pf_adjK h03,
      pf_adjK h12, pf_adjK h13, pf_adjK h23]
  · have : lenL (a :: b :: c :: d :: e :: t) = t.length + 5 := by
      rw [lenL_eq]
      simp
    unfold frameOK at h
    rw [this] at h
    cases h

theorem pf_frameAll (T : Nat) : ∀ (G : List (Array Nat)),
    List.rec (motive := fun _ => Bool) true (fun fr _ ih => bAnd(frameOK T fr.toList, ih)) G = true →
      ∀ fr ∈ G, frameOK T fr.toList = true
  | [], _, fr, hfr => absurd hfr (by simp)
  | g :: G, h, fr, hfr => by
    change (frameOK T g.toList && List.rec (motive := fun _ => Bool) true
      (fun fr _ ih => bAnd(frameOK T fr.toList, ih)) G) = true at h
    rw [Bool.and_eq_true] at h
    rcases List.mem_cons.1 hfr with e | e
    · rw [e]
      exact h.1
    · exact pf_frameAll T G h.2 fr e

theorem pf_mkTabs_frames (P : Array Nat) (F : Array (Array Nat)) : (mkTabs P F).frames = F := rfl

theorem pf_mkTabs_pts (P : Array Nat) (F : Array (Array Nat)) : (mkTabs P F).pts = P := rfl

theorem pf_ptK_lt {L : List Nat} (h : ptK L = true) : ∀ x ∈ L, x < 65536 := by
  change (incFrom L 0 && Nat.beq (plOf L) ptPl) = true at h
  rw [Bool.and_eq_true] at h
  exact fun x hx => ((pf_incFrom L 0 h.1).1 x hx).1

theorem frameK_sound {L : List Nat} {F : Array (Array Nat)} (hp : ptK L = true)
    (h : frameK L F.toList = true) : frameCheck (mkTabs (ptCodes ()) F) = true := by
  have hL := pf_ptK_lt hp
  unfold frameK at h
  rw [pf_strictB] at h
  have hall := pf_frameAll (packL L) F.toList h
  unfold frameCheck
  rw [pf_mkTabs_frames, pf_mkTabs_pts, ptK_sound hp, ← Array.all_toList, List.all_eq_true]
  intro fr hfr
  exact pf_frame hL fr (hall fr hfr)

theorem mr_tb_land (a b i : Nat) : (Nat.land a b).testBit i = (a.testBit i && b.testBit i) :=
  Nat.testBit_and a b i

theorem mr_tb_lor (a b i : Nat) : (Nat.lor a b).testBit i = (a.testBit i || b.testBit i) :=
  Nat.testBit_or a b i

theorem mr_tb_xor (a b i : Nat) : (Nat.xor a b).testBit i = (a.testBit i ^^ b.testBit i) :=
  Nat.testBit_xor a b i

theorem mr_tb_shl (a n i : Nat) :
    (Nat.shiftLeft a n).testBit i = (decide (n ≤ i) && a.testBit (i - n)) :=
  Nat.testBit_shiftLeft a

theorem mr_tb_shr (a n i : Nat) : (Nat.shiftRight a n).testBit i = a.testBit (n + i) :=
  Nat.testBit_shiftRight a

theorem mr_rec_succ {α : Sort _} (z : α) (s : Nat → α → α) (n : Nat) :
    Nat.rec (motive := fun _ => α) z s (n + 1) = s n (Nat.rec (motive := fun _ => α) z s n) := rfl

theorem mr_rec_zero {α : Sort _} (z : α) (s : Nat → α → α) :
    Nat.rec (motive := fun _ => α) z s 0 = z := rfl

theorem mr_strictB (y : Nat) (k : Nat → Bool) : CFSG.KC.Enum.strictB y k = k y := by
  cases y <;> rfl

theorem mr_strictN (y : Nat) (k : Nat → Nat) : CFSG.KC.Enum.strictN y k = k y := by
  cases y <;> rfl

theorem mr_rec_or_iff (f : Nat → Bool) (n : Nat) :
    Nat.rec (motive := fun _ => Bool) false (fun c acc => acc || f c) n = true ↔
      ∃ c < n, f c = true := by
  induction n with
  | zero => simp [mr_rec_zero]
  | succ n ih =>
    simp only [mr_rec_succ]
    rw [Bool.or_eq_true, ih]
    constructor
    · rintro (⟨c, hc, h⟩ | h)
      · exact ⟨c, by omega, h⟩
      · exact ⟨n, by omega, h⟩
    · rintro ⟨c, hc, h⟩
      by_cases hcn : c = n
      · subst hcn
        exact Or.inr h
      · exact Or.inl ⟨c, by omega, h⟩

theorem mr_rec_or_false {f : Nat → Bool} {n : Nat} (h : ∀ c < n, f c = false) :
    Nat.rec (motive := fun _ => Bool) false (fun c acc => acc || f c) n = false := by
  rw [Bool.eq_false_iff]
  intro hr
  obtain ⟨c, hc, hf⟩ := (mr_rec_or_iff f n).mp hr
  rw [h c hc] at hf
  exact Bool.false_ne_true hf

theorem mr_rec_xor_false {f : Nat → Bool} {n : Nat} (h : ∀ c < n, f c = false) :
    Nat.rec (motive := fun _ => Bool) false (fun c acc => acc ^^ f c) n = false := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [mr_rec_succ]
    rw [ih (fun c hc => h c (by omega)), h n (by omega)]
    rfl

theorem mr_rec_or_congr {f g : Nat → Bool} {n : Nat} (h : ∀ c < n, f c = g c) :
    Nat.rec (motive := fun _ => Bool) false (fun c acc => acc || f c) n =
      Nat.rec (motive := fun _ => Bool) false (fun c acc => acc || g c) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [mr_rec_succ]
    rw [ih (fun c hc => h c (by omega)), h n (by omega)]

theorem mr_rec_xor_congr {f g : Nat → Bool} {n : Nat} (h : ∀ c < n, f c = g c) :
    Nat.rec (motive := fun _ => Bool) false (fun c acc => acc ^^ f c) n =
      Nat.rec (motive := fun _ => Bool) false (fun c acc => acc ^^ g c) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [mr_rec_succ]
    rw [ih (fun c hc => h c (by omega)), h n (by omega)]

theorem mr_rec_xor_tb (f : Nat → Nat) (n i : Nat) :
    (Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun c acc => Nat.xor acc (f c)) n).testBit i =
      Nat.rec (motive := fun _ => Bool) false (fun c acc => acc ^^ (f c).testBit i) n := by
  induction n with
  | zero => exact Nat.zero_testBit i
  | succ n ih =>
    simp only [mr_rec_succ]
    rw [mr_tb_xor, ih]

theorem mr_rec_lor_tb (f : Nat → Nat) (n i : Nat) :
    (Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun c acc => Nat.lor acc (f c)) n).testBit i =
      Nat.rec (motive := fun _ => Bool) false (fun c acc => acc || (f c).testBit i) n := by
  induction n with
  | zero => exact Nat.zero_testBit i
  | succ n ih =>
    simp only [mr_rec_succ]
    rw [mr_tb_lor, ih]

theorem mr_mul4_lt (a : Nat) {b : Nat} (hb : b < 4) : mul4 a b < 4 := by
  unfold mul4
  split <;> omega

theorem mr_frob4_lt {a : Nat} (ha : a < 4) : frob4 a < 4 := by
  unfold frob4
  split <;> omega

theorem mr_cd_lt (v c : Nat) : cd v c < 4 := Nat.mod_lt _ (by decide)

theorem mr_cd_tb (v c j : Nat) :
    (cd v c).testBit j = (decide (j < 2) && v.testBit (2 * c + j)) := by
  unfold cd
  have h4 : (4 : Nat) = 2 ^ 2 := rfl
  rw [h4, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]

theorem mr_cdK (v k : Nat) : cdK v k = cd v k := by
  apply Nat.eq_of_testBit_eq
  intro j
  change (v >>> (2 * k) &&& 3).testBit j = _
  have h3 : (3 : Nat) = 2 ^ 2 - 1 := rfl
  rw [Nat.testBit_and, Nat.testBit_shiftRight, h3, Nat.testBit_two_pow_sub_one, mr_cd_tb,
    Bool.and_comm]

theorem mr_cdK_lt (v k : Nat) : cdK v k < 4 := by
  rw [mr_cdK]
  exact mr_cd_lt v k

theorem mr_frobK : ∀ a < 4, frobK a = frob4 a := by decide

theorem mr_frobK_lt (a : Nat) : frobK a < 4 :=
  Nat.lt_of_le_of_lt (Nat.and_le_right (n := Nat.shiftRight frobT (Nat.mul 2 a)) (m := 3))
    (by decide)

theorem mr_mul4_tb0 : ∀ a < 4, ∀ y < 4, (mul4 a y).testBit 0 =
    ((a.testBit 0 && y.testBit 0) ^^ (a.testBit 1 && y.testBit 1)) := by decide

theorem mr_mul4_tb1 : ∀ a < 4, ∀ y < 4, (mul4 a y).testBit 1 =
    (((a.testBit 0 && y.testBit 1) ^^ (a.testBit 1 && y.testBit 0)) ^^
      (a.testBit 1 && y.testBit 1)) := by
  decide

theorem mr_mul4_comm : ∀ a < 4, ∀ b < 4, mul4 a b = mul4 b a := by decide

theorem mr_frob4_tb : ∀ a < 4, (frob4 a).testBit 0 = (a.testBit 0 ^^ a.testBit 1) ∧
    (frob4 a).testBit 1 = a.testBit 1 := by decide

theorem mr_ne4 : ∀ x < 4, ∀ y < 4,
    (x != y) = ((x.testBit 0 ^^ y.testBit 0) || (x.testBit 1 ^^ y.testBit 1)) := by decide

theorem mr_beq0 : ∀ x < 4, (x == 0) = !(x.testBit 0 || x.testBit 1) := by decide

theorem mr_cd_xor (x y c : Nat) : cd (x ^^^ y) c = cd x c ^^^ cd y c := by
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [mr_cd_tb, Nat.testBit_xor]
  cases decide (j < 2) <;> simp

theorem mr_cd_digits (d0 d1 d2 d3 d4 d5 d6 d7 : Nat) (h0 : d0 < 4) (h1 : d1 < 4) (h2 : d2 < 4)
    (h3 : d3 < 4) (h4 : d4 < 4) (h5 : d5 < 4) (h6 : d6 < 4) (h7 : d7 < 4) :
    (fun x => cd x 0 = d0 ∧ cd x 1 = d1 ∧ cd x 2 = d2 ∧ cd x 3 = d3 ∧ cd x 4 = d4 ∧ cd x 5 = d5 ∧
      cd x 6 = d6 ∧ cd x 7 = d7)
      (d0 + 4 * d1 + 16 * d2 + 64 * d3 + 256 * d4 + 1024 * d5 + 4096 * d6 + 16384 * d7) := by
  simp only [cd, Nat.shiftRight_eq_div_pow, Nat.reducePow, Nat.reduceMul]
  omega

theorem mr_cd_smulC (a b c : Nat) (hc : c < 8) : cd (smulC a b) c = mul4 a (cd b c) := by
  have hd : ∀ k, mul4 a (cd b k) < 4 := fun k => mr_mul4_lt a (mr_cd_lt b k)
  have H := mr_cd_digits _ _ _ _ _ _ _ _ (hd 0) (hd 1) (hd 2) (hd 3) (hd 4) (hd 5) (hd 6) (hd 7)
  match c, hc with
  | 0, _ => exact H.1
  | 1, _ => exact H.2.1
  | 2, _ => exact H.2.2.1
  | 3, _ => exact H.2.2.2.1
  | 4, _ => exact H.2.2.2.2.1
  | 5, _ => exact H.2.2.2.2.2.1
  | 6, _ => exact H.2.2.2.2.2.2.1
  | 7, _ => exact H.2.2.2.2.2.2.2

theorem mr_smulC_lt (a b : Nat) : smulC a b < 65536 := by
  have hd : ∀ k, mul4 a (cd b k) < 4 := fun k => mr_mul4_lt a (mr_cd_lt b k)
  have := hd 0
  have := hd 1
  have := hd 2
  have := hd 3
  have := hd 4
  have := hd 5
  have := hd 6
  have := hd 7
  unfold smulC
  omega

theorem mr_hermC_lt (u v : Nat) : hermC u v < 4 := by
  have h : ∀ k, mul4 (cd u k) (frob4 (cd v k)) < 2 ^ 2 :=
    fun k => mr_mul4_lt _ (mr_frob4_lt (mr_cd_lt v k))
  unfold hermC
  change _ < 2 ^ 2
  repeat' apply Nat.xor_lt_two_pow
  all_goals exact h _

theorem mr_polarC_lt (u v : Nat) : polarC u v < 4 := by
  have h : ∀ k l, mul4 (cd u k) (cd v l) < 2 ^ 2 := fun k l => mr_mul4_lt _ (mr_cd_lt v l)
  unfold polarC
  change _ < 2 ^ 2
  repeat' apply Nat.xor_lt_two_pow
  all_goals exact h _ _

theorem mr_hermC_rec (u v e : Nat) : (hermC u v).testBit e =
    Nat.rec (motive := fun _ => Bool) false
      (fun k acc => acc ^^ (mul4 (cd u k) (frob4 (cd v k))).testBit e) (nat_lit 8) := by
  unfold hermC
  simp only [mr_rec_succ, mr_rec_zero, Nat.testBit_xor, Bool.false_xor]

theorem mr_polarC_rec (u v e : Nat) : (polarC u v).testBit e =
    Nat.rec (motive := fun _ => Bool) false
      (fun c acc => acc ^^ ((mul4 (cd u c) (cd v (c + 4))).testBit e ^^
        (mul4 (cd u (c + 4)) (cd v c)).testBit e)) (nat_lit 4) := by
  unfold polarC
  simp only [mr_rec_succ, mr_rec_zero, Nat.testBit_xor, Bool.false_xor, Bool.xor_assoc,
    Nat.reduceAdd]

theorem mr_shl_one (n : Nat) : Nat.shiftLeft 1 n = 2 ^ n := by
  rw [← Nat.one_mul (2 ^ n), ← Nat.shiftLeft_eq]
  rfl

theorem mr_low_tb (n i : Nat) :
    (Nat.sub (Nat.shiftLeft (nat_lit 1) n) (nat_lit 1)).testBit i = decide (i < n) := by
  rw [mr_shl_one, Nat.sub_eq, Nat.testBit_two_pow_sub_one]

theorem mr_allP_tb (i : Nat) : allP.testBit i = decide (i < 2240) := mr_low_tb 2240 i

theorem mr_cst_tb {c : Nat} (hc : c < 2) (i : Nat) :
    (cst c).testBit i = (c.testBit 0 && decide (i < 2240)) := by
  unfold cst
  match c, hc with
  | 0, _ =>
    change (0 * allP).testBit i = _
    rw [Nat.zero_mul, Nat.zero_testBit, Nat.zero_testBit, Bool.false_and]
  | 1, _ =>
    change (1 * allP).testBit i = _
    rw [Nat.one_mul, mr_allP_tb]
    rfl

theorem mr_mlo_tb {y : Nat} (hy : y < 4) (x0 x1 i : Nat) :
    (mlo x0 x1 y).testBit i =
      (((x0.testBit i && y.testBit 0) ^^ (x1.testBit i && y.testBit 1)) && decide (i < 2240)) := by
  have h0 : Nat.land y (nat_lit 1) < 2 := Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  have h1 : Nat.shiftRight y (nat_lit 1) < 2 := by
    change y >>> 1 < 2
    rw [Nat.shiftRight_eq_div_pow]
    omega
  have t10 : Nat.testBit (nat_lit 1) 0 = true := by decide
  unfold mlo m0
  rw [mr_tb_xor, mr_tb_land, mr_tb_land, mr_cst_tb h0, mr_cst_tb h1, mr_tb_land, mr_tb_shr, t10]
  generalize x0.testBit i = a
  generalize x1.testBit i = b
  generalize y.testBit 0 = p
  generalize y.testBit (1 + 0) = q
  generalize decide (i < 2240) = d
  revert a b p q d
  decide

theorem mr_mhi_tb {y : Nat} (hy : y < 4) (x0 x1 i : Nat) :
    (mhi x0 x1 y).testBit i =
      ((((x0.testBit i && y.testBit 1) ^^ (x1.testBit i && y.testBit 0)) ^^
        (x1.testBit i && y.testBit 1)) && decide (i < 2240)) := by
  have h0 : Nat.land y (nat_lit 1) < 2 := Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  have h1 : Nat.shiftRight y (nat_lit 1) < 2 := by
    change y >>> 1 < 2
    rw [Nat.shiftRight_eq_div_pow]
    omega
  have t10 : Nat.testBit (nat_lit 1) 0 = true := by decide
  unfold mhi m1
  rw [mr_tb_xor, mr_tb_xor, mr_tb_land, mr_tb_land, mr_tb_land, mr_cst_tb h0, mr_cst_tb h1,
    mr_tb_land, mr_tb_shr, t10]
  generalize x0.testBit i = a
  generalize x1.testBit i = b
  generalize y.testBit 0 = p
  generalize y.testBit (1 + 0) = q
  generalize decide (i < 2240) = d
  revert a b p q d
  decide

theorem mr_mlo_gen {x0 x1 a y i : Nat} (h0 : x0.testBit i = a.testBit 0)
    (h1 : x1.testBit i = a.testBit 1) (ha : a < 4) (hy : y < 4) (hi : i < 2240) :
    (mlo x0 x1 y).testBit i = (mul4 a y).testBit 0 := by
  rw [mr_mlo_tb hy, h0, h1, mr_mul4_tb0 a ha y hy, decide_eq_true hi, Bool.and_true]

theorem mr_mhi_gen {x0 x1 a y i : Nat} (h0 : x0.testBit i = a.testBit 0)
    (h1 : x1.testBit i = a.testBit 1) (ha : a < 4) (hy : y < 4) (hi : i < 2240) :
    (mhi x0 x1 y).testBit i = (mul4 a y).testBit 1 := by
  rw [mr_mhi_tb hy, h0, h1, mr_mul4_tb1 a ha y hy, decide_eq_true hi, Bool.and_true]

theorem mr_X0 {X : Nat → Nat} {v i : Nat} (hX : ∀ b, (X b).testBit i = v.testBit b) (c : Nat) :
    (X (Nat.mul (nat_lit 2) c)).testBit i = (cd v c).testBit 0 := by
  rw [hX, mr_cd_tb]
  rfl

theorem mr_X1 {X : Nat → Nat} {v i : Nat} (hX : ∀ b, (X b).testBit i = v.testBit b) (c : Nat) :
    (X (Nat.succ (Nat.mul (nat_lit 2) c))).testBit i = (cd v c).testBit 1 := by
  rw [hX, mr_cd_tb]
  rfl

theorem mr_mulP_pt {X : Nat → Nat} {v i : Nat} (hX : ∀ b, (X b).testBit i = v.testBit b)
    (hi : i < 2240) {e y : Nat} (he : e < 2) (hy : y < 4) (c : Nat) :
    (mulP e (X (Nat.mul (nat_lit 2) c)) (X (Nat.succ (Nat.mul (nat_lit 2) c))) y).testBit i =
      (mul4 (cd v c) y).testBit e := by
  match e, he with
  | 0, _ => exact mr_mlo_gen (mr_X0 hX c) (mr_X1 hX c) (mr_cd_lt v c) hy hi
  | 1, _ => exact mr_mhi_gen (mr_X0 hX c) (mr_X1 hX c) (mr_cd_lt v c) hy hi

theorem mr_mulQ_pt {X : Nat → Nat} {v i : Nat} (hX : ∀ b, (X b).testBit i = v.testBit b)
    (hi : i < 2240) {e y : Nat} (he : e < 2) (hy : y < 4) (c : Nat) :
    (mulP e (Nat.xor (X (Nat.mul (nat_lit 2) c)) (X (Nat.succ (Nat.mul (nat_lit 2) c))))
      (X (Nat.succ (Nat.mul (nat_lit 2) c))) y).testBit i =
      (mul4 (frob4 (cd v c)) y).testBit e := by
  have hf := mr_frob4_tb _ (mr_cd_lt v c)
  have h0 : (Nat.xor (X (Nat.mul (nat_lit 2) c)) (X (Nat.succ (Nat.mul (nat_lit 2) c)))).testBit i =
      (frob4 (cd v c)).testBit 0 := by
    rw [mr_tb_xor, mr_X0 hX c, mr_X1 hX c, hf.1]
  have h1 : (X (Nat.succ (Nat.mul (nat_lit 2) c))).testBit i = (frob4 (cd v c)).testBit 1 := by
    rw [mr_X1 hX c, hf.2]
  match e, he with
  | 0, _ => exact mr_mlo_gen h0 h1 (mr_frob4_lt (mr_cd_lt v c)) hy hi
  | 1, _ => exact mr_mhi_gen h0 h1 (mr_frob4_lt (mr_cd_lt v c)) hy hi

theorem mr_mulP_hi {e y : Nat} (he : e < 2) (hy : y < 4) (x0 x1 i : Nat) (hi : 2240 ≤ i) :
    (mulP e x0 x1 y).testBit i = false := by
  have hn : decide (i < 2240) = false := decide_eq_false (by omega)
  match e, he with
  | 0, _ =>
    change (mlo x0 x1 y).testBit i = false
    rw [mr_mlo_tb hy, hn, Bool.and_false]
  | 1, _ =>
    change (mhi x0 x1 y).testBit i = false
    rw [mr_mhi_tb hy, hn, Bool.and_false]

theorem mr_hermP_tb {X : Nat → Nat} {v i : Nat} (hX : ∀ b, (X b).testBit i = v.testBit b)
    (hi : i < 2240) {e : Nat} (he : e < 2) (b : Nat) :
    (hermP X b e).testBit i = (hermC v b).testBit e := by
  unfold hermP
  rw [mr_hermC_rec]
  generalize (nat_lit 8) = n
  rw [mr_rec_xor_tb]
  apply mr_rec_xor_congr
  intro c _
  rw [← mr_frobK _ (mr_cd_lt b c), ← mr_cdK b c]
  match e, he with
  | 0, _ => exact mr_mulP_pt hX hi (e := 0) (by decide) (mr_frobK_lt _) c
  | 1, _ => exact mr_mulP_pt hX hi (e := 1) (by decide) (mr_frobK_lt _) c

theorem mr_beq_cd {v w : Nat} (hv : v < 65536) (hw : w < 65536) :
    (v == w) = !(Nat.rec (motive := fun _ => Bool) false
      (fun c acc => acc || (cd v c != cd w c)) (nat_lit 8)) := by
  generalize hn' : (nat_lit 8) = n
  have hn : n = 8 := by rw [← hn']
  by_cases h : v = w
  · subst h
    rw [mr_rec_or_false (fun c _ => by simp)]
    simp
  · have hr : Nat.rec (motive := fun _ => Bool) false
        (fun c acc => acc || (cd v c != cd w c)) n = true := by
      apply (mr_rec_or_iff _ _).mpr
      apply Classical.byContradiction
      intro hne
      apply h
      apply Nat.eq_of_testBit_eq
      intro k
      by_cases hk : k < 16
      · have hc : cd v (k / 2) = cd w (k / 2) := by
          apply Classical.byContradiction
          intro hcne
          exact hne ⟨k / 2, by omega, by simp [hcne]⟩
        have e1 : ∀ x : Nat, x.testBit k = (cd x (k / 2)).testBit (k % 2) := by
          intro x
          rw [mr_cd_tb, decide_eq_true (Nat.mod_lt k (by decide : 2 > 0)), Bool.true_and]
          congr 1
          omega
        rw [e1 v, e1 w, hc]
      · have h16 : ∀ x : Nat, x < 65536 → x.testBit k = false := fun x hx =>
          Nat.testBit_lt_two_pow
            (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (n := 2) (by decide) (by omega : 16 ≤ k)))
        rw [h16 v hv, h16 w hw]
    rw [hr]
    simp [h]

theorem mr_maskOf_tb {X : Nat → Nat} {v i : Nat} (hX : ∀ b, (X b).testBit i = v.testBit b)
    (hi : i < 2240) (hv : v < 65536) (b0 b1 b2 b3 : Nat) :
    (maskOf X b0 b1 b2 b3).testBit i = (v == (smulC (hermC v b0) b0 ^^^ smulC (hermC v b1) b1 ^^^
      smulC (hermC v b2) b2 ^^^ smulC (hermC v b3) b3)) := by
  have hw : (smulC (hermC v b0) b0 ^^^ smulC (hermC v b1) b1 ^^^ smulC (hermC v b2) b2 ^^^
      smulC (hermC v b3) b3) < 65536 := by
    have h16 : (65536 : Nat) = 2 ^ 16 := rfl
    rw [h16]
    repeat' apply Nat.xor_lt_two_pow
    all_goals exact mr_smulC_lt _ _
  have hL : ∀ b y : Nat, y < 4 → (mlo (hermP X b (nat_lit 0)) (hermP X b (nat_lit 1)) y).testBit i =
      (mul4 (hermC v b) y).testBit 0 := fun b _ hy =>
    mr_mlo_gen (mr_hermP_tb hX hi (by decide) b) (mr_hermP_tb hX hi (by decide) b)
      (mr_hermC_lt v b) hy hi
  have hH : ∀ b y : Nat, y < 4 → (mhi (hermP X b (nat_lit 0)) (hermP X b (nat_lit 1)) y).testBit i =
      (mul4 (hermC v b) y).testBit 1 := fun b _ hy =>
    mr_mhi_gen (mr_hermP_tb hX hi (by decide) b) (mr_hermP_tb hX hi (by decide) b)
      (mr_hermC_lt v b) hy hi
  rw [mr_beq_cd hv hw]
  unfold maskOf
  generalize hn' : (nat_lit 8) = n
  have hn : n = 8 := by rw [← hn']
  simp only [mr_strictN]
  rw [mr_tb_xor, mr_allP_tb, decide_eq_true hi, mr_rec_lor_tb, Bool.true_xor]
  congr 1
  apply mr_rec_or_congr
  intro c hc
  have hc8 : c < 8 := by omega
  rw [mr_ne4 _ (mr_cd_lt v c) _ (mr_cd_lt _ c)]
  simp only [mr_tb_lor, mr_tb_xor, hL, hH, mr_cd_lt, mr_cdK_lt, mr_X0 hX,
    mr_X1 hX, mr_cdK, mr_cd_xor, mr_cd_smulC _ _ _ hc8, Nat.testBit_xor, Bool.xor_assoc]

theorem mr_incFrom {L : List Nat} {c : Nat} (h : incFrom L c = true) :
    L.Pairwise (· < ·) ∧ ∀ x ∈ L, c ≤ x ∧ x < 65536 := by
  induction L generalizing c with
  | nil => exact ⟨List.Pairwise.nil, by simp⟩
  | cons p l ih =>
    have h' : (Nat.ble c p && (Nat.blt p 65536 && incFrom l (p + 1))) = true := h
    simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at h'
    obtain ⟨h1, h2, h3⟩ := h'
    obtain ⟨ih1, ih2⟩ := ih h3
    refine ⟨List.Pairwise.cons (fun x hx => (ih2 x hx).1) ih1, ?_⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨h1, h2⟩
    · have := ih2 x hx
      omega

theorem mr_ptK {L : List Nat} (hp : ptK L = true) :
    L.Pairwise (· < ·) ∧ ∀ x ∈ L, x < 65536 := by
  have h' : (incFrom L 0 && Nat.beq (plOf L) ptPl) = true := hp
  rw [Bool.and_eq_true] at h'
  obtain ⟨h1, h2⟩ := mr_incFrom h'.1
  exact ⟨h1, fun x hx => (h2 x hx).2⟩

theorem mr_getD_lt {L : List Nat} (hL : ∀ x ∈ L, x < 65536) (k : Nat) : L.getD k 0 < 65536 := by
  rw [List.getD_eq_getElem?_getD]
  by_cases hk : k < L.length
  · rw [List.getElem?_eq_getElem hk]
    exact hL _ (List.getElem_mem hk)
  · rw [List.getElem?_eq_none (by omega)]
    decide

theorem mr_bitOf_tb (L : List Nat) (b i : Nat) :
    (bitOf L b).testBit i = (L.getD i 0).testBit b := by
  induction L generalizing i with
  | nil =>
    change (0 : Nat).testBit i = _
    simp
  | cons p l ih =>
    change (Nat.lor (Nat.land (Nat.shiftRight p b) 1) (Nat.shiftLeft (bitOf l b) 1)).testBit i = _
    rw [mr_tb_lor, mr_tb_land, mr_tb_shr, mr_tb_shl]
    cases i with
    | zero => simp
    | succ i =>
      have h1 : Nat.testBit 1 (i + 1) = false :=
        Nat.testBit_lt_two_pow (Nat.one_lt_two_pow (by omega))
      simp [ih, h1]

theorem mr_getL (l : List Nat) (k : Nat) : getL l k = l.getD k 0 := by
  induction l generalizing k with
  | nil => simp [getL]
  | cons x l ih =>
    cases k with
    | zero => rfl
    | succ k =>
      rw [List.getD_cons_succ, ← ih k]
      rfl

theorem mr_packL_tb {L : List Nat} (hL : ∀ x ∈ L, x < 65536) (k j : Nat) (hj : j < 16) :
    (packL L).testBit (16 * k + j) = (L.getD k 0).testBit j := by
  induction L generalizing k with
  | nil =>
    change (0 : Nat).testBit _ = _
    simp
  | cons p l ih =>
    change (Nat.lor p (Nat.shiftLeft (packL l) 16)).testBit _ = _
    rw [mr_tb_lor, mr_tb_shl]
    have hp : p < 2 ^ 16 := hL p (List.mem_cons_self ..)
    cases k with
    | zero =>
      simp only [Nat.mul_zero, Nat.zero_add, List.getD_cons_zero]
      rw [decide_eq_false (by omega), Bool.false_and, Bool.or_false]
    | succ k =>
      rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hp (Nat.pow_le_pow_right (by decide)
        (by omega))), decide_eq_true (by omega), Bool.true_and, Bool.false_or,
        List.getD_cons_succ, ← ih (fun x hx => hL x (List.mem_cons_of_mem _ hx)) k]
      congr 1
      omega

theorem mr_ptAt_packL {L : List Nat} (hL : ∀ x ∈ L, x < 65536) (k : Nat) :
    ptAt (packL L) k = L.getD k 0 := by
  apply Nat.eq_of_testBit_eq
  intro j
  change ((packL L >>> (16 * k)) &&& (2 ^ 16 - 1)).testBit j = _
  rw [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one]
  by_cases hj : j < 16
  · rw [mr_packL_tb hL k j hj, decide_eq_true hj, Bool.and_true]
  · rw [decide_eq_false hj, Bool.and_false, Nat.testBit_lt_two_pow
      (Nat.lt_of_lt_of_le (mr_getD_lt hL k)
        (Nat.pow_le_pow_right (n := 2) (by decide) (by omega : 16 ≤ j)))]

theorem mr_dropL {α : Type} (k : Nat) (l : List α) : dropL k l = l.drop k := by
  induction k generalizing l with
  | zero => rfl
  | succ k ih =>
    cases l with
    | nil =>
      change dropL k [] = _
      rw [ih]
      simp
    | cons x t =>
      change dropL k t = _
      rw [ih]
      rfl

theorem mr_masksN {X : Nat → Nat} {T : Nat} {M : Nat → Nat} {n j : Nat} {F : List (Array Nat)}
    (h : masksN X T M n j F = true) {t : Nat} (ht : t < n) :
    ∃ fr, F[t]? = some fr ∧ frMask X T fr.toList = M (j + t) := by
  induction n generalizing j F t with
  | zero => omega
  | succ n ih =>
    cases F with
    | nil => exact absurd h Bool.false_ne_true
    | cons fr F' =>
      have h' : (Nat.beq (frMask X T fr.toList) (M j) && masksN X T M n (j + 1) F') = true := h
      rw [Bool.and_eq_true] at h'
      cases t with
      | zero => exact ⟨fr, rfl, Nat.eq_of_beq_eq_true h'.1⟩
      | succ t =>
        obtain ⟨fr', h1, h2⟩ := ih h'.2 (t := t) (by omega)
        refine ⟨fr', h1, ?_⟩
        rw [h2]
        congr 1
        omega

theorem mr_allBlk {b : Nat} {f : Nat → Bool} {len : Nat} (h : CFSG.KC.Enum.allBlk b f len = true)
    {l : Nat} (hl : l < len) : f (b + l) = true := by
  induction len with
  | zero => omega
  | succ len ih =>
    have h' : (f (b + len) && CFSG.KC.Enum.allBlk b f len) = true := h
    rw [Bool.and_eq_true] at h'
    by_cases hll : l = len
    · subst hll
      exact h'.1
    · exact ih h'.2 (by omega)

theorem mr_arr_get (a : Array Nat) (k : Nat) : a[k]! = a.toList.getD k 0 := by
  rw [List.getD_eq_getElem?_getD, Array.getElem?_toList, getElem!_def]
  cases a[k]? <;> rfl

theorem mr_polarP_tb {X : Nat → Nat} {v i : Nat} (hX : ∀ b, (X b).testBit i = v.testBit b)
    (hi : i < 2240) {e : Nat} (he : e < 2) (u : Nat) :
    (polarP X u e).testBit i = (polarC u v).testBit e := by
  unfold polarP
  rw [mr_polarC_rec]
  generalize hn : (nat_lit 4) = n
  rw [mr_rec_xor_tb]
  apply mr_rec_xor_congr
  intro c _
  subst hn
  rw [mr_tb_xor, mr_mulP_pt hX hi he (mr_cdK_lt _ _), mr_mulP_pt hX hi he (mr_cdK_lt _ _), mr_cdK,
    mr_cdK, mr_mul4_comm (cd v (Nat.add c 4)) (mr_cd_lt _ _) (cd u c) (mr_cd_lt _ _),
    mr_mul4_comm (cd v c) (mr_cd_lt _ _) (cd u (Nat.add c 4)) (mr_cd_lt _ _)]

theorem mr_hermQ_tb {X : Nat → Nat} {v i : Nat} (hX : ∀ b, (X b).testBit i = v.testBit b)
    (hi : i < 2240) {e : Nat} (he : e < 2) (u : Nat) :
    (hermQ X u e).testBit i = (hermC u v).testBit e := by
  unfold hermQ
  rw [mr_hermC_rec]
  generalize (nat_lit 8) = n
  rw [mr_rec_xor_tb]
  apply mr_rec_xor_congr
  intro k _
  rw [mr_mulQ_pt hX hi he (mr_cdK_lt _ _), mr_cdK,
    mr_mul4_comm _ (mr_frob4_lt (mr_cd_lt v k)) _ (mr_cd_lt u k)]

theorem mr_polarP_hi {X : Nat → Nat} {i e : Nat} (he : e < 2) (u : Nat) (hi : 2240 ≤ i) :
    (polarP X u e).testBit i = false := by
  unfold polarP
  generalize (nat_lit 4) = n
  rw [mr_rec_xor_tb]
  apply mr_rec_xor_false
  intro c _
  rw [mr_tb_xor, mr_mulP_hi he (mr_cdK_lt _ _) _ _ _ hi, mr_mulP_hi he (mr_cdK_lt _ _) _ _ _ hi]
  rfl

theorem mr_hermQ_hi {X : Nat → Nat} {i e : Nat} (he : e < 2) (u : Nat) (hi : 2240 ≤ i) :
    (hermQ X u e).testBit i = false := by
  unfold hermQ
  generalize (nat_lit 8) = n
  rw [mr_rec_xor_tb]
  apply mr_rec_xor_false
  intro c _
  rw [mr_mulP_hi he (mr_cdK_lt _ _) _ _ _ hi]

theorem mr_adjRow_tb {X : Nat → Nat} {v i' : Nat} (hX : ∀ b, (X b).testBit i' = v.testBit b)
    (hi' : i' < 2240) (u i : Nat) :
    (adjRow X u i).testBit i' =
      (!decide (i = i') && (polarC u v == 0) && (hermC u v == 0)) := by
  have p0 := mr_polarP_tb hX hi' (e := 0) (by decide) u
  have p1 := mr_polarP_tb hX hi' (e := 1) (by decide) u
  have q0 := mr_hermQ_tb hX hi' (e := 0) (by decide) u
  have q1 := mr_hermQ_tb hX hi' (e := 1) (by decide) u
  unfold adjRow
  rw [mr_tb_xor, mr_allP_tb, decide_eq_true hi', mr_tb_lor, mr_tb_lor, mr_tb_lor, mr_tb_lor,
    mr_shl_one, Nat.testBit_two_pow, p0, p1, q0, q1, mr_beq0 _ (mr_polarC_lt u v),
    mr_beq0 _ (mr_hermC_lt u v)]
  generalize decide (i = i') = d
  generalize (polarC u v).testBit 0 = a
  generalize (polarC u v).testBit 1 = b
  generalize (hermC u v).testBit 0 = c
  generalize (hermC u v).testBit 1 = f
  revert d a b c f
  decide

theorem mr_adjRow_hi {X : Nat → Nat} {i i' : Nat} (u : Nat) (hi : i < 2240) (hi' : 2240 ≤ i') :
    (adjRow X u i).testBit i' = false := by
  unfold adjRow
  rw [mr_tb_xor, mr_allP_tb, decide_eq_false (by omega), mr_tb_lor, mr_tb_lor, mr_tb_lor,
    mr_tb_lor, mr_shl_one, Nat.testBit_two_pow, decide_eq_false (by omega),
    mr_polarP_hi (e := 0) (by decide) u hi', mr_polarP_hi (e := 1) (by decide) u hi',
    mr_hermQ_hi (e := 0) (by decide) u hi', mr_hermQ_hi (e := 1) (by decide) u hi']
  rfl

theorem mr_ne_idx {L : List Nat} (hs : L.Pairwise (· < ·)) {i i' : Nat} (hi : i < L.length)
    (hi' : i' < L.length) : (L.getD i 0 != L.getD i' 0) = !decide (i = i') := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
    List.getElem?_eq_getElem hi']
  simp only [Option.getD_some]
  by_cases h : i = i'
  · subst h
    simp
  · have hne : L[i] ≠ L[i'] := by
      rcases Nat.lt_or_gt_of_ne h with h1 | h1
      · exact Nat.ne_of_lt (List.pairwise_iff_getElem.mp hs i i' hi hi' h1)
      · exact (Nat.ne_of_lt (List.pairwise_iff_getElem.mp hs i' i hi' hi h1)).symm
    simp [h, hne]

theorem mr_maskOf_hi {X : Nat → Nat} {i : Nat} (hX : ∀ b, (X b).testBit i = false)
    (hi : 2240 ≤ i) (b0 b1 b2 b3 : Nat) : (maskOf X b0 b1 b2 b3).testBit i = false := by
  have hn : decide (i < 2240) = false := decide_eq_false (by omega)
  unfold maskOf
  generalize (nat_lit 8) = n
  simp only [mr_strictN]
  rw [mr_tb_xor, mr_allP_tb, hn, Bool.false_xor, mr_rec_lor_tb]
  apply mr_rec_or_false
  intro c _
  simp [mr_tb_lor, mr_tb_xor, hX, mr_mlo_tb, mr_mhi_tb, mr_cdK_lt, hn]

theorem masksK_sound {L : List Nat} {F : Array (Array Nat)} {M : Nat → Nat} (hp : ptK L = true)
    (hL : L.length = 2240) (h : ∀ c < 16, masksK L F.toList M (280 * c) 280 = true) {j : Nat}
    (hj : j < 4480) :
    M j < 2 ^ 2240 ∧ ∀ i < 2240, Nat.testBit (M j) i = ((mkTabs (ptCodes ()) F).inc[j]!)[i]! := by
  obtain ⟨_, hlt⟩ := mr_ptK hp
  have hm := h (j / 280) (by omega)
  unfold masksK at hm
  rw [mr_strictB, mr_dropL] at hm
  obtain ⟨fr, hfr, hM⟩ := mr_masksN hm (t := j % 280) (Nat.mod_lt _ (by decide))
  rw [List.getElem?_drop, Nat.div_add_mod] at hfr
  rw [Nat.div_add_mod] at hM
  obtain ⟨hjF, hfrj⟩ := List.getElem?_eq_some_iff.mp hfr
  rw [Array.length_toList] at hjF
  rw [Array.getElem_toList] at hfrj
  subst hfrj
  rw [← hM]
  unfold frMask
  simp only [mr_getL, mr_ptAt_packL hlt]
  refine ⟨?_, ?_⟩
  · apply Nat.lt_pow_two_of_testBit
    intro i hi
    apply mr_maskOf_hi _ hi
    intro b
    rw [mr_bitOf_tb, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    exact Nat.zero_testBit b
  · intro i hi
    rw [mr_maskOf_tb (fun b => mr_bitOf_tb L b i) hi (mr_getD_lt hlt i), ptK_sound hp]
    simp [mkTabs, hjF, hi, hL, getElem!_pos, memC, mr_arr_get]

theorem ck_strictB (y : Nat) (k : Nat → Bool) : CFSG.KC.Enum.strictB y k = k y := by
  cases y <;> rfl

theorem ck_bAnd_true {a b : Bool} (h : Bool.rec (motive := fun _ => Bool) false b a = true) :
    a = true ∧ b = true := by
  cases a
  · exact absurd h Bool.false_ne_true
  · exact ⟨rfl, h⟩

theorem ck_dropL {α : Type} (k : Nat) (l : List α) : dropL k l = l.drop k := by
  induction k generalizing l with
  | zero => rfl
  | succ k ih =>
    cases l with
    | nil =>
      change dropL k [] = _
      rw [ih]
      simp
    | cons x t =>
      change dropL k t = _
      rw [ih]
      simp

theorem ck_allBlk {b : Nat} {f : Nat → Bool} :
    ∀ {len : Nat}, CFSG.KC.Enum.allBlk b f len = true → ∀ l < len, f (b + l) = true
  | 0, _, l, hl => absurd hl (Nat.not_lt_zero l)
  | n + 1, h, l, hl => by
    obtain ⟨h1, h2⟩ := ck_bAnd_true (a := f (Nat.add b n)) (b := CFSG.KC.Enum.allBlk b f n) h
    rcases Nat.lt_succ_iff_lt_or_eq.mp hl with hl | rfl
    · exact ck_allBlk h2 l hl
    · exact h1

theorem ck_allBlkC {f : Nat → Bool} {w C : Nat}
    (h : ∀ c < C, CFSG.KC.Enum.allBlk (w * c) f w = true) {i : Nat} (hi : i < w * C) :
    f i = true := by
  have hw : 0 < w := Nat.pos_of_ne_zero (by rintro rfl; simp at hi)
  have hc : i / w < C := (Nat.div_lt_iff_lt_mul hw).mpr (by rw [Nat.mul_comm]; exact hi)
  have := ck_allBlk (h (i / w) hc) (i % w) (Nat.mod_lt i hw)
  rwa [Nat.div_add_mod] at this

theorem ck_allN {n : Nat} {f : Nat → Bool} (h : CFSG.KC.Enum.allN n f = true) :
    ∀ i < n, f i = true := by
  obtain ⟨h1, h2⟩ := ck_bAnd_true h
  have hq : ∀ q, Nat.rec (motive := fun _ => Bool) true
      (fun h ih => Bool.rec (motive := fun _ => Bool) false ih
        (CFSG.KC.Enum.allBlk (Nat.shiftLeft h 6) f 64)) q = true →
      ∀ h < q, ∀ l < 64, f (Nat.shiftLeft h 6 + l) = true := by
    intro q
    induction q with
    | zero => intro _ h hh; omega
    | succ q ih =>
      intro hr h hh
      obtain ⟨r1, r2⟩ := ck_bAnd_true hr
      rcases Nat.lt_succ_iff_lt_or_eq.mp hh with hh | rfl
      · exact ih r2 h hh
      · exact ck_allBlk r1
  intro i hi
  have e1 : Nat.shiftRight n 6 = n / 64 := Nat.shiftRight_eq_div_pow n 6
  have e2 : ∀ h, Nat.shiftLeft h 6 = 64 * h := fun h => by
    rw [Nat.mul_comm]; exact Nat.shiftLeft_eq h 6
  have e3 : Nat.land n 63 = n % 64 := Nat.and_two_pow_sub_one_eq_mod n 6
  rw [e1] at h1 h2
  rw [e2, e3] at h1
  by_cases hb : 64 * (n / 64) ≤ i
  · have := ck_allBlk h1 (i - 64 * (n / 64)) (by have := Nat.div_add_mod n 64; omega)
    rwa [Nat.add_sub_cancel' hb] at this
  · have := hq _ h2 (i / 64) (by omega) (i % 64) (Nat.mod_lt i (by decide))
    rwa [e2, Nat.div_add_mod] at this

noncomputable def ckEach {β : Type} (f : Nat → β → Bool) (n : Nat) : Nat → List β → Bool :=
  Nat.rec (motive := fun _ => Nat → List β → Bool) (fun _ _ => true)
    (fun _ ih j LL => List.rec (motive := fun _ => Bool) false
      (fun l LL' _ => bAnd(f j l, ih (Nat.succ j) LL')) LL) n

theorem ck_each {β : Type} {f : Nat → β → Bool} :
    ∀ {n j : Nat} {LL : List β}, ckEach f n j LL = true →
      ∀ t < n, ∃ l, LL[t]? = some l ∧ f (j + t) l = true
  | 0, _, _, _, t, ht => absurd ht (Nat.not_lt_zero t)
  | n + 1, j, [], h, _, _ => absurd h Bool.false_ne_true
  | n + 1, j, l :: LL, h, t, ht => by
    obtain ⟨h1, h2⟩ := ck_bAnd_true (b := ckEach f n (Nat.succ j) LL) h
    cases t with
    | zero => exact ⟨l, rfl, h1⟩
    | succ t =>
      obtain ⟨l', h3, h4⟩ := ck_each h2 t (by omega)
      have e : j + (t + 1) = Nat.succ j + t := by omega
      exact ⟨l', by simpa using h3, by rw [e]; exact h4⟩

theorem ck_eachC {β : Type} {f : Nat → β → Bool} {LL : List β} {w C : Nat}
    (h : ∀ c < C, ckEach f w (w * c) (dropL (w * c) LL) = true) {i : Nat} (hi : i < w * C) :
    ∃ l, LL[i]? = some l ∧ f i l = true := by
  have hw : 0 < w := Nat.pos_of_ne_zero (by rintro rfl; simp at hi)
  have hc : i / w < C := (Nat.div_lt_iff_lt_mul hw).mpr (by rw [Nat.mul_comm]; exact hi)
  obtain ⟨l, h1, h2⟩ := ck_each (h (i / w) hc) (i % w) (Nat.mod_lt i hw)
  rw [ck_dropL, List.getElem?_drop, Nat.div_add_mod] at h1
  rw [Nat.div_add_mod] at h2
  exact ⟨l, h1, h2⟩

theorem ck_lall {α : Type} {g : α → Bool} :
    ∀ {l : List α}, List.rec (motive := fun _ => Bool) true
      (fun x _ ih => Bool.rec (motive := fun _ => Bool) false ih (g x)) l = true →
      ∀ x ∈ l, g x = true
  | [], _, x, hx => absurd hx (List.not_mem_nil)
  | y :: l, h, x, hx => by
    obtain ⟨h1, h2⟩ := ck_bAnd_true h
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h1
    · exact ck_lall h2 x hx

theorem ck_tor (x y i : Nat) : (Nat.lor x y).testBit i = (x.testBit i || y.testBit i) :=
  Nat.testBit_or x y i

theorem ck_tand (x y i : Nat) : (Nat.land x y).testBit i = (x.testBit i && y.testBit i) :=
  Nat.testBit_and x y i

theorem ck_tshl1 (p i : Nat) : (Nat.shiftLeft 1 p).testBit i = decide (p = i) := by
  change (1 <<< p).testBit i = _
  rw [Nat.one_shiftLeft, Nat.testBit_two_pow]

theorem ck_plOf (l : List Nat) (i : Nat) : (plOf l).testBit i = decide (i ∈ l) := by
  induction l with
  | nil => exact Nat.zero_testBit i
  | cons p l ih =>
    change (Nat.lor (Nat.shiftLeft 1 p) (plOf l)).testBit i = _
    rw [ck_tor, ih, ck_tshl1]
    by_cases h : p = i
    · subst h
      simp
    · simp [h, Ne.symm h]

theorem ck_lt_of_bits {x n : Nat} (h : ∀ i, n ≤ i → x.testBit i = false) : x < 2 ^ n :=
  Nat.lt_pow_two_of_testBit x h

theorem ck_bit_lt {x n i : Nat} (hx : x < 2 ^ n) (hi : x.testBit i = true) : i < n := by
  apply Nat.lt_of_not_le
  intro hn
  have : x < 2 ^ i := Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) hn)
  rw [Nat.testBit_lt_two_pow this] at hi
  exact absurd hi (by decide)

theorem ck_plOf_lt {l : List Nat} {n : Nat} (h : ∀ j ∈ l, j < n) : plOf l < 2 ^ n :=
  ck_lt_of_bits fun i hi => by
    rw [ck_plOf]
    exact decide_eq_false fun hm => absurd (h i hm) (by omega)

theorem ck_eq_of_bits {x y n : Nat} (hx : x < 2 ^ n) (hy : y < 2 ^ n)
    (h : ∀ i < n, x.testBit i = y.testBit i) : x = y := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < n
  · exact h i hi
  · have hn : n ≤ i := by omega
    have h2 : 2 ^ n ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) hn
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx h2),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hy h2)]

theorem ck_bitAt (x i : Nat) : bitAt x i = x.testBit i := by
  change Nat.blt 0 (Nat.land x (Nat.shiftLeft 1 i)) = _
  cases hb : x.testBit i
  · have : Nat.land x (Nat.shiftLeft 1 i) = 0 := Nat.eq_of_testBit_eq fun k => by
      rw [ck_tand, ck_tshl1, Nat.zero_testBit]
      by_cases hk : i = k
      · subst hk
        simp [hb]
      · simp [hk]
    rw [this]
    rfl
  · have : Nat.land x (Nat.shiftLeft 1 i) ≠ 0 := fun h0 => by
      have := congrArg (Nat.testBit · i) h0
      simp only [ck_tand, ck_tshl1, hb, Nat.zero_testBit] at this
      simp at this
    simpa using Nat.pos_of_ne_zero this

theorem ck_abv (x p i : Nat) : (abv x p).testBit i = (decide (p < i) && x.testBit i) := by
  change (Nat.shiftRight x (p + 1) <<< (p + 1)).testBit i = _
  rw [Nat.testBit_shiftLeft]
  change (decide (i ≥ p + 1) && (x >>> (p + 1)).testBit (i - (p + 1))) = _
  rw [Nat.testBit_shiftRight]
  by_cases h : p < i
  · have e : p + 1 + (i - (p + 1)) = i := by omega
    rw [e]
    simp [h, Nat.succ_le_of_lt h]
  · simp [h]
    omega

theorem ck_inc_size {P : Array Nat} {F : Array (Array Nat)} {j : Nat} (hj : j < F.size) :
    ((mkTabs P F).inc[j]!).size = P.size := by
  simp [mkTabs, hj]

theorem ck_solPts_mem {P : Array Nat} {F : Array (Array Nat)} {j i : Nat} (hj : j < F.size) :
    i ∈ (mkTabs P F).solPts[j]! ↔ i < P.size ∧ ((mkTabs P F).inc[j]!)[i]! = true := by
  have e : (mkTabs P F).solPts[j]! = (Array.range ((mkTabs P F).inc[j]!).size).filter
      (fun i => ((mkTabs P F).inc[j]!)[i]!) := by
    simp [mkTabs, hj]
  rw [e]
  simp only [Array.mem_filter, Array.mem_range]
  rw [ck_inc_size hj]

theorem ck_rmap {β : Type} [Inhabited β] (f : Nat → β) {n i : Nat} (hi : i < n) :
    ((Array.range n).map f)[i]! = f i := by
  rw [getElem!_pos _ _ (by simp [hi])]
  simp

theorem ck_plOfF {β : Type} (l : List (Nat × β)) (i : Nat) :
    (plOfF l).testBit i = true ↔ ∃ b, (i, b) ∈ l := by
  induction l with
  | nil =>
    change (0 : Nat).testBit i = true ↔ _
    simp
  | cons t l ih =>
    obtain ⟨r, b⟩ := t
    change (Nat.lor (Nat.shiftLeft 1 r) (plOfF l)).testBit i = true ↔ _
    rw [ck_tor, Bool.or_eq_true_iff, ih, ck_tshl1]
    by_cases h : r = i
    · subst h
      simp only [decide_true, true_or, true_iff]
      exact ⟨b, List.mem_cons_self⟩
    · simp [h, Ne.symm h]

theorem ck_mul4_comm : ∀ a < 4, ∀ b < 4, mul4 a b = mul4 b a := by decide

theorem ck_mcd (x y i k : Nat) : mul4 (cd x i) (cd y k) = mul4 (cd y k) (cd x i) :=
  ck_mul4_comm _ (Nat.mod_lt _ (by decide)) _ (Nat.mod_lt _ (by decide))

theorem ck_xlc (a b c : Nat) : a ^^^ (b ^^^ c) = b ^^^ (a ^^^ c) := by
  rw [← Nat.xor_assoc, Nat.xor_comm a b, Nat.xor_assoc]

theorem ck_polarC_comm (u v : Nat) : polarC v u = polarC u v := by
  unfold polarC
  rw [ck_mcd v u 0 4, ck_mcd v u 4 0, ck_mcd v u 1 5, ck_mcd v u 5 1, ck_mcd v u 2 6,
    ck_mcd v u 6 2, ck_mcd v u 3 7, ck_mcd v u 7 3]
  simp only [Nat.xor_comm, Nat.xor_assoc, ck_xlc]

theorem ck_frob_xs : ∀ (l : List Nat) (acc : Nat), acc < 4 → (∀ x ∈ l, x < 4) →
    l.foldl (· ^^^ ·) acc < 4 ∧
      frob4 (l.foldl (· ^^^ ·) acc) = (l.map frob4).foldl (· ^^^ ·) (frob4 acc) := by
  have hx : ∀ x < 4, ∀ y < 4, x ^^^ y < 4 ∧ frob4 (x ^^^ y) = frob4 x ^^^ frob4 y := by decide
  intro l
  induction l with
  | nil => intro acc ha _; exact ⟨ha, rfl⟩
  | cons x l ih =>
    intro acc ha h
    have h3 := h x List.mem_cons_self
    obtain ⟨h1, h2⟩ := ih (acc ^^^ x) (hx _ ha _ h3).1 fun y hy => h y (List.mem_cons_of_mem _ hy)
    simp only [List.foldl_cons, List.map_cons]
    rw [← (hx _ ha _ h3).2]
    exact ⟨h1, h2⟩

theorem ck_hermC_comm (u v : Nat) : hermC v u = frob4 (hermC u v) ∧ hermC u v < 4 := by
  have hc : ∀ x k, cd x k < 4 := fun _ _ => Nat.mod_lt _ (by decide)
  have ht : ∀ a < 4, ∀ b < 4, mul4 a (frob4 b) < 4 ∧
      frob4 (mul4 a (frob4 b)) = mul4 b (frob4 a) := by decide
  have := ck_frob_xs [mul4 (cd u 0) (frob4 (cd v 0)), mul4 (cd u 1) (frob4 (cd v 1)),
    mul4 (cd u 2) (frob4 (cd v 2)), mul4 (cd u 3) (frob4 (cd v 3)),
    mul4 (cd u 4) (frob4 (cd v 4)), mul4 (cd u 5) (frob4 (cd v 5)),
    mul4 (cd u 6) (frob4 (cd v 6)), mul4 (cd u 7) (frob4 (cd v 7))] 0 (by decide) (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact (ht _ (hc _ _) _ (hc _ _)).1)
  have f0 : frob4 0 = 0 := rfl
  have hfm : ∀ x y k i, frob4 (mul4 (cd x k) (frob4 (cd y i))) = mul4 (cd y i) (frob4 (cd x k)) :=
    fun x y k i => (ht _ (hc x k) _ (hc y i)).2
  simp only [List.foldl_cons, List.foldl_nil, List.map_cons, List.map_nil, Nat.zero_xor, f0,
    hfm] at this
  unfold hermC
  exact ⟨this.2.symm, this.1⟩

theorem ck_ptAdjC_comm (u v : Nat) : ptAdjC v u = ptAdjC u v := by
  have hf : ∀ x < 4, (frob4 x == 0) = (x == 0) := by decide
  unfold ptAdjC
  rw [ck_polarC_comm, (ck_hermC_comm u v).1, hf _ (ck_hermC_comm u v).2, bne_comm]

theorem ck_ptAdjC_ne {u v : Nat} (h : ptAdjC u v = true) : u ≠ v := by
  intro e
  subst e
  simp [ptAdjC] at h

theorem ck_bAndE (a b : Bool) : Bool.rec (motive := fun _ => Bool) false b a = (a && b) := by
  cases a <;> rfl

theorem ck_bNot (a : Bool) : Bool.rec (motive := fun _ => Bool) true false a = !a := by
  cases a <;> rfl

theorem ck_beq_false {a b : Nat} (h : Nat.beq a b = false) : a ≠ b := fun e => by
  rw [e, Nat.beq_refl] at h
  exact Bool.noConfusion h

theorem ck_tshr64 (x k : Nat) : (Nat.shiftRight x 64).testBit k = x.testBit (k + 64) := by
  change (x >>> 64).testBit k = _
  rw [Nat.testBit_shiftRight, Nat.add_comm]

theorem ck_tagT (f : Nat → Nat) {i : Nat} (a : Nat) (hi : i < 4480) :
    (tagT f i).testBit (a + 64) = (f i).testBit a := by
  have h64 : Nat.succ i < 2 ^ (a + 64) := by
    have h1 : (4481 : Nat) ≤ 2 ^ 64 := Nat.le_of_ble_eq_true rfl
    have h2 : 2 ^ 64 ≤ 2 ^ (a + 64) := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have e : tagT f i = Nat.lor (Nat.shiftLeft (f i) 64) (Nat.succ i) := rfl
  rw [e, ck_tor, Nat.testBit_lt_two_pow h64, Bool.or_false]
  change ((f i) <<< 64).testBit (a + 64) = _
  rw [Nat.testBit_shiftLeft]
  simp

theorem ck_tfOf (TW : Nat → List Nat) (j j' : Nat) :
    (tfOf TW j).testBit j' = true ↔ ∃ w ∈ TW j, wJ w = j' := by
  unfold tfOf
  generalize TW j = l
  induction l with
  | nil =>
    change (0 : Nat).testBit j' = true ↔ _
    simp
  | cons w l ih =>
    change (Nat.lor (Nat.shiftLeft 1 (wJ w)) _).testBit j' = true ↔ _
    rw [ck_tor, Bool.or_eq_true_iff, ih, ck_tshl1]
    simp

theorem ck_sort3 {Q : Nat → Prop} {R : Nat → Nat → Prop} (hs : ∀ x y, R x y → R y x)
    (hne : ∀ x y, R x y → x ≠ y) {a b c : Nat} (qa : Q a) (qb : Q b) (qc : Q c)
    (hab : R a b) (hac : R a c) (hbc : R b c) :
    ∃ p q r, p < q ∧ q < r ∧ Q p ∧ Q q ∧ Q r ∧ R p q ∧ R p r ∧ R q r := by
  have hba := hs _ _ hab
  have hca := hs _ _ hac
  have hcb := hs _ _ hbc
  have n1 := hne _ _ hab
  have n2 := hne _ _ hac
  have n3 := hne _ _ hbc
  rcases Nat.lt_or_gt_of_ne n1 with h1 | h1 <;> rcases Nat.lt_or_gt_of_ne n2 with h2 | h2 <;>
    rcases Nat.lt_or_gt_of_ne n3 with h3 | h3
  all_goals first
    | exact ⟨a, b, c, by omega, by omega, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›⟩
    | exact ⟨a, c, b, by omega, by omega, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›⟩
    | exact ⟨b, a, c, by omega, by omega, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›⟩
    | exact ⟨b, c, a, by omega, by omega, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›⟩
    | exact ⟨c, a, b, by omega, by omega, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›⟩
    | exact ⟨c, b, a, by omega, by omega, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›⟩
    | (exfalso; omega)

theorem ck_triOK {M : Nat → Nat} {D p q r : Nat} : ∀ (js : List Nat) (u : Nat),
    List.rec (motive := fun _ => Nat → Bool) (fun u => Nat.beq (Nat.land D u) D)
      (fun j _ ih u => Bool.rec (motive := fun _ => Bool) false
        (CFSG.KC.Enum.strictB (M j) fun m => Bool.rec (motive := fun _ => Bool) false
          (Bool.rec (motive := fun _ => Bool) false
            (Bool.rec (motive := fun _ => Bool) false (ih (Nat.lor u m)) (bitAt m r))
            (bitAt m q)) (bitAt m p))
        (Nat.blt j 4480)) js u = true →
    ∀ i, D.testBit i = true → u.testBit i = true ∨ ∃ j ∈ js, j < 4480 ∧ (M j).testBit p = true ∧
      (M j).testBit q = true ∧ (M j).testBit r = true ∧ (M j).testBit i = true
  | [], u, h, i, hi => by
    left
    have e := Nat.eq_of_beq_eq_true h
    rw [← e, ck_tand] at hi
    exact (Bool.and_eq_true _ _ ▸ hi).2
  | j :: js, u, h, i, hi => by
    obtain ⟨h1, h2⟩ := ck_bAnd_true h
    rw [ck_strictB] at h2
    obtain ⟨hp, h2⟩ := ck_bAnd_true h2
    obtain ⟨hq, h2⟩ := ck_bAnd_true h2
    obtain ⟨hr, h2⟩ := ck_bAnd_true h2
    rcases ck_triOK js _ h2 i hi with h3 | ⟨j', hj', h3⟩
    · rw [ck_tor] at h3
      rcases Bool.or_eq_true_iff.mp h3 with h3 | h3
      · exact Or.inl h3
      · rw [ck_bitAt] at hp hq hr
        exact Or.inr ⟨j, List.mem_cons_self, by simpa using h1, hp, hq, hr, h3⟩
    · exact Or.inr ⟨j', List.mem_cons_of_mem _ hj', h3⟩

theorem distinctK_sound {L : List Nat} {F : Array (Array Nat)} {M : Nat → Nat} (hp : ptK L = true)
    (hL : L.length = 2240) (hF : F.size = 4480)
    (h : ∀ c < 16, masksK L F.toList M (280 * c) 280 = true) (hinc : incK M 4479 = true) :
    distinctCheck (mkTabs (ptCodes ()) F) = true := by
  have hP : (ptCodes ()).size = 2240 := by rw [ptK_sound hp, List.size_toArray, hL]
  have hs : ∀ j < 4479, M j < M (j + 1) := fun j hj => by
    have := ck_allN hinc j hj
    simpa using this
  have hmono : ∀ j j', j' < j → j < 4480 → M j' < M j := by
    intro j
    induction j with
    | zero => intro j' h1 _; omega
    | succ j ih =>
      intro j' h1 h2
      rcases Nat.lt_succ_iff_lt_or_eq.mp h1 with h3 | rfl
      · exact Nat.lt_trans (ih j' h3 (by omega)) (hs j (by omega))
      · exact hs j' (by omega)
  change ((List.range 4480).all fun j => (List.range j).all fun j' =>
    (mkTabs (ptCodes ()) F).solPts[j]! != (mkTabs (ptCodes ()) F).solPts[j']!) = true
  simp only [List.all_eq_true, List.mem_range, bne_iff_ne, ne_eq]
  intro j hj j' hj' heq
  have hb : ∀ i < 2240, (M j).testBit i = (M j').testBit i := by
    intro i hi
    rw [(masksK_sound hp hL h hj).2 i hi, (masksK_sound hp hL h (by omega)).2 i hi]
    have m1 := @ck_solPts_mem (ptCodes ()) F j i (by omega)
    have m2 := @ck_solPts_mem (ptCodes ()) F j' i (by omega)
    rw [heq] at m1
    rw [hP] at m1 m2
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro hx
      exact (m2.mp (m1.mpr ⟨hi, hx⟩)).2
    · intro hx
      exact (m1.mp (m2.mpr ⟨hi, hx⟩)).2
  have := ck_eq_of_bits (masksK_sound hp hL h hj).1 (masksK_sound hp hL h (by omega)).1 hb
  exact absurd this (Nat.ne_of_gt (hmono j j' hj' hj))

theorem rowsK_sound {L : List Nat} {A : Nat → Nat} (hp : ptK L = true) (hL : L.length = 2240)
    (h : ∀ c < 8, rowsK L A (280 * c) 280 = true) {i : Nat} (hi : i < 2240) :
    A i < 2 ^ 2240 ∧
      ∀ i' < 2240, Nat.testBit (A i) i' = ptAdjC (ptCodes ())[i]! (ptCodes ())[i']! := by
  obtain ⟨hs, hlt⟩ := mr_ptK hp
  have hr := h (i / 280) (by omega)
  unfold rowsK at hr
  rw [mr_strictB] at hr
  have hb := mr_allBlk hr (l := i % 280) (Nat.mod_lt _ (by decide))
  rw [Nat.div_add_mod] at hb
  have hA := Nat.eq_of_beq_eq_true hb
  rw [mr_ptAt_packL hlt] at hA
  rw [← hA, ptK_sound hp]
  refine ⟨?_, ?_⟩
  · apply Nat.lt_pow_two_of_testBit
    intro i' hi'
    exact mr_adjRow_hi _ hi hi'
  · intro i' hi'
    rw [mr_adjRow_tb (fun b => mr_bitOf_tb L b i') hi', mr_arr_get, mr_arr_get,
      List.toList_toArray]
    unfold ptAdjC
    rw [mr_ne_idx hs (by omega) (by omega)]

theorem cliqueK_sound {L : List Nat} {F : Array (Array Nat)} {M A : Nat → Nat}
    {CL : List (List (Nat × List (Nat × List Nat)))} (hp : ptK L = true) (hL : L.length = 2240)
    (hF : F.size = 4480) (hM : ∀ c < 16, masksK L F.toList M (280 * c) 280 = true)
    (hA : ∀ c < 8, rowsK L A (280 * c) 280 = true) (h : ∀ s < 112, cliqueK A M CL (20 * s) 20 = true) :
    cliqueCheck (mkTabs (ptCodes ()) F) = true := by
  have hpts : (mkTabs (ptCodes ()) F).pts = ptCodes () := rfl
  simp only [cliqueCheck, List.all_eq_true, List.mem_range, Array.all_eq_true_iff_forall_mem,
    Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, hpts]
  intro i1 hi1 i2 hi2
  rw [ck_rmap _ hi1] at hi2
  rw [ck_rmap _ hi1, ck_rmap _ hi1]
  simp only [Array.mem_filter, Array.mem_range, Array.any_eq_true', Bool.and_eq_true,
    decide_eq_true_eq, Nat.not_lt] at hi2 ⊢
  rcases Nat.lt_or_ge i1 i2 with h12 | h12
  · refine Or.inr ?_
    rintro i3 ⟨⟨hi3, a13⟩, h23, a23⟩ i4 ⟨⟨⟨hi4, a14⟩, h24, a24⟩, h34, a34⟩
    have hR := fun {i} (hi : i < 2240) => rowsK_sound hp hL hA hi
    have hMs := fun {j} (hj : j < 4480) => masksK_sound (F := F) hp hL hM hj
    obtain ⟨E, -, hok⟩ :=
      ck_eachC (f := ptOK A M) (w := 20) (C := 112) h (by omega : i1 < 20 * 112)
    simp only [ptOK, ck_strictB] at hok
    obtain ⟨hpl, hall⟩ := ck_bAnd_true hok
    have b2 : (plOfF E).testBit i2 = true := by
      rw [Nat.eq_of_beq_eq_true hpl, ck_abv, (hR hi1).2 i2 hi2.1]
      simp [h12, hi2.2]
    obtain ⟨rs, hrs⟩ := (ck_plOfF E i2).mp b2
    have hpair := ck_lall (g := pairOK A M i1 (A i1)) hall _ hrs
    simp only [pairOK, ck_strictB] at hpair
    obtain ⟨hpl2, hall2⟩ := ck_bAnd_true hpair
    have b3 : (plOfF rs).testBit i3 = true := by
      rw [Nat.eq_of_beq_eq_true hpl2, ck_abv, ck_tand, (hR hi1).2 i3 hi3, (hR hi2.1).2 i3 hi3]
      simp [h23, a13, a23]
    obtain ⟨js, hjs⟩ := (ck_plOfF rs i3).mp b3
    have htri := ck_lall (g := triOK A M i1 i2 (abv (Nat.land (A i1) (A i2)) i2)) hall2 _ hjs
    simp only [triOK] at htri
    rw [ck_strictB] at htri
    have hD : (abv (Nat.land (abv (Nat.land (A i1) (A i2)) i2) (A i3)) i3).testBit i4 = true := by
      rw [ck_abv, ck_tand, ck_abv, ck_tand, (hR hi1).2 i4 hi4, (hR hi2.1).2 i4 hi4,
        (hR hi3).2 i4 hi4]
      simp [h34, h24, a14, a24, a34]
    rcases ck_triOK js 0 htri i4 hD with h0 | ⟨j, -, hj, m1, m2, m3, m4⟩
    · simp at h0
    · refine ⟨j, ⟨hj, ?_⟩, ⟨?_, ?_⟩, ?_⟩
      · rw [← (hMs hj).2 _ hi1]
        exact m1
      · rw [← (hMs hj).2 _ hi2.1]
        exact m2
      · rw [← (hMs hj).2 _ hi3]
        exact m3
      · rw [← (hMs hj).2 _ hi4]
        exact m4
  · exact Or.inl h12

theorem solK_sound {L : List Nat} {F : Array (Array Nat)} {M S : Nat → Nat}
    {SP SI : List (List Nat)} (hp : ptK L = true) (hL : L.length = 2240)
    (hM : ∀ c < 16, masksK L F.toList M (280 * c) 280 = true)
    (hA : ∀ c < 16, solAK M S SP (280 * c) 280 = true)
    (hB : ∀ c < 8, solBK M S SI (280 * c) 280 = true) {i : Nat} (hi : i < 2240) :
    S i < 2 ^ 4480 ∧ ∀ j < 4480, Nat.testBit (S i) j = ((mkTabs (ptCodes ()) F).inc[j]!)[i]! := by
  obtain ⟨l, -, hl⟩ := ck_eachC (f := solB M S) (w := 280) (C := 8) hB (by omega : i < 280 * 8)
  obtain ⟨hpl, hall⟩ := ck_bAnd_true hl
  have hSi : S i = plOf l := (Nat.eq_of_beq_eq_true hpl).symm
  have hmem : ∀ j ∈ l, j < 4480 ∧ (M j).testBit i = true := by
    clear hpl hl hSi
    induction l with
    | nil => intro j hj; exact absurd hj List.not_mem_nil
    | cons x l ih =>
      obtain ⟨h1, h2⟩ := ck_bAnd_true hall
      obtain ⟨h2, h3⟩ := ck_bAnd_true h2
      intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · exact ⟨by simpa using h1, by rwa [ck_bitAt] at h2⟩
      · exact ih h3 j hj
  refine ⟨?_, fun j hj => ?_⟩
  · rw [hSi]
    exact ck_plOf_lt (n := 4480) fun j hj => (hmem j hj).1
  rw [hSi, ck_plOf, ← (masksK_sound hp hL hM hj).2 i hi]
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_iff]
  constructor
  · intro hj'
    exact (hmem j hj').2
  · intro hb
    obtain ⟨l', -, hl'⟩ := ck_eachC (f := solA M S) (w := 280) (C := 16) hA (by omega : j < 280 * 16)
    obtain ⟨hpl', hall'⟩ := ck_bAnd_true hl'
    have hi' : i ∈ l' := by
      have := ck_plOf l' i
      rw [Nat.eq_of_beq_eq_true hpl', hb] at this
      exact of_decide_eq_true this.symm
    have := ck_lall (g := fun i => bitAt (S i) j) hall' i hi'
    rw [ck_bitAt, hSi, ck_plOf] at this
    exact of_decide_eq_true this

theorem triK_sound {L : List Nat} {F : Array (Array Nat)} {M A S TF : Nat → Nat}
    {SP SI : List (List Nat)} {CL : List (List (Nat × List (Nat × List Nat)))}
    {TW : Nat → List Nat} (hp : ptK L = true) (hL : L.length = 2240) (hF : F.size = 4480)
    (hM : ∀ c < 16, masksK L F.toList M (280 * c) 280 = true)
    (hA : ∀ c < 8, rowsK L A (280 * c) 280 = true)
    (hSA : ∀ c < 16, solAK M S SP (280 * c) 280 = true)
    (hSB : ∀ c < 8, solBK M S SI (280 * c) 280 = true)
    (hC : ∀ s < 112, cliqueK A M CL (20 * s) 20 = true)
    (hTS : ∀ c < 16, triSK A M TW (280 * c) 280 = true)
    (hTF : ∀ c < 16, tfK TW TF (280 * c) 280 = true)
    (hTC : ∀ s < 112, triCK S TF CL (20 * s) 20 = true) {j : Nat} (hj : j < 4480) :
    TF j < 2 ^ 4480 ∧ ∀ j' < 4480, Nat.testBit (TF j) j' =
      (j != j' && triTest (mkTabs (ptCodes ()) F) j j') := by
  have hP : (ptCodes ()).size = 2240 := by rw [ptK_sound hp, List.size_toArray, hL]
  have hpts : (mkTabs (ptCodes ()) F).pts = ptCodes () := rfl
  have hR := fun {i} (hi : i < 2240) => rowsK_sound hp hL hA hi
  have hMs := fun {j} (hj : j < 4480) => masksK_sound (F := F) hp hL hM hj
  have hS := fun {i} (hi : i < 2240) => solK_sound (F := F) hp hL hM hSA hSB hi
  have hTFj : TF j = tfOf TW j :=
    (Nat.eq_of_beq_eq_true (ck_allBlkC (w := 280) (C := 16) hTF (by omega : j < 280 * 16))).symm
  have hW : ∀ w ∈ TW j, twOK A M j (M j) w = true := by
    have h1 := ck_allBlkC (w := 280) (C := 16) hTS (by omega : j < 280 * 16)
    rw [ck_strictB] at h1
    exact ck_lall h1
  have hWw : ∀ w ∈ TW j, wJ w < 4480 ∧ wJ w ≠ j ∧ (M j).testBit (wF w 13) = true ∧
      (M j).testBit (wF w 25) = true ∧ (M j).testBit (wF w 37) = true ∧
      (M (wJ w)).testBit (wF w 13) = true ∧ (M (wJ w)).testBit (wF w 25) = true ∧
      (M (wJ w)).testBit (wF w 37) = true ∧ (A (wF w 13)).testBit (wF w 25) = true ∧
      (A (wF w 13)).testBit (wF w 37) = true ∧ (A (wF w 25)).testBit (wF w 37) = true := by
    intro w hw
    have := hW w hw
    simp only [twOK, ck_strictB, ck_bAndE, ck_bNot, ck_bitAt, Bool.and_eq_true, Nat.blt_eq,
      Bool.not_eq_true'] at this
    obtain ⟨h1, h2, h3⟩ := this
    exact ⟨h1, ck_beq_false h2, h3⟩
  refine ⟨?_, fun j' hj' => ?_⟩
  · rw [hTFj]
    apply ck_lt_of_bits
    intro i hi
    cases hb : (tfOf TW j).testBit i
    · rfl
    · obtain ⟨w, hw, rfl⟩ := (ck_tfOf TW j _).mp hb
      exact absurd (hWw w hw).1 (by omega)
  apply Bool.eq_iff_iff.mpr
  rw [Bool.and_eq_true, bne_iff_ne]
  simp only [triTest, commonPts, Array.any_eq_true', Array.mem_filter, Bool.and_eq_true,
    ck_solPts_mem (by omega : j < F.size), hP, hpts]
  constructor
  · intro hb
    rw [hTFj, ck_tfOf] at hb
    obtain ⟨w, hw, rfl⟩ := hb
    obtain ⟨h1, h2, mp, mq, mr, mp', mq', mr', apq, apr, aqr⟩ := hWw w hw
    have hp2 : wF w 13 < 2240 := ck_bit_lt (hMs hj).1 mp
    have hq2 : wF w 25 < 2240 := ck_bit_lt (hMs hj).1 mq
    have hr2 : wF w 37 < 2240 := ck_bit_lt (hMs hj).1 mr
    refine ⟨Ne.symm h2, wF w 13, ⟨⟨hp2, ?_⟩, ?_⟩, wF w 25, ⟨⟨hq2, ?_⟩, ?_⟩, wF w 37,
      ⟨⟨hr2, ?_⟩, ?_⟩, ⟨?_, ?_⟩, ?_⟩
    · rw [← (hMs hj).2 _ hp2]
      exact mp
    · rw [← (hMs hj').2 _ hp2]
      exact mp'
    · rw [← (hMs hj).2 _ hq2]
      exact mq
    · rw [← (hMs hj').2 _ hq2]
      exact mq'
    · rw [← (hMs hj).2 _ hr2]
      exact mr
    · rw [← (hMs hj').2 _ hr2]
      exact mr'
    · rw [← (hR hp2).2 _ hq2]
      exact apq
    · rw [← (hR hp2).2 _ hr2]
      exact apr
    · rw [← (hR hq2).2 _ hr2]
      exact aqr
  · rintro ⟨hne, a, ⟨⟨ha, ia⟩, ia'⟩, b, ⟨⟨hb, ib⟩, ib'⟩, c, ⟨⟨hc, ic⟩, ic'⟩, ⟨aab, aac⟩, abc⟩
    obtain ⟨p, q, r, hpq, hqr, ⟨hp2, ip, ip'⟩, ⟨hq2, iq, iq'⟩, ⟨hr2, ir, ir'⟩, apq, apr, aqr⟩ :=
      ck_sort3 (Q := fun x => x < 2240 ∧ ((mkTabs (ptCodes ()) F).inc[j]!)[x]! = true ∧
          ((mkTabs (ptCodes ()) F).inc[j']!)[x]! = true)
        (R := fun x y => ptAdjC (ptCodes ())[x]! (ptCodes ())[y]! = true)
        (fun x y h => by rw [ck_ptAdjC_comm]; exact h)
        (fun x y h e => ck_ptAdjC_ne h (by rw [e]))
        ⟨ha, ia, ia'⟩ ⟨hb, ib, ib'⟩ ⟨hc, ic, ic'⟩ aab aac abc
    obtain ⟨E, hE, hok⟩ :=
      ck_eachC (f := ptOK A M) (w := 20) (C := 112) hC (by omega : p < 20 * 112)
    simp only [ptOK, ck_strictB] at hok
    obtain ⟨hpl, hall⟩ := ck_bAnd_true hok
    have b2 : (plOfF E).testBit q = true := by
      rw [Nat.eq_of_beq_eq_true hpl, ck_abv, (hR hp2).2 q hq2]
      simp [hpq, apq]
    obtain ⟨rs, hrs⟩ := (ck_plOfF E q).mp b2
    have hpair := ck_lall (g := pairOK A M p (A p)) hall _ hrs
    simp only [pairOK, ck_strictB] at hpair
    obtain ⟨hpl2, -⟩ := ck_bAnd_true hpair
    have b3 : (plOfF rs).testBit r = true := by
      rw [Nat.eq_of_beq_eq_true hpl2, ck_abv, ck_tand, (hR hp2).2 r hr2, (hR hq2).2 r hr2]
      simp [hqr, apr, aqr]
    obtain ⟨js, hjs⟩ := (ck_plOfF rs r).mp b3
    obtain ⟨E', hE', hok'⟩ := ck_eachC (f := triCpt (tagT S) (tagT TF)) (w := 20) (C := 112) hTC
      (by omega : p < 20 * 112)
    rw [hE] at hE'
    obtain rfl := Option.some.inj hE'
    simp only [triCpt, ck_strictB] at hok'
    have h1 := ck_lall (g := triCp (tagT S) (tagT TF) (tagT S p)) hok' _ hrs
    simp only [triCp, ck_strictB] at h1
    have h2 := ck_lall (g := triCt (tagT S) (tagT TF) (Nat.land (tagT S p) (tagT S q))) h1 _ hjs
    simp only [triCt] at h2
    obtain ⟨h3, h4⟩ := ck_bAnd_true h2
    have hmem : ∀ k < 4480, ((mkTabs (ptCodes ()) F).inc[k]!)[p]! = true →
        ((mkTabs (ptCodes ()) F).inc[k]!)[q]! = true →
        ((mkTabs (ptCodes ()) F).inc[k]!)[r]! = true → k ∈ js := by
      intro k hk e1 e2 e3
      have := ck_plOf js k
      rw [Nat.eq_of_beq_eq_true h3, ck_tshr64, ck_tand, ck_tand, ck_tagT _ _ (by omega : p < 4480),
        ck_tagT _ _ (by omega : q < 4480), ck_tagT _ _ (by omega : r < 4480), (hS hp2).2 k hk,
        (hS hq2).2 k hk, (hS hr2).2 k hk, e1, e2, e3] at this
      simpa using this.symm
    have hj1 := hmem j hj ip iq ir
    have hj2 := hmem j' hj' ip' iq' ir'
    have h5 := ck_lall (g := fun a => CFSG.KC.Enum.strictB (tagT TF a) fun ta =>
      List.rec (motive := fun _ => Bool) true
        (fun b _ ih2 => bAnd(bIf(Nat.beq a b, true, bitAt ta (Nat.add b 64)), ih2)) js) h4 j hj1
    simp only [ck_strictB] at h5
    have h6 := ck_lall (g := fun b => bIf(Nat.beq j b, true, bitAt (tagT TF j) (Nat.add b 64)))
      h5 j' hj2
    have hb : Nat.beq j j' = false := by
      cases e : Nat.beq j j'
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true e) hne
    simp only [hb] at h6
    rw [ck_bitAt] at h6
    rw [← ck_tagT TF j' hj]
    exact h6

theorem ck_allS_tb (i : Nat) : allS.testBit i = decide (i < 4480) := mr_low_tb 4480 i

theorem ck_cstS_tb {c : Nat} (hc : c < 2) (i : Nat) :
    (cstS c).testBit i = (c.testBit 0 && decide (i < 4480)) := by
  unfold cstS
  match c, hc with
  | 0, _ =>
    change (0 * allS).testBit i = _
    rw [Nat.zero_mul, Nat.zero_testBit, Nat.zero_testBit, Bool.false_and]
  | 1, _ =>
    change (1 * allS).testBit i = _
    rw [Nat.one_mul, ck_allS_tb]
    rfl

theorem ck_cstS0 {y i : Nat} (hi : i < 4480) :
    (cstS (Nat.land y (nat_lit 1))).testBit i = y.testBit 0 := by
  have h0 : Nat.land y (nat_lit 1) < 2 := Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  have t10 : Nat.testBit (nat_lit 1) 0 = true := by decide
  rw [ck_cstS_tb h0, mr_tb_land, t10, decide_eq_true hi, Bool.and_true, Bool.and_true]

theorem ck_cstS1 {y i : Nat} (hy : y < 4) (hi : i < 4480) :
    (cstS (Nat.shiftRight y (nat_lit 1))).testBit i = y.testBit 1 := by
  have h1 : Nat.shiftRight y (nat_lit 1) < 2 := by
    change y >>> 1 < 2
    rw [Nat.shiftRight_eq_div_pow]
    omega
  rw [ck_cstS_tb h1, mr_tb_shr, decide_eq_true hi, Bool.and_true]

theorem ck_mS_gen {x0 x1 a y i : Nat} (h0 : x0.testBit i = a.testBit 0)
    (h1 : x1.testBit i = a.testBit 1) (ha : a < 4) (hy : y < 4) (hi : i < 4480) {e : Nat}
    (he : e < 2) : (mulS e x0 x1 y).testBit i = (mul4 a y).testBit e := by
  match e, he with
  | 0, _ =>
    change (m0 x0 x1 (cstS (Nat.land y (nat_lit 1))) (cstS (Nat.shiftRight y (nat_lit 1)))).testBit i
      = _
    rw [pf_tb_m0, ck_cstS0 hi, ck_cstS1 hy hi, h0, h1, mr_mul4_tb0 a ha y hy]
  | 1, _ =>
    change (m1 x0 x1 (cstS (Nat.land y (nat_lit 1))) (cstS (Nat.shiftRight y (nat_lit 1)))).testBit i
      = _
    rw [pf_tb_m1, ck_cstS0 hi, ck_cstS1 hy hi, h0, h1, mr_mul4_tb1 a ha y hy]

theorem ck_hermS_tb {FP : Nat → Nat} {B j s : Nat}
    (hF : ∀ t < 16, (FP (16 * s + t)).testBit j = B.testBit t) (hj : j < 4480)
    {e : Nat} (he : e < 2) (x : Nat) :
    (hermS FP x s e).testBit j = (hermC x B).testBit e := by
  unfold hermS
  rw [mr_hermC_rec]
  generalize hn' : (nat_lit 8) = n
  have hn : n = 8 := by rw [← hn']
  simp only [mr_rec_xor_tb]
  apply mr_rec_xor_congr
  intro c hc
  have hlo : (FP (Nat.add (Nat.mul (nat_lit 16) s) (Nat.mul (nat_lit 2) c))).testBit j =
      (cd B c).testBit 0 := by
    have h := hF (2 * c) (by omega)
    rw [mr_cd_tb]
    exact h
  have hhi : (FP (Nat.succ (Nat.add (Nat.mul (nat_lit 16) s) (Nat.mul (nat_lit 2) c)))).testBit j =
      (cd B c).testBit 1 := by
    have h := hF (2 * c + 1) (by omega)
    rw [mr_cd_tb]
    exact h
  have hf := mr_frob4_tb _ (mr_cd_lt B c)
  have h0 : (Nat.xor (FP (Nat.add (Nat.mul (nat_lit 16) s) (Nat.mul (nat_lit 2) c)))
      (FP (Nat.succ (Nat.add (Nat.mul (nat_lit 16) s) (Nat.mul (nat_lit 2) c))))).testBit j =
      (frob4 (cd B c)).testBit 0 := by
    rw [mr_tb_xor, hlo, hhi, hf.1]
  rw [ck_mS_gen h0 (hhi.trans hf.2.symm) (mr_frob4_lt (mr_cd_lt B c)) (mr_cdK_lt x c) hj he,
    mr_cdK, mr_mul4_comm _ (mr_frob4_lt (mr_cd_lt B c)) _ (mr_cd_lt x c)]

theorem ck_fpc_tb {FP : Nat → Nat} {B j s : Nat}
    (hF : ∀ t < 16, (FP (16 * s + t)).testBit j = B.testBit t) {c e : Nat} (hc : c < 8)
    (he : e < 2) : (fpc FP s c e).testBit j = (cd B c).testBit e := by
  have h := hF (2 * c + e) (by omega)
  have e1 : 16 * s + (2 * c + e) = 16 * s + 2 * c + e := by omega
  rw [e1] at h
  rw [mr_cd_tb, decide_eq_true he, Bool.true_and]
  exact h

theorem ck_cxOf_tb {FP : Nat → Nat} {B : Nat → Nat} {j x : Nat}
    (hF : ∀ s < 4, ∀ t < 16, (FP (16 * s + t)).testBit j = (B s).testBit t) (hj : j < 4480)
    (hx : x < 65536) :
    (cxOf FP x).testBit j = (x == (smulC (hermC x (B 0)) (B 0) ^^^ smulC (hermC x (B 1)) (B 1) ^^^
      smulC (hermC x (B 2)) (B 2) ^^^ smulC (hermC x (B 3)) (B 3))) := by
  have hw : (smulC (hermC x (B 0)) (B 0) ^^^ smulC (hermC x (B 1)) (B 1) ^^^
      smulC (hermC x (B 2)) (B 2) ^^^ smulC (hermC x (B 3)) (B 3)) < 65536 := by
    have h16 : (65536 : Nat) = 2 ^ 16 := rfl
    rw [h16]
    repeat' apply Nat.xor_lt_two_pow
    all_goals exact mr_smulC_lt _ _
  have hL : ∀ s < 4, ∀ c < 8, (m0 (hermS FP x s (nat_lit 0)) (hermS FP x s (nat_lit 1))
      (fpc FP s c (nat_lit 0)) (fpc FP s c (nat_lit 1))).testBit j =
      (mul4 (hermC x (B s)) (cd (B s) c)).testBit 0 := fun s hs c hc => by
    rw [pf_tb_m0, ck_hermS_tb (hF s hs) hj (by decide), ck_hermS_tb (hF s hs) hj (by decide),
      ck_fpc_tb (hF s hs) hc (by decide), ck_fpc_tb (hF s hs) hc (by decide),
      mr_mul4_tb0 _ (mr_hermC_lt x _) _ (mr_cd_lt _ c)]
  have hH : ∀ s < 4, ∀ c < 8, (m1 (hermS FP x s (nat_lit 0)) (hermS FP x s (nat_lit 1))
      (fpc FP s c (nat_lit 0)) (fpc FP s c (nat_lit 1))).testBit j =
      (mul4 (hermC x (B s)) (cd (B s) c)).testBit 1 := fun s hs c hc => by
    rw [pf_tb_m1, ck_hermS_tb (hF s hs) hj (by decide), ck_hermS_tb (hF s hs) hj (by decide),
      ck_fpc_tb (hF s hs) hc (by decide), ck_fpc_tb (hF s hs) hc (by decide),
      mr_mul4_tb1 _ (mr_hermC_lt x _) _ (mr_cd_lt _ c)]
  have hC0 : ∀ c, (cstS (Nat.land (cdK x c) (nat_lit 1))).testBit j = (cd x c).testBit 0 :=
    fun c => by rw [ck_cstS0 hj, mr_cdK]
  have hC1 : ∀ c, (cstS (Nat.shiftRight (cdK x c) (nat_lit 1))).testBit j = (cd x c).testBit 1 :=
    fun c => by rw [ck_cstS1 (mr_cdK_lt x c) hj, mr_cdK]
  rw [mr_beq_cd hx hw]
  unfold cxOf
  generalize hn' : (nat_lit 8) = n
  have hn : n = 8 := by rw [← hn']
  simp only [mr_strictN]
  rw [mr_tb_xor, ck_allS_tb, decide_eq_true hj, mr_rec_lor_tb, Bool.true_xor]
  congr 1
  apply mr_rec_or_congr
  intro c hc
  have hc8 : c < 8 := by omega
  rw [mr_ne4 _ (mr_cd_lt x c) _ (mr_cd_lt _ c)]
  simp only [mr_tb_lor, mr_tb_xor, hC0, hC1, hL 0 (by decide) c hc8, hL 1 (by decide) c hc8,
    hL 2 (by decide) c hc8, hL 3 (by decide) c hc8, hH 0 (by decide) c hc8,
    hH 1 (by decide) c hc8, hH 2 (by decide) c hc8, hH 3 (by decide) c hc8, mr_cd_xor,
    mr_cd_smulC _ _ _ hc8, Nat.testBit_xor, Bool.xor_assoc]

theorem ck_fpOf_tb (T s b : Nat) : ∀ (Fl : List (Array Nat)) (j : Nat) (hj : j < Fl.length),
    (fpOf T Fl s b).testBit j = (ptAt T (getL (Fl[j]'hj).toList s)).testBit b
  | [], j, hj => absurd hj (Nat.not_lt_zero j)
  | fr :: Fl, j, hj => by
    change (Nat.lor (Nat.land (Nat.shiftRight (ptAt T (getL fr.toList s)) b) (nat_lit 1))
      (Nat.shiftLeft (fpOf T Fl s b) (nat_lit 1))).testBit j = _
    rw [mr_tb_lor, mr_tb_land, mr_tb_shr, mr_tb_shl]
    cases j with
    | zero => simp
    | succ j =>
      have h1 : Nat.testBit (nat_lit 1) (j + 1) = false := by
        rw [Nat.testBit_succ]
        simp
      rw [h1, Bool.and_false, Bool.false_or]
      have := ck_fpOf_tb T s b Fl j (by simpa using hj)
      simpa using this

theorem ck_or8 {t : Nat → Nat} (ht : ∀ k, t k < 4) : ∀ n i,
    (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun c acc => Nat.lor acc (Nat.shiftLeft (t c) (Nat.mul (nat_lit 2) c))) n).testBit i =
      (decide (i < 2 * n) && (t (i / 2)).testBit (i % 2))
  | 0, i => by
    simp only [mr_rec_zero]
    simp
  | n + 1, i => by
    simp only [mr_rec_succ]
    rw [mr_tb_lor, ck_or8 ht n i, mr_tb_shl]
    have h2 : Nat.mul 2 n = 2 * n := rfl
    rw [h2]
    by_cases h1 : i < 2 * n
    · have : ¬ (2 * n ≤ i) := by omega
      simp [h1, this]
      omega
    · by_cases h3 : i < 2 * n + 2
      · have e1 : i / 2 = n := by omega
        have e2 : i % 2 = i - 2 * n := by omega
        rw [decide_eq_false h1, decide_eq_true (by omega : i ≥ 2 * n),
          decide_eq_true (by omega : i < 2 * (n + 1)), e1, e2]
        simp
      · have hb : (t n).testBit (i - 2 * n) = false := Nat.testBit_lt_two_pow
          (Nat.lt_of_lt_of_le (ht n) (by
            have : 2 ^ 2 ≤ 2 ^ (i - 2 * n) := Nat.pow_le_pow_right (by decide) (by omega)
            simpa using this))
        have : ¬ (i < 2 * (n + 1)) := by omega
        simp [h1, hb, this]

theorem ck_smulK {a : Nat} (v : Nat) {c : Nat} (hc : c < 8) :
    cd (smulK a v) c = mulK a (cdK v c) ∧ smulK a v < 65536 := by
  have ht : ∀ k, mulK a (cdK v k) < 4 := fun k =>
    Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  have hb := ck_or8 ht 8
  refine ⟨?_, ?_⟩
  · apply Nat.eq_of_testBit_eq
    intro e
    rw [mr_cd_tb]
    change _ = (mulK a (cdK v c)).testBit e
    by_cases he : e < 2
    · rw [decide_eq_true he, Bool.true_and]
      change (Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun c acc => Nat.lor acc
        (Nat.shiftLeft (mulK a (cdK v c)) (Nat.mul (nat_lit 2) c))) 8).testBit (2 * c + e) = _
      rw [hb]
      have e1 : (2 * c + e) / 2 = c := by omega
      have e2 : (2 * c + e) % 2 = e := by omega
      rw [e1, e2, decide_eq_true (by omega : 2 * c + e < 2 * 8), Bool.true_and]
    · rw [decide_eq_false he, Bool.false_and, Nat.testBit_lt_two_pow
        (Nat.lt_of_lt_of_le (ht c) (by
          have : 2 ^ 2 ≤ 2 ^ e := Nat.pow_le_pow_right (by decide) (by omega)
          simpa using this))]
  · have h16 : (65536 : Nat) = 2 ^ 16 := rfl
    rw [h16]
    apply Nat.lt_pow_two_of_testBit
    intro i hi
    change (Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun c acc => Nat.lor acc
      (Nat.shiftLeft (mulK a (cdK v c)) (Nat.mul (nat_lit 2) c))) 8).testBit i = _
    rw [hb, decide_eq_false (by omega), Bool.false_and]

theorem ck_herm_smul {X Y l : Nat} (hl : l < 4) (h : ∀ c < 8, cd X c = mul4 l (cd Y c)) (b : Nat) :
    hermC X b = mul4 l (hermC Y b) := by
  have ha : ∀ k, mul4 (mul4 l (cd Y k)) (frob4 (cd b k)) =
      mul4 l (mul4 (cd Y k) (frob4 (cd b k))) := fun k => by
    have : ∀ p < 4, ∀ q < 4, ∀ r < 4, mul4 (mul4 p q) r = mul4 p (mul4 q r) := by decide
    exact this _ hl _ (mr_cd_lt Y k) _ (mr_frob4_lt (mr_cd_lt b k))
  have hd : ∀ p < 4, ∀ q < 4, mul4 l p ^^^ mul4 l q = mul4 l (p ^^^ q) := by
    have : ∀ r < 4, ∀ p < 4, ∀ q < 4, mul4 r p ^^^ mul4 r q = mul4 r (p ^^^ q) := by decide
    exact this l hl
  have hx : ∀ p < 4, ∀ q < 4, p ^^^ q < 4 := by decide
  have ht : ∀ k, mul4 (cd Y k) (frob4 (cd b k)) < 4 := fun k =>
    mr_mul4_lt _ (mr_frob4_lt (mr_cd_lt b k))
  unfold hermC
  rw [h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide),
    h 5 (by decide), h 6 (by decide), h 7 (by decide), ha, ha, ha, ha, ha, ha, ha, ha]
  rw [hd _ (ht 0) _ (ht 1)]
  rw [hd _ (hx _ (ht 0) _ (ht 1)) _ (ht 2)]
  rw [hd _ (hx _ (hx _ (ht 0) _ (ht 1)) _ (ht 2)) _ (ht 3)]
  rw [hd _ (hx _ (hx _ (hx _ (ht 0) _ (ht 1)) _ (ht 2)) _ (ht 3)) _ (ht 4)]
  rw [hd _ (hx _ (hx _ (hx _ (hx _ (ht 0) _ (ht 1)) _ (ht 2)) _ (ht 3)) _ (ht 4)) _ (ht 5)]
  rw [hd _ (hx _ (hx _ (hx _ (hx _ (hx _ (ht 0) _ (ht 1)) _ (ht 2)) _ (ht 3)) _ (ht 4)) _ (ht 5))
    _ (ht 6)]
  rw [hd _ (hx _ (hx _ (hx _ (hx _ (hx _ (hx _ (ht 0) _ (ht 1)) _ (ht 2)) _ (ht 3)) _ (ht 4))
    _ (ht 5)) _ (ht 6)) _ (ht 7)]

theorem ck_memC_smul {P fr : Array Nat} {X Y l : Nat} (hX : X < 65536) (hY : Y < 65536)
    (hl0 : 0 < l) (hl : l < 4) (h : ∀ c < 8, cd X c = mul4 l (cd Y c)) :
    memC P fr X = memC P fr Y := by
  have hw : ∀ Z, (smulC (hermC Z P[fr[0]!]!) P[fr[0]!]! ^^^ smulC (hermC Z P[fr[1]!]!) P[fr[1]!]! ^^^
      smulC (hermC Z P[fr[2]!]!) P[fr[2]!]! ^^^ smulC (hermC Z P[fr[3]!]!) P[fr[3]!]!) < 65536 := by
    intro Z
    have h16 : (65536 : Nat) = 2 ^ 16 := rfl
    rw [h16]
    repeat' apply Nat.xor_lt_two_pow
    all_goals exact mr_smulC_lt _ _
  have hd : ∀ p < 4, ∀ q < 4, mul4 l p ^^^ mul4 l q = mul4 l (p ^^^ q) := by
    have : ∀ r < 4, ∀ p < 4, ∀ q < 4, mul4 r p ^^^ mul4 r q = mul4 r (p ^^^ q) := by decide
    exact this l hl
  have hx : ∀ p < 4, ∀ q < 4, p ^^^ q < 4 := by decide
  have ha : ∀ p < 4, ∀ q < 4, mul4 (mul4 l p) q = mul4 l (mul4 p q) := by
    have : ∀ r < 4, ∀ p < 4, ∀ q < 4, mul4 (mul4 r p) q = mul4 r (mul4 p q) := by decide
    exact this l hl
  have hne : ∀ p < 4, ∀ q < 4, (mul4 l p != mul4 l q) = (p != q) := by
    have : ∀ r < 4, 0 < r → ∀ p < 4, ∀ q < 4, (mul4 r p != mul4 r q) = (p != q) := by decide
    exact this l hl hl0
  simp only [memC]
  rw [mr_beq_cd hX (hw X), mr_beq_cd hY (hw Y)]
  congr 1
  generalize hn' : (nat_lit 8) = n
  have hn : n = 8 := by rw [← hn']
  apply mr_rec_or_congr
  intro c hc
  have hc8 : c < 8 := by omega
  simp only [mr_cd_xor, mr_cd_smulC _ _ _ hc8, ck_herm_smul hl h, h c hc8]
  have hm : ∀ s, mul4 (hermC Y s) (cd s c) < 4 := fun s => mr_mul4_lt _ (mr_cd_lt s c)
  rw [ha _ (mr_hermC_lt _ _) _ (mr_cd_lt _ c), ha _ (mr_hermC_lt _ _) _ (mr_cd_lt _ c),
    ha _ (mr_hermC_lt _ _) _ (mr_cd_lt _ c), ha _ (mr_hermC_lt _ _) _ (mr_cd_lt _ c),
    hd _ (hm _) _ (hm _), hd _ (hx _ (hm _) _ (hm _)) _ (hm _),
    hd _ (hx _ (hx _ (hm _) _ (hm _)) _ (hm _)) _ (hm _),
    hne _ (mr_cd_lt Y c) _ (hx _ (hx _ (hx _ (hm _) _ (hm _)) _ (hm _)) _ (hm _))]

theorem ck_lor_list (g : Nat → Nat) (i : Nat) : ∀ l : List Nat,
    (List.rec (motive := fun _ => Nat) (nat_lit 0) (fun w _ ih => Nat.lor (g w) ih) l).testBit i =
      true → ∃ w ∈ l, (g w).testBit i = true
  | [], h => by
    change (0 : Nat).testBit i = true at h
    simp at h
  | w :: l, h => by
    change (Nat.lor (g w) _).testBit i = true at h
    rw [mr_tb_lor, Bool.or_eq_true] at h
    rcases h with h | h
    · exact ⟨w, List.mem_cons_self, h⟩
    · obtain ⟨w', hw', h'⟩ := ck_lor_list g i l h
      exact ⟨w', List.mem_cons_of_mem _ hw', h'⟩

theorem ck_vec_memC {P fr : Array Nat} {XC : Nat → Nat} {u v c f : Nat} (hc : c < 4)
    (hf : f < 32768) (h : vecOK XC 4989 u v c f = true) :
    Nat.land f 8191 < 4989 ∧ XC (Nat.land f 8191) < 65536 ∧ ∀ Y, Y < 65536 →
      (∀ i < 8, cd Y i = cd u i ^^^ mul4 c (cd v i)) →
      memC P fr (XC (Nat.land f 8191)) = memC P fr Y := by
  simp only [vecOK, ck_strictB] at h
  obtain ⟨h1, h2⟩ := ck_bAnd_true h
  obtain ⟨h2, h3⟩ := ck_bAnd_true h2
  have hX := (Nat.eq_of_beq_eq_true h3).symm
  have hl : Nat.shiftRight f 13 < 4 := by
    change f >>> 13 < 4
    rw [Nat.shiftRight_eq_div_pow]
    omega
  have hl0 : 0 < Nat.shiftRight f 13 := by simpa using h2
  have hlt : XC (Nat.land f 8191) < 65536 := by
    rw [hX]
    exact (ck_smulK _ (c := 0) (by decide)).2
  refine ⟨by simpa using h1, hlt, fun Y hY hYc => ck_memC_smul hlt hY hl0 hl fun i hi => ?_⟩
  have hx : ∀ p < 4, ∀ q < 4, p ^^^ q < 4 := by decide
  rw [hX, (ck_smulK _ hi).1, mr_cdK, pf_xor_eq, mr_cd_xor, (ck_smulK _ hi).1, mr_cdK,
    pf_mulK4 c hc _ (mr_cd_lt v i),
    pf_mulK4 _ hl _ (hx _ (mr_cd_lt u i) _ (mr_mul4_lt _ (mr_cd_lt v i))), hYc i hi]

theorem apartK_sound {L : List Nat} {F : Array (Array Nat)} {M S TF FP XC CX : Nat → Nat}
    {AP : Nat → List Nat} (hp : ptK L = true) (hL : L.length = 2240) (hF : F.size = 4480)
    (hM : ∀ c < 16, masksK L F.toList M (280 * c) 280 = true)
    (hS : ∀ i < 2240, S i < 2 ^ 4480 ∧
      ∀ j < 4480, Nat.testBit (S i) j = ((mkTabs (ptCodes ()) F).inc[j]!)[i]!)
    (hT : ∀ j < 4480, TF j < 2 ^ 4480 ∧
      ∀ j' < 4480, Nat.testBit (TF j) j' = (j != j' && triTest (mkTabs (ptCodes ()) F) j j'))
    (hfp : fpK L F.toList FP = true) (hcx : ∀ t < 4989, cxK FP XC CX t 1 = true)
    (hap : ∀ c < 16, apK L M S TF XC CX AP 4989 (280 * c) 280 = true) :
    apartCheck (mkTabs (ptCodes ()) F) = true := by
  have hPL : ptCodes () = L.toArray := ptK_sound hp
  have hPsz : (ptCodes ()).size = 2240 := by rw [hPL, List.size_toArray, hL]
  have hLb : ∀ x ∈ L, x < 65536 := (mr_ptK hp).2
  have hMs := fun {j} (hj : j < 4480) => masksK_sound (F := F) hp hL hM hj
  have hPa : ∀ a, (ptCodes ())[a]! = L.getD a 0 := fun a => by
    rw [hPL, mr_arr_get, List.toList_toArray]
  have hTa : ∀ a, ptAt (packL L) a = L.getD a 0 := mr_ptAt_packL hLb
  have hGb : ∀ a, L.getD a 0 < 65536 := mr_getD_lt hLb
  have hFP : ∀ t < 64, FP t = fpOf (packL L) F.toList (Nat.shiftRight t 4) (Nat.land t 15) := by
    intro t ht
    have h1 : CFSG.KC.Enum.allBlk 0 (fun t => Nat.beq (fpOf (packL L) F.toList
        (Nat.shiftRight t 4) (Nat.land t 15)) (FP t)) 64 = true := by
      have := hfp
      unfold fpK at this
      rw [ck_strictB] at this
      exact this
    have := ck_allBlk h1 t ht
    rw [Nat.zero_add] at this
    exact (Nat.eq_of_beq_eq_true this).symm
  have hFPb : ∀ j' < 4480, ∀ s < 4, ∀ t < 16, (FP (16 * s + t)).testBit j' =
      (L.getD ((F[j']!).toList.getD s 0) 0).testBit t := by
    intro j' hj' s hs t ht
    rw [hFP _ (by omega)]
    have e1 : Nat.shiftRight (16 * s + t) 4 = s := by
      change (16 * s + t) >>> 4 = s
      rw [Nat.shiftRight_eq_div_pow]
      omega
    have e2 : Nat.land (16 * s + t) 15 = t := by
      change (16 * s + t) &&& (2 ^ 4 - 1) = t
      rw [Nat.and_two_pow_sub_one_eq_mod]
      omega
    have hjl : j' < F.toList.length := by simp [hF, hj']
    rw [e1, e2, ck_fpOf_tb _ _ _ _ _ hjl, hTa, mr_getL]
    rw [getElem!_pos F j' (by omega)]
    simp
  have hCX : ∀ k < 4989, CX k = cxOf FP (XC k) := fun k hk => by
    have := ck_allBlk (hcx k hk) 0 (by decide)
    exact (Nat.eq_of_beq_eq_true this).symm
  have hmemCX : ∀ j' < 4480, ∀ x < 65536,
      (cxOf FP x).testBit j' = memC (ptCodes ()) F[j']! x := by
    intro j' hj' x hx
    rw [ck_cxOf_tb (B := fun s => L.getD ((F[j']!).toList.getD s 0) 0)
      (fun s hs t ht => hFPb j' hj' s hs t ht) hj' hx]
    simp only [memC, hPa, mr_arr_get]
  have hk : ∀ x, Nat.land (Nat.land x 32767) 8191 = Nat.land x 8191 := fun x => by
    change (x &&& 32767) &&& 8191 = x &&& 8191
    rw [Nat.and_assoc]
    rfl
  have hf : ∀ x, Nat.land x 32767 < 32768 := fun x =>
    Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  simp only [apartCheck, List.all_eq_true, List.mem_range]
  intro j hj j' hj'
  simp only [Bool.or_eq_true, beq_iff_eq]
  by_cases hjj : j = j'
  · exact Or.inl (Or.inl hjj)
  by_cases htt : triTest (mkTabs (ptCodes ()) F) j j' = true
  · exact Or.inl (Or.inr htt)
  right
  have hTF : (TF j).testBit j' = false := by
    rw [(hT j hj).2 j' hj']
    simp [hjj, htt]
  have hok := ck_allBlkC (w := 280) (C := 16) (f := apOK M S TF XC CX AP 4989 (packL L))
    (fun c hc => by
      have := hap c hc
      unfold apK at this
      rw [ck_strictB] at this
      exact this) (by omega : j < 280 * 16)
  simp only [apOK, ck_strictB] at hok
  obtain ⟨hW, hcov⟩ := ck_bAnd_true hok
  have hbit := congrArg (Nat.testBit · j') (Nat.eq_of_beq_eq_true hcov)
  simp only [mr_tb_lor, hTF, ck_allS_tb, ck_tshl1, decide_eq_true hj', Bool.false_or,
    decide_eq_false hjj] at hbit
  obtain ⟨w, hw, hcw⟩ := ck_lor_list (apC S CX) j' (AP j) hbit
  have hapw := ck_lall (g := apW XC 4989 (packL L) (M j)) hW w hw
  simp only [apW, ck_strictB] at hapw
  obtain ⟨ha, hapw⟩ := ck_bAnd_true hapw
  obtain ⟨hb, hapw⟩ := ck_bAnd_true hapw
  obtain ⟨v1, hapw⟩ := ck_bAnd_true hapw
  obtain ⟨v2, v3⟩ := ck_bAnd_true hapw
  rw [hTa, hTa] at v1 v2 v3
  rw [ck_bitAt] at ha hb
  unfold apC at hcw
  simp only [mr_tb_xor, mr_tb_lor, ck_allS_tb, decide_eq_true hj', Bool.true_xor, Bool.not_or,
    Bool.and_eq_true, Bool.not_eq_true'] at hcw
  obtain ⟨⟨sa, sb⟩, c1, c2, c3⟩ := hcw
  have ha2 : Nat.land w 4095 < 2240 := ck_bit_lt (hMs hj).1 ha
  have hb2 : wF w 12 < 2240 := ck_bit_lt (hMs hj).1 hb
  have hpts : (mkTabs (ptCodes ()) F).pts = ptCodes () := rfl
  have hfrs : (mkTabs (ptCodes ()) F).frames = F := rfl
  obtain ⟨k1, x1, m1⟩ := ck_vec_memC (P := ptCodes ()) (fr := F[j']!) (by decide) (hf _) v1
  obtain ⟨k2, x2, m2⟩ := ck_vec_memC (P := ptCodes ()) (fr := F[j']!) (by decide) (hf _) v2
  obtain ⟨k3, x3, m3⟩ := ck_vec_memC (P := ptCodes ()) (fr := F[j']!) (by decide) (hf _) v3
  rw [hk] at k1 k2 k3 x1 x2 x3 m1 m2 m3
  have hx16 : ∀ p q : Nat, p < 65536 → q < 65536 → p ^^^ q < 65536 := fun p q hp hq => by
    have h16 : (65536 : Nat) = 2 ^ 16 := rfl
    rw [h16] at hp hq ⊢
    exact Nat.xor_lt_two_pow hp hq
  rw [Array.any_eq_true']
  refine ⟨Nat.land w 4095, (ck_solPts_mem (by omega)).mpr ⟨by omega, ?_⟩, ?_⟩
  · rw [← (hMs hj).2 _ ha2]
    exact ha
  rw [Array.any_eq_true']
  refine ⟨wF w 12, (ck_solPts_mem (by omega)).mpr ⟨by omega, ?_⟩, ?_⟩
  · rw [← (hMs hj).2 _ hb2]
    exact hb
  simp only [Bool.and_eq_true, Bool.not_eq_true', hpts, hfrs, hPa]
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [← (hS _ ha2).2 j' hj']
    exact sa
  · rw [← (hS _ hb2).2 j' hj']
    exact sb
  · rw [← m1 _ (hx16 _ _ (hGb _) (hGb _)) fun i _ => by rw [mr_cd_xor]; rfl,
      ← hmemCX j' hj' _ x1, ← hCX _ k1]
    exact c1
  · rw [← m2 _ (hx16 _ _ (hGb _) (mr_smulC_lt _ _)) fun i hi => by
      rw [mr_cd_xor, mr_cd_smulC _ _ _ hi], ← hmemCX j' hj' _ x2, ← hCX _ k2]
    exact c2
  · rw [← m3 _ (hx16 _ _ (hGb _) (mr_smulC_lt _ _)) fun i hi => by
      rw [mr_cd_xor, mr_cd_smulC _ _ _ hi], ← hmemCX j' hj' _ x3, ← hCX _ k3]
    exact c3

end CFSG.KC.D4Q2K

end
