module

public import Certificates.Data.Kernel.Misc.F7Fast
public import CFSG.Certificates.Kernel.Misc.F7Echelon

public section

namespace CFSG.KC.Misc.F7

open CFSG.KC.Loop

theorem f7S_m001 : ∀ k < 360, m001.testBit (3 * k) = true := by decide +kernel

theorem f7S_lt_of_shl {c n : ℕ} (h : c.succ ≤ Nat.shiftLeft 1 n) : c < 2 ^ n := by
  have h2 : Nat.shiftLeft 1 n = 2 ^ n := Nat.one_shiftLeft n
  omega

theorem f7S_testBit_high {c n b : ℕ} (hc : c < 2 ^ n) (hb : n ≤ b) : c.testBit b = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hc (Nat.pow_le_pow_right (by decide) hb))

theorem f7S_canon_tail {c pw : ℕ} (h : f7Canon c pw = true) :
    Nat.land (Nat.land c (Nat.land (Nat.shiftRight c 1) (Nat.shiftRight c 2))) m001 = 0 ∧
      c < 2 ^ 1080 := by
  unfold f7Canon at h
  simp only [bAnd_eq] at h
  obtain ⟨_, _, _, hm, hlt⟩ := h
  refine ⟨Nat.eq_of_beq_eq_true hm, ?_⟩
  exact f7S_lt_of_shl (Nat.le_of_ble_eq_true hlt)

theorem f7S_testBit_field (c k r : ℕ) (hr : r < 3) :
    c.testBit (3 * k + r) = (c / 2 ^ (3 * k) % 8).testBit r := by
  rw [show (8 : ℕ) = 2 ^ 3 from rfl, Nat.testBit_mod_two_pow, decide_eq_true hr, Bool.true_and,
    Nat.testBit_div_two_pow, Nat.add_comm]

theorem f7S_field_lt {c : ℕ}
    (hm : Nat.land (Nat.land c (Nat.land (Nat.shiftRight c 1) (Nat.shiftRight c 2))) m001 = 0)
    {k : ℕ} (hk : k < 360) : c / 2 ^ (3 * k) % 8 < 7 := by
  by_contra hc
  have h7 : c / 2 ^ (3 * k) % 8 = 7 := by
    have := Nat.mod_lt (c / 2 ^ (3 * k)) (by decide : 0 < 8)
    omega
  have hb : ∀ r < 3, c.testBit (3 * k + r) = true := fun r hr => by
    rw [f7S_testBit_field c k r hr, h7]
    rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2) with rfl | rfl | rfl <;> rfl
  have hm2 : (c &&& ((c >>> 1) &&& (c >>> 2))) &&& m001 = 0 := hm
  have e := congrArg (fun x => x.testBit (3 * k)) hm2
  simp only [Nat.testBit_and, Nat.testBit_shiftRight, Nat.zero_testBit] at e
  have h0 : c.testBit (3 * k) = true := hb 0 (by decide)
  have h1 : c.testBit (1 + 3 * k) = true := by
    rw [Nat.add_comm]
    exact hb 1 (by decide)
  have h2 : c.testBit (2 + 3 * k) = true := by
    rw [Nat.add_comm]
    exact hb 2 (by decide)
  rw [f7S_m001 k hk, h0, h1, h2] at e
  simp at e

theorem f7Canon_inj {c c' pw pw' : ℕ} (h : f7Canon c pw = true) (h' : f7Canon c' pw' = true)
    (e : decC 8 c = decC 8 c') : c = c' := by
  obtain ⟨hm, hc⟩ := f7S_canon_tail h
  obtain ⟨hm', hc'⟩ := f7S_canon_tail h'
  apply Nat.eq_of_testBit_eq
  intro b
  by_cases hb : b < 1080
  · set k := b / 3 with hkd
    have hk : k < 360 := by omega
    have hbk : b = 3 * k + b % 3 := by omega
    have hi : k / 45 < 8 := by omega
    have hj : k % 45 < 45 := Nat.mod_lt _ (by decide)
    have he := congrFun (congrFun e ⟨k / 45, hi⟩) ⟨k % 45, hj⟩
    simp only [decC] at he
    have hk45 : 45 * (k / 45) + k % 45 = k := Nat.div_add_mod k 45
    rw [hk45, ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (f7S_field_lt hm hk),
      Nat.mod_eq_of_lt (f7S_field_lt hm' hk)] at he
    rw [hbk, f7S_testBit_field c k _ (Nat.mod_lt _ (by decide)),
      f7S_testBit_field c' k _ (Nat.mod_lt _ (by decide)), he]
  · rw [f7S_testBit_high hc (by omega), f7S_testBit_high hc' (by omega)]

theorem f7S_colMask3 : ∀ q < 1080, colMask3.testBit q = decide (q % 135 < 3) := by decide +kernel

theorem f7S_field_eq {c m v : ℕ} (hv : v < 8) (h : ∀ r < 3, c.testBit (3 * m + r) = v.testBit r) :
    c / 2 ^ (3 * m) % 8 = v := by
  apply Nat.eq_of_testBit_eq
  intro r
  by_cases hr : r < 3
  · rw [← f7S_testBit_field c m r hr, h r hr]
  · rw [f7S_testBit_high (c := c / 2 ^ (3 * m) % 8) (n := 3)
        (Nat.lt_of_lt_of_eq (Nat.mod_lt _ (by decide)) rfl) (by omega),
      f7S_testBit_high (c := v) (n := 3) (Nat.lt_of_lt_of_eq hv rfl) (by omega)]

theorem f7S_nthF : ∀ (l : List ℕ) (i : ℕ), nthF l i = l.getD i 0
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: l, i + 1 => f7S_nthF l i

theorem f7S_unit {c p k : ℕ} (hk : k < 8)
    (hu : Nat.land (Nat.shiftRight c (Nat.mul 3 p)) colMask3 = Nat.shiftLeft 1 (Nat.mul 135 k))
    {i : ℕ} (hi : i < 8) : c / 2 ^ (3 * (45 * i + p)) % 8 = if i = k then 1 else 0 := by
  have e1 : Nat.shiftLeft 1 (Nat.mul 135 k) = 2 ^ (135 * k) := Nat.one_shiftLeft _
  rw [e1] at hu
  refine f7S_field_eq (by split_ifs <;> decide) fun r hr => ?_
  have ht := congrArg (fun x => x.testBit (135 * i + r)) hu
  have hq : 135 * i + r < 1080 := by omega
  change ((c >>> (3 * p)) &&& colMask3).testBit (135 * i + r) =
    (2 ^ (135 * k)).testBit (135 * i + r) at ht
  rw [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow, f7S_colMask3 _ hq,
    decide_eq_true (by omega), Bool.and_true] at ht
  rw [show 3 * (45 * i + p) + r = 3 * p + (135 * i + r) by omega, ht]
  by_cases hik : i = k
  · subst hik
    rw [if_pos rfl]
    rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2) with rfl | rfl | rfl <;> simp <;> decide
  · rw [if_neg hik, decide_eq_false (by omega), Nat.zero_testBit]

theorem f7S_zero {c p k j : ℕ} (hj : j < p)
    (hz : Nat.land (Nat.shiftRight c (Nat.mul 135 k))
      (Nat.sub (Nat.shiftLeft 1 (Nat.mul 3 p)) 1) = 0) :
    c / 2 ^ (3 * (45 * k + j)) % 8 = 0 := by
  have e1 : Nat.shiftLeft 1 (Nat.mul 3 p) = 2 ^ (3 * p) := Nat.one_shiftLeft _
  rw [e1] at hz
  refine f7S_field_eq (v := 0) (by decide) fun r hr => ?_
  have ht := congrArg (fun x => x.testBit (3 * j + r)) hz
  change ((c >>> (135 * k)) &&& (2 ^ (3 * p) - 1)).testBit (3 * j + r) =
    (0 : ℕ).testBit (3 * j + r) at ht
  rw [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one,
    decide_eq_true (by omega), Bool.and_true, Nat.zero_testBit] at ht
  rw [show 3 * (45 * k + j) + r = 135 * k + (3 * j + r) by omega, ht, Nat.zero_testBit]

theorem f7Canon_echelon {c pw : ℕ} (h : f7Canon c pw = true) :
    ∃ p : Fin 8 → Fin 45, (∀ k, (p k : ℕ) = pvF pw k) ∧ Echelon (decC 8 c) p := by
  unfold f7Canon at h
  simp only [bAnd_eq, allN_iff] at h
  obtain ⟨h1, h2, h3, _, _⟩ := h
  have hstep : ∀ k < 7, pvF pw k < pvF pw (k + 1) := fun k hk => by
    have := h2 k hk
    rw [Nat.blt_eq] at this
    exact this
  have hmono : ∀ a b, a < b → b < 8 → pvF pw a < pvF pw b := by
    intro a b hab hb
    induction b, hab using Nat.le_induction with
    | base => exact hstep a (by omega)
    | succ b hab ih => exact Nat.lt_trans (ih (by omega)) (hstep b (by omega))
  have h7 : pvF pw 7 < 45 := by
    rw [Nat.blt_eq] at h3
    exact h3
  have hlt : ∀ k < 8, pvF pw k < 45 := fun k hk => by
    rcases (by omega : k = 7 ∨ k < 7) with rfl | hk7
    · exact h7
    · exact Nat.lt_trans (hmono k 7 hk7 (by decide)) h7
  set piv := (List.range 8).map (pvF pw) with hpiv
  have hnth : ∀ k < 8, nthF piv k = pvF pw k := fun k hk => by
    rw [f7S_nthF, hpiv]
    simp [List.getD_eq_getElem?_getD, List.getElem?_range, hk]
  have hok : pivOK (enc (decC 8 c)) piv = true := by
    rw [pivOK, allN_iff]
    intro k hk
    rw [bAnd_eq, allN_iff, hnth k hk, Nat.blt_eq]
    refine ⟨hlt k hk, fun i hi => ?_⟩
    rw [row_enc (decC 8 c) ⟨i, hi⟩, lane_encV, ev, dif_pos (hlt k hk), nIf_eq, Nat.beq_eq]
    change (((c / 2 ^ (3 * (45 * i + pvF pw k)) % 8 : ℕ) : ZMod 7)).val =
      if Nat.beq i k = true then 1 else 0
    rw [f7S_unit hk (Nat.eq_of_beq_eq_true (h1 k hk).2) hi]
    by_cases hik : i = k
    · rw [if_pos hik, if_pos (by rw [hik]; exact Nat.beq_refl k)]
      rfl
    · rw [if_neg hik, if_neg (fun h => hik (Nat.eq_of_beq_eq_true h))]
      rfl
  obtain ⟨p, hp, hpv⟩ := pivOK_spec hok
  have hp' : ∀ k : Fin 8, (p k : ℕ) = pvF pw k := fun k => by rw [hp, hnth k k.isLt]
  refine ⟨p, hp', ⟨hpv, ?_, ?_⟩⟩
  · intro a b hab
    change (p a : ℕ) < p b
    rw [hp', hp']
    exact hmono a b hab b.isLt
  · intro k j hj
    have hj' : (j : ℕ) < pvF pw k := by
      have : (j : ℕ) < p k := hj
      rwa [hp'] at this
    change ((c / 2 ^ (3 * (45 * (k : ℕ) + j)) % 8 : ℕ) : ZMod 7) = 0
    rw [f7S_zero hj' (Nat.eq_of_beq_eq_true (h1 k k.isLt).1), Nat.cast_zero]

theorem enc_two_smul_one :
    2 * enc (1 : Matrix (Fin 45) (Fin 45) (ZMod 7)) =
      enc ((2 : ZMod 7) • (1 : Matrix (Fin 45) (Fin 45) (ZMod 7))) := by
  rw [enc, enc, D_mul]
  refine D_congr fun k hk => ?_
  rw [ent_pos _ hk, ent_pos _ hk, Matrix.smul_apply, Matrix.one_apply]
  split_ifs <;> rfl

theorem linearIndependent_rows {V : Matrix (Fin 8) (Fin 45) (ZMod 7)} {p : Fin 8 → Fin 45}
    (hp : Pivots V p) : Module.finrank (ZMod 7) (rowSpan V) = 8 := by
  rw [rowSpan, finrank_span_eq_card (linearIndependent_of_pivots hp), Fintype.card_fin]

theorem rowSpan_mul_eq_of_le {U V : Matrix (Fin 8) (Fin 45) (ZMod 7)} {pU pV : Fin 8 → Fin 45}
    {G H : Matrix (Fin 45) (Fin 45) (ZMod 7)} (hU : Pivots U pU) (hV : Pivots V pV)
    (hG : G * H = 1) (h : rowSpan (U * G) ≤ rowSpan V) : rowSpan (U * G) = rowSpan V := by
  refine Submodule.eq_of_le_of_finrank_eq h ?_
  rw [linearIndependent_rows hV]
  have hker : LinearMap.ker G.vecMulLinear = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 fun v hv => ?_
    rw [Matrix.vecMulLinear_apply] at hv
    rw [← Matrix.vecMul_one v, ← hG, ← Matrix.vecMul_vecMul, hv, Matrix.zero_vecMul]
  have e : rows (U * G) = G.vecMulLinear ∘ rows U := by
    funext i
    ext j
    simp [rows, Matrix.mul_apply, Matrix.vecMul, dotProduct]
  have hli : LinearIndependent (ZMod 7) (rows (U * G)) := by
    rw [e]
    exact (linearIndependent_of_pivots hU).map' G.vecMulLinear hker
  rw [rowSpan, finrank_span_eq_card hli, Fintype.card_fin]

section Fast

open Finset

theorem f7S_add_eq_or {a b : ℕ} (h : a &&& b = 0) : a + b = a ||| b := by
  have ha : a < 2 ^ (a + b) :=
    Nat.lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by decide) (by omega))
  have hb : b < 2 ^ (a + b) :=
    Nat.lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by decide) (by omega))
  have hxy : BitVec.ofNat (a + b) a &&& BitVec.ofNat (a + b) b = 0#(a + b) := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_and, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, h]
  have h1 := BitVec.toNat_add_of_and_eq_zero hxy
  rw [BitVec.add_eq_or_of_and_eq_zero _ _ hxy, BitVec.toNat_or, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h1
  exact h1.symm

theorem f7S_tb_iff {x y : ℕ} (h : ∀ b, x.testBit b = true ↔ y.testBit b = true) : x = y :=
  Nat.eq_of_testBit_eq fun b => Bool.eq_iff_iff.2 (h b)

theorem f7S_tb_lt {x w t : ℕ} (hx : x < 2 ^ w) (h : x.testBit t = true) : t < w := by
  by_contra hc
  rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (by omega)))]
    at h
  exact Bool.false_ne_true h

theorem f7S_mul_tb {x e b : ℕ} : (x * 2 ^ e).testBit b = true ↔ e ≤ b ∧ x.testBit (b - e) = true := by
  rw [Nat.testBit_mul_two_pow, Bool.and_eq_true, decide_eq_true_iff]

theorem f7S_testBit_sum {ι : Type*} [DecidableEq ι] (s : Finset ι) (f e : ι → ℕ) (w : ℕ)
    (hf : ∀ i ∈ s, f i < 2 ^ w)
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → e i + w ≤ e j ∨ e j + w ≤ e i) (b : ℕ) :
    (∑ i ∈ s, f i * 2 ^ e i).testBit b = true ↔
      ∃ i ∈ s, e i ≤ b ∧ (f i).testBit (b - e i) = true := by
  revert hf hd b
  refine Finset.induction_on s (fun _ _ _ => by simp) ?_
  intro j s hj ih hf hd b
  have hf' : ∀ i ∈ s, f i < 2 ^ w := fun i hi => hf i (mem_insert_of_mem hi)
  have hd' : ∀ i ∈ s, ∀ k ∈ s, i ≠ k → e i + w ≤ e k ∨ e k + w ≤ e i :=
    fun i hi k hk => hd i (mem_insert_of_mem hi) k (mem_insert_of_mem hk)
  have hwin : ∀ i ∈ insert j s, ∀ b', (f i * 2 ^ e i).testBit b' = true → e i ≤ b' ∧ b' < e i + w :=
    fun i hi b' hb => by
      rw [f7S_mul_tb] at hb
      exact ⟨hb.1, by have := f7S_tb_lt (hf i hi) hb.2; omega⟩
  have hand : (f j * 2 ^ e j) &&& (∑ i ∈ s, f i * 2 ^ e i) = 0 := by
    apply Nat.eq_of_testBit_eq
    intro b'
    rw [Nat.testBit_and, Nat.zero_testBit, Bool.and_eq_false_iff]
    by_contra hc
    simp only [not_or, Bool.not_eq_false] at hc
    obtain ⟨i, hi, hle, hbit⟩ := (ih hf' hd' b').1 hc.2
    have w1 := hwin j (mem_insert_self j s) b' hc.1
    have w2 := hwin i (mem_insert_of_mem hi) b' (f7S_mul_tb.2 ⟨hle, hbit⟩)
    have hne : j ≠ i := fun h => hj (h ▸ hi)
    rcases hd j (mem_insert_self j s) i (mem_insert_of_mem hi) hne with h | h <;> omega
  rw [sum_insert hj, f7S_add_eq_or hand, Nat.testBit_or, Bool.or_eq_true, ih hf' hd' b,
    f7S_mul_tb]
  constructor
  · rintro (h | ⟨i, hi, h⟩)
    · exact ⟨j, mem_insert_self j s, h⟩
    · exact ⟨i, mem_insert_of_mem hi, h⟩
  · rintro ⟨i, hi, h⟩
    rcases mem_insert.1 hi with rfl | hi
    · exact Or.inl h
    · exact Or.inr ⟨i, hi, h⟩

theorem f7S_fld_tb (c k t : ℕ) :
    (c / 2 ^ (3 * k) % 8).testBit t = (decide (t < 3) && c.testBit (3 * k + t)) := by
  rw [show (8 : ℕ) = 2 ^ 3 from rfl, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow,
    Nat.add_comm t]

theorem f7S_seven_tb (t : ℕ) : (7 : ℕ).testBit t = decide (t < 3) := by
  rw [show (7 : ℕ) = 2 ^ 3 - 1 from rfl, Nat.testBit_two_pow_sub_one]

theorem f7S_fld_lt (c k : ℕ) : c / 2 ^ (3 * k) % 8 < 2 ^ 3 := Nat.mod_lt _ (by decide)

theorem f7S_m8W_eq : m8W = D 360 fun _ => 255 := by
  rw [m8W, sumN_eq, D]
  refine sum_congr rfl fun j _ => ?_
  change 255 <<< (32 * j) = _
  rw [Nat.shiftLeft_eq]

theorem f7S_red7W_D {n : ℕ} {c : ℕ → ℕ} (hn : n ≤ 360) (hc : ∀ k < n, c k < 1621) :
    red7W (D n c) = D n fun k => c k % 7 := by
  have p32 : (2 : ℕ) ^ 32 = 4294967296 := by norm_num
  have hm : ∀ i, laneV m8W i = if i < 360 then 255 else 0 := fun i => by
    rw [f7S_m8W_eq, lane_D (n := 360) (c := fun _ => 255) (fun _ _ => by norm_num)]
  have hy : ∀ i, laneV (D n c * 4682) i = if i < n then c i * 4682 else 0 := fun i => by
    rw [D_mul_right, lane_D (n := n) (c := fun k => c k * 4682)
      (fun k hk => by have := hc k hk; rw [p32]; omega)]
  have hq : ((D n c * 4682) >>> 15) &&& m8W = D n fun k => c k / 7 := by
    apply laneV_ext
    intro i
    rw [laneV_and, hm, lane_D (n := n) (c := fun k => c k / 7)
      (fun k hk => by have := hc k hk; rw [p32]; omega)]
    by_cases h45 : i < 360
    · have h255 : (255 : ℕ) = 2 ^ 8 - 1 := by norm_num
      rw [ite_eq_left h45, h255, Nat.and_two_pow_sub_one_eq_mod, laneV_shift15, hy]
      by_cases hi : i < n
      · rw [ite_eq_left hi, ite_eq_left hi]
        have := hc i hi
        have h1 : (2 : ℕ) ^ 15 = 32768 := by norm_num
        have h2 : (2 : ℕ) ^ 8 = 256 := by norm_num
        rw [h1, h2]
        have hq7 : c i * 4682 / 32768 = c i / 7 := by omega
        rw [hq7]
        exact Nat.mod_eq_of_lt (by omega)
      · rw [ite_eq_right hi, ite_eq_right hi]
        rfl
    · rw [ite_eq_right h45, Nat.and_zero, ite_eq_right (by omega)]
  have e : D n c = (D n fun k => c k % 7) + 7 * D n fun k => c k / 7 := by
    rw [D_mul, D_add]
    exact D_congr fun k _ => (Nat.mod_add_div _ _).symm
  change D n c - 7 * (((D n c * 4682) >>> 15) &&& m8W) = _
  rw [hq]
  omega

theorem f7S_D_lt8 {n : ℕ} {c : ℕ → ℕ} (hc : ∀ k < n + 1, c k < 8) :
    D (n + 1) c < 2 ^ (32 * n + 3) := by
  rw [D_succ]
  have h1 := D_lt (n := n) (c := c) fun k hk => lt_trans (hc k (by omega)) (by norm_num)
  have h2 : c n * 2 ^ (32 * n) ≤ 7 * 2 ^ (32 * n) :=
    Nat.mul_le_mul_right _ (by have := hc n (by omega); omega)
  have h3 : 2 ^ (32 * n + 3) = 8 * 2 ^ (32 * n) := by rw [pow_add]; ring
  omega

theorem f7S_D_sum {n : ℕ} (s : Finset ℕ) (g : ℕ → ℕ → ℕ) :
    ∑ c ∈ s, D n (g c) = D n fun j => ∑ c ∈ s, g c j := by
  simp only [D]
  rw [sum_comm]
  exact sum_congr rfl fun j _ => (sum_mul _ _ _).symm

theorem f7S_D_sub {n : ℕ} {c d : ℕ → ℕ} (h : ∀ k < n, d k ≤ c k) :
    D n c - D n d = D n fun k => c k - d k := by
  have e := D_add n (fun k => c k - d k) d
  rw [D_congr (n := n) (d := c) fun k hk => Nat.sub_add_cancel (h k hk)] at e
  omega

theorem f7S_rows8 (h : ℕ → ℕ) :
    ∑ i ∈ range 8, h i * 2 ^ (1440 * i) = D 360 fun l => if l % 45 = 0 then h (l / 45) else 0 := by
  rw [show (360 : ℕ) = 45 * 8 from rfl, D_blocks]
  refine sum_congr rfl fun i _ => congrArg (fun x => x * 2 ^ (1440 * i)) ?_
  rw [D, sum_eq_single 0]
  · rw [show (45 * i + 0) % 45 = 0 by omega, show (45 * i + 0) / 45 = i by omega]
    simp
  · intro j hj hj0
    have hj' := mem_range.1 hj
    rw [if_neg (by omega), zero_mul]
  · intro h0
    exact absurd (mem_range.2 (by norm_num)) h0

theorem f7S_enc_rows (U : Matrix (Fin 8) (Fin 45) (ZMod 7)) :
    enc U = ∑ i ∈ range 8, row (enc U) i * 2 ^ (1440 * i) := by
  conv_lhs => rw [enc, D_blocks]
  refine sum_congr rfl fun i hi => ?_
  have hi' := mem_range.1 hi
  rw [row_enc U ⟨i, hi'⟩, encV]
  refine congrArg (fun x => x * 2 ^ (1440 * i)) (D_congr fun j hj => ?_)
  have e1 : (45 * i + j) / 45 = i := by omega
  have e2 : (45 * i + j) % 45 = j := by omega
  rw [e1, e2, ev_row U hi']

theorem f7S_red7W_rows (y : ℕ → ℕ) (a : ℕ → ℕ → ℕ) (hy : ∀ i < 8, y i = D 45 (a i))
    (ha : ∀ i < 8, ∀ j < 45, a i j < 1621) :
    red7W (∑ i ∈ range 8, y i * 2 ^ (1440 * i)) = ∑ i ∈ range 8, red7 (y i) * 2 ^ (1440 * i) := by
  have e : ∑ i ∈ range 8, y i * 2 ^ (1440 * i) = D (45 * 8) fun l => a (l / 45) (l % 45) := by
    rw [D_blocks]
    refine sum_congr rfl fun i hi => ?_
    have hi' := mem_range.1 hi
    rw [hy i hi']
    refine congrArg (fun x => x * 2 ^ (1440 * i)) (D_congr fun j hj => ?_)
    have e1 : (45 * i + j) / 45 = i := by omega
    have e2 : (45 * i + j) % 45 = j := by omega
    rw [e1, e2]
  rw [e, f7S_red7W_D (by norm_num) fun l hl => ha _ (by omega) _ (Nat.mod_lt _ (by norm_num)),
    D_blocks]
  refine sum_congr rfl fun i hi => ?_
  have hi' := mem_range.1 hi
  rw [hy i hi', red7_D le_rfl (ha i hi')]
  refine congrArg (fun x => x * 2 ^ (1440 * i)) (D_congr fun j hj => ?_)
  have e1 : (45 * i + j) / 45 = i := by omega
  have e2 : (45 * i + j) % 45 = j := by omega
  rw [e1, e2]

def f7S_g (c r m : ℕ) : ℕ := if r + 13 * m < 360 then c / 2 ^ (3 * (r + 13 * m)) % 8 else 0

theorem f7S_g_lt (c r m : ℕ) : f7S_g c r m < 2 ^ 3 := by
  rw [f7S_g]
  split_ifs
  · exact f7S_fld_lt _ _
  · exact Nat.two_pow_pos 3

theorem f7S_ifN7 (a x : ℕ) :
    ifN (Nat.blt a 360) (7 <<< x) 0 = (if a < 360 then 7 else 0) * 2 ^ x := by
  rw [nIf_eq, Nat.shiftLeft_eq]
  by_cases h : a < 360 <;> simp [h, Nat.blt_eq]

theorem f7S_wMaskC (c r : ℕ) :
    c &&& wMaskC r = ∑ m ∈ range 28, f7S_g c r m * 2 ^ (3 * (r + 13 * m)) := by
  have hM : wMaskC r = ∑ m ∈ range 28, (if r + 13 * m < 360 then 7 else 0) *
      2 ^ (3 * (r + 13 * m)) := by
    rw [wMaskC, sumN_eq]
    exact sum_congr rfl fun m _ => f7S_ifN7 (r + 13 * m) (3 * (r + 13 * m))
  rw [hM]
  have hd : ∀ i ∈ range 28, ∀ j ∈ range 28, i ≠ j →
      3 * (r + 13 * i) + 3 ≤ 3 * (r + 13 * j) ∨ 3 * (r + 13 * j) + 3 ≤ 3 * (r + 13 * i) :=
    fun i _ j _ hij => by omega
  apply f7S_tb_iff
  intro b
  rw [Nat.testBit_and, Bool.and_eq_true,
    f7S_testBit_sum (range 28) (fun m => if r + 13 * m < 360 then 7 else 0)
      (fun m => 3 * (r + 13 * m)) 3 (fun m _ => by split_ifs <;> decide) hd b,
    f7S_testBit_sum (range 28) (f7S_g c r) (fun m => 3 * (r + 13 * m)) 3
      (fun m _ => f7S_g_lt c r m) hd b]
  constructor
  · rintro ⟨hc, m, hm, hle, hb⟩
    refine ⟨m, hm, hle, ?_⟩
    by_cases h : r + 13 * m < 360
    · rw [if_pos h, f7S_seven_tb, decide_eq_true_iff] at hb
      rw [f7S_g, if_pos h, f7S_fld_tb, show 3 * (r + 13 * m) + (b - 3 * (r + 13 * m)) = b by omega,
        hc, decide_eq_true hb]
      rfl
    · rw [if_neg h, Nat.zero_testBit] at hb
      exact absurd hb (by decide)
  · rintro ⟨m, hm, hle, hb⟩
    by_cases h : r + 13 * m < 360
    · rw [f7S_g, if_pos h, f7S_fld_tb, Bool.and_eq_true, decide_eq_true_iff,
        show 3 * (r + 13 * m) + (b - 3 * (r + 13 * m)) = b by omega] at hb
      refine ⟨hb.2, m, hm, hle, ?_⟩
      rw [if_pos h, f7S_seven_tb, decide_eq_true_iff]
      exact hb.1
    · rw [f7S_g, if_neg h, Nat.zero_testBit] at hb
      exact absurd hb (by decide)

theorem f7S_wSpread (r : ℕ) : wSpread r = ∑ m ∈ range 28, 2 ^ (29 * r + 377 * m) := by
  rw [wSpread, sumN_eq]
  refine sum_congr rfl fun m _ => ?_
  change 1 <<< (29 * r + 377 * m) = _
  rw [Nat.one_shiftLeft]

theorem f7S_wMaskT (r : ℕ) : wMaskT r = ∑ n ∈ range 28, (if r + 13 * n < 360 then 7 else 0) *
    2 ^ (32 * (r + 13 * n)) := by
  rw [wMaskT, sumN_eq]
  exact sum_congr rfl fun m _ => f7S_ifN7 (r + 13 * m) (32 * (r + 13 * m))

theorem f7S_wTerm (c r : ℕ) (hr : r < 13) : ((c &&& wMaskC r) * wSpread r) &&& wMaskT r =
    ∑ n ∈ range 28, f7S_g c r n * 2 ^ (32 * (r + 13 * n)) := by
  have hP : (c &&& wMaskC r) * wSpread r =
      ∑ x ∈ range 28 ×ˢ range 28, f7S_g c r x.1 * 2 ^ (32 * r + 39 * x.1 + 377 * x.2) := by
    rw [f7S_wMaskC, f7S_wSpread, sum_mul_sum, sum_product]
    refine sum_congr rfl fun m _ => sum_congr rfl fun m' _ => ?_
    rw [mul_assoc, ← pow_add]
    congr 2
    ring
  have hdP : ∀ i ∈ range 28 ×ˢ range 28, ∀ j ∈ range 28 ×ˢ range 28, i ≠ j →
      (32 * r + 39 * i.1 + 377 * i.2) + 3 ≤ 32 * r + 39 * j.1 + 377 * j.2 ∨
        (32 * r + 39 * j.1 + 377 * j.2) + 3 ≤ 32 * r + 39 * i.1 + 377 * i.2 := by
    rintro ⟨m, m'⟩ hi ⟨n, n'⟩ hj hne
    simp only [mem_product, mem_range] at hi hj
    have : m ≠ n ∨ m' ≠ n' := by
      by_contra h
      push Not at h
      exact hne (by rw [h.1, h.2])
    dsimp only
    omega
  have hdN : ∀ i ∈ range 28, ∀ j ∈ range 28, i ≠ j →
      32 * (r + 13 * i) + 3 ≤ 32 * (r + 13 * j) ∨ 32 * (r + 13 * j) + 3 ≤ 32 * (r + 13 * i) :=
    fun i _ j _ hij => by omega
  rw [hP, f7S_wMaskT]
  apply f7S_tb_iff
  intro b
  rw [Nat.testBit_and, Bool.and_eq_true,
    f7S_testBit_sum (range 28 ×ˢ range 28) (fun x => f7S_g c r x.1)
      (fun x => 32 * r + 39 * x.1 + 377 * x.2) 3 (fun x _ => f7S_g_lt c r x.1) hdP b,
    f7S_testBit_sum (range 28) (fun n => if r + 13 * n < 360 then 7 else 0)
      (fun n => 32 * (r + 13 * n)) 3 (fun n _ => by split_ifs <;> decide) hdN b,
    f7S_testBit_sum (range 28) (f7S_g c r) (fun n => 32 * (r + 13 * n)) 3
      (fun n _ => f7S_g_lt c r n) hdN b]
  constructor
  · rintro ⟨⟨⟨m, m'⟩, hi, hle, hb⟩, n, hn, hle', hb'⟩
    simp only [mem_product, mem_range] at hi
    have hn' := mem_range.1 hn
    dsimp only at hle hb hle' hb'
    by_cases h : r + 13 * n < 360
    · rw [if_pos h, f7S_seven_tb, decide_eq_true_iff] at hb'
      have hlt := f7S_tb_lt (f7S_g_lt c r m) hb
      have hmn : m = n ∧ m' = n := by omega
      refine ⟨n, hn, hle', ?_⟩
      have e : 32 * r + 39 * m + 377 * m' = 32 * (r + 13 * n) := by omega
      rw [e, hmn.1] at hb
      exact hb
    · rw [if_neg h, Nat.zero_testBit] at hb'
      exact absurd hb' (by decide)
  · rintro ⟨n, hn, hle, hb⟩
    have hn' := mem_range.1 hn
    have hlt := f7S_tb_lt (f7S_g_lt c r n) hb
    have h : r + 13 * n < 360 := by
      by_contra h
      rw [f7S_g, if_neg h, Nat.zero_testBit] at hb
      exact absurd hb (by decide)
    have e : 32 * r + 39 * n + 377 * n = 32 * (r + 13 * n) := by ring
    refine ⟨⟨(n, n), mem_product.2 ⟨hn, hn⟩, by dsimp only; omega, ?_⟩, n, hn, hle, ?_⟩
    · dsimp only
      rw [e]
      exact hb
    · rw [if_pos h, f7S_seven_tb, decide_eq_true_iff]
      exact hlt

theorem f7S_widenSum (c : ℕ) :
    (sumN 13 fun r => ((c &&& wMaskC r) * wSpread r) &&& wMaskT r) =
      D 360 fun k => c / 2 ^ (3 * k) % 8 := by
  rw [sumN_eq, sum_congr rfl fun r hr => f7S_wTerm c r (mem_range.1 hr),
    ← sum_product' (f := fun r n => f7S_g c r n * 2 ^ (32 * (r + 13 * n))), D]
  have hd : ∀ i ∈ range 13 ×ˢ range 28, ∀ j ∈ range 13 ×ˢ range 28, i ≠ j →
      32 * (i.1 + 13 * i.2) + 3 ≤ 32 * (j.1 + 13 * j.2) ∨
        32 * (j.1 + 13 * j.2) + 3 ≤ 32 * (i.1 + 13 * i.2) := by
    rintro ⟨m, m'⟩ hi ⟨n, n'⟩ hj hne
    simp only [mem_product, mem_range] at hi hj
    have : m ≠ n ∨ m' ≠ n' := by
      by_contra h
      push Not at h
      exact hne (by rw [h.1, h.2])
    dsimp only
    omega
  have hdK : ∀ i ∈ range 360, ∀ j ∈ range 360, i ≠ j → 32 * i + 3 ≤ 32 * j ∨ 32 * j + 3 ≤ 32 * i :=
    fun i _ j _ hij => by omega
  apply f7S_tb_iff
  intro b
  rw [f7S_testBit_sum (range 13 ×ˢ range 28) (fun x => f7S_g c x.1 x.2)
      (fun x => 32 * (x.1 + 13 * x.2)) 3 (fun x _ => f7S_g_lt c x.1 x.2) hd b,
    f7S_testBit_sum (range 360) (fun k => c / 2 ^ (3 * k) % 8) (fun k => 32 * k) 3
      (fun k _ => f7S_fld_lt c k) hdK b]
  constructor
  · rintro ⟨⟨r, n⟩, hi, hle, hb⟩
    dsimp only at hle hb
    by_cases h : r + 13 * n < 360
    · rw [f7S_g, if_pos h] at hb
      exact ⟨r + 13 * n, mem_range.2 h, hle, hb⟩
    · rw [f7S_g, if_neg h, Nat.zero_testBit] at hb
      exact absurd hb (by decide)
  · rintro ⟨k, hk, hle, hb⟩
    have hk' := mem_range.1 hk
    have e : k % 13 + 13 * (k / 13) = k := Nat.mod_add_div k 13
    refine ⟨(k % 13, k / 13), mem_product.2 ⟨mem_range.2 (Nat.mod_lt _ (by norm_num)),
      mem_range.2 (by omega)⟩, ?_, ?_⟩
    · dsimp only
      rw [e]
      exact hle
    · dsimp only
      rw [f7S_g, e, if_pos hk']
      exact hb

theorem widenF_eq (c : ℕ) : widenF c = enc (decC 8 c) := by
  have h : widenF c = red7W (D 360 fun k => c / 2 ^ (3 * k) % 8) :=
    congrArg red7W (f7S_widenSum c)
  rw [h, f7S_red7W_D le_rfl fun k _ => lt_trans (Nat.mod_lt _ (by norm_num)) (by norm_num), enc]
  refine D_congr (n := 360) fun k hk => ?_
  rw [ent_pos _ (by omega : k < 45 * 8)]
  change _ = (((c / 2 ^ (3 * (45 * (k / 45) + k % 45)) % 8 : ℕ) : ZMod 7)).val
  rw [Nat.div_add_mod, ZMod.val_natCast]

theorem f7S_pow_eq (a b c : ℕ) (h : a + b = c) : (2 : ℕ) ^ a * 2 ^ b = 2 ^ c := by
  rw [← pow_add, h]

theorem f7S_fld135 (S c : ℕ) :
    Nat.land (Nat.shiftRight S (Nat.mul 135 c)) 43556142965880123323311949751266331066367 =
      ∑ k ∈ range 45, S / 2 ^ (3 * (45 * c + k)) % 8 * 2 ^ (3 * k) := by
  have hM : (43556142965880123323311949751266331066367 : ℕ) = 2 ^ 135 - 1 := by norm_num
  have hd : ∀ i ∈ range 45, ∀ j ∈ range 45, i ≠ j → 3 * i + 3 ≤ 3 * j ∨ 3 * j + 3 ≤ 3 * i :=
    fun i _ j _ hij => by omega
  apply f7S_tb_iff
  intro b
  change ((S >>> (135 * c)) &&& 43556142965880123323311949751266331066367).testBit b = true ↔ _
  rw [hM, Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one, Bool.and_eq_true,
    decide_eq_true_iff,
    f7S_testBit_sum (range 45) (fun k => S / 2 ^ (3 * (45 * c + k)) % 8) (fun k => 3 * k) 3
      (fun k _ => f7S_fld_lt S _) hd b]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨b / 3, mem_range.2 (by omega), by omega, ?_⟩
    rw [f7S_fld_tb, decide_eq_true (by omega), Bool.true_and,
      show 3 * (45 * c + b / 3) + (b - 3 * (b / 3)) = 135 * c + b by omega]
    exact h1
  · rintro ⟨k, hk, hle, hb⟩
    have hk' := mem_range.1 hk
    rw [f7S_fld_tb, Bool.and_eq_true, decide_eq_true_iff,
      show 3 * (45 * c + k) + (b - 3 * k) = 135 * c + b by omega] at hb
    exact ⟨hb.2, by omega⟩

theorem f7S_spread (f : ℕ → ℕ) (hf : ∀ k, f k < 2 ^ 3) :
    ((∑ k ∈ range 45, f k * 2 ^ (3 * k)) * f7SP) &&& f7SpMask =
      ∑ k ∈ range 45, f k * 2 ^ (1440 * k) := by
  have hSP : f7SP = ∑ t ∈ range 45, 2 ^ (1437 * t) := by
    rw [f7SP, sumN_eq]
    refine sum_congr rfl fun t _ => ?_
    change 1 <<< (1437 * t) = _
    rw [Nat.one_shiftLeft]
  have hMk : f7SpMask = ∑ k ∈ range 45, 7 * 2 ^ (1440 * k) := by
    rw [f7SpMask, sumN_eq]
    refine sum_congr rfl fun k _ => ?_
    change 7 <<< (1440 * k) = _
    rw [Nat.shiftLeft_eq]
  have hP : (∑ k ∈ range 45, f k * 2 ^ (3 * k)) * f7SP =
      ∑ x ∈ range 45 ×ˢ range 45, f x.1 * 2 ^ (3 * x.1 + 1437 * x.2) := by
    rw [hSP, sum_mul_sum, sum_product]
    refine sum_congr rfl fun k _ => sum_congr rfl fun t _ => ?_
    rw [mul_assoc, ← pow_add]
  have hdP : ∀ i ∈ range 45 ×ˢ range 45, ∀ j ∈ range 45 ×ˢ range 45, i ≠ j →
      (3 * i.1 + 1437 * i.2) + 3 ≤ 3 * j.1 + 1437 * j.2 ∨
        (3 * j.1 + 1437 * j.2) + 3 ≤ 3 * i.1 + 1437 * i.2 := by
    rintro ⟨m, m'⟩ hi ⟨n, n'⟩ hj hne
    simp only [mem_product, mem_range] at hi hj
    have : m ≠ n ∨ m' ≠ n' := by
      by_contra h
      push Not at h
      exact hne (by rw [h.1, h.2])
    dsimp only
    omega
  have hdN : ∀ i ∈ range 45, ∀ j ∈ range 45, i ≠ j →
      1440 * i + 3 ≤ 1440 * j ∨ 1440 * j + 3 ≤ 1440 * i := fun i _ j _ hij => by omega
  rw [hP, hMk]
  apply f7S_tb_iff
  intro b
  rw [Nat.testBit_and, Bool.and_eq_true,
    f7S_testBit_sum (range 45 ×ˢ range 45) (fun x => f x.1) (fun x => 3 * x.1 + 1437 * x.2) 3
      (fun x _ => hf x.1) hdP b,
    f7S_testBit_sum (range 45) (fun _ => 7) (fun k => 1440 * k) 3 (fun _ _ => by decide) hdN b,
    f7S_testBit_sum (range 45) f (fun k => 1440 * k) 3 (fun k _ => hf k) hdN b]
  constructor
  · rintro ⟨⟨⟨k, t⟩, hi, hle, hb⟩, n, hn, hle', hb'⟩
    simp only [mem_product, mem_range] at hi
    have hn' := mem_range.1 hn
    dsimp only at hle hb hle' hb'
    rw [f7S_seven_tb, decide_eq_true_iff] at hb'
    have hlt := f7S_tb_lt (hf k) hb
    have hkn : k = n ∧ t = n := by omega
    refine ⟨n, hn, hle', ?_⟩
    have e : 3 * k + 1437 * t = 1440 * n := by omega
    rw [e, hkn.1] at hb
    exact hb
  · rintro ⟨n, hn, hle, hb⟩
    have hlt := f7S_tb_lt (hf n) hb
    have e : 3 * n + 1437 * n = 1440 * n := by ring
    refine ⟨⟨(n, n), mem_product.2 ⟨hn, hn⟩, by dsimp only; omega, ?_⟩, n, hn, hle, ?_⟩
    · dsimp only
      rw [e]
      exact hb
    · rw [f7S_seven_tb, decide_eq_true_iff]
      exact hlt

theorem f7S_revM (B : ℕ) : revM B = ∑ k ∈ range 45, row B k * 2 ^ (1440 * (44 - k)) := by
  rw [revM, sumN_eq]
  refine sum_congr rfl fun k _ => ?_
  change row B k <<< (1440 * (44 - k)) = _
  rw [Nat.shiftLeft_eq]

theorem f7S_row_lt (G : Matrix (Fin 45) (Fin 45) (ZMod 7)) {k : ℕ} (hk : k < 45) :
    row (enc G) k < 2 ^ (32 * 44 + 3) := by
  rw [row_enc G ⟨k, hk⟩, encV]
  exact f7S_D_lt8 (n := 44) fun j _ => lt_trans (ev_lt _ j) (by norm_num)

theorem f7S_pow_aux (a b x y : ℕ) : a * 2 ^ x * (b * 2 ^ y) = a * b * 2 ^ (x + y) := by
  rw [pow_add]
  ring

theorem f7S_pow_aux2 (a b p q z : ℕ) :
    2 ^ p * (2 ^ q * (a * b * 2 ^ z)) = a * b * 2 ^ (p + q + z) := by
  rw [pow_add, pow_add]
  ring

theorem f7S_slot (w v : ℕ) (f R : ℕ → ℕ) (hFR : ∀ k < 45, ∀ k' < 45, f k * R k' < 2 ^ v)
    (hv : 2025 * 2 ^ v < 2 ^ w) :
    ((∑ k ∈ range 45, f k * 2 ^ (w * k)) * ∑ k ∈ range 45, R k * 2 ^ (w * (44 - k))) /
      2 ^ (w * 44) % 2 ^ w = ∑ k ∈ range 45, f k * R k := by
  obtain ⟨L, hLd⟩ : ∃ L, L = ∑ k ∈ range 45, ∑ k' ∈ range 45,
      if k < k' then f k * R k' * 2 ^ (w * (44 + k - k')) else 0 := ⟨_, rfl⟩
  obtain ⟨H, hHd⟩ : ∃ H, H = ∑ k ∈ range 45, ∑ k' ∈ range 45,
      if k' < k then f k * R k' * 2 ^ (w * (k - k' - 1)) else 0 := ⟨_, rfl⟩
  have hM' : ∑ k ∈ range 45, f k * R k =
      ∑ k ∈ range 45, ∑ k' ∈ range 45, if k = k' then f k * R k' else 0 := by
    refine sum_congr rfl fun k hk => ?_
    rw [sum_ite_eq, if_pos hk]
  have hterm : ∀ k ∈ range 45, ∀ k' ∈ range 45,
      f k * 2 ^ (w * k) * (R k' * 2 ^ (w * (44 - k'))) =
        (if k < k' then f k * R k' * 2 ^ (w * (44 + k - k')) else 0) +
          2 ^ (w * 44) * ((if k = k' then f k * R k' else 0) +
            2 ^ w * (if k' < k then f k * R k' * 2 ^ (w * (k - k' - 1)) else 0)) := by
    intro k hk k' hk'
    have hk1 := mem_range.1 hk
    have hk2 := mem_range.1 hk'
    have e1 : w * k + w * (44 - k') = w * (k + (44 - k')) := by ring
    rw [f7S_pow_aux, e1]
    rcases lt_trichotomy k k' with h | rfl | h
    · rw [if_pos h, if_neg (ne_of_lt h), if_neg (by omega), mul_zero, add_zero, mul_zero,
        add_zero, show k + (44 - k') = 44 + k - k' by omega]
    · rw [if_neg (lt_irrefl _), if_pos rfl, if_neg (lt_irrefl _), mul_zero, add_zero, zero_add,
        mul_comm (2 ^ (w * 44)), show k + (44 - k) = 44 by omega]
    · have e2 : w * 44 + w + w * (k - k' - 1) = w * (44 + 1 + (k - k' - 1)) := by ring
      rw [if_neg (by omega), if_neg (by omega), if_pos h, zero_add, zero_add, f7S_pow_aux2, e2,
        show k + (44 - k') = 44 + 1 + (k - k' - 1) by omega]
  have hP : (∑ k ∈ range 45, f k * 2 ^ (w * k)) * (∑ k ∈ range 45, R k * 2 ^ (w * (44 - k))) =
      L + 2 ^ (w * 44) * ((∑ k ∈ range 45, f k * R k) + 2 ^ w * H) := by
    rw [hLd, hHd, hM', sum_mul_sum, sum_congr rfl fun k hk => sum_congr rfl fun k' hk' =>
      hterm k hk k' hk']
    simp only [mul_add, mul_sum, sum_add_distrib]
  have hpos := Nat.two_pow_pos v
  have hLb : L < 2 ^ (w * 44) := by
    rw [hLd]
    calc _ ≤ ∑ k ∈ range 45, ∑ k' ∈ range 45, 2 ^ v * 2 ^ (w * 43) :=
          sum_le_sum fun k hk => sum_le_sum fun k' hk' => by
            split_ifs with h
            · have hk1 := mem_range.1 hk
              have hk2 := mem_range.1 hk'
              exact Nat.mul_le_mul (hFR k hk1 k' hk2).le
                (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left w (by omega)))
            · exact Nat.zero_le _
      _ = 2025 * 2 ^ v * 2 ^ (w * 43) := by
          simp only [sum_const, card_range, smul_eq_mul]
          ring
      _ < 2 ^ w * 2 ^ (w * 43) := Nat.mul_lt_mul_of_pos_right hv (Nat.two_pow_pos _)
      _ = 2 ^ (w * 44) := by rw [← pow_add, show w + w * 43 = w * 44 by ring]
  have hMb : ∑ k ∈ range 45, f k * R k < 2 ^ w := by
    calc _ ≤ ∑ k ∈ range 45, 2 ^ v :=
          sum_le_sum fun k hk => (hFR k (mem_range.1 hk) k (mem_range.1 hk)).le
      _ = 45 * 2 ^ v := by simp only [sum_const, card_range, smul_eq_mul]
      _ < 2 ^ w := by omega
  rw [hP, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hLb, zero_add,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hMb]

theorem f7S_rowImgK_eq (r Bv : ℕ) :
    rowImgK r Bv = red7 (row ((r * f7SP &&& f7SpMask) * Bv) 44) := rfl

theorem f7S_rowImgK {S c : ℕ} (hc : c < 8) (hf : ∀ k < 45, S / 2 ^ (3 * (45 * c + k)) % 8 < 7)
    (G : Matrix (Fin 45) (Fin 45) (ZMod 7)) :
    rowImgK (Nat.land (Nat.shiftRight S (Nat.mul 135 c)) 43556142965880123323311949751266331066367)
      (revM (enc G)) = encV (Matrix.vecMul (rows (decC 8 S) ⟨c, hc⟩) G) := by
  have hev : ∀ k < 45, ev (rows (decC 8 S) ⟨c, hc⟩) k = S / 2 ^ (3 * (45 * c + k)) % 8 := by
    intro k hk
    rw [ev, dif_pos hk]
    change (((S / 2 ^ (3 * (45 * c + k)) % 8 : ℕ) : ZMod 7)).val = _
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (hf k hk)]
  have hFR : ∀ k < 45, ∀ k' < 45,
      S / 2 ^ (3 * (45 * c + k)) % 8 * row (enc G) k' < 2 ^ (3 + (32 * 44 + 3)) := by
    intro k _ k' hk'
    rw [pow_add]
    exact Nat.mul_lt_mul'' (f7S_fld_lt S _) (f7S_row_lt G hk')
  have hv : 2025 * 2 ^ (3 + (32 * 44 + 3)) < 2 ^ 1440 := by
    have h1 : (2 : ℕ) ^ (3 + (32 * 44 + 3)) * 2 ^ 26 = 2 ^ 1440 :=
      f7S_pow_eq (3 + (32 * 44 + 3)) 26 1440 (by norm_num)
    have h2 : (2 : ℕ) ^ 26 = 67108864 := by norm_num
    have h3 := Nat.two_pow_pos (3 + (32 * 44 + 3))
    rw [← h1, h2]
    omega
  rw [f7S_rowImgK_eq, f7S_fld135, f7S_spread _ fun k => f7S_fld_lt S _, f7S_revM, row_eq,
    f7S_slot 1440 _ _ _ hFR hv, ← rowMul_enc, rowMul_eq]
  refine congrArg red7 (sum_congr rfl fun k hk => ?_)
  rw [lane_encV, hev k (mem_range.1 hk)]

theorem f7Img_eq {c pw : ℕ} (h : f7Canon c pw = true) (G : Matrix (Fin 45) (Fin 45) (ZMod 7)) :
    f7Img c (revM (enc G)) = enc (decC 8 c * G) := by
  obtain ⟨hm, _⟩ := f7S_canon_tail h
  have e : f7Img c (revM (enc G)) = ∑ i ∈ range 8, rowImgK (Nat.land (Nat.shiftRight c
      (Nat.mul 135 i)) 43556142965880123323311949751266331066367) (revM (enc G)) *
        2 ^ (1440 * i) := by
    rw [f7Img, sumN_eq]
    exact sum_congr rfl fun i _ => Nat.shiftLeft_eq _ _
  rw [e]
  conv_rhs => rw [enc, D_blocks]
  refine sum_congr rfl fun i hi => ?_
  have hi' := mem_range.1 hi
  rw [f7S_rowImgK hi' (fun k hk => f7S_field_lt hm (by omega)) G, encV]
  refine congrArg (fun x => x * 2 ^ (1440 * i)) (D_congr fun j hj => ?_)
  have e1 : (45 * i + j) / 45 = i := by omega
  have e2 : (45 * i + j) % 45 = j := by omega
  rw [e1, e2]
  simp [ev, ent, rows, hj, hi', Matrix.mul_apply, Matrix.vecMul, dotProduct]

theorem f7S_laneV_shr (x q l : ℕ) : laneV (x >>> (32 * q)) l = laneV x (l + q) := by
  rw [laneV, laneV, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, ← pow_add,
    show 32 * q + 32 * l = 32 * (l + q) by ring]

theorem f7S_col (U : Matrix (Fin 8) (Fin 45) (ZMod 7)) {q : ℕ} (hq : q < 45) :
    f7Col (enc U) q = ∑ i ∈ range 8, (7 - ent U i q) * 2 ^ (1440 * i) := by
  have h7 : f7Seven = D 360 fun l => if l % 45 = 0 then 7 else 0 := by
    rw [f7Seven, sumN_eq]
    exact (sum_congr rfl fun i _ => Nat.shiftLeft_eq _ _).trans (f7S_rows8 fun _ => 7)
  have hmask : f7ColMask = D 360 fun l => if l % 45 = 0 then 4294967295 else 0 := by
    rw [f7ColMask, sumN_eq]
    exact (sum_congr rfl fun i _ => Nat.shiftLeft_eq _ _).trans (f7S_rows8 fun _ => 4294967295)
  have hlt32 : ∀ l < 360, (if l % 45 = 0 then (4294967295 : ℕ) else 0) < 2 ^ 32 := fun l _ => by
    split_ifs <;> norm_num
  have hlt' : ∀ l < 360, (if l % 45 = 0 then ent U (l / 45) q else 0) < 2 ^ 32 := fun l _ => by
    split_ifs
    exacts [lt_trans (ent_lt U _ _) (by norm_num), by norm_num]
  have hcol : (enc U >>> (32 * q)) &&& f7ColMask =
      D 360 fun l => if l % 45 = 0 then ent U (l / 45) q else 0 := by
    apply laneV_ext
    intro l
    rw [laneV_and, f7S_laneV_shr, hmask, lane_D hlt32, enc, lane_D (ent_lt32 U), lane_D hlt']
    by_cases hl : l < 360
    · rw [if_pos hl, if_pos hl]
      by_cases h0 : l % 45 = 0
      · rw [if_pos h0, if_pos h0, if_pos (by omega : l + q < 45 * 8),
          show (l + q) / 45 = l / 45 by omega, show (l + q) % 45 = q by omega,
          show (4294967295 : ℕ) = 2 ^ 32 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod,
          Nat.mod_eq_of_lt (lt_trans (ent_lt U _ _) (by norm_num))]
      · rw [if_neg h0, if_neg h0, Nat.and_zero]
    · rw [if_neg hl, if_neg hl, Nat.and_zero]
  change f7Seven - ((enc U >>> (32 * q)) &&& f7ColMask) = _
  rw [hcol, h7, f7S_D_sub fun l _ => by split_ifs; exacts [(ent_lt U _ _).le, le_rfl], f7S_rows8]
  refine D_congr fun l _ => ?_
  split_ifs <;> rfl

theorem inSpan8_iff {U V : Matrix (Fin 8) (Fin 45) (ZMod 7)} {p : Fin 8 → Fin 45} {pw : ℕ}
    (hV : Pivots V p) (hpv : ∀ c, (p c : ℕ) = pvF pw c) :
    inSpan8 (enc U) (enc V) pw = true ↔ rowSpan U ≤ rowSpan V := by
  set piv := (List.range 8).map (pvF pw) with hpiv
  have hnth : ∀ c < 8, nthF piv c = pvF pw c := fun c hc => by
    rw [f7S_nthF, hpiv]
    simp [List.getD_eq_getElem?_getD, List.getElem?_range, hc]
  have hpv' : ∀ c, (p c : ℕ) = nthF piv c := fun c => by rw [hnth c c.isLt, hpv]
  have hq : ∀ c < 8, pvF pw c < 45 := fun c hc => by
    rw [← hpv ⟨c, hc⟩]
    exact (p _).isLt
  have hA : enc U + ∑ c ∈ range 8, f7Col (enc U) (pvF pw c) * row (enc V) c =
      ∑ i ∈ range 8, (row (enc U) i + ∑ c ∈ range 8,
        (7 - lane (row (enc U) i) (nthF piv c)) * row (enc V) c) * 2 ^ (1440 * i) := by
    have e1 : ∀ c ∈ range 8, f7Col (enc U) (pvF pw c) * row (enc V) c = ∑ i ∈ range 8,
        (7 - lane (row (enc U) i) (nthF piv c)) * row (enc V) c * 2 ^ (1440 * i) := by
      intro c hc
      have hc' := mem_range.1 hc
      rw [f7S_col U (hq c hc'), sum_mul]
      refine sum_congr rfl fun i hi => ?_
      have hi' := mem_range.1 hi
      rw [hnth c hc', row_enc U ⟨i, hi'⟩, lane_encV, ev_row U hi']
      ring
    rw [sum_congr rfl e1, sum_comm]
    conv_lhs => arg 1; rw [f7S_enc_rows U]
    rw [← sum_add_distrib]
    refine sum_congr rfl fun i _ => ?_
    rw [add_mul, sum_mul]
  have ha : ∀ i < 8, row (enc U) i + ∑ c ∈ range 8,
      (7 - lane (row (enc U) i) (nthF piv c)) * row (enc V) c =
      D 45 (fun j => ent U i j + ∑ c ∈ range 8, (7 - ent U i (pvF pw c)) * ent V c j) := by
    intro i hi
    have e2 : D 45 (fun j => ent U i j + ∑ c ∈ range 8, (7 - ent U i (pvF pw c)) * ent V c j) =
        D 45 (fun j => ent U i j) +
          ∑ c ∈ range 8, D 45 (fun j => (7 - ent U i (pvF pw c)) * ent V c j) := by
      rw [f7S_D_sum (range 8) (fun c j => (7 - ent U i (pvF pw c)) * ent V c j), D_add]
    rw [e2]
    refine congrArg₂ (· + ·) ?_ ?_
    · rw [row_enc U ⟨i, hi⟩, encV]
      exact D_congr fun j _ => ev_row U hi j
    · refine sum_congr rfl fun c hc => ?_
      have hc' := mem_range.1 hc
      rw [row_enc U ⟨i, hi⟩, lane_encV, ev_row U hi, hnth c hc', row_enc V ⟨c, hc'⟩, encV, D_mul]
      exact D_congr fun j _ => by rw [ev_row V hc']
  have hbound : ∀ i < 8, ∀ j < 45,
      ent U i j + ∑ c ∈ range 8, (7 - ent U i (pvF pw c)) * ent V c j < 1621 := by
    intro i _ j _
    have h1 : ∑ c ∈ range 8, (7 - ent U i (pvF pw c)) * ent V c j ≤ ∑ _c ∈ range 8, 42 :=
      sum_le_sum fun c _ => by
        have := ent_lt V c j
        have : (7 - ent U i (pvF pw c)) * ent V c j ≤ 7 * 6 := Nat.mul_le_mul (by omega) (by omega)
        omega
    simp only [sum_const, card_range, smul_eq_mul] at h1
    have := ent_lt U i j
    omega
  have hred : red7W (enc U + ∑ c ∈ range 8, f7Col (enc U) (pvF pw c) * row (enc V) c) =
      ∑ i ∈ range 8, redRow (row (enc U) i) (enc V) piv * 2 ^ (1440 * i) := by
    rw [hA, f7S_red7W_rows _ _ ha hbound]
    refine sum_congr rfl fun i _ => ?_
    rw [redRow, sumN_eq]
    rfl
  have key : inSpan8 (enc U) (enc V) pw = true ↔
      ∀ i < 8, redRow (row (enc U) i) (enc V) piv = 0 := by
    change Nat.beq (red7W (enc U + sumN 8 fun c => f7Col (enc U) (pvF pw c) * row (enc V) c)) 0
      = true ↔ _
    rw [sumN_eq, hred, Nat.beq_eq, sum_eq_zero_iff]
    constructor
    · intro h i hi
      rcases mul_eq_zero.1 (h i (mem_range.2 hi)) with h | h
      · exact h
      · exact absurd h (Nat.two_pow_pos _).ne'
    · intro h i hi
      rw [h i (mem_range.1 hi), zero_mul]
  rw [key, rowSpan, Submodule.span_le, Set.range_subset_iff]
  constructor
  · intro h1 i
    have h2 := h1 i i.isLt
    rw [row_enc U i, redRow_enc hpv'] at h2
    exact (mem_rowSpan_iff hV _).2 (sub_eq_zero.1 (encV_inj (h2.trans encV_zero.symm)))
  · intro h1 i hi
    have h2 := (mem_rowSpan_iff hV _).1 (h1 ⟨i, hi⟩)
    rw [row_enc U ⟨i, hi⟩, redRow_enc hpv']
    change encV (rows U ⟨i, hi⟩ - _) = 0
    rw [← h2, sub_self, encV_zero]

end Fast

end CFSG.KC.Misc.F7

end
