module

public import Certificates.Data.Kernel.Spor.ONCK
public import CFSG.Certificates.Kernel.Spor.OrdSound
public import CFSG.Certificates.Kernel.Spor.ONVecLib
public import CFSG.Sporadic.Th.TableSpec
public import CFSG.F3.Spec
import CFSG.Certificates.Kernel.Spor.Mat3Sound
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.Ring

public section

namespace CFSG.KS.ONC

open CFSG.KC.Enum CFSG.KS CFSG.KS.ON CFSG.KC.Ord CFSG.KS.Ord CFSG.Sporadic.Th.Native
open scoped Matrix

theorem strictN_eq' (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

theorem strictB_eq' (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem strictS_eq {α : Type} (y : Nat) (k : Nat → α) : strictS y k = k y := by
  cases y <;> rfl

theorem bAnd_iff' (a b : Bool) : bAnd(a, b) = true ↔ a = true ∧ b = true := by
  cases a <;> simp

noncomputable abbrev omat (X : Nat) : Matrix (Fin 154) (Fin 154) (ZMod 3) := ordMat 3 154 11 1694 X

@[expose] noncomputable def vecK (X : Nat) : Fin 154 → ZMod 3 :=
  fun r => CFSG.F3.Native.bitVal ((vP X).testBit r.val) ((vM X).testBit r.val)

@[expose] def PV (X : Nat) : Prop := vP X &&& vM X = 0 ∧ vP X < 2 ^ 154 ∧ vM X < 2 ^ 154

theorem pv_of_canon {X : Nat} (h : canon X = true) : PV X := canon_bits h

theorem mul_rep1_testBit {s v : Nat} (hs : 0 < s) (hv : v < 2 ^ s) (m u : Nat) :
    (v * rep1 s m).testBit u = (decide (u / s < m) && v.testBit (u % s)) := by
  rw [CFSG.KS.Mat3.rep1_eq3 hs]
  induction m with
  | zero => simp
  | succ m ih =>
    have hsum := CFSG.KS.Mat3.rep1_sum s m
    have hlt : v * ∑ i ∈ Finset.range m, 2 ^ (s * i) < 2 ^ (s * m) := by
      have h1 : v ≤ 2 ^ s - 1 := by omega
      have h2 := Nat.mul_le_mul_right (∑ i ∈ Finset.range m, 2 ^ (s * i)) h1
      omega
    rw [Finset.sum_range_succ, Nat.mul_add, Nat.add_comm, Nat.mul_comm v (2 ^ (s * m)),
      Nat.testBit_two_pow_mul_add _ hlt, ih]
    by_cases h : u < s * m
    · have hq : u / s < m := (Nat.div_lt_iff_lt_mul hs).2 (by rwa [Nat.mul_comm])
      simp [h, hq, Nat.lt_succ_of_lt hq]
    · rw [if_neg h]
      have hq : m ≤ u / s := (Nat.le_div_iff_mul_le hs).2 (by rw [Nat.mul_comm]; omega)
      by_cases he : u / s = m
      · have e : u - s * m = u % s := by
          have := Nat.div_add_mod u s
          rw [he] at this
          omega
        simp [he, e]
      · have hq' : m + 1 ≤ u / s := by omega
        have hge : s ≤ u - s * m := by
          have := (Nat.le_div_iff_mul_le hs).1 hq'
          rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm] at this
          omega
        have hf : v.testBit (u - s * m) = false :=
          Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hv (Nat.pow_le_pow_right (by omega) hge))
        have hd : ¬ u / s < m + 1 := by omega
        simp [hf, hd]

theorem rep1D_testBit (u : Nat) :
    (rep1 1694 154).testBit u = (decide (u % 1694 = 0) && decide (u / 1694 < 154)) := by
  apply Bool.eq_iff_iff.2
  rw [CFSG.KS.Mat3.rep1_testBit (by norm_num)]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨by omega, by omega⟩
  · rintro ⟨h1, h2⟩
    exact ⟨u / 1694, h2, by omega⟩

private theorem spr_eq (cs ds v : Nat) : spr cs ds v = v * cs &&& ds := rfl

private theorem CS_eq : CS = rep1 1693 154 := rfl

private theorem DS_eq : DS = rep1 1694 154 := rfl

theorem spr_testBit {v : Nat} (hv : v < 2 ^ 154) (r q : Nat) (hq : q < 1694) :
    (spr CS DS v).testBit (1694 * r + q) = (decide (q = 0) && decide (r < 154) && v.testBit r) := by
  rw [spr_eq, CS_eq, DS_eq, Nat.testBit_and, mul_rep1_testBit (by norm_num)
    (Nat.lt_of_lt_of_le hv (Nat.pow_le_pow_right (by norm_num) (by norm_num))), rep1D_testBit]
  have e1 : (1694 * r + q) % 1694 = q := by omega
  have e2 : (1694 * r + q) / 1694 = r := by omega
  rw [e1, e2]
  by_cases h0 : q = 0
  · subst h0
    by_cases hr : r < 154
    · have e3 : 1694 * r / 1693 = r := by omega
      have e4 : 1694 * r % 1693 = r := by omega
      simp [hr, e3, e4]
    · simp [hr]
  · simp [h0]

theorem colK_testBit {x i : Nat} (hp : vP x < 2 ^ 154) (hm : vM x < 2 ^ 154) (hi : i < 154)
    (r q : Nat) (hq : q < 1694) :
    (colK CS DS x i).testBit (1694 * r + q) = (decide (r < 154) &&
      ((decide (q = 11 * i) && (vP x).testBit r) || (decide (q = 11 * i + 1) && (vM x).testBit r))) := by
  unfold colK
  change ((spr CS DS (vP x) ||| spr CS DS (vM x) <<< 1) <<< (11 * i)).testBit (1694 * r + q) = _
  rw [Nat.testBit_shiftLeft]
  by_cases hu : 11 * i ≤ q
  · have hle : 1694 * r + q ≥ 11 * i := by omega
    have e : 1694 * r + q - 11 * i = 1694 * r + (q - 11 * i) := by omega
    rw [decide_eq_true hle, Bool.true_and, e, Nat.testBit_or, Nat.testBit_shiftLeft,
      spr_testBit hp r (q - 11 * i) (by omega)]
    by_cases hq1 : q - 11 * i = 0
    · have hq' : q = 11 * i := by omega
      have hne : q ≠ 11 * i + 1 := by omega
      subst hq'
      by_cases hr : r = 0
      · subst hr
        simp
      · have e2 : 1694 * r + (11 * i - 11 * i) - 1 = 1694 * (r - 1) + 1693 := by omega
        rw [e2, spr_testBit hm (r - 1) 1693 (by norm_num)]
        simp
    · have e2 : 1694 * r + (q - 11 * i) - 1 = 1694 * r + (q - 11 * i - 1) := by omega
      have hge : 1694 * r + (q - 11 * i) ≥ 1 := by omega
      rw [e2, spr_testBit hm r (q - 11 * i - 1) (by omega)]
      have hne : q ≠ 11 * i := by omega
      by_cases hq2 : q = 11 * i + 1
      · have : q - 11 * i - 1 = 0 := by omega
        simp [hq1, this, hq2, hne, hge]
      · have : q - 11 * i - 1 ≠ 0 := by omega
        simp [hq1, this, hq2, hne, hge]
  · have hne1 : q ≠ 11 * i := by omega
    have hne2 : q ≠ 11 * i + 1 := by omega
    by_cases hr : r = 0
    · subst hr
      have : ¬ 1694 * 0 + q ≥ 11 * i := by omega
      rw [decide_eq_false this, Bool.false_and]
      simp [hne1, hne2]
    · have hge : 1694 * r + q ≥ 11 * i := by omega
      have e : 1694 * r + q - 11 * i = 1694 * (r - 1) + (1694 + q - 11 * i) := by omega
      rw [e, Nat.testBit_or, Nat.testBit_shiftLeft, spr_testBit hp (r - 1) (1694 + q - 11 * i)
        (by omega)]
      have e2 : 1694 * (r - 1) + (1694 + q - 11 * i) - 1 = 1694 * (r - 1) + (1694 + q - 11 * i - 1) := by
        omega
      rw [e2, spr_testBit hm (r - 1) (1694 + q - 11 * i - 1) (by omega)]
      have h3 : 1694 + q - 11 * i ≠ 0 := by omega
      have h4 : 1694 + q - 11 * i - 1 ≠ 0 := by omega
      simp [hge, h3, h4, hne1, hne2]

theorem batK_testBit {F : Nat → Nat} {lo cnt : Nat} (hcnt : cnt ≤ 154)
    (hF : ∀ c < cnt, vP (F (lo + c)) < 2 ^ 154 ∧ vM (F (lo + c)) < 2 ^ 154) (r q : Nat)
    (hq : q < 1694) :
    (batK CS DS F lo cnt).testBit (1694 * r + q) = (decide (r < 154) && decide (q / 11 < cnt) &&
      ((decide (q % 11 = 0) && (vP (F (lo + q / 11))).testBit r) ||
       (decide (q % 11 = 1) && (vM (F (lo + q / 11))).testBit r))) := by
  induction cnt with
  | zero =>
    change (0 : Nat).testBit _ = _
    simp
  | succ c ih =>
    change (strictN (colK CS DS (F (Nat.add lo c)) c) fun x => Nat.lor (batK CS DS F lo c) x).testBit _ = _
    rw [strictN_eq']
    change ((batK CS DS F lo c) ||| colK CS DS (F (lo + c)) c).testBit _ = _
    rw [Nat.testBit_or, ih (by omega) (fun c' hc' => hF c' (by omega)),
      colK_testBit (hF c (by omega)).1 (hF c (by omega)).2 (by omega) r q hq]
    by_cases hqc : q / 11 = c
    · have hA : decide (q / 11 < c) = false := by simp; omega
      have hC : decide (q / 11 < c + 1) = true := by simp; omega
      have e0 : decide (q = 11 * c) = decide (q % 11 = 0) := by
        simp only [decide_eq_decide]; omega
      have e1 : decide (q = 11 * c + 1) = decide (q % 11 = 1) := by
        simp only [decide_eq_decide]; omega
      rw [hA, hC, e0, e1, hqc]
      simp
    · have hB0 : decide (q = 11 * c) = false := by simp; omega
      have hB1 : decide (q = 11 * c + 1) = false := by simp; omega
      have hC : decide (q / 11 < c + 1) = decide (q / 11 < c) := by
        simp only [decide_eq_decide]; omega
      rw [hB0, hB1, hC]
      simp

theorem pair_testBit (b0 b1 : Bool) (j : Nat) :
    ((if b0 then 1 else 0) + (if b1 then 2 else 0) : Nat).testBit j =
      (decide (j = 0) && b0 || decide (j = 1) && b1) := by
  rcases j with _ | _ | j <;> cases b0 <;> cases b1 <;> simp [Nat.testBit_succ]

theorem batK_lane {F : Nat → Nat} {lo cnt : Nat} (hcnt : cnt ≤ 154)
    (hF : ∀ c < cnt, vP (F (lo + c)) < 2 ^ 154 ∧ vM (F (lo + c)) < 2 ^ 154) {r c : Nat}
    (hr : r < 154) (hc : c < 154) :
    batK CS DS F lo cnt / 2 ^ (1694 * r + 11 * c) % 2 ^ 11 =
      if c < cnt then (if (vP (F (lo + c))).testBit r then 1 else 0) +
        (if (vM (F (lo + c))).testBit r then 2 else 0) else 0 := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases hj : j < 11
  · have e : j + (1694 * r + 11 * c) = 1694 * r + (11 * c + j) := by omega
    rw [e, batK_testBit hcnt hF r (11 * c + j) (by omega)]
    have e1 : (11 * c + j) / 11 = c := by omega
    have e2 : (11 * c + j) % 11 = j := by omega
    rw [e1, e2]
    by_cases h : c < cnt
    · rw [if_pos h, pair_testBit]
      simp [hj, hr, h]
    · rw [if_neg h]
      simp [hj, hr, h]
  · have hz : ∀ v : Nat, v < 4 → v.testBit j = false := fun v hv =>
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hv (by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)))
    simp only [hj, decide_false, Bool.false_and]
    symm
    apply hz
    by_cases h : c < cnt
    · rw [if_pos h]
      split_ifs <;> norm_num
    · rw [if_neg h]
      norm_num

theorem batK_lt {F : Nat → Nat} {lo cnt : Nat} (hcnt : cnt ≤ 154)
    (hF : ∀ c < cnt, vP (F (lo + c)) < 2 ^ 154 ∧ vM (F (lo + c)) < 2 ^ 154) :
    batK CS DS F lo cnt < 2 ^ (11 * (154 * 154)) := by
  apply Nat.lt_pow_two_of_testBit
  intro u hu
  have e : u = 1694 * (u / 1694) + u % 1694 := (Nat.div_add_mod u 1694).symm
  rw [e, batK_testBit hcnt hF _ _ (Nat.mod_lt _ (by norm_num))]
  have : ¬ u / 1694 < 154 := by omega
  simp [this]

theorem batK_canon {F : Nat → Nat} {lo cnt : Nat} (hcnt : cnt ≤ 154) (hF : ∀ c < cnt, PV (F (lo + c))) :
    Canon 3 154 11 (batK CS DS F lo cnt) := by
  have hF' : ∀ c < cnt, vP (F (lo + c)) < 2 ^ 154 ∧ vM (F (lo + c)) < 2 ^ 154 :=
    fun c hc => ⟨(hF c hc).2.1, (hF c hc).2.2⟩
  refine ⟨batK_lt hcnt hF', fun t ht => ?_⟩
  unfold lane
  have e : 11 * t = 1694 * (t / 154) + 11 * (t % 154) := by omega
  rw [e, batK_lane hcnt hF' (by omega) (Nat.mod_lt _ (by norm_num))]
  split_ifs with h1 h2 h3 <;> try omega
  · exfalso
    have hd := (hF _ h1).1
    have := congrArg (fun z => z.testBit (t / 154)) hd
    simp only [Nat.testBit_and, Nat.zero_testBit, h2, h3, Bool.and_self] at this
    exact absurd this (by decide)

theorem bitVal_pair {b0 b1 : Bool} (h : ¬ (b0 = true ∧ b1 = true)) :
    (((if b0 then 1 else 0) + (if b1 then 2 else 0) : Nat) : ZMod 3) = CFSG.F3.Native.bitVal b0 b1 := by
  cases b0 <;> cases b1 <;> simp_all [CFSG.F3.Native.bitVal] <;> rfl

theorem batK_omat {F : Nat → Nat} {lo cnt : Nat} (hcnt : cnt ≤ 154) (hF : ∀ c < cnt, PV (F (lo + c)))
    (r c : Fin 154) :
    omat (batK CS DS F lo cnt) r c = if c.val < cnt then vecK (F (lo + c.val)) r else 0 := by
  have hF' : ∀ c < cnt, vP (F (lo + c)) < 2 ^ 154 ∧ vM (F (lo + c)) < 2 ^ 154 :=
    fun c hc => ⟨(hF c hc).2.1, (hF c hc).2.2⟩
  unfold omat ordMat
  rw [batK_lane hcnt hF' r.isLt c.isLt]
  by_cases h : c.val < cnt
  · rw [if_pos h, if_pos h]
    unfold vecK
    apply bitVal_pair
    rintro ⟨h2, h3⟩
    have hd := (hF _ h).1
    have := congrArg (fun z => z.testBit r.val) hd
    simp only [Nat.testBit_and, Nat.zero_testBit, h2, h3, Bool.and_self] at this
    exact absurd this (by decide)
  · rw [if_neg h, if_neg h]
    simp

theorem redK_eq (w L H p T x : Nat) : redK w L H p T x = redP w L H p T x := by
  unfold redK redP
  simp only [strictN_eq']

theorem mulK_eq (p w S d T L H CM RM A B : Nat) :
    mulK p w S d T L H CM RM A B = mulR p w S d T L H CM RM A B := by
  unfold mulK mulR
  rw [strictN_eq', redK_eq]

set_option maxRecDepth 100000 in
theorem consts_ok : constsOK (nat_lit 3) (nat_lit 11) (nat_lit 1694) (nat_lit 154) (nat_lit 8) LL HH CM RM ONE
    LV HV = true := by
  quickRfl

theorem mul3_sound {A B : Nat} (hA : Canon 3 154 11 A) (hB : Canon 3 154 11 B) :
    Canon 3 154 11 (mul3 LL HH CM RM A B) ∧ omat (mul3 LL HH CM RM A B) = omat A * omat B := by
  unfold mul3
  rw [mulK_eq]
  exact mulR_sound consts_ok hA hB

theorem one_canon : Canon 3 154 11 ONE ∧ omat ONE = 1 := one_sound consts_ok

theorem vld3_canon {X : Nat} (h : vld3 LL HH X = true) : Canon 3 154 11 X :=
  validM_canon consts_ok h

theorem batCnt_eq (n s : Nat) :
    batCnt n s = if (s + 1) * 154 ≤ n then 154 else n - s * 154 := by
  unfold batCnt
  by_cases h : (s + 1) * 154 ≤ n
  · have hb : Nat.ble (Nat.mul (Nat.succ s) 154) n = true := Nat.ble_eq_true_of_le h
    rw [hb, if_pos h]
    try rfl
  · have hb : Nat.ble (Nat.mul (Nat.succ s) 154) n = false := by
      cases e : Nat.ble (Nat.mul (Nat.succ s) 154) n
      · rfl
      · exact absurd (Nat.le_of_ble_eq_true e) h
    rw [hb, if_neg h]
    try rfl

theorem batCnt_le (n s : Nat) : batCnt n s ≤ 154 := by
  rw [batCnt_eq]
  split_ifs with h
  · exact le_refl _
  · rw [Nat.add_mul] at h
    omega

theorem batCnt_spec {n s : Nat} (hs : s * 154 < n) {i : Nat} (hi : i < batCnt n s) :
    s * 154 + i < n := by
  rw [batCnt_eq] at hi
  split_ifs at hi with h
  · rw [Nat.add_mul] at h
    omega
  · omega

theorem allN_spec' {n : Nat} {f : Nat → Bool} (h : allN n f = true) : ∀ i < n, f i = true :=
  CFSG.KS.Raw.Orb.allN_iff.1 h

theorem letS_sound {ML : Nat → Nat} {LT : Nat → Nat → Nat} {K : Nat → Nat} {n s : Nat}
    (h : letS ML LT K n s = true) (hML : ∀ j < 4, Canon 3 154 11 (ML j))
    (hK : ∀ x < n, PV (K x)) (hLT : ∀ j < 4, ∀ x < n, LT (2 * j) x < n) (hs : s * 154 < n)
    {j : Nat} (hj : j < 4) {i : Nat} (hi : i < batCnt n s) :
    omat (ML j) *ᵥ vecK (K (s * 154 + i)) = vecK (K (LT (2 * j) (s * 154 + i))) := by
  unfold letS at h
  simp only [strictB_eq'] at h
  have e1 : Nat.mul s 154 = s * 154 := rfl
  have e2 : ∀ j, Nat.mul 2 j = 2 * j := fun _ => rfl
  simp only [e1, e2] at h
  have hc := batCnt_le n s
  have hX := batK_canon (F := K) (lo := s * 154) hc fun c hc' => hK _ (batCnt_spec hs hc')
  have e := Nat.eq_of_beq_eq_true (allN_spec' h j hj)
  have hm := (mul3_sound (hML j hj) hX).2
  rw [e] at hm
  have hi' : i < 154 := Nat.lt_of_lt_of_le hi hc
  funext r
  have hrc := congrFun (congrFun hm r) ⟨i, hi'⟩
  rw [batK_omat (F := fun x => K (LT (2 * j) x)) hc
    (fun c hc' => hK _ (hLT j hj _ (batCnt_spec hs hc'))), Matrix.mul_apply, if_pos hi] at hrc
  have hcol : ∀ k : Fin 154, omat (batK CS DS K (s * 154) (batCnt n s)) k ⟨i, hi'⟩ =
      vecK (K (s * 154 + i)) k := fun k => by
    rw [batK_omat (F := K) hc (fun c hc' => hK _ (batCnt_spec hs hc')), if_pos hi]
  have hv : (omat (ML j) *ᵥ vecK (K (s * 154 + i))) r =
      ∑ k, omat (ML j) r k * omat (batK CS DS K (s * 154) (batCnt n s)) k ⟨i, hi'⟩ := by
    simp only [Matrix.mulVec, dotProduct, hcol]
  rw [hv, hrc]

section Slp

variable {G : Type*} [Group G] (φ : G →* Matrix (Fin 154) (Fin 154) (ZMod 3))

@[expose] def SInv (nr : Nat) (st : List Nat × Nat × Bool) (ρ : ℕ → G) : Prop :=
  st.1.length = nr ∧ (st.2.2 = true → ∀ r < nr,
    Canon 3 154 11 (st.1.getD r 0) ∧ omat (st.1.getD r 0) = φ (ρ r))

theorem getD_set' (R : List Nat) {k : Nat} (hk : k < R.length) (x r : Nat) :
    (R.set k x).getD r 0 = if r = k then x else R.getD r 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases h : r = k
  · subst h
    simp [hk]
  · simp [h, Ne.symm h]

variable {φ} in
theorem step_inv {nr : Nat} {V : Nat → Nat} {ins : CFSG.Sporadic.Th.Native.Instr}
    (hins : CFSG.Sporadic.Th.instrRegsLt nr ins) {st : List Nat × Nat × Bool} {ρ : ℕ → G}
    (H : SInv φ nr st ρ) :
    SInv φ nr (slpStep (mul3 LL HH CM RM) (vld3 LL HH) ONE V st ins)
      (CFSG.Sporadic.Th.stepG ρ ins) := by
  obtain ⟨R, t, ok⟩ := st
  obtain ⟨hl, hR⟩ := H
  dsimp only at hl hR
  cases ins with
  | mu i j k =>
    obtain ⟨hi, hj, hk⟩ := hins
    refine ⟨?_, fun hok => ?_⟩
    · simp only [slpStep, strictS_eq, List.length_set, hl]
    · simp only [slpStep, strictS_eq] at hok ⊢
      intro r hr
      obtain ⟨ci, ei⟩ := hR hok i hi
      obtain ⟨cj, ej⟩ := hR hok j hj
      rw [getD_set' R (by omega), CFSG.Sporadic.Th.stepG, Function.update_apply]
      by_cases e : r = k
      · rw [if_pos e, if_pos e]
        obtain ⟨c, hm⟩ := mul3_sound ci cj
        exact ⟨c, by rw [hm, ei, ej, map_mul]⟩
      · rw [if_neg e, if_neg e]
        exact hR hok r hr
  | pwr e i k =>
    exact ⟨by simp only [slpStep, hl], fun h => absurd h (by simp [slpStep])⟩
  | iv i k =>
    obtain ⟨hi, hk⟩ := hins
    refine ⟨?_, fun hok => ?_⟩
    · simp only [slpStep, strictS_eq, List.length_set, hl]
    · simp only [slpStep, strictS_eq, bAnd_iff'] at hok ⊢
      obtain ⟨hok0, hv, he⟩ := hok
      intro r hr
      obtain ⟨ci, ei⟩ := hR hok0 i hi
      have cx := vld3_canon hv
      rw [getD_set' R (by omega), CFSG.Sporadic.Th.stepG, Function.update_apply]
      by_cases e : r = k
      · rw [if_pos e, if_pos e]
        refine ⟨cx, ?_⟩
        have hm := (mul3_sound ci cx).2
        rw [Nat.eq_of_beq_eq_true he, one_canon.2, ei] at hm
        calc omat (V t) = φ (ρ i)⁻¹ * (φ (ρ i) * omat (V t)) := by
              rw [← Matrix.mul_assoc, ← map_mul, inv_mul_cancel, map_one, Matrix.one_mul]
          _ = φ (ρ i)⁻¹ := by rw [← hm, Matrix.mul_one]
      · rw [if_neg e, if_neg e]
        exact hR hok0 r hr

variable {φ} in
theorem run_inv {nr : Nat} {V : Nat → Nat} {fin : List Nat × Nat × Bool → Bool} :
    ∀ (prog : List CFSG.Sporadic.Th.Native.Instr) (st : List Nat × Nat × Bool) (ρ : ℕ → G),
      (∀ ins ∈ prog, CFSG.Sporadic.Th.instrRegsLt nr ins) → SInv φ nr st ρ →
      slpRun (mul3 LL HH CM RM) (vld3 LL HH) ONE V fin prog st = true →
      ∃ st', fin st' = true ∧ SInv φ nr st' (CFSG.Sporadic.Th.runSLPG prog ρ)
  | [], st, ρ, _, H, h => ⟨st, h, H⟩
  | ins :: prog, st, ρ, hp, H, h => by
    have e : slpRun (mul3 LL HH CM RM) (vld3 LL HH) ONE V fin (ins :: prog) st =
        slpRun (mul3 LL HH CM RM) (vld3 LL HH) ONE V fin prog
          (slpStep (mul3 LL HH CM RM) (vld3 LL HH) ONE V st ins) := by
      change Prod.rec (motive := fun _ => Bool) (fun R rest => Prod.rec (motive := fun _ => Bool)
        (fun t ok => slpRun (mul3 LL HH CM RM) (vld3 LL HH) ONE V fin prog (R, t, ok)) rest)
        (slpStep (mul3 LL HH CM RM) (vld3 LL HH) ONE V st ins) = _
      obtain ⟨R, t, ok⟩ := slpStep (mul3 LL HH CM RM) (vld3 LL HH) ONE V st ins
      rfl
    rw [e] at h
    have := run_inv prog _ (CFSG.Sporadic.Th.stepG ρ ins) (fun i hi => hp i (List.mem_cons_of_mem _ hi))
      (step_inv (hp ins List.mem_cons_self) H) h
    simpa only [CFSG.Sporadic.Th.runSLPG, List.foldl_cons] using this

theorem selK_spec {ML : Nat → Nat} {R : List Nat} :
    ∀ (sel : List Nat) (j0 : Nat), List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
      (fun s _ ih j => bAnd(Nat.beq (List.getD R s (nat_lit 0)) (ML j), ih (Nat.succ j))) sel j0 = true →
      ∀ j < sel.length, R.getD (sel.getD j 0) 0 = ML (j0 + j)
  | [], _, _, j, hj => absurd hj (Nat.not_lt_zero j)
  | s :: sel, j0, h, j, hj => by
    have h' : bAnd(Nat.beq (List.getD R s 0) (ML j0), List.rec (motive := fun _ => Nat → Bool)
        (fun _ => true) (fun s _ ih j => bAnd(Nat.beq (List.getD R s (nat_lit 0)) (ML j),
          ih (Nat.succ j))) sel (Nat.succ j0)) = true := h
    rw [bAnd_iff'] at h'
    rcases j with _ | j
    · simpa using Nat.eq_of_beq_eq_true h'.1
    · have := selK_spec sel (j0 + 1) h'.2 j (by simpa using hj)
      rw [show j0 + (j + 1) = j0 + 1 + j by omega]
      simpa using this

theorem slpK_sound {prog : List CFSG.Sporadic.Th.Native.Instr} {nr : Nat} {FA FB V ML : Nat → Nat}
    {sel : List Nat} {gA gB : G} (h : slpK prog nr FA FB V ML sel = true) (hnr : 2 ≤ nr)
    (hprog : ∀ ins ∈ prog, CFSG.Sporadic.Th.instrRegsLt nr ins) (hsel : ∀ s ∈ sel, s < nr)
    (hFA : ∀ c < 154, PV (FA c)) (hFB : ∀ c < 154, PV (FB c))
    (hA : ∀ r c : Fin 154, φ gA r c = vecK (FA c.val) r)
    (hB : ∀ r c : Fin 154, φ gB r c = vecK (FB c.val) r) :
    ∀ j < sel.length, Canon 3 154 11 (ML j) ∧ omat (ML j) = φ (CFSG.Sporadic.Th.runSLPG prog
      (fun r => if r = 0 then gA else if r = 1 then gB * gA * gB else 1) (sel.getD j 0)) := by
  unfold slpK at h
  simp only [strictB_eq'] at h
  have hFA' : ∀ c < 154, PV (FA (0 + c)) := fun c hc => by rw [Nat.zero_add]; exact hFA c hc
  have hFB' : ∀ c < 154, PV (FB (0 + c)) := fun c hc => by rw [Nat.zero_add]; exact hFB c hc
  have ca := batK_canon (le_refl 154) hFA'
  have cb := batK_canon (le_refl 154) hFB'
  have ea : omat (batK CS DS FA 0 154) = φ gA := by
    ext r c
    rw [batK_omat (le_refl 154) hFA', if_pos c.isLt, Nat.zero_add, hA]
  have eb : omat (batK CS DS FB 0 154) = φ gB := by
    ext r c
    rw [batK_omat (le_refl 154) hFB', if_pos c.isLt, Nat.zero_add, hB]
  obtain ⟨cba, eba⟩ := mul3_sound cb ca
  obtain ⟨cbab, ebab⟩ := mul3_sound cba cb
  have H0 : SInv φ nr (batK CS DS FA 0 154 :: mul3 LL HH CM RM (mul3 LL HH CM RM
      (batK CS DS FB 0 154) (batK CS DS FA 0 154)) (batK CS DS FB 0 154) ::
        List.replicate (Nat.sub nr 2) ONE, 0, true)
      (fun r => if r = 0 then gA else if r = 1 then gB * gA * gB else 1) := by
    refine ⟨?_, fun _ r hr => ?_⟩
    · change (List.replicate (nr - 2) ONE).length + 1 + 1 = nr
      rw [List.length_replicate]
      omega
    · rcases r with _ | _ | r
      · have e : (fun r => if r = 0 then gA else if r = 1 then gB * gA * gB else (1 : G)) 0 = gA := by
          simp
        rw [List.getD_cons_zero, e]
        exact ⟨ca, ea⟩
      · have e : (fun r => if r = 0 then gA else if r = 1 then gB * gA * gB else (1 : G)) (0 + 1) =
            gB * gA * gB := by simp
        rw [List.getD_cons_succ, List.getD_cons_zero, e]
        refine ⟨cbab, ?_⟩
        rw [ebab, eba, ea, eb, map_mul, map_mul]
      · have hr' : r < Nat.sub nr 2 := by change r < nr - 2; omega
        have e : (fun r => if r = 0 then gA else if r = 1 then gB * gA * gB else (1 : G)) (r + 1 + 1) =
            1 := by simp
        rw [List.getD_cons_succ, List.getD_cons_succ, List.getD_eq_getElem?_getD,
          List.getElem?_replicate, if_pos hr', Option.getD_some, e, map_one]
        exact one_canon
  obtain ⟨st', hfin, hinv⟩ := run_inv prog _ _ hprog H0 h
  rw [bAnd_iff'] at hfin
  have hs := selK_spec sel 0 hfin.2
  intro j hj
  have hsj : sel.getD j 0 < nr := hsel _ (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; simp)
  obtain ⟨c, e⟩ := hinv.2 hfin.1 _ hsj
  rw [hs j hj, Nat.zero_add] at c e
  exact ⟨c, e⟩

end Slp

end CFSG.KS.ONC

end
