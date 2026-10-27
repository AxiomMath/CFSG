module

public import Certificates.Data.Kernel.Misc.YamakiLbar
public import CFSG.Certificates.Kernel.Misc.YamakiA0Sound

public section

namespace CFSG.KC.YamakiLbar

open CFSG.ClassicalInvolution.Solomon73.Yamaki CFSG.ClassicalInvolution.Sp62Rec CFSG.KD.YamakiLbar
  CFSG.KD.BfsK CFSG.KC.BfsEnum CFSG.KC.YamakiS0 CFSG.KC.YamakiA0 CFSG.KC.Misc.Spec Matrix
  CFSG.KD.YamakiA0
open CFSG.KD.Sp62 (MULF ONE)
open CFSG.KC.Sp62 (MULF_lt pkMat_MULF pkMat_inj)

theorem mulF_assoc (a b c : ℕ) : MULF (MULF a b) c = MULF a (MULF b c) :=
  pkMat_inj (MULF_lt _ _) (MULF_lt _ _) (by
    rw [pkMat_MULF, pkMat_MULF, pkMat_MULF, pkMat_MULF, mul_assoc])

theorem one_mulF {x : ℕ} (hx : x < 2 ^ 36) : MULF ONE x = x :=
  pkMat_inj (MULF_lt _ _) hx (by rw [pkMat_MULF, pkMat_ONE, one_mul])

theorem mulF_one {x : ℕ} (hx : x < 2 ^ 36) : MULF x ONE = x :=
  pkMat_inj (MULF_lt _ _) hx (by rw [pkMat_MULF, pkMat_ONE, mul_one])

theorem pkMat_zero : pkMat 6 0 = 0 := by
  ext i j
  simp [pkMat]

theorem pkMat_xor (a b : ℕ) : pkMat 6 (a ^^^ b) = pkMat 6 a + pkMat 6 b := by
  ext i j
  simp only [pkMat, Matrix.of_apply, Matrix.add_apply, Nat.testBit_xor]
  cases a.testBit (6 * i.val + j.val) <;> cases b.testBit (6 * i.val + j.val) <;> decide

theorem xor_lt36 {a b : ℕ} (ha : a < 2 ^ 36) (hb : b < 2 ^ 36) : a ^^^ b < 2 ^ 36 :=
  Nat.xor_lt_two_pow ha hb

theorem xor_lt64 {a b : ℕ} (ha : a < 64) (hb : b < 64) : a ^^^ b < 64 :=
  Nat.xor_lt_two_pow (n := 6) ha hb

theorem xor_mulF (a b N : ℕ) : MULF (a ^^^ b) N = MULF a N ^^^ MULF b N :=
  pkMat_inj (MULF_lt _ _) (xor_lt36 (MULF_lt _ _) (MULF_lt _ _)) (by
    rw [pkMat_MULF, pkMat_xor, pkMat_xor, add_mul, pkMat_MULF, pkMat_MULF])

theorem mulF_xor (N a b : ℕ) : MULF N (a ^^^ b) = MULF N a ^^^ MULF N b :=
  pkMat_inj (MULF_lt _ _) (xor_lt36 (MULF_lt _ _) (MULF_lt _ _)) (by
    rw [pkMat_MULF, pkMat_xor, pkMat_xor, mul_add, pkMat_MULF, pkMat_MULF])

theorem zero_mulF (N : ℕ) : MULF 0 N = 0 :=
  pkMat_inj (MULF_lt _ _) (by norm_num) (by rw [pkMat_MULF, pkMat_zero, zero_mul])

theorem testBit_vec {c : ℕ} (hc : c < 64) {p : ℕ} (hp : 6 ≤ p) : c.testBit p = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le hc (by
    calc 64 = 2 ^ 6 := rfl
      _ ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) hp))

theorem pkMat_vec {c : ℕ} (hc : c < 64) (i j : Fin 6) (hi : i.val ≠ 0) : pkMat 6 c i j = 0 := by
  simp only [pkMat, Matrix.of_apply]
  rw [testBit_vec hc (by omega)]
  rfl

theorem testBit_ite (a b : Bool)
    (h : ((if a then 1 else 0 : ZMod 2) = if b then 1 else 0)) : a = b :=
  CFSG.KC.Sp62.ite_inj a b h

theorem testBit_eq_entry (x : ℕ) {p : ℕ} (hp : p < 36) :
    ((if x.testBit p then 1 else 0 : ZMod 2)) = pkMat 6 x ⟨p / 6, by omega⟩ ⟨p % 6, by omega⟩ := by
  simp only [pkMat, Matrix.of_apply]
  rw [show 6 * (p / 6) + p % 6 = p by omega]

theorem vec_lt {c : ℕ} (hc : c < 64) (N : ℕ) : MULF c N < 64 := by
  have : MULF c N < 2 ^ 6 := by
    apply Nat.lt_pow_two_of_testBit
    intro p hp
    by_cases hp36 : p < 36
    · have h0 : (pkMat 6 c * pkMat 6 N) ⟨p / 6, by omega⟩ ⟨p % 6, by omega⟩ = 0 := by
        rw [Matrix.mul_apply]
        apply Finset.sum_eq_zero
        intro l _
        rw [pkMat_vec hc _ _ (by simp only; omega), zero_mul]
      rw [← pkMat_MULF, ← testBit_eq_entry _ hp36] at h0
      revert h0
      cases (MULF c N).testBit p <;> simp
    · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le (MULF_lt _ _)
        (Nat.pow_le_pow_right (by norm_num) (by omega)))
  simpa using this

theorem vec_ext {x y : ℕ} (hx : x < 64) (hy : y < 64) (h : ∀ k < 6, x.testBit k = y.testBit k) :
    x = y := by
  apply Nat.eq_of_testBit_eq
  intro p
  by_cases hp : p < 6
  · exact h p hp
  · rw [testBit_vec hx (by omega), testBit_vec hy (by omega)]

theorem pkMat_pow_row {j : ℕ} (hj : j < 6) {i : Fin 6} (hi : i.val = 0) (l : Fin 6) :
    pkMat 6 (2 ^ j) i l = if l.val = j then 1 else 0 := by
  simp only [pkMat, Matrix.of_apply, hi, Nat.mul_zero, Nat.zero_add, Nat.testBit_two_pow]
  by_cases h : l.val = j
  · simp [h]
  · simp only [h, if_false]
    rw [if_neg (by simp only [decide_eq_true_eq]; omega)]

theorem testBit_row (N : ℕ) {j k : ℕ} (hj : j < 6) (hk : k < 6) :
    (MULF (2 ^ j) N).testBit k = N.testBit (6 * j + k) := by
  apply testBit_ite
  have e := testBit_eq_entry (MULF (2 ^ j) N) (p := k) (by omega)
  rw [e, pkMat_MULF, Matrix.mul_apply, Finset.sum_eq_single ⟨j, hj⟩]
  · rw [pkMat_pow_row hj (Nat.div_eq_of_lt hk), if_pos rfl, one_mul]
    simp only [pkMat, Matrix.of_apply, Nat.mod_eq_of_lt hk]
  · intro l _ hl
    rw [pkMat_pow_row hj (Nat.div_eq_of_lt hk), if_neg (fun e => hl (Fin.ext e)), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem pow_lt64 {j : ℕ} (hj : j < 6) : 2 ^ j < 64 :=
  lt_of_lt_of_le (Nat.pow_lt_pow_right (by norm_num) hj) (by norm_num)

theorem rows_ext {N N' : ℕ} (hN : N < 2 ^ 36) (hN' : N' < 2 ^ 36)
    (h : ∀ j < 6, MULF (2 ^ j) N = MULF (2 ^ j) N') : N = N' := by
  apply Nat.eq_of_testBit_eq
  intro p
  by_cases hp : p < 36
  · have e1 := testBit_row N (j := p / 6) (k := p % 6) (by omega) (by omega)
    have e2 := testBit_row N' (j := p / 6) (k := p % 6) (by omega) (by omega)
    rw [show 6 * (p / 6) + p % 6 = p by omega] at e1 e2
    rw [← e1, ← e2, h _ (by omega)]
  · have h36 : 2 ^ 36 ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_lt_two_pow (by omega), Nat.testBit_lt_two_pow (by omega)]

theorem rowS_eq (S : ℕ) {i : ℕ} (hi : i < 6) : rowS S i = MULF (2 ^ i) S := by
  have hr : rowS S i < 64 := by
    unfold rowS
    exact lt_of_le_of_lt Nat.and_le_right (by norm_num)
  refine vec_ext hr (vec_lt (pow_lt64 hi) _) fun k hk => ?_
  rw [testBit_row S hi hk]
  unfold rowS
  change ((S >>> (6 * i)) &&& 63).testBit k = _
  rw [Nat.testBit_and, Nat.testBit_shiftRight,
    show (63 : ℕ) = 2 ^ 6 - 1 by rfl, Nat.testBit_two_pow_sub_one]
  simp [hk, Nat.add_comm]

noncomputable def sumBits (f : ℕ → ℕ) (r : ℕ) (n : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0
    (fun i ih => Nat.xor ih (cond (Nat.beq (Nat.land (Nat.shiftRight r i) 1) 1) (f i) 0)) n

theorem sumBits_pow : ∀ r < 64, sumBits (fun i => 2 ^ i) r 6 = r := by decide

theorem mulF_sumBits (f : ℕ → ℕ) (r S : ℕ) :
    ∀ n, MULF (sumBits f r n) S = sumBits (fun i => MULF (f i) S) r n
  | 0 => zero_mulF S
  | n + 1 => by
    change MULF (sumBits f r n ^^^ _) S = sumBits (fun i => MULF (f i) S) r n ^^^ _
    rw [xor_mulF, mulF_sumBits f r S n]
    cases Nat.beq (Nat.land (Nat.shiftRight r n) 1) 1
    · simp only [cond_false, zero_mulF]
    · rfl

theorem sumBits_congr {f g : ℕ → ℕ} (r : ℕ) (h : ∀ i < 6, f i = g i) :
    ∀ n ≤ 6, sumBits f r n = sumBits g r n
  | 0, _ => rfl
  | n + 1, hn => by
    change sumBits f r n ^^^ _ = sumBits g r n ^^^ _
    rw [sumBits_congr r h n (by omega), h n (by omega)]

theorem vmul_eq {r : ℕ} (hr : r < 64) (S : ℕ) : vmul r S = MULF r S := by
  have e : vmul r S = sumBits (rowS S) r 6 := rfl
  rw [e, sumBits_congr r (g := fun i => MULF (2 ^ i) S) (fun i hi => rowS_eq S hi) 6 le_rfl,
    ← mulF_sumBits, sumBits_pow r hr]

theorem testBit_packL : ∀ (rs : List ℕ), (∀ r ∈ rs, r < 64) → ∀ j k, k < 6 →
    (packL rs).testBit (6 * j + k) = (rs.getD j 0).testBit k
  | [], _, j, k, _ => by
    change (0 : ℕ).testBit _ = _
    simp
  | r :: rs, h, j, k, hk => by
    have hr := h r List.mem_cons_self
    change (r + 64 * packL rs).testBit (6 * j + k) = _
    rw [show r + 64 * packL rs = 2 ^ 6 * packL rs + r by ring,
      Nat.testBit_two_pow_mul_add _ (by simpa using hr)]
    cases j with
    | zero => simp [hk]
    | succ j =>
      rw [if_neg (by omega), show 6 * (j + 1) + k - 6 = 6 * j + k by omega,
        testBit_packL rs (fun x hx => h x (List.mem_cons_of_mem _ hx)) j k hk]
      simp

theorem packL_lt : ∀ (rs : List ℕ), (∀ r ∈ rs, r < 64) → packL rs < 2 ^ (6 * rs.length)
  | [], _ => by
    change (0 : ℕ) < _
    positivity
  | r :: rs, h => by
    have hr := h r List.mem_cons_self
    have ih := packL_lt rs fun x hx => h x (List.mem_cons_of_mem _ hx)
    change r + 64 * packL rs < _
    rw [List.length_cons, show 6 * (rs.length + 1) = 6 * rs.length + 6 by ring, pow_add]
    have : 2 ^ 6 = 64 := rfl
    omega

theorem row_packL {rs : List ℕ} (h : ∀ r ∈ rs, r < 64) {j : ℕ} (hj : j < 6) :
    MULF (2 ^ j) (packL rs) = rs.getD j 0 := by
  have hl : rs.getD j 0 < 64 := by
    rw [List.getD_eq_getElem?_getD]
    cases hx : rs[j]? with
    | none => simp
    | some x => simpa using h x (List.mem_of_getElem? hx)
  refine vec_ext (vec_lt (pow_lt64 hj) _) hl fun k hk => ?_
  rw [testBit_row _ hj hk, testBit_packL rs h j k hk]

theorem vmul_lt {r : ℕ} (hr : r < 64) (S : ℕ) : vmul r S < 64 := by
  rw [vmul_eq hr]
  exact vec_lt hr S

theorem gmat6_lt {r : ℕ} (hr : r < 64) (S0 S1 S2 S3 S4 S5 : ℕ) :
    gmat6 r S0 S1 S2 S3 S4 S5 < 2 ^ 36 := by
  have := packL_lt [vmul r S0, vmul r S1, vmul r S2, vmul r S3, vmul r S4, vmul r S5]
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro x (rfl | rfl | rfl | rfl |
      rfl | rfl) <;> exact vmul_lt hr _)
  exact this

theorem row_gmat6 {r : ℕ} (hr : r < 64) (S : ℕ → ℕ) {j : ℕ} (hj : j < 6) :
    MULF (2 ^ j) (gmat6 r (S 0) (S 1) (S 2) (S 3) (S 4) (S 5)) = MULF r (S j) := by
  unfold gmat6
  rw [row_packL (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro x (rfl | rfl |
    rfl | rfl | rfl | rfl) <;> exact vmul_lt hr _) hj]
  interval_cases j <;> simp [vmul_eq hr]

variable {R Q : ℕ → ℕ}

theorem a0_facts (h : a0TabK R 64 = true) :
    recX R 12 0 = ONE ∧
      (∀ i < 63, recF R 12 0 i ≤ i ∧ recF R 12 1 i < 6 ∧
        recX R 12 (i + 1) = MULF (recX R 12 (recF R 12 0 i)) (R (recF R 12 1 i + 3))) ∧
      (∀ i < 384, recPOS R 12 6 i < 64 ∧
        recX R 12 (recPOS R 12 6 i) = MULF (recX R 12 (i / 6)) (R (i % 6 + 3))) ∧
      ∀ t < 64, ∀ t' < 64, recX R 12 t = recX R 12 t' → t = t' := by
  unfold a0TabK tableKk at h
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨h0, ⟨hB, hS⟩, hT⟩ := h
  have hBi := CFSG.KC.BfsK.buildG_at hB (by norm_num)
  obtain ⟨-, -, hSi⟩ := CFSG.KC.BfsK.stepG_facts hS (by norm_num)
  refine ⟨h0, fun i hi => ?_, fun i hi => ?_, CFSG.KC.G2Three.sort_inj hT (by norm_num)⟩
  · obtain ⟨a, b, c⟩ := hBi i hi
    exact ⟨a, b, by rw [c, rstA, Nat.add_eq]⟩
  · obtain ⟨-, -, c, d, -, -⟩ := hSi i hi
    exact ⟨c, by rw [d, rstA, Nat.add_eq]⟩

theorem coord_facts (hc : coordK R Q = true) :
    crd Q 0 = 0 ∧ (∀ k < 64, crd Q k < 64 ∧ psc Q (crd Q k) = k ∧ psc Q k < 64 ∧
      crd Q (psc Q k) = k) ∧
      ∀ i < 384, crd Q (recPOS R 12 6 i) = crd Q (i / 6) ^^^ 2 ^ (i % 6) := by
  unfold coordK at hc
  simp only [Bool.and_eq_true, Nat.beq_eq] at hc
  obtain ⟨⟨h0, h1⟩, h2⟩ := hc
  refine ⟨h0, fun k hk => ?_, fun i hi => ?_⟩
  · have e := CFSG.KC.G2Three.allBelow_g2 h1 (by norm_num) k hk
    simp only [Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq] at e
    obtain ⟨⟨⟨a, b⟩, c⟩, d⟩ := e
    exact ⟨a, b, c, d⟩
  · have e := CFSG.KC.G2Three.allBelow_g2 h2 (by norm_num) i hi
    rw [Nat.beq_eq] at e
    rw [e]
    change crd Q (i / 6) ^^^ 1 <<< (i % 6) = _
    rw [Nat.one_shiftLeft]

section A0

variable (hG : ∀ j : Fin 12, yamakiMat6 j = pkMat 6 (R j.val)) (hA : a0TabK R 64 = true)
  (hc : coordK R Q = true)

include hA hc in
theorem crd_lt {k : ℕ} (hk : k < 64) : crd Q k < 64 := ((coord_facts hc).2.1 k hk).1

include hA hc in
theorem psc_crd {k : ℕ} (hk : k < 64) : psc Q (crd Q k) = k := ((coord_facts hc).2.1 k hk).2.1

include hA hc in
theorem psc_lt {k : ℕ} (hk : k < 64) : psc Q k < 64 := ((coord_facts hc).2.1 k hk).2.2.1

include hA hc in
theorem crd_psc {k : ℕ} (hk : k < 64) : crd Q (psc Q k) = k := ((coord_facts hc).2.1 k hk).2.2.2

include hA hc in
theorem psc_zero : psc Q 0 = 0 := by
  have := psc_crd hA hc (Q := Q) (k := 0) (by norm_num)
  rwa [(coord_facts hc).1] at this

include hA hc in
theorem crd_succ {t : ℕ} (ht : t < 63) :
    crd Q (t + 1) = crd Q (recF R 12 0 t) ^^^ 2 ^ (recF R 12 1 t) := by
  obtain ⟨-, hB, hS, hd⟩ := a0_facts hA
  obtain ⟨p1, p2, p3⟩ := hB t ht
  have hi : 6 * recF R 12 0 t + recF R 12 1 t < 384 := by omega
  obtain ⟨s1, s2⟩ := hS _ hi
  have e1 : (6 * recF R 12 0 t + recF R 12 1 t) / 6 = recF R 12 0 t := by omega
  have e2 : (6 * recF R 12 0 t + recF R 12 1 t) % 6 = recF R 12 1 t := by omega
  rw [e1, e2, ← p3] at s2
  have := hd _ s1 _ (by omega) s2
  rw [← this, (coord_facts hc).2.2 _ hi, e1, e2]

noncomputable abbrev MX (R : ℕ → ℕ) (k : ℕ) : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  pkMat 6 (recX R 12 k)

include hA hc in
theorem mulX : ∀ b < 64, ∀ a < 64, MX R a * MX R b = MX R (psc Q (crd Q a ^^^ crd Q b)) := by
  obtain ⟨h0, hB, hS, -⟩ := a0_facts hA
  intro b
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    intro hb a ha
    cases b with
    | zero =>
      rw [show MX R 0 = 1 by rw [MX, h0, pkMat_ONE], mul_one, (coord_facts hc).1, Nat.xor_zero,
        psc_crd hA hc ha]
    | succ t =>
      obtain ⟨p1, p2, p3⟩ := hB t (by omega)
      have hm : crd Q a ^^^ crd Q (recF R 12 0 t) < 64 :=
        xor_lt64 (crd_lt hA hc ha) (crd_lt hA hc (by omega))
      have hi : 6 * psc Q (crd Q a ^^^ crd Q (recF R 12 0 t)) + recF R 12 1 t < 384 := by
        have := psc_lt hA hc hm
        omega
      obtain ⟨s1, s2⟩ := hS _ hi
      have e1 : (6 * psc Q (crd Q a ^^^ crd Q (recF R 12 0 t)) + recF R 12 1 t) / 6 =
          psc Q (crd Q a ^^^ crd Q (recF R 12 0 t)) := by omega
      have e2 : (6 * psc Q (crd Q a ^^^ crd Q (recF R 12 0 t)) + recF R 12 1 t) % 6 =
          recF R 12 1 t := by omega
      rw [e1, e2] at s2
      have hc2 := (coord_facts hc).2.2 _ hi
      rw [e1, e2, crd_psc hA hc hm] at hc2
      rw [show MX R (t + 1) = MX R (recF R 12 0 t) * pkMat 6 (R (recF R 12 1 t + 3)) by
          rw [MX, p3, pkMat_MULF], ← mul_assoc, ih _ (by omega) (by omega) a ha, MX, ← pkMat_MULF,
        ← s2, crd_succ hA hc (by omega), ← Nat.xor_assoc, ← hc2, psc_crd hA hc s1]

include hA hc in
theorem genX {j : ℕ} (hj : j < 6) : pkMat 6 (R (j + 3)) = MX R (psc Q (2 ^ j)) := by
  obtain ⟨h0, -, hS, -⟩ := a0_facts hA
  obtain ⟨s1, s2⟩ := hS j (by omega)
  have hc2 := (coord_facts hc).2.2 j (by omega)
  rw [Nat.div_eq_of_lt (by omega), Nat.mod_eq_of_lt hj, (coord_facts hc).1, Nat.zero_xor] at hc2
  rw [Nat.div_eq_of_lt (by omega), Nat.mod_eq_of_lt hj, h0] at s2
  rw [← hc2, psc_crd hA hc s1, MX, s2, pkMat_MULF, pkMat_ONE, one_mul]

theorem gl_facts (hg : glK R Q = true) {i : ℕ} (hi : i < 11) :
    MULF (R i) (R i) = ONE ∧ ∀ j < 6, MULF (MULF (R i) (R (j + 3))) (R i) =
      recX R 12 (psc Q (MULF (2 ^ j) (Q i))) := by
  unfold glK at hg
  have e := CFSG.KC.G2Three.allBelow_g2 hg (by norm_num) i hi
  simp only [Bool.and_eq_true, Nat.beq_eq] at e
  refine ⟨e.1, fun j hj => ?_⟩
  have e2 := CFSG.KC.G2Three.allBelow_g2 e.2 (by norm_num) j hj
  rw [Nat.beq_eq, Nat.add_eq] at e2
  rw [e2]
  change recX R 12 (psc Q (MULF (1 <<< j) (Q i))) = _
  rw [Nat.one_shiftLeft]

include hA hc in
theorem conjX (hg : glK R Q = true) {i : ℕ} (hi : i < 11) :
    ∀ k < 64, pkMat 6 (R i) * MX R k * pkMat 6 (R i) = MX R (psc Q (MULF (crd Q k) (Q i))) := by
  obtain ⟨h0, hB, -, -⟩ := a0_facts hA
  obtain ⟨g1, g2⟩ := gl_facts hg hi
  have hsq : pkMat 6 (R i) * pkMat 6 (R i) = 1 := by rw [← pkMat_MULF, g1, pkMat_ONE]
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    cases k with
    | zero =>
      have hM0 : MX R 0 = 1 := by rw [MX, h0, pkMat_ONE]
      rw [hM0, mul_one, hsq, (coord_facts hc).1, zero_mulF, psc_zero hA hc, hM0]
    | succ t =>
      obtain ⟨p1, p2, p3⟩ := hB t (by omega)
      have hp := crd_lt hA hc (show recF R 12 0 t < 64 by omega)
      have hx1 := vec_lt hp (Q i)
      have hx2 := vec_lt (pow_lt64 p2) (Q i)
      have e : pkMat 6 (R i) * MX R (t + 1) * pkMat 6 (R i) =
          (pkMat 6 (R i) * MX R (recF R 12 0 t) * pkMat 6 (R i)) *
            (pkMat 6 (R i) * pkMat 6 (R (recF R 12 1 t + 3)) * pkMat 6 (R i)) := by
        rw [MX, p3, pkMat_MULF]
        calc pkMat 6 (R i) * (pkMat 6 (recX R 12 (recF R 12 0 t)) *
              pkMat 6 (R (recF R 12 1 t + 3))) * pkMat 6 (R i)
            = pkMat 6 (R i) * pkMat 6 (recX R 12 (recF R 12 0 t)) *
                (pkMat 6 (R i) * pkMat 6 (R i)) * pkMat 6 (R (recF R 12 1 t + 3)) *
                pkMat 6 (R i) := by rw [hsq]; noncomm_ring
          _ = _ := by noncomm_ring
      rw [e, ih _ (by omega) (by omega), ← pkMat_MULF, ← pkMat_MULF, g2 _ p2, ← MX,
        mulX hA hc _ (psc_lt hA hc hx2) _ (psc_lt hA hc hx1), crd_psc hA hc hx1,
        crd_psc hA hc hx2, ← xor_mulF, ← crd_succ hA hc (by omega)]

end A0

end CFSG.KC.YamakiLbar

end
