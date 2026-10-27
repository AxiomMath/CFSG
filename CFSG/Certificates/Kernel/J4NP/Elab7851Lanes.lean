module

public import CFSG.Certificates.Kernel.J4NP.Elab7851Facts
public import CFSG.Certificates.Kernel.J4Loc.TrioSound
public import CFSG.Sporadic.J4.QTRankProof

public section

namespace CFSG.KC.J4NP

open CFSG.KC.J4Q CFSG.KC.J4Loc CFSG.KS.J4Loc CFSG.Sporadic.J4.QT

@[expose] noncomputable def dec (K : ℕ) : List ℕ := (List.range 11).map fun j => fld 11 K j

theorem ivt_eq (KK i : ℕ) : ivt KK i = dec (lnS 121 KK i) := rfl

theorem testBit_fld (w P i r : ℕ) :
    (fld w P i).testBit r = (decide (r < w) && P.testBit (w * i + r)) := by
  rw [fld_eq, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]

theorem lnS_lt (w P i : ℕ) : lnS w P i < 2 ^ w := by
  change fld (w + 64) P i >>> 64 < 2 ^ w
  rw [Nat.shiftRight_eq_div_pow]
  refine Nat.div_lt_of_lt_mul ?_
  rw [← pow_add, Nat.add_comm 64 w]
  exact fld_lt _ _ _

theorem testBit_lt {x n : ℕ} (k : ℕ) (hx : x < 2 ^ k) (hn : k ≤ n) : x.testBit n = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) hn))

theorem length_dec (K : ℕ) : (dec K).length = 11 := by simp [dec]

theorem getD_dec (K j : ℕ) : (dec K).getD j 0 = if j < 11 then fld 11 K j else 0 := by
  unfold dec
  split_ifs with h
  · simp [h]
  · simp [List.getD_eq_getElem?_getD, show ¬ j < 11 from h]

theorem dec_lt {K x : ℕ} (hx : x ∈ dec K) : x < 2 ^ 11 := by
  obtain ⟨j, -, rfl⟩ := List.mem_map.mp hx
  exact fld_lt _ _ _

theorem lenOK_dec (K : ℕ) : lenOK (dec K) = true := by
  unfold lenOK
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq]
  exact ⟨length_dec K, fun x hx => dec_lt hx⟩

theorem keyT_cons (x : ℕ) (l : List ℕ) : keyT (x :: l) = x ||| keyT l <<< 11 := rfl

theorem testBit_keyT : ∀ (l : List ℕ), (∀ x ∈ l, x < 2 ^ 11) → ∀ n,
    (keyT l).testBit n = (l.getD (n / 11) 0).testBit (n % 11)
  | [], _, n => by simp [keyT]
  | x :: l, hl, n => by
    rw [keyT_cons, Nat.testBit_or, Nat.testBit_shiftLeft]
    have hx : x < 2 ^ 11 := hl x (by simp)
    rcases Nat.lt_or_ge n 11 with h | h
    · rw [Nat.div_eq_of_lt h, Nat.mod_eq_of_lt h]
      simp [show ¬ n ≥ 11 by omega]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 11 := ⟨n - 11, by omega⟩
      rw [testBit_lt 11 hx h, Nat.add_sub_cancel, testBit_keyT l (fun y hy => hl y (by simp [hy])) m]
      simp [Nat.add_div_right, Nat.add_mod_right]

theorem keyT_lt : ∀ (l : List ℕ), (∀ x ∈ l, x < 2 ^ 11) → keyT l < 2 ^ (11 * l.length)
  | [], _ => by simp [keyT]
  | x :: l, hl => by
    rw [keyT_cons, List.length_cons]
    have hx : x < 2 ^ 11 := hl x (by simp)
    have ih := keyT_lt l fun y hy => hl y (by simp [hy])
    refine Nat.or_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) (by omega))) ?_
    rw [Nat.shiftLeft_eq, show 11 * (l.length + 1) = 11 * l.length + 11 by ring, pow_add]
    exact Nat.mul_lt_mul_of_pos_right ih (by positivity)

theorem dec_keyT {t : List ℕ} (hl : t.length = 11) (ht : ∀ x ∈ t, x < 2 ^ 11) :
    dec (keyT t) = t := by
  apply List.ext_getElem (by rw [length_dec, hl])
  intro j hj hj'
  have hj11 : j < 11 := by rw [length_dec] at hj; exact hj
  simp only [dec, List.getElem_map, List.getElem_range]
  apply Nat.eq_of_testBit_eq
  intro r
  rw [testBit_fld]
  rcases Nat.lt_or_ge r 11 with hr | hr
  · rw [testBit_keyT t ht, show (11 * j + r) / 11 = j by omega, show (11 * j + r) % 11 = r by omega,
      List.getD_eq_getElem _ _ hj']
    simp [hr]
  · rw [testBit_lt 11 (ht _ (List.getElem_mem hj')) hr]
    simp [show ¬ r < 11 by omega]

theorem keyT_dec {K : ℕ} (hK : K < 2 ^ 121) : keyT (dec K) = K := by
  apply Nat.eq_of_testBit_eq
  intro n
  rw [testBit_keyT _ (fun x hx => dec_lt hx), getD_dec]
  split_ifs with h
  · rw [testBit_fld, show 11 * (n / 11) + n % 11 = n by omega]
    simp [Nat.mod_lt n (by norm_num : 11 > 0)]
  · rw [Nat.zero_testBit, testBit_lt 121 hK (by omega)]

theorem dec_inj {K K' : ℕ} (hK : K < 2 ^ 121) (hK' : K' < 2 ^ 121) (h : dec K = dec K') :
    K = K' := by
  rw [← keyT_dec hK, ← keyT_dec hK', h]

@[expose] noncomputable def prodN (K K' n : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0
    (fun k ih => Nat.xor ih (Nat.mul (Nat.land (Nat.shiftRight K' k) e11) (fld 11 K k))) n

theorem prodK_eq_prodN (K K' : ℕ) : prodK K K' = prodN K K' 11 := rfl

theorem prodN_succ (K K' k : ℕ) :
    prodN K K' (k + 1) = prodN K K' k ^^^ ((K' >>> k) &&& e11) * fld 11 K k := rfl

theorem testBit_e11 (p : ℕ) : e11.testBit p = (decide (p < 121) && decide (p % 11 = 0)) := by
  rcases Nat.lt_or_ge p 121 with h | h
  · have : ∀ q < 121, e11.testBit q = decide (q % 11 = 0) := by decide
    rw [this p h]
    simp [h]
  · rw [testBit_lt 121 (by unfold e11; norm_num) h]
    simp [show ¬ p < 121 by omega]

theorem lor_shift_eq_add {x : ℕ} (hx : x < 2 ^ 11) (y : ℕ) : x ||| y <<< 11 = x + y * 2 ^ 11 := by
  rw [Nat.lor_comm, ← Nat.shiftLeft_add_eq_or_of_lt hx, Nat.shiftLeft_eq, Nat.add_comm]

theorem keyT_mul (t : ℕ) : ∀ l : List ℕ, (∀ x ∈ l, x < 2 ^ 11 ∧ x * t < 2 ^ 11) →
    keyT l * t = keyT (l.map (· * t))
  | [], _ => by simp [keyT]
  | x :: l, hl => by
    have hx := hl x (by simp)
    have ih := keyT_mul t l fun y hy => hl y (by simp [hy])
    rw [List.map_cons, keyT_cons, keyT_cons, lor_shift_eq_add hx.1, lor_shift_eq_add hx.2, ← ih]
    ring

@[expose] noncomputable def bitsL (K' k : ℕ) : List ℕ :=
  (List.range 11).map fun j => if K'.testBit (11 * j + k) then 1 else 0

theorem mask_eq_keyT {K' k : ℕ} (hk : k < 11) : (K' >>> k) &&& e11 = keyT (bitsL K' k) := by
  apply Nat.eq_of_testBit_eq
  intro n
  rw [Nat.testBit_and, Nat.testBit_shiftRight, testBit_e11, testBit_keyT]
  · unfold bitsL
    rw [List.getD_eq_getElem?_getD]
    rcases Nat.lt_or_ge n 121 with h | h
    · rw [List.getElem?_map, List.getElem?_range (by omega)]
      simp only [Option.map_some, Option.getD_some]
      by_cases hn : n % 11 = 0
      · have e' : 11 * (n / 11) + k = k + n := by omega
        rw [e']
        split_ifs with hb <;> simp [h, hn, hb]
      · split_ifs
        · have h1 : Nat.testBit 1 (n % 11) = false :=
            testBit_lt (x := 1) 1 (by norm_num) (by omega)
          simp [hn, h1]
        · simp [hn]
    · rw [List.getElem?_map, List.getElem?_eq_none (by simp; omega)]
      simp [show ¬ n < 121 by omega]
  · intro x hx
    unfold bitsL at hx
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hx
    split_ifs <;> norm_num

theorem testBit_term {K K' k : ℕ} (hk : k < 11) (n : ℕ) :
    (((K' >>> k) &&& e11) * fld 11 K k).testBit n =
      (decide (n < 121) && (fld 11 K' (n / 11)).testBit k && (fld 11 K k).testBit (n % 11)) := by
  have ht : fld 11 K k < 2048 := fld_lt 11 K k
  rw [mask_eq_keyT hk, keyT_mul]
  · rw [testBit_keyT]
    · unfold bitsL
      rw [List.getD_eq_getElem?_getD, testBit_fld]
      rcases Nat.lt_or_ge n 121 with h | h
      · rw [List.map_map, List.getElem?_map, List.getElem?_range (by omega)]
        simp only [Option.map_some, Option.getD_some, Function.comp]
        split_ifs with hb
        · simp [h, hb, hk]
        · simp [h, hb, hk]
      · rw [List.map_map, List.getElem?_map, List.getElem?_eq_none (by simp; omega)]
        simp [show ¬ n < 121 by omega]
    · intro x hx
      unfold bitsL at hx
      rw [List.map_map] at hx
      obtain ⟨j, -, rfl⟩ := List.mem_map.mp hx
      simp only [Function.comp]
      split_ifs <;> simp [ht]
  · intro x hx
    unfold bitsL at hx
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hx
    split_ifs <;> simp [ht]

@[expose] def xr (f : ℕ → Bool) : ℕ → Bool :=
  Nat.rec (motive := fun _ => Bool) false (fun j acc => acc ^^ f j)

theorem xr_zero (f : ℕ → Bool) : xr f 0 = false := rfl

theorem xr_succ (f : ℕ → Bool) (m : ℕ) : xr f (m + 1) = (xr f m ^^ f m) := rfl

theorem xr_congr {f g : ℕ → Bool} : ∀ {m : ℕ}, (∀ j < m, f j = g j) → xr f m = xr g m
  | 0, _ => rfl
  | m + 1, h => by
    rw [xr_succ, xr_succ, xr_congr fun j hj => h j (by omega), h m (by omega)]

theorem testBit_rowsXor (r : ℕ → ℕ) (c i : ℕ) : ∀ m,
    (rowsXor r m c).testBit i = xr (fun j => c.testBit j && (r j).testBit i) m
  | 0 => by rw [rowsXor_zero, Nat.zero_testBit, xr_zero]
  | m + 1 => by
    rw [rowsXor_succ, Nat.testBit_xor, testBit_rowsXor r c i m, xr_succ]
    split_ifs with h <;> simp [h]

theorem testBit_prodN (K K' n : ℕ) : ∀ k ≤ 11, (prodN K K' k).testBit n =
    (decide (n < 121) &&
      xr (fun j => (fld 11 K' (n / 11)).testBit j && (fld 11 K j).testBit (n % 11)) k)
  | 0, _ => by simp [prodN, xr_zero]
  | k + 1, hk => by
    rw [prodN_succ, Nat.testBit_xor, testBit_prodN K K' n k (by omega), testBit_term (by omega),
      xr_succ]
    by_cases h : n < 121 <;> simp [h]

theorem prodK_spec {K K' : ℕ} :
    prodK K K' = keyT (compT (dec K) (dec K')) := by
  apply Nat.eq_of_testBit_eq
  intro n
  have hlt : ∀ x ∈ compT (dec K) (dec K'), x < 2 ^ 11 := by
    intro x hx
    obtain ⟨c, -, rfl⟩ := List.mem_map.mp hx
    exact actT_lt (lenOK_dec K) c
  rw [prodK_eq_prodN, testBit_prodN K K' n 11 le_rfl, testBit_keyT _ hlt]
  unfold compT
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  rcases Nat.lt_or_ge n 121 with h | h
  · have hq : n / 11 < 11 := by omega
    have e : (dec K')[n / 11]? = some (fld 11 K' (n / 11)) := by simp [dec, hq]
    rw [e]
    simp only [Option.map_some, Option.getD_some, h, decide_true, Bool.true_and]
    unfold actT
    rw [testBit_rowsXor]
    exact xr_congr fun j hj => by rw [getD_dec, if_pos hj]
  · have e : (dec K')[n / 11]? = none := by simp [dec, show ¬ n / 11 < 11 by omega]
    rw [e]
    simp [show ¬ n < 121 by omega]

theorem compT_dec_ok (K K' : ℕ) : (compT (dec K) (dec K')).length = 11 ∧
    ∀ x ∈ compT (dec K) (dec K'), x < 2 ^ 11 := by
  refine ⟨by simp [compT, length_dec], fun x hx => ?_⟩
  obtain ⟨c, -, rfl⟩ := List.mem_map.mp hx
  exact actT_lt (lenOK_dec K) c

theorem dec_prodK (K K' : ℕ) : dec (prodK K K') = compT (dec K) (dec K') := by
  rw [prodK_spec]
  exact dec_keyT (compT_dec_ok K K').1 (compT_dec_ok K K').2

theorem prodK_lt (K K' : ℕ) : prodK K K' < 2 ^ 121 := by
  rw [prodK_spec]
  have h := keyT_lt _ (compT_dec_ok K K').2
  rwa [(compT_dec_ok K K').1] at h

theorem brec_eq (b : Bool) (x : ℕ) : Bool.rec (motive := fun _ => ℕ) 0 x b = if b then x else 0 := by
  cases b <;> rfl

@[expose] noncomputable def planeN (j m : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun c acc => Nat.lor acc (Bool.rec (motive := fun _ => Nat) (nat_lit 0)
      (Nat.shiftLeft (nat_lit 1) c) (bitB c j))) m

theorem testBit_onesK (w c : ℕ) : (onesK w).testBit c = decide (c < w) := by
  change (1 <<< w - 1).testBit c = _
  rw [Nat.one_shiftLeft, Nat.testBit_two_pow_sub_one]

theorem testBit_planeN (j c : ℕ) : ∀ m, (planeN j m).testBit c = (decide (c < m) && c.testBit j)
  | 0 => by simp [planeN]
  | m + 1 => by
    have e : planeN j (m + 1) = planeN j m ||| (if m.testBit j then 2 ^ m else 0) := by
      have hs : Nat.shiftLeft 1 m = 2 ^ m := Nat.one_shiftLeft m
      change Nat.lor (planeN j m) _ = _
      rw [brec_eq, bitB_eq, hs]
      rfl
    rw [e, Nat.testBit_or, testBit_planeN j c m]
    split_ifs with hb
    · rw [Nat.testBit_two_pow]
      by_cases hc : c = m
      · subst hc
        simp [hb]
      · have : c < m + 1 ↔ c < m := by omega
        simp [this, hc, Ne.symm hc]
    · rw [Nat.zero_testBit]
      by_cases hc : c = m
      · subst hc
        simp [hb]
      · have : c < m + 1 ↔ c < m := by omega
        simp [this]

theorem planeK_eq (j c : ℕ) : (planeK j).testBit c = (decide (c < 2048) && c.testBit j) := by
  have e : planeK j = planeN j (nat_lit 2048) := rfl
  rw [e, testBit_planeN]

@[expose] noncomputable def outN (XP K i k : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0
    (fun j acc => Nat.xor acc (Bool.rec (motive := fun _ => ℕ) 0
      (lnS 2048 XP j) (bitB (fld 11 K j) i))) k

theorem testBit_outN {XP : ℕ} (hXP : ∀ j < 11, lnS 2048 XP j = planeK j) (K i c : ℕ) :
    ∀ k ≤ 11, (outN XP K i k).testBit c =
      (decide (c < 2048) && xr (fun j => c.testBit j && (fld 11 K j).testBit i) k)
  | 0, _ => by simp [outN, xr_zero]
  | k + 1, hk => by
    have e : outN XP K i (k + 1) =
        outN XP K i k ^^^ (if (fld 11 K k).testBit i then lnS 2048 XP k else 0) := by
      change Nat.xor (outN XP K i k) _ = _
      rw [brec_eq, bitB_eq]
      rfl
    rw [e, Nat.testBit_xor, testBit_outN hXP K i c k (by omega), xr_succ]
    split_ifs with hb
    · rw [hXP k (by omega), planeK_eq]
      by_cases hc : c < 2048 <;> simp [hc, hb]
    · rw [Nat.zero_testBit]
      simp [hb]

theorem testBit_actT_dec (K c i : ℕ) :
    (actT (dec K) c).testBit i = xr (fun j => c.testBit j && (fld 11 K j).testBit i) 11 := by
  unfold actT
  rw [testBit_rowsXor]
  exact xr_congr fun j hj => by rw [getD_dec, if_pos hj]

@[expose] noncomputable def diffN (XP K m : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0
    (fun i acc => Nat.lor acc (Nat.xor (outK XP K i) (lnS 2048 XP i))) m

theorem testBit_diffN {XP : ℕ} (hXP : ∀ j < 11, lnS 2048 XP j = planeK j) (K c : ℕ) :
    ∀ m ≤ 11, (diffN XP K m).testBit c = true ↔
      c < 2048 ∧ ∃ i < m, (actT (dec K) c).testBit i ≠ c.testBit i
  | 0, _ => by simp [diffN]
  | m + 1, hm => by
    have e : diffN XP K (m + 1) = diffN XP K m ||| (outK XP K m ^^^ lnS 2048 XP m) := rfl
    have hout : (outK XP K m).testBit c =
        (decide (c < 2048) && (actT (dec K) c).testBit m) := by
      rw [testBit_actT_dec]
      exact testBit_outN hXP K m c 11 le_rfl
    have hx : (lnS 2048 XP m).testBit c = (decide (c < 2048) && c.testBit m) := by
      rw [hXP m (by omega), planeK_eq]
    rw [e, Nat.testBit_or, Nat.testBit_xor, hout, hx, Bool.or_eq_true,
      testBit_diffN hXP K c m (by omega)]
    by_cases hc : c < 2048
    · simp only [hc, decide_true, Bool.true_and, true_and]
      constructor
      · rintro (⟨i, hi, h⟩ | h)
        · exact ⟨i, by omega, h⟩
        · refine ⟨m, by omega, ?_⟩
          revert h
          cases (actT (dec K) c).testBit m <;> cases c.testBit m <;> simp
      · rintro ⟨i, hi, h⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
        · exact Or.inl ⟨i, hi, h⟩
        · right
          revert h
          cases (actT (dec K) c).testBit i <;> cases c.testBit i <;> simp
    · simp [hc]

theorem fixK_spec {XP : ℕ} (hXP : ∀ j < 11, lnS 2048 XP j = planeK j) (K : ℕ) {c : ℕ}
    (hc : c < 2048) : (fixK XP K).testBit c = true ↔ actT (dec K) c = c := by
  have e : fixK XP K = onesK 2048 ^^^ diffN XP K 11 := rfl
  have hones : (onesK 2048).testBit c = true := by
    rw [testBit_onesK]
    exact decide_eq_true hc
  rw [e, Nat.testBit_xor, hones]
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rcases Nat.lt_or_ge i 11 with hi | hi
    · by_contra hne
      have : (diffN XP K 11).testBit c = true := (testBit_diffN hXP K c 11 le_rfl).mpr ⟨hc, i, hi, hne⟩
      rw [this] at h
      exact absurd h (by decide)
    · rw [testBit_lt 11 (actT_lt (lenOK_dec K) c) hi, testBit_lt 11 (by omega) hi]
  · intro h
    cases hd : (diffN XP K 11).testBit c
    · rfl
    · obtain ⟨-, i, -, hne⟩ := (testBit_diffN hXP K c 11 le_rfl).mp hd
      exact absurd (by rw [h]) hne

end CFSG.KC.J4NP

end
