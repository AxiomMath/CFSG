module

public import CFSG.Certificates.Kernel.Fi22Snd.Rows
public import CFSG.Certificates.Kernel.Fi22Snd.AdjBfs
public import Certificates.Data.CFSGNative.FischerOddCore.Checks

public section

namespace CFSG.KC.Fi22Snd

open CFSG.KC.Enum CFSG.KC.N3153 CFSG.KS CFSG.KS.Raw CFSG.Certificates.Native
open CFSG.Monster.B.Co2.Native CFSG.Sporadic.FischerOddCore.Native

theorem packSum_lt {w : Nat} {g : Nat → Nat} :
    ∀ m, (∀ v < m, g v < 2 ^ w) → ∑ v ∈ Finset.range m, g v * 2 ^ (w * v) < 2 ^ (w * m)
  | 0, _ => by simp
  | m + 1, hg => by
    rw [Finset.sum_range_succ]
    have h1 := packSum_lt m fun v hv => hg v (by omega)
    have h2 := hg m (by omega)
    calc _ < 2 ^ (w * m) + g m * 2 ^ (w * m) := Nat.add_lt_add_right h1 _
      _ = (g m + 1) * 2 ^ (w * m) := by ring
      _ ≤ 2 ^ w * 2 ^ (w * m) := Nat.mul_le_mul_right _ h2
      _ = 2 ^ (w * (m + 1)) := by rw [← pow_add]; ring_nf

theorem packSum_get {w : Nat} {g : Nat → Nat} :
    ∀ m, (∀ v < m, g v < 2 ^ w) → ∀ u,
      (∑ v ∈ Finset.range m, g v * 2 ^ (w * v)) / 2 ^ (w * u) % 2 ^ w = if u < m then g u else 0
  | 0, _, u => by simp
  | m + 1, hg, u => by
    have hg' : ∀ v < m, g v < 2 ^ w := fun v hv => hg v (by omega)
    have hlt := packSum_lt m hg'
    have ih := packSum_get m hg' u
    rw [Finset.sum_range_succ]
    rcases Nat.lt_trichotomy u m with hu | rfl | hu
    · obtain ⟨j, rfl⟩ : ∃ j, m = u + 1 + j := ⟨m - u - 1, by omega⟩
      have e : g (u + 1 + j) * 2 ^ (w * (u + 1 + j)) =
          2 ^ (w * u) * (2 ^ w * (g (u + 1 + j) * 2 ^ (w * j))) := by
        rw [show w * (u + 1 + j) = w * u + (w + w * j) by ring, pow_add, pow_add]
        ring
      rw [e, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.add_mul_mod_self_left, ih,
        if_pos (by omega), if_pos (by omega)]
    · rw [Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hlt, Nat.zero_add,
        Nat.mod_eq_of_lt (hg u (by omega)), if_pos (by omega)]
    · have hlt' := packSum_lt (m + 1) hg
      rw [Finset.sum_range_succ] at hlt'
      rw [Nat.div_eq_of_lt (lt_of_lt_of_le hlt' (Nat.pow_le_pow_right (by norm_num)
        (Nat.mul_le_mul_left _ (by omega)))), Nat.zero_mod, if_neg (by omega)]

theorem cget_eq (C v : Nat) : cget C v = C / 2 ^ (64 + 32 * v) % 2 ^ 32 :=
  CFSG.KS.Raw.Orb.fld_eq C (64 + 32 * v) 32

theorem cget_packed {n : Nat} {f : Nat → Nat} (hn : n < 2 ^ 64) (hf : ∀ v < n, f v < 2 ^ 32)
    (u : Nat) :
    cget (∑ v ∈ Finset.range n, (f v * 2 ^ (64 + 32 * v) + 1)) u = if u < n then f u else 0 := by
  have e : ∑ v ∈ Finset.range n, (f v * 2 ^ (64 + 32 * v) + 1) =
      n + 2 ^ 64 * ∑ v ∈ Finset.range n, f v * 2 ^ (32 * v) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul, Nat.mul_one,
      Finset.mul_sum, Nat.add_comm]
    congr 1
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [pow_add]
    ring
  rw [cget_eq, e, pow_add, ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _),
    Nat.div_eq_of_lt hn, Nat.zero_add]
  exact packSum_get n hf u

theorem initK_eq (n T : Nat) (pre : List Nat) :
    initK n T pre = ∑ v ∈ Finset.range n, (initVal T pre v * 2 ^ (64 + 32 * v) + 1) := by
  have h := foldN_add (f := fun v a => Nat.add (Nat.add a (Nat.shiftLeft (initVal T pre v)
    (Nat.add (nat_lit 64) (Nat.mul (nat_lit 32) v)))) (nat_lit 1))
    (g := fun v => initVal T pre v * 2 ^ (64 + 32 * v) + 1) (fun v a => by
      change a + initVal T pre v <<< (64 + 32 * v) + 1 = _
      rw [Nat.shiftLeft_eq]
      omega) n 0
  rw [Nat.zero_add] at h
  exact h

theorem stepK_eq (n : Nat) (S : Nat → Nat) (T C : Nat) :
    stepK n S T C = ∑ v ∈ Finset.range n, (newCol T C (accK n S C) v * 2 ^ (64 + 32 * v) + 1) := by
  unfold stepK
  rw [CFSG.KC.Pack.strictN_eq]
  have h := foldN_add (f := fun v a => Nat.add (Nat.add a (Nat.shiftLeft
    (newCol T C (accK n S C) v) (Nat.add (nat_lit 64) (Nat.mul (nat_lit 32) v)))) (nat_lit 1))
    (g := fun v => newCol T C (accK n S C) v * 2 ^ (64 + 32 * v) + 1) (fun v a => by
      change a + newCol T C (accK n S C) v <<< (64 + 32 * v) + 1 = _
      rw [Nat.shiftLeft_eq]
      omega) n 0
  rw [Nat.zero_add] at h
  exact h

theorem accK_eq (n : Nat) (S : Nat → Nat) (C : Nat) :
    accK n S C = ∑ w ∈ Finset.range n, hcK (cget C w) * S w := by
  have h := foldN_add (f := fun w a => Nat.add a (Nat.mul (hcK (cget C w)) (S w)))
    (g := fun w => hcK (cget C w) * S w) (fun _ _ => rfl) n 0
  rw [Nat.zero_add] at h
  exact h

theorem hcK_eq (x : Nat) : hcK x = hcol x := by
  unfold hcK
  simp only [CFSG.KC.Pack.strictN_eq]
  rfl

theorem hcol_lt (x : Nat) : hcol x < 2147483629 := Nat.mod_lt _ (by decide)

theorem idxK_eq (pre : List Nat) (v : Nat) :
    idxK pre v = ((pre.idxOf? v).map (· + 1)).getD 0 := by
  induction pre with
  | nil => rfl
  | cons a l ih =>
    change Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat)
      (Nat.add (idxK l v) (nat_lit 1)) (nat_lit 0) (Nat.beq (idxK l v) (nat_lit 0))) (nat_lit 1)
      (Nat.beq a v) = _
    rw [List.idxOf?_cons]
    by_cases hav : a = v
    · subst hav
      rw [Nat.beq_refl]
      simp
    · have h1 : Nat.beq a v = false := Bool.eq_false_iff.2 fun h => hav (Nat.eq_of_beq_eq_true h)
      rw [h1]
      have h2 : (a == v) = false := by simpa using hav
      rw [if_neg (by simp [h2]), ih]
      cases h : l.idxOf? v with
      | none => rfl
      | some j =>
        have : Nat.beq (j + 1) 0 = false := rfl
        simp only [Option.map_some, Option.getD_some]
        rw [this]

theorem idxK_le (pre : List Nat) (v : Nat) : idxK pre v ≤ pre.length := by
  rw [idxK_eq]
  cases h : pre.idxOf? v with
  | none => simp
  | some j =>
    obtain ⟨hj, -⟩ := List.idxOf?_eq_some_iff.1 h
    simp only [Option.map_some, Option.getD_some]
    omega

theorem initVal_lt {T : Nat} {pre : List Nat} (hpre : pre.length < 65536) (v : Nat) :
    initVal T pre v < 2 ^ 32 := by
  have h1 := idxK_le pre v
  have h2 : nIf(Nat.beq (pg (nat_lit 12) (nat_lit 4095) T v) v, nat_lit 1, nat_lit 0) ≤ 1 := by
    cases Nat.beq (pg 12 4095 T v) v <;> decide
  change 2 * idxK pre v + nIf(Nat.beq (pg (nat_lit 12) (nat_lit 4095) T v) v, nat_lit 1,
    nat_lit 0) < 2 ^ 32
  omega

theorem initVal_eq (T : Nat) (pre : List Nat) (v : Nat) :
    initVal T pre v =
      2 * idxK pre v + if pg (nat_lit 12) (nat_lit 4095) T v = v then 1 else 0 := by
  unfold initVal
  cases hb : Nat.beq (pg (nat_lit 12) (nat_lit 4095) T v) v
  · simp [Nat.ne_of_beq_eq_false hb]
  · simp [Nat.eq_of_beq_eq_true hb]

theorem newCol_lt (T C A v : Nat) : newCol T C A v < 2 ^ 32 :=
  lt_trans (Nat.mod_lt _ (by decide)) (by decide)

theorem newCol_eq (T C A v : Nat) :
    newCol T C A v = ((cget C v % 2147483629 * 1000003 +
      cget C (pg (nat_lit 12) (nat_lit 4095) T v) % 2147483629) % 2147483629 * 1000003 +
        A / 2 ^ (128 + 48 * v) % 2 ^ 48) % 2147483629 := by
  have h : Nat.land (Nat.shiftRight A (128 + 48 * v)) 281474976710655 =
      A / 2 ^ (128 + 48 * v) % 2 ^ 48 := CFSG.KS.Raw.Orb.fld_eq A (128 + 48 * v) 48
  unfold newCol
  rw [← h]
  rfl

private theorem list_sum_range (g : Nat → Nat) :
    ∀ m, ((List.range m).map g).sum = ∑ i ∈ Finset.range m, g i
  | 0 => rfl
  | m + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, list_sum_range g m,
      Finset.sum_range_succ]
    simp

section Rows

variable {n d x : Nat} {R M S : Nat → Nat}

theorem row_sum_rg (f : Nat → Nat) :
    ∑ i ∈ Finset.range d, f (rg (R x) i) = ((decodeRow d (R x)).map f).sum := by
  simp only [decodeRow_eq, List.map_map, list_sum_range, Function.comp_apply]

theorem sum_ite_row (hrow : rowOK n d R M S x = true) (f : Nat → Nat) :
    (∑ p ∈ Finset.range n, if p ∈ decodeRow d (R x) then f p else 0) =
      ((decodeRow d (R x)).map f).sum := by
  rw [← Finset.sum_filter]
  have e : (Finset.range n).filter (fun p => p ∈ decodeRow d (R x)) =
      (decodeRow d (R x)).toFinset := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_range, List.mem_toFinset]
    exact ⟨fun h => h.2, fun h => ⟨row_entry_lt hrow h, h⟩⟩
  rw [e, List.sum_toFinset _ (row_pairwise hrow).nodup]

theorem spread_eq (hrow : rowOK n d R M S x = true) :
    S x = x + 1 +
      ∑ p ∈ Finset.range n, if p ∈ decodeRow d (R x) then 2 ^ (128 + 48 * p) else 0 := by
  rw [row_spread hrow, sum_ite_row hrow, ← row_sum_rg]

end Rows

private def nsum (n d : Nat) (R h : Nat → Nat) (p : Nat) : Nat :=
  ∑ w ∈ Finset.range n, if p ∈ decodeRow d (R w) then h w else 0

private theorem nsum_le (n d : Nat) (R h : Nat → Nat) {b : Nat} (hb : ∀ w, h w ≤ b) (p : Nat) :
    nsum n d R h p ≤ n * b := by
  unfold nsum
  calc _ ≤ ∑ _w ∈ Finset.range n, b := Finset.sum_le_sum fun w _ => by
          split_ifs
          · exact hb w
          · exact Nat.zero_le _
    _ = n * b := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

section Acc

variable {n d : Nat} {R M S : Nat → Nat}

private theorem accK_split (hrow : ∀ x < n, rowOK n d R M S x = true) (C : Nat) :
    accK n S C = (∑ w ∈ Finset.range n, hcK (cget C w) * (w + 1)) +
      2 ^ 128 * ∑ p ∈ Finset.range n, nsum n d R (fun w => hcK (cget C w)) p * 2 ^ (48 * p) := by
  have e1 : ∀ w ∈ Finset.range n, hcK (cget C w) * S w = hcK (cget C w) * (w + 1) +
      ∑ p ∈ Finset.range n,
        (if p ∈ decodeRow d (R w) then hcK (cget C w) else 0) * 2 ^ (128 + 48 * p) := by
    intro w hw
    rw [spread_eq (hrow w (Finset.mem_range.1 hw)), Nat.mul_add, Finset.mul_sum]
    refine Nat.add_left_cancel_iff.2 (Finset.sum_congr rfl fun p _ => ?_)
    split_ifs <;> simp
  rw [accK_eq, Finset.sum_congr rfl e1, Finset.sum_add_distrib, Finset.sum_comm, Finset.mul_sum]
  refine Nat.add_left_cancel_iff.2 (Finset.sum_congr rfl fun p _ => ?_)
  rw [← Finset.sum_mul, pow_add]
  unfold nsum
  ring

theorem accK_field (hn : n < 4096) (hrow : ∀ x < n, rowOK n d R M S x = true)
    (hsym : ∀ x < n, ∀ y < n, y ∈ decodeRow d (R x) → x ∈ decodeRow d (R y)) (C : Nat)
    {v : Nat} (hv : v < n) :
    accK n S C / 2 ^ (128 + 48 * v) % 2 ^ 48 =
      ((decodeRow d (R v)).map fun w => hcK (cget C w)).sum := by
  have hh : ∀ w, hcK (cget C w) ≤ 2 ^ 31 := fun w => by
    rw [hcK_eq]
    exact (lt_trans (hcol_lt _) (by norm_num)).le
  have hF : ∀ p < n, nsum n d R (fun w => hcK (cget C w)) p < 2 ^ 48 := fun p _ => by
    have := nsum_le n d R (fun w => hcK (cget C w)) hh p
    omega
  have hL : ∑ w ∈ Finset.range n, hcK (cget C w) * (w + 1) < 2 ^ 128 := by
    calc _ ≤ ∑ _w ∈ Finset.range n, 2 ^ 31 * 4096 := Finset.sum_le_sum fun w hw =>
            Nat.mul_le_mul (hh w) (by have := Finset.mem_range.1 hw; omega)
      _ = n * (2 ^ 31 * 4096) := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
      _ < 2 ^ 128 := by omega
  rw [accK_split hrow C, pow_add, ← Nat.div_div_eq_div_mul,
    Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hL, Nat.zero_add,
    packSum_get n hF v, if_pos hv, nsum, ← sum_ite_row (hrow v hv)]
  refine Finset.sum_congr rfl fun w hw => ?_
  have hw' := Finset.mem_range.1 hw
  by_cases h1 : v ∈ decodeRow d (R w)
  · rw [if_pos h1, if_pos (hsym w hw' v hv h1)]
  · rw [if_neg h1, if_neg fun h2 => h1 (hsym v hv w hw' h2)]

end Acc

section Colour

variable {n d : Nat} {R M S : Nat → Nat}

theorem initT_get {t : Array Nat} {pre : List Nat} {u : Nat} (hu : u < n) :
    (initT n t pre)[u]! = 2 * idxK pre u + if t[u]! = u then 1 else 0 := by
  rw [idxK_eq, initT, getElem!_pos _ _ (by simpa using hu), Array.getElem_ofFn]
  cases h : pre.idxOf? u <;> simp [h]

theorem cget_colourK {k T : Nat} {nbr : Array (List Nat)} {t : Array Nat} {pre : List Nat}
    (hn : n < 4096) (hnbr : nbr = rowsArr n d R) (hrow : ∀ x < n, rowOK n d R M S x = true)
    (hsym : ∀ x < n, ∀ y ∈ nbr[x]!, x ∈ nbr[y]!) (ht : t = unpack n 12 T)
    (hpre : pre.length < 65536) :
    ∀ u, cget (colourK n S T pre k) u = (colourT n nbr t pre k)[u]! := by
  have hsym' : ∀ x < n, ∀ y < n, y ∈ decodeRow d (R x) → x ∈ decodeRow d (R y) := by
    intro x hx y hy h
    have := hsym x hx y (by rw [hnbr, rowsArr_get hx]; exact h)
    rwa [hnbr, rowsArr_get hy] at this
  have htv : ∀ v < n, t[v]! = pg (nat_lit 12) (nat_lit 4095) T v := fun v hv => by
    rw [ht]
    exact unpack12_get hv
  induction k with
  | zero =>
    intro u
    change cget (initK n T pre) u = (initT n t pre)[u]!
    rw [initK_eq, cget_packed (by omega) (fun v _ => initVal_lt hpre v)]
    by_cases hu : u < n
    · rw [if_pos hu, initT_get hu, initVal_eq, htv u hu]
    · rw [if_neg hu, getElem!_neg _ _ (by simpa [initT] using hu)]
      rfl
  | succ k ih =>
    intro u
    have e1 : colourK n S T pre (k + 1) = stepK n S T (colourK n S T pre k) := by
      show strictN (colourK n S T pre k) (fun C => stepK n S T C) = _
      rw [CFSG.KC.Pack.strictN_eq]
    have e2 : colourT n nbr t pre (k + 1) = stepT n nbr t (colourT n nbr t pre k) := rfl
    rw [e1, e2, stepK_eq, cget_packed (by omega) (fun v _ => newCol_lt _ _ _ v)]
    by_cases hu : u < n
    · rw [if_pos hu, stepT, getElem!_pos _ _ (by simpa using hu), Array.getElem_ofFn]
      have hmap : ((decodeRow d (R u)).map fun w => hcK (cget (colourK n S T pre k) w)) =
          (nbr[u]!).map fun w => hcol (colourT n nbr t pre k)[w]! := by
        rw [show nbr[u]! = decodeRow d (R u) by rw [hnbr, rowsArr_get hu]]
        exact List.map_congr_left fun w _ => by rw [hcK_eq, ih w]
      rw [newCol_eq, accK_field hn hrow hsym' _ hu, hmap, ih u,
        ih (pg (nat_lit 12) (nat_lit 4095) T u), ← htv u hu]
      rfl
    · rw [if_neg hu, getElem!_neg _ _ (by simpa [stepT] using hu)]
      rfl

end Colour

private theorem countP_range (p : Nat → Bool) :
    ∀ m, (List.range m).countP p = ∑ i ∈ Finset.range m, if p i = true then 1 else 0
  | 0 => rfl
  | m + 1 => by
    rw [List.range_succ, List.countP_append, countP_range p m, Finset.sum_range_succ]
    cases h : p m <;> simp [h]

theorem cellCnt_eq {n C col : Nat} {c : Array Nat} (hc : ∀ w < n, cget C w = c[w]!) :
    cellCnt n C col = cellCount n c col := by
  have h1 := foldN_add (f := fun w a => nIf(Nat.beq (cget C w) col, Nat.add a (nat_lit 1), a))
    (g := fun w => if cget C w = col then 1 else 0) (fun w a => by
      cases hb : Nat.beq (cget C w) col
      · simp [Nat.ne_of_beq_eq_false hb]
      · simp [Nat.eq_of_beq_eq_true hb]) n 0
  rw [Nat.zero_add] at h1
  rw [cellCnt, h1, cellCount, countP_range]
  refine Finset.sum_congr rfl fun w hw => ?_
  simp only [hc w (Finset.mem_range.1 hw), beq_iff_eq]

theorem injK_facts {n k T P : Nat} {S : Nat → Nat} {pts : List Nat}
    (h : injK n S T pts k P = true) :
    (∀ i < n, rg P i < n) ∧ ∀ i < n - 1,
      cget (colourK n S T pts k) (rg P i) < cget (colourK n S T pts k) (rg P (i + 1)) := by
  unfold injK at h
  rw [CFSG.KC.Pack.strictB_eq] at h
  obtain ⟨h1, h2⟩ := CFSG.KC.Pack.band_iff.1 h
  exact ⟨fun i hi => Nat.le_of_ble_eq_true (CFSG.KC.Pack.allN_spec h1 i hi),
    fun i hi => Nat.le_of_ble_eq_true (CFSG.KC.Pack.allN_spec h2 i hi)⟩

theorem inj_of_order {n : Nat} {c : Array Nat} {π : Nat → Nat} (hlt : ∀ i < n, π i < n)
    (hinc : ∀ i < n - 1, c[π i]! < c[π (i + 1)]!) : ∀ v < n, ∀ w < n, c[v]! = c[w]! → v = w := by
  have hmono : ∀ i j, i < j → j < n → c[π i]! < c[π j]! := by
    intro i j hij hj
    induction j with
    | zero => omega
    | succ j ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h | rfl
      · exact lt_trans (ih h (by omega)) (hinc j (by omega))
      · exact hinc i (by omega)
  have hinjπ : ∀ i < n, ∀ j < n, c[π i]! = c[π j]! → i = j := by
    intro i hi j hj h
    rcases Nat.lt_trichotomy i j with hij | hij | hij
    · exact absurd h (Nat.ne_of_lt (hmono i j hij hj))
    · exact hij
    · exact absurd h (Nat.ne_of_gt (hmono j i hij hi))
  have hl : ((List.range n).map π).Nodup :=
    List.Nodup.map_on (fun i hi j hj h => hinjπ i (List.mem_range.1 hi) j (List.mem_range.1 hj)
      (by rw [h])) List.nodup_range
  have hperm : ((List.range n).map π).Perm (List.range n) :=
    (hl.subperm fun y hy => by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hy
      exact List.mem_range.2 (hlt i (List.mem_range.1 hi))).perm_of_length_le (by simp)
  have honto : ∀ w < n, ∃ i < n, π i = w := fun w hw => by
    obtain ⟨i, hi, e⟩ := List.mem_map.1 (hperm.mem_iff.2 (List.mem_range.2 hw))
    exact ⟨i, List.mem_range.1 hi, e⟩
  intro v hv w hw h
  obtain ⟨i, hi, rfl⟩ := honto v hv
  obtain ⟨j, hj, rfl⟩ := honto w hw
  rw [hinjπ i hi j hj h]

theorem colInj_of_order {n : Nat} {c : Array Nat} {π : Nat → Nat} (hlt : ∀ i < n, π i < n)
    (hinc : ∀ i < n - 1, c[π i]! < c[π (i + 1)]!) : colInj n c = true := by
  have hinj := inj_of_order hlt hinc
  have hnd : ((List.range n).map fun w => c[w]!).Nodup :=
    List.Nodup.map_on (fun v hv w hw h => hinj v (List.mem_range.1 hv) w (List.mem_range.1 hw) h)
      List.nodup_range
  dsimp only [colInj]
  apply strictIncr_of_pairwise
  exact List.sortedLT_iff_pairwise.1 (List.sortedLE_mergeSort.sortedLT_of_nodup
    ((List.mergeSort_perm _ _).nodup_iff.2 hnd))

section Bounds

variable {n d : Nat} {R M S : Nat → Nat}

theorem colInj_of_injK {k T P : Nat} {nbr : Array (List Nat)} {t : Array Nat} {pts : List Nat}
    (hn : n < 4096) (hnbr : nbr = rowsArr n d R) (hrow : ∀ x < n, rowOK n d R M S x = true)
    (hsym : ∀ x < n, ∀ y ∈ nbr[x]!, x ∈ nbr[y]!) (ht : t = unpack n 12 T)
    (hpts : pts.length < 65536) (hinj : injK n S T pts k P = true) :
    colInj n (colourT n nbr t pts k) = true := by
  have hcol := cget_colourK (k := k) hn hnbr hrow hsym ht hpts
  obtain ⟨h1, h2⟩ := injK_facts hinj
  exact colInj_of_order h1 fun i hi => by rw [← hcol, ← hcol]; exact h2 i hi

theorem inj_of_injK {k T P : Nat} {nbr : Array (List Nat)} {t : Array Nat} {pts : List Nat}
    (hn : n < 4096) (hnbr : nbr = rowsArr n d R) (hrow : ∀ x < n, rowOK n d R M S x = true)
    (hsym : ∀ x < n, ∀ y ∈ nbr[x]!, x ∈ nbr[y]!) (ht : t = unpack n 12 T)
    (hpts : pts.length < 65536) (hinj : injK n S T pts k P = true) :
    ∀ v < n, ∀ w < n, (colourT n nbr t pts k)[v]! = (colourT n nbr t pts k)[w]! → v = w := by
  have hcol := cget_colourK (k := k) hn hnbr hrow hsym ht hpts
  obtain ⟨h1, h2⟩ := injK_facts hinj
  exact inj_of_order h1 fun i hi => by rw [← hcol, ← hcol]; exact h2 i hi

theorem bounds_sound' {k T P : Nat} {nbr : Array (List Nat)} {t : Array Nat}
    {pts bounds : List Nat} (hn : n < 4096) (hnbr : nbr = rowsArr n d R)
    (hrow : ∀ x < n, rowOK n d R M S x = true) (hsym : ∀ x < n, ∀ y ∈ nbr[x]!, x ∈ nbr[y]!)
    (ht : t = unpack n 12 T) (hlen : pts.length = bounds.length) (hpts : pts.length < 65536)
    (hcell : ∀ s < pts.length, cellK n S T pts k s (bounds.getD s 0) = true)
    (hinj : injK n S T pts k P = true) :
    boundsOK n nbr t pts bounds k = true := by
  unfold boundsOK
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨hlen, ?_⟩, colInj_of_injK hn hnbr hrow hsym ht hpts hinj⟩
  rw [CFSG.Monster.B.Co2.allLt_iff]
  intro s hs
  have hpre : (pts.take s).length < 65536 := by rw [List.length_take]; omega
  have hcol := cget_colourK (k := k) hn hnbr hrow hsym ht hpre
  have h := hcell s hs
  unfold cellK at h
  rw [CFSG.KC.Pack.strictB_eq] at h
  rw [beq_iff_eq, ← cellCnt_eq (fun w _ => hcol w), ← hcol]
  exact Nat.eq_of_beq_eq_true h

end Bounds

end CFSG.KC.Fi22Snd

end
