
module

public import Certificates.Data.Kernel.ExcIns.A8
public import CFSG.Certificates.Kernel.ExcIns.GrowSound
public import CFSG.Certificates.Kernel.ExcIns.WitSound

public section

noncomputable section

namespace CFSG.ExcInsK

open CFSG.ExcExtK CFSG.StandardType.GGQ2Frame.ExcRaw

@[expose] def decA8 (w : KA8) : Chk.A8W where
  b := w.b.toArray
  span := (w.sp.map fun e => (e % 16, e / 16 % 16, decide (e / 256 = 1))).toArray
  cz := w.cz
  hyp := w.hyp.toArray

theorem gramRow_sound {K : KT} {a ba : Nat} : ∀ (b : List Nat) (a' : Nat),
    gramRow K a ba b a' = true → ∀ q < b.length, prK K ba b[q]! = gramL a (a' + q)
  | [], _, _, q, hq => absurd hq (Nat.not_lt_zero q)
  | bb :: b, a', hL, q, hq => by
    have e : gramRow K a ba (bb :: b) a' =
        band (Nat.beq (prK K ba bb) (gramL a a')) (gramRow K a ba b (Nat.succ a')) := rfl
    rw [e, band_eq_true, Nat.beq_eq] at hL
    rcases q with _ | q
    · rw [List.getElem!_cons_zero, Nat.add_zero]
      exact hL.1
    · rw [List.getElem!_cons_succ, show a' + (q + 1) = Nat.succ a' + q by omega]
      exact gramRow_sound b (Nat.succ a') hL.2 q (by simpa using hq)

theorem gramK_sound {K : KT} {b0 : List Nat} : ∀ (b : List Nat) (a : Nat),
    gramK K b0 b a = true → ∀ p < b.length, gramRow K (a + p) b[p]! b0 0 = true
  | [], _, _, p, hp => absurd hp (Nat.not_lt_zero p)
  | ba :: b, a, hL, p, hp => by
    have e : gramK K b0 (ba :: b) a = band (gramRow K a ba b0 0) (gramK K b0 b (Nat.succ a)) := rfl
    rw [e, band_eq_true] at hL
    rcases p with _ | p
    · rw [List.getElem!_cons_zero, Nat.add_zero]
      exact hL.1
    · rw [List.getElem!_cons_succ, show a + (p + 1) = Nat.succ a + p by omega]
      exact gramK_sound b (Nat.succ a) hL.2 p (by simpa using hp)

theorem gramL_eq (a a' : Nat) : (gramL a a' : Int) = Chk.chainGramN a a' + 8 := by
  unfold gramL Chk.chainGramN
  rw [nif_eq, nif_eq, nbeq_eq, bor_eq_or, nbeq_eq, nbeq_eq]
  by_cases h1 : a = a'
  · simp [h1]
  · by_cases h2 : a + 1 = a' ∨ a' + 1 = a
    · rcases h2 with h2 | h2 <;> simp [h1, h2]
    · have h3 : a + 1 ≠ a' := fun e => h2 (Or.inl e)
      have h4 : a' + 1 ≠ a := fun e => h2 (Or.inr e)
      simp [h1, h3, h4]

theorem fold_if_range (n : Nat) (P : Nat → Prop) [DecidablePred P] (g : Nat → Int) :
    Nat.fold n (fun s _ acc => if P s then acc + g s else acc) 0 =
      ∑ s ∈ Finset.range n, if P s then g s else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Nat.fold_succ]
    rw [ih, Finset.sum_range_succ]
    split_ifs <;> simp

theorem chainS_sum (fx D a a' kk : Nat) : ∀ (b : List Nat) (s : Nat),
    (chainS fx D a a' kk b s : Int) = ∑ p ∈ Finset.range b.length,
      if a ≤ s + p ∧ s + p < a' then (qlK fx D b[p]! kk : Int) else 0
  | [], _ => by
    change ((0 : Nat) : Int) = _
    simp
  | bs :: b, s => by
    have e : chainS fx D a a' kk (bs :: b) s =
        Nat.add (nif (band (Nat.ble a s) (Nat.blt s a')) (qlK fx D bs kk) 0)
          (chainS fx D a a' kk b (Nat.succ s)) := rfl
    rw [e, List.length_cons, Finset.sum_range_succ', xk_add, Int.natCast_add,
      chainS_sum fx D a a' kk b (Nat.succ s), nif_eq, band_eq_and, nble_eq, nblt_eq]
    simp only [List.getElem!_cons_succ, List.getElem!_cons_zero, Nat.add_zero, Bool.and_eq_true,
      decide_eq_true_eq]
    rw [add_comm]
    congr 1
    · refine Finset.sum_congr rfl fun p _ => ?_
      rw [show Nat.succ s + p = s + (p + 1) by omega]
    · split_ifs <;> simp

theorem expK_sum (K : KT) (t : Nat) : ∀ (b : List Nat) (a : Nat),
    (expK K t b a : Int) = ∑ p ∈ Finset.range b.length,
      ((a + p + 1 : Nat) : Int) * (prK K t b[p]! : Int)
  | [], _ => by
    change ((0 : Nat) : Int) = _
    simp
  | ba :: b, a => by
    have e : expK K t (ba :: b) a =
        Nat.add (Nat.mul (Nat.succ a) (prK K t ba)) (expK K t b (Nat.succ a)) := rfl
    rw [e, List.length_cons, Finset.sum_range_succ', xk_add, xk_mul, Int.natCast_add,
      Int.natCast_mul, expK_sum K t b (Nat.succ a)]
    simp only [List.getElem!_cons_succ, List.getElem!_cons_zero, Nat.add_zero]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [show Nat.succ a + p + 1 = a + (p + 1) + 1 by omega]

theorem spansFrom_sound {r fx D c : Nat} {b : List Nat} :
    ∀ (sp : List Nat) (i : Nat), spansFrom r fx D c b sp i = true →
      i + sp.length = r ∧ ∀ p (hp : p < sp.length), c.testBit (i + p) = true →
        spanOK fx D (i + p) sp[p] b = true
  | [], i, hL => by
    refine ⟨?_, fun p hp => absurd hp (Nat.not_lt_zero p)⟩
    have e : spansFrom r fx D c b [] i = Nat.beq i r := rfl
    rw [e, Nat.beq_eq] at hL
    simpa using hL
  | e0 :: sp, i, hL => by
    have e : spansFrom r fx D c b (e0 :: sp) i =
        band (bor (bnot (bit c i)) (spanOK fx D i e0 b)) (spansFrom r fx D c b sp (Nat.succ i)) := rfl
    rw [e, band_eq_true] at hL
    obtain ⟨h1, h2⟩ := spansFrom_sound sp (Nat.succ i) hL.2
    refine ⟨by simp only [List.length_cons]; omega, fun p hp hc => ?_⟩
    rcases p with _ | p
    · have h0 := hL.1
      rw [Nat.add_zero] at hc
      rw [bor_iff, bnot_eq, bit_eq, hc] at h0
      rcases h0 with h0 | h0
      · exact absurd h0 (by decide)
      · simpa using h0
    · have := h2 p (by simpa using hp) (by rw [show Nat.succ i + p = i + (p + 1) by omega]; exact hc)
      rw [show i + (p + 1) = Nat.succ i + p by omega]
      simpa using this

theorem hypFrom_sound {K : KT} {d r c cz : Nat} :
    ∀ (hyp : List (Nat × List (Nat × Nat))) (k : Nat), hypFrom K d r c cz hyp k = true →
      k + hyp.length = d ∧ ∀ p (hp : p < hyp.length), hyp[p].1 < 3 ∧ coefOK r c hyp[p].2 = true ∧
        ∀ k' < d, (coefSum K k' hyp[p].2 + 2 * ((nif (Nat.beq (k + p) k') 1 0 +
          (3 - hyp[p].1) * digK cz k') % 3)) % 3 = 0
  | [], k, hL => by
    refine ⟨?_, fun p hp => absurd hp (Nat.not_lt_zero p)⟩
    have e : hypFrom K d r c cz [] k = Nat.beq k d := rfl
    rw [e, Nat.beq_eq] at hL
    simpa using hL
  | (x, coef) :: hyp, k, hL => by
    have e : hypFrom K d r c cz ((x, coef) :: hyp) k =
        band (band (Nat.blt x 3) <| band (coefOK r c coef) <|
          allN d fun k' => Nat.beq (Nat.mod (Nat.add (coefSum K k' coef)
            (Nat.mul 2 (Nat.mod (Nat.add (nif (Nat.beq k k') 1 0) (Nat.mul (Nat.sub 3 x) (digK cz k')))
              3))) 3) 0) (hypFrom K d r c cz hyp (Nat.succ k)) := rfl
    rw [e, band_eq_true] at hL
    obtain ⟨h1, h2⟩ := hypFrom_sound hyp (Nat.succ k) hL.2
    refine ⟨by simp only [List.length_cons]; omega, fun p hp => ?_⟩
    rcases p with _ | p
    · have h0 := hL.1
      rw [band_eq_true, band_eq_true, Nat.blt_eq, allN_iff] at h0
      refine ⟨h0.1, h0.2.1, fun k' hk' => ?_⟩
      have := h0.2.2 k' hk'
      rw [Nat.beq_eq] at this
      rw [Nat.add_zero]
      exact this
    · have := h2 p (by simpa using hp)
      rw [show k + (p + 1) = Nat.succ k + p by omega]
      simpa using this

theorem coefOK_sound {r c : Nat} : ∀ {coef : List (Nat × Nat)}, coefOK r c coef = true →
    ∀ e ∈ coef, e.1 < r ∧ c.testBit e.1 = true
  | [], _, e, he => by simp at he
  | (i, a) :: coef, h, e, he => by
    have e1 : coefOK r c ((i, a) :: coef) = band (band (Nat.blt i r) (bit c i)) (coefOK r c coef) := rfl
    rw [e1, band_eq_true, band_eq_true, Nat.blt_eq, bit_eq] at h
    rcases List.mem_cons.mp he with rfl | he
    · exact h.1
    · exact coefOK_sound h.2 e he

theorem coefSum_dvd {m : Fin 6} {K : KT} {fx hx fx' hx' : Nat} (h : TabsOK m K fx hx fx' hx')
    {k' : Nat} (hk' : k' < dim m) : ∀ (coef : List (Nat × Nat)) (s : Int),
    (∀ e ∈ coef, e.1 < nroots m) →
    (3 : Int) ∣ (s + (coefSum K k' coef : Int)) -
      coef.foldl (fun s e => s + (e.2 : Int) * ((tabsK m K).h[e.1]!)[k']!) s
  | [], s, _ => by
    change (3 : Int) ∣ (s + ((0 : Nat) : Int)) - s
    simp
  | (i, a) :: coef, s, hc => by
    have e : coefSum K k' ((i, a) :: coef) = Nat.add (coefSum K k' coef) (Nat.mul a (hK K i k')) := rfl
    have hi : i < nroots m := hc (i, a) (by simp)
    have ih := coefSum_dvd h hk' coef (s + (a : Int) * ((tabsK m K).h[i]!)[k']!)
      (fun e he => hc e (List.mem_cons_of_mem _ he))
    rw [List.foldl_cons, e, xk_add, xk_mul, Int.natCast_add, Int.natCast_mul]
    have hd := hK_dvd h hi hk'
    rw [← tabsK_h hi hk'] at hd
    obtain ⟨q1, hq1⟩ := ih
    obtain ⟨q2, hq2⟩ := hd
    exact ⟨q1 + (a : Int) * q2, by rw [Int.mul_add, ← hq1, Int.mul_left_comm, ← hq2]; ring⟩

theorem ofDigits_succ (f : Nat → Nat) (d : Nat) :
    Chk.ofDigits (d + 1) f = Chk.ofDigits d f + f d % 3 * 3 ^ d := by
  simp only [Chk.ofDigits, Nat.fold_succ]

theorem ofDigits_lt (f : Nat → Nat) : ∀ d, Chk.ofDigits d f < 3 ^ d
  | 0 => by simp [Chk.ofDigits]
  | d + 1 => by
    rw [ofDigits_succ, pow_succ]
    have h1 := ofDigits_lt f d
    have h2 : f d % 3 ≤ 2 := by omega
    have h3 : f d % 3 * 3 ^ d ≤ 2 * 3 ^ d := Nat.mul_le_mul_right _ h2
    omega

theorem dig_ofDigits (f : Nat → Nat) : ∀ d j, j < d → Chk.dig (Chk.ofDigits d f) j = f j % 3
  | 0, j, hj => absurd hj (Nat.not_lt_zero j)
  | d + 1, j, hj => by
    rw [Chk.dig, ofDigits_succ]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · have hp : f d % 3 * 3 ^ d = 3 ^ j * (3 * (f d % 3 * 3 ^ (d - j - 1))) := by
        rw [show d = j + (d - j - 1) + 1 by omega, pow_succ, pow_add]
        rw [show j + (d - j - 1) + 1 - j - 1 = d - j - 1 by omega]
        ring
      rw [hp, Nat.add_mul_div_left _ _ (Nat.pow_pos (by decide : 0 < 3)), Nat.add_mul_mod_self_left]
      exact dig_ofDigits f d j hj
    · rw [Nat.add_mul_div_right _ _ (Nat.pow_pos (by decide : 0 < 3)),
        Nat.div_eq_of_lt (ofDigits_lt f j), Nat.zero_add, Nat.mod_mod]

theorem dig_pow3 (k k' : Nat) : Chk.dig (3 ^ k) k' = if k = k' then 1 else 0 := by
  rw [Chk.dig]
  rcases Nat.lt_trichotomy k k' with hk | rfl | hk
  · rw [if_neg (by omega), Nat.div_eq_of_lt (Nat.pow_lt_pow_right (by decide) hk)]
  · rw [if_pos rfl, Nat.div_self (Nat.pow_pos (by decide : 0 < 3))]
  · rw [if_neg (by omega), show k = k' + (k - k' - 1) + 1 by omega, pow_succ, pow_add,
      Nat.mul_assoc, Nat.mul_div_cancel_left _ (Nat.pow_pos (by decide : 0 < 3)), Nat.mul_mod_left]

theorem a8K_sound {m : Fin 6} {K : KT} {fx hx fx' hx' : Nat} (h : TabsOK m K fx hx fx' hx')
    {c : Nat} {w : KA8} (hs : a8K K fx' (dim (pairMode m)) (dim m) c w = true) :
    Chk.a8OK (tabsK m K) (dim m) (nroots m) (dim (pairMode m)) (Qarr m) c (decA8 w) = true := by
  have hs' := hs
  unfold a8K at hs'
  simp only [band_eq_true] at hs'
  obtain ⟨hlen, hb, hgram, hspan, hcz, hexp, hhyp⟩ := hs'
  rw [Nat.beq_eq, lenK_eq] at hlen
  rw [Nat.blt_eq, xk_pow] at hcz
  have hbget : ∀ a, (decA8 w).b[a]! = w.b[a]! := fun _ => List.getElem!_toArray
  have hbmem : ∀ a < 8, w.b[a]! < nroots m ∧ c.testBit w.b[a]! = true := by
    intro a ha
    have hmem : w.b[a]! ∈ w.b := by
      rw [getElem!_pos w.b a (by omega)]
      exact List.getElem_mem (by omega)
    rw [← h.hr]
    exact bOK_sound hb _ hmem
  have hQ : ∀ i kk, i < nroots m → kk < dim (pairMode m) →
      ((Qarr m)[i]!)[kk]! = (qlK fx' (dim (pairMode m)) i kk : Int) - 8 := by
    intro i kk hi hkk
    rw [Qarr, getElem!_map_range _ hi, getElem!_map_range _ hkk, fN'_eq h hi hkk]
    rfl
  have hpair : ∀ i j, i < nroots m → j < nroots m →
      ((tabsK m K).pair[i]!)[j]! = (prK K i j : Int) - 8 := by
    intro i j hi hj
    rw [tabsK_pair hi hj, prK_eq h hi hj]
    ring
  obtain ⟨hsplen, hsp⟩ := spansFrom_sound w.sp 0 hspan
  rw [Nat.zero_add, h.hr] at hsplen
  obtain ⟨hhlen, hhy⟩ := hypFrom_sound w.hyp 0 hhyp
  rw [Nat.zero_add] at hhlen
  simp only [Chk.a8OK, Bool.and_eq_true, hbget]
  refine ⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [ExcExtK.nat_all_iff]
    intro a ha
    obtain ⟨h1, h2⟩ := hbmem a ha
    rw [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨h1, h2⟩
  · rw [ExcExtK.nat_all_iff]
    intro a ha
    rw [ExcExtK.nat_all_iff]
    intro a' ha'
    have hr := gramRow_sound w.b 0 (gramK_sound w.b 0 hgram a (by omega)) a' (by omega)
    rw [Nat.zero_add, Nat.zero_add] at hr
    rw [beq_iff_eq, hpair _ _ (hbmem a ha).1 (hbmem a' ha').1, hr, gramL_eq]
    ring
  · rw [ExcExtK.nat_all_iff]
    intro i hi
    by_cases hc : c.testBit i = true
    · rw [hc, Bool.not_true, Bool.false_or]
      have hin : i < w.sp.length := by omega
      have hS := hsp i hin (by rw [Nat.zero_add]; exact hc)
      rw [Nat.zero_add, ← getElem!_pos w.sp i hin] at hS
      have hspan_eq : (decA8 w).span[i]! =
          (w.sp[i]! % 16, w.sp[i]! / 16 % 16, decide (w.sp[i]! / 256 = 1)) := by
        change (w.sp.map fun e => (e % 16, e / 16 % 16, decide (e / 256 = 1))).toArray[i]! = _
        rw [List.getElem!_toArray, getElem!_pos _ i (by simpa using hin), List.getElem_map,
          getElem!_pos w.sp i hin]
      rw [hspan_eq]
      generalize w.sp[i]! = e at hS
      unfold spanOK at hS
      simp only [band_eq_true, Nat.blt_eq, Nat.ble_eq, allN_iff, xk_mod, xk_div] at hS
      obtain ⟨-, hlt, hle, hk⟩ := hS
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨⟨hlt, hle⟩, ?_⟩
      rw [ExcExtK.nat_all_iff]
      intro kk hkk
      have hkk' := hk kk hkk
      rw [beq_iff_eq, hQ i kk hi hkk, Chk.chainSumN, fold_if_range]
      simp only [hbget]
      have hcs := chainS_sum fx' (dim (pairMode m)) (e % 16) (e / 16 % 16) kk w.b 0
      simp only [Nat.zero_add] at hcs
      rw [hlen] at hcs
      have hsum : (∑ s ∈ Finset.range 8, if e % 16 ≤ s ∧ s < e / 16 % 16 then
            ((Qarr m)[w.b[s]!]!)[kk]! else 0) =
          (chainS fx' (dim (pairMode m)) (e % 16) (e / 16 % 16) kk w.b 0 : Int) -
            8 * ((e / 16 % 16 - e % 16 : Nat) : Int) := by
        rw [hcs]
        have hcnt : ∀ n, n ≤ 8 → (∑ s ∈ Finset.range n, if e % 16 ≤ s ∧ s < e / 16 % 16 then
            ((Qarr m)[w.b[s]!]!)[kk]! else 0) =
            (∑ s ∈ Finset.range n, if e % 16 ≤ s ∧ s < e / 16 % 16 then
              (qlK fx' (dim (pairMode m)) w.b[s]! kk : Int) else 0) -
            8 * ((min n (e / 16 % 16) - min n (e % 16) : Nat) : Int) := by
          intro n
          induction n with
          | zero => simp
          | succ n ih =>
            intro hn
            rw [Finset.sum_range_succ, Finset.sum_range_succ, ih (by omega)]
            split_ifs with hs
            · rw [hQ _ _ (hbmem n (by omega)).1 hkk]
              have : ((min (n + 1) (e / 16 % 16) - min (n + 1) (e % 16) : Nat) : Int) =
                  ((min n (e / 16 % 16) - min n (e % 16) : Nat) : Int) + 1 := by omega
              rw [this]
              ring
            · have : ((min (n + 1) (e / 16 % 16) - min (n + 1) (e % 16) : Nat) : Int) =
                  ((min n (e / 16 % 16) - min n (e % 16) : Nat) : Int) := by omega
              rw [this]
              ring
        rw [hcnt 8 le_rfl]
        congr 3
        omega
      rw [hsum]
      generalize chainS fx' (dim (pairMode m)) (e % 16) (e / 16 % 16) kk w.b 0 = S at hkk'
      generalize qlK fx' (dim (pairMode m)) i kk = q at hkk'
      by_cases hneg : e / 256 = 1
      · have hn : Nat.beq (e / 256) 1 = true := by
          rw [nbeq_eq]
          simpa using hneg
        rw [hn] at hkk'
        change Nat.beq (q + S) (8 + 8 * (e / 16 % 16 - e % 16)) = true at hkk'
        rw [Nat.beq_eq] at hkk'
        rw [if_pos hneg]
        omega
      · have hn : Nat.beq (e / 256) 1 = false := by
          rw [nbeq_eq]
          simpa using hneg
        rw [hn] at hkk'
        change Nat.beq (q + 8 * (e / 16 % 16 - e % 16)) (S + 8) = true at hkk'
        rw [Nat.beq_eq] at hkk'
        rw [if_neg hneg]
        omega
    · rw [Bool.not_eq_true] at hc
      rw [hc]
      rfl
  · exact decide_eq_true hcz
  · rw [ExcExtK.nat_all_iff]
    intro t ht
    have hX := allN_iff.mp hexp t (by rw [h.hr]; exact ht)
    unfold expT at hX
    rw [band_eq_true, Nat.beq_eq, Nat.beq_eq] at hX
    have hce : Chk.chainExpN (tabsK m K) (decA8 w).b t = (expK K t w.b 0 : Int) - 288 := by
      change Chk.chainExpN (tabsK m K) w.b.toArray t = _
      rw [Chk.chainExpN, fold_range, expK_sum, hlen]
      have hterm : ∀ a ∈ Finset.range 8, ((a + 1 : Nat) : Int) *
          ((tabsK m K).pair[t]!)[w.b.toArray[a]!]! =
          ((0 + a + 1 : Nat) : Int) * (prK K t w.b[a]! : Int) - 8 * ((a + 1 : Nat) : Int) := by
        intro a ha
        rw [List.getElem!_toArray (xs := w.b), hpair _ _ ht (hbmem a (Finset.mem_range.mp ha)).1,
          Nat.zero_add]
        ring
      rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← Finset.mul_sum]
      simp [Finset.sum_range_succ]
    have hev : (3 : Int) ∣ (evK K t w.cz : Int) - Chk.evA (tabsK m K) (dim m) t w.cz := by
      have key : (3 : Int) ∣ ((sumN (dim m) fun k => Nat.mul (fK K t k) (digK w.cz k) : Nat) : Int) -
          Nat.fold (dim m) (fun k _ s => s + ((tabsK m K).f[t]!)[k]! * (Chk.dig w.cz k : Int)) 0 := by
        rw [sumN_cast]
        apply fold_dvd
        intro k hk
        rw [tabsK_f ht hk]
        exact dvd_term (fK_dvd h ht hk)
      unfold evK Chk.evA
      rw [h.hd]
      generalize (sumN (dim m) fun k => Nat.mul (fK K t k) (digK w.cz k)) = S at key ⊢
      generalize Nat.fold (dim m) (fun k _ s => s + ((tabsK m K).f[t]!)[k]! * (Chk.dig w.cz k : Int)) 0
        = F at key ⊢
      change (3 : Int) ∣ ((S % 3 : Nat) : Int) - F % 3
      omega
    have hevA : 0 ≤ Chk.evA (tabsK m K) (dim m) t w.cz ∧ Chk.evA (tabsK m K) (dim m) t w.cz < 3 := by
      unfold Chk.evA
      omega
    have hevK : evK K t w.cz < 3 := Nat.mod_lt _ (by decide)
    have hczd : (decA8 w).cz = w.cz := rfl
    rw [hce, hczd, Bool.and_eq_true, beq_iff_eq, beq_iff_eq]
    generalize expK K t w.b 0 = X at hX ⊢
    generalize evK K t w.cz = E at hX hev hevK
    generalize Chk.evA (tabsK m K) (dim m) t w.cz = A at hev hevA ⊢
    simp only [xk_mod, xk_div] at hX
    omega
  · rw [ExcExtK.nat_all_iff]
    intro k hk
    have hkl : k < w.hyp.length := by omega
    obtain ⟨hx, hco, hid⟩ := hhy k hkl
    rw [Nat.zero_add] at hid
    have hget : (decA8 w).hyp[k]! = w.hyp[k] := by
      change w.hyp.toArray[k]! = _
      rw [List.getElem!_toArray, getElem!_pos w.hyp k hkl]
    rw [hget, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨hx, ?_⟩
    have hcm := coefOK_sound hco
    rw [Chk.inOK, Bool.and_eq_true, List.all_eq_true]
    refine ⟨fun e he => ?_, ?_⟩
    · obtain ⟨h1, h2⟩ := hcm e he
      rw [Bool.and_eq_true, decide_eq_true_eq, ← h.hr]
      exact ⟨h1, h2⟩
    · rw [ExcExtK.nat_all_iff]
      intro k' hk'
      have hi := hid k' hk'
      have hd := coefSum_dvd h hk' w.hyp[k].2 0 (fun e he => by rw [← h.hr]; exact (hcm e he).1)
      have hczd : (decA8 w).cz = w.cz := rfl
      rw [beq_iff_eq, Chk.combN, dig_ofDigits _ _ _ hk', dig_pow3, hczd]
      rw [nif_eq, nbeq_eq] at hi
      simp only [Int.zero_add] at hd
      generalize w.hyp[k].2.foldl (fun s e => s + (e.2 : Int) * ((tabsK m K).h[e.1]!)[k']!) 0 = F
        at hd ⊢
      generalize coefSum K k' w.hyp[k].2 = S at hd hi
      have hdg : Chk.dig w.cz k' < 3 := Nat.mod_lt _ (by decide)
      have hdg' : digK w.cz k' = Chk.dig w.cz k' := rfl
      rw [hdg'] at hi
      generalize Chk.dig w.cz k' = g at hi hdg ⊢
      generalize w.hyp[k].1 = x at hi hx ⊢
      by_cases hkk : k = k'
      · simp only [hkk, beq_self_eq_true, if_true] at hi ⊢
        interval_cases x <;> interval_cases g <;> omega
      · have hkk2 : (k == k') = false := by simpa using hkk
        simp only [hkk, hkk2, if_false, Bool.false_eq_true] at hi ⊢
        interval_cases x <;> interval_cases g <;> omega

theorem imgsFrom_sound {K : KT} {AP n c : Nat} :
    ∀ (img : List Nat) (u : Nat), imgsFrom K AP n c img u = true →
      ∀ v, u ≤ v → v < 8 → ∃ idx < n, ln128 AP idx = imgK (rowK K v) K.r c
  | [], u, hL, v, hv, hv8 => by
    have e : imgsFrom K AP n c [] u = Nat.beq u 8 := rfl
    rw [e, Nat.beq_eq] at hL
    omega
  | idx :: img, u, hL, v, hv, hv8 => by
    have e : imgsFrom K AP n c (idx :: img) u =
        band (band (Nat.blt idx n) (Nat.beq (ln128 AP idx) (imgK (rowK K u) K.r c)))
          (imgsFrom K AP n c img (Nat.succ u)) := rfl
    rw [e, band_eq_true, band_eq_true, Nat.blt_eq, Nat.beq_eq] at hL
    rcases Nat.eq_or_lt_of_le hv with rfl | hv
    · exact ⟨idx, hL.1.1, hL.1.2⟩
    · exact imgsFrom_sound img (Nat.succ u) hL.2 v hv hv8

theorem chunkK_sound {K : KT} {fx D d AP n hi : Nat} :
    ∀ (L : List KA8R) (i : Nat), chunkK K fx D d AP n hi L i = true →
      i + L.length = hi ∧ ∀ p (hp : p < L.length), recA K fx D d AP n (i + p) L[p] = true
  | [], i, hL => by
    refine ⟨?_, fun p hp => absurd hp (Nat.not_lt_zero p)⟩
    have e : chunkK K fx D d AP n hi [] i = Nat.beq i hi := rfl
    rw [e, Nat.beq_eq] at hL
    simpa using hL
  | x :: L, i, hL => by
    have e : chunkK K fx D d AP n hi (x :: L) i =
        band (recA K fx D d AP n i x) (chunkK K fx D d AP n hi L (Nat.succ i)) := rfl
    rw [e, band_eq_true] at hL
    obtain ⟨h1, h2⟩ := chunkK_sound L (Nat.succ i) hL.2
    refine ⟨by simp only [List.length_cons]; omega, fun p hp => ?_⟩
    rcases p with _ | p
    · simpa using hL.1
    · have := h2 p (by simpa using hp)
      rw [show i + (p + 1) = Nat.succ i + p by omega]
      simpa using this

theorem chunk_facts {m : Fin 6} {K : KT} {fx hx fx' hx' : Nat} (h : TabsOK m K fx hx fx' hx')
    {AP n lo hi : Nat} {L : List KA8R}
    (hL : chunkK K fx' (dim (pairMode m)) (dim m) AP n hi L lo = true) :
    ∀ i, lo ≤ i → i < hi → Nonempty (A8Witness m (ofMask m (ln128 AP i))) ∧
      ∀ u : Root m, u.val < 8 → ∃ idx < n,
        ln128 AP idx = Chk.imgN (tabsK m K) (nroots m) u.val (ln128 AP i) := by
  obtain ⟨hlen, hall⟩ := chunkK_sound L lo hL
  intro i h1 h2
  have hp : i - lo < L.length := by omega
  have hr := hall (i - lo) hp
  rw [Nat.add_sub_cancel' h1] at hr
  have e : recA K fx' (dim (pairMode m)) (dim m) AP n i L[i - lo] =
      band (a8K K fx' (dim (pairMode m)) (dim m) (ln128 AP i) L[i - lo].w)
        (imgsFrom K AP n (ln128 AP i) L[i - lo].img 0) := rfl
  rw [e, band_eq_true] at hr
  refine ⟨nonempty_a8Witness_of_a8OK (tabsOK_tabsK h) (factorOK_tabsK m K) (a8K_sound h hr.1),
    fun u hu => ?_⟩
  obtain ⟨idx, hidx, he⟩ := imgsFrom_sound _ 0 hr.2 u.val (Nat.zero_le _) hu
  refine ⟨idx, hidx, ?_⟩
  have hw := wordK_eq h [u.val] (by simp) (ln128 AP i)
  rw [he]
  exact hw

end CFSG.ExcInsK

end
