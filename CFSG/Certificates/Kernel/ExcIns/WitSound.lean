
module

public import Certificates.Data.Kernel.ExcIns.Wit
public import CFSG.Certificates.Kernel.ExcExt.Sound
public import CFSG.LocalAnalysis.StandardType.GGQ2ExtExcRefl
public import CFSG.LocalAnalysis.StandardType.GGQ2ExcCensusInsideCodeBase

public section

noncomputable section

namespace CFSG.ExcInsK

open CFSG.ExcExtK CFSG.StandardType.GGQ2Frame.ExcRaw

theorem pairing_eq_prK {m : Fin 6} {K : KT} {fx hx fx' hx' : Nat} (h : TabsOK m K fx hx fx' hx')
    (a b : Root m) : pairing m a b = (prK K a.val b.val : ℤ) - 8 := by
  rw [← tabsOK_pair (tabsOK_tabsK h) a b, tabsK_pair a.isLt b.isLt, prK_eq h a.isLt b.isLt]
  ring

theorem sgnOK_sound {m : Fin 6} {K : KT} {fx hx fx' hx' : Nat} (h : TabsOK m K fx hx fx' hx')
    {u s : Nat} (hu : u < nroots m) (hs : sgnOK K u s = true) :
    ∃ ε : Root m → ℤ, (∀ i, ε i = 1 ∨ ε i = -1) ∧ ∀ i j : Root m,
      pairing m (rtR (tabsOK_tabsK h) ⟨u, hu⟩ i) (rtR (tabsOK_tabsK h) ⟨u, hu⟩ j) =
        ε i * ε j * pairing m i j := by
  refine ⟨fun i => if s.testBit i.val then -1 else 1, fun i => by dsimp only; split_ifs <;> simp,
    fun i j => ?_⟩
  dsimp only
  have hrt : ∀ t : Root m, (rtR (tabsOK_tabsK h) ⟨u, hu⟩ t).val = rtK K u t.val :=
    fun t => tabsK_rt hu t.isLt
  have hi : i.val < K.r := by rw [h.hr]; exact i.isLt
  have hj : j.val < K.r := by rw [h.hr]; exact j.isLt
  have hc := allN_iff.mp (allN_iff.mp hs i.val hi) j.val hj
  rw [pairing_eq_prK h, pairing_eq_prK h, hrt, hrt]
  revert hc
  rw [bit_eq, bit_eq]
  cases hsi : s.testBit i.val <;> cases hsj : s.testBit j.val <;> intro hc <;>
    simp only [sgnEq, bnot, Nat.beq_eq, Nat.add_eq, Bool.false_eq_true, if_true, if_false] at hc ⊢ <;>
    omega

theorem sgnsFrom_sound {K : KT} {n : Nat} :
    ∀ (SG : List Nat) (u : Nat), sgnsFrom K SG n u = true →
      u + SG.length = n ∧ ∀ p (hp : p < SG.length), sgnOK K (u + p) SG[p] = true
  | [], u, hL => by
    refine ⟨?_, fun p hp => absurd hp (Nat.not_lt_zero p)⟩
    have e : sgnsFrom K [] n u = Nat.beq u n := rfl
    rw [e, Nat.beq_eq] at hL
    simpa using hL
  | s :: SG, u, hL => by
    have e : sgnsFrom K (s :: SG) n u = band (sgnOK K u s) (sgnsFrom K SG n (Nat.succ u)) := rfl
    rw [e, band_eq_true] at hL
    obtain ⟨h1, h2⟩ := sgnsFrom_sound SG (Nat.succ u) hL.2
    refine ⟨by simp only [List.length_cons]; omega, fun p hp => ?_⟩
    rcases p with _ | p
    · simpa using hL.1
    · have := h2 p (by simpa using hp)
      rw [show u + (p + 1) = Nat.succ u + p by omega]
      simpa using this

theorem pairSigned_of {m : Fin 6} {K : KT} {fx hx fx' hx' : Nat} (h : TabsOK m K fx hx fx' hx')
    {SG : List Nat} {n : Nat} (hS : sgnsFrom K SG n 0 = true) (u : Root m) (hu : u.val < n) :
    ∃ ε : Root m → ℤ, (∀ i, ε i = 1 ∨ ε i = -1) ∧ ∀ i j : Root m,
      pairing m (rtR (tabsOK_tabsK h) u i) (rtR (tabsOK_tabsK h) u j) = ε i * ε j * pairing m i j := by
  obtain ⟨hlen, hall⟩ := sgnsFrom_sound SG 0 hS
  have := hall u.val (by omega)
  rw [Nat.zero_add] at this
  exact sgnOK_sound h u.isLt this

@[expose] def Parr (m : Fin 6) : Array (Array ℤ) :=
  (Array.range (nroots m)).map fun i => (Array.range (dim (pairMode m))).map fun k =>
    Chk.hN (pairMode m) i k

@[expose] def Qarr (m : Fin 6) : Array (Array ℤ) :=
  (Array.range (nroots m)).map fun i => (Array.range (dim (pairMode m))).map fun k =>
    Chk.fN (pairMode m) i k

theorem factorOK_tabsK (m : Fin 6) (K : KT) :
    Chk.factorOK (tabsK m K) (nroots m) (dim (pairMode m)) (Qarr m) (Parr m) = true := by
  rw [Chk.factorOK, ExcExtK.nat_all_iff]
  intro i hi
  rw [ExcExtK.nat_all_iff]
  intro j hj
  rw [beq_iff_eq, tabsK_pair hi hj, pairN_eq, nat_fold_add, nat_fold_add]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Qarr, Parr, getElem!_map_range _ hi, getElem!_map_range _ k.isLt, getElem!_map_range _ hj,
    getElem!_map_range _ k.isLt]

@[expose] def decSat (w : KSat) : Chk.SatW where
  b := w.b.toArray
  e := (w.E : ℤ) - offK
  n := (w.n.map fun row => (row.map fun N => (N : ℤ) - offK).toArray).toArray
  k := w.k.toArray
  B := (Array.range (lenK w.b)).map fun a => (Array.range (lenK w.b)).map fun a' =>
    ((ln2 w.B (8 * a + a') : ℕ) : ℤ)

theorem lenK_eq : ∀ l : List Nat, lenK l = l.length
  | [] => rfl
  | _ :: l => by
    change Nat.succ (lenK l) = _
    rw [lenK_eq l, List.length_cons]

theorem bOK_sound {r c : Nat} : ∀ {b : List Nat}, bOK r c b = true →
    ∀ a ∈ b, a < r ∧ c.testBit a = true
  | [], _, a, ha => by simp at ha
  | x :: b, h, a, ha => by
    have e : bOK r c (x :: b) = band (band (Nat.blt x r) (bit c x)) (bOK r c b) := rfl
    rw [e, band_eq_true, band_eq_true, Nat.blt_eq, bit_eq] at h
    rcases List.mem_cons.mp ha with rfl | ha
    · exact h.1
    · exact bOK_sound h.2 a ha

theorem ltOK_sound {r : Nat} : ∀ {k : List Nat}, ltOK r k = true → ∀ a ∈ k, a < r
  | [], _, a, ha => by simp at ha
  | x :: k, h, a, ha => by
    have e : ltOK r (x :: k) = band (Nat.blt x r) (ltOK r k) := rfl
    rw [e, band_eq_true, Nat.blt_eq] at h
    rcases List.mem_cons.mp ha with rfl | ha
    · exact h.1
    · exact ltOK_sound h.2 a ha

theorem fold_range (n : Nat) (g : Nat → Int) :
    Nat.fold n (fun a _ s => s + g a) 0 = ∑ a ∈ Finset.range n, g a := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Nat.fold_succ]
    rw [ih, Finset.sum_range_succ]

theorem sumL_sum : ∀ row : List Nat,
    (sumL row : Int) = ∑ a ∈ Finset.range row.length, (row[a]! : Int)
  | [] => by
    change ((0 : Nat) : Int) = _
    simp
  | N :: row => by
    have e : sumL (N :: row) = Nat.add N (sumL row) := rfl
    rw [e, List.length_cons, Finset.sum_range_succ', xk_add, Int.natCast_add, sumL_sum row]
    simp only [List.getElem!_cons_succ, List.getElem!_cons_zero]
    ring

theorem sumP_sum (hx D kk : Nat) : ∀ b : List Nat,
    (sumP hx D kk b : Int) = ∑ a ∈ Finset.range b.length, (plK hx D b[a]! kk : Int)
  | [] => by
    change ((0 : Nat) : Int) = _
    simp
  | ba :: b => by
    have e : sumP hx D kk (ba :: b) = Nat.add (plK hx D ba kk) (sumP hx D kk b) := rfl
    rw [e, List.length_cons, Finset.sum_range_succ', xk_add, Int.natCast_add, sumP_sum hx D kk b]
    simp only [List.getElem!_cons_succ, List.getElem!_cons_zero]
    ring

theorem dotK_sum (hx D kk : Nat) : ∀ (row b : List Nat), row.length = b.length →
    (dotK hx D kk row b : Int) =
      ∑ a ∈ Finset.range row.length, (row[a]! : Int) * (plK hx D b[a]! kk : Int)
  | [], _, _ => by
    change ((0 : Nat) : Int) = _
    simp
  | _ :: _, [], h => by simp at h
  | N :: row, ba :: b, h => by
    have e : dotK hx D kk (N :: row) (ba :: b) =
        Nat.add (Nat.mul N (plK hx D ba kk)) (dotK hx D kk row b) := rfl
    rw [e, List.length_cons, Finset.sum_range_succ', xk_add, xk_mul, Int.natCast_add,
      Int.natCast_mul, dotK_sum hx D kk row b (by simpa using h)]
    simp only [List.getElem!_cons_succ, List.getElem!_cons_zero]
    ring

theorem sum_shift (n : Nat) (x y : Nat → Int) (O : Int) :
    ∑ a ∈ Finset.range n, (x a - O) * (y a - 8) =
      ∑ a ∈ Finset.range n, x a * y a - 8 * ∑ a ∈ Finset.range n, x a -
        O * ∑ a ∈ Finset.range n, y a + 8 * O * n := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Finset.sum_range_succ, ih]
    push_cast
    ring

theorem rowsFrom_sound {r hx D E rho c : Nat} {b : List Nat} :
    ∀ (n : List (List Nat)) (i : Nat), rowsFrom r hx D E rho c b n i = true →
      i + n.length = r ∧ ∀ p (hp : p < n.length), c.testBit (i + p) = true →
        lenK n[p] = rho ∧ ∀ kk < D, identK hx D E rho (i + p) kk n[p] b = true
  | [], i, hL => by
    refine ⟨?_, fun p hp => absurd hp (Nat.not_lt_zero p)⟩
    have e : rowsFrom r hx D E rho c b [] i = Nat.beq i r := rfl
    rw [e, Nat.beq_eq] at hL
    simpa using hL
  | row :: n, i, hL => by
    have e : rowsFrom r hx D E rho c b (row :: n) i = band
        (bor (bnot (bit c i)) (band (Nat.beq (lenK row) rho)
          (allN D fun kk => identK hx D E rho i kk row b)))
        (rowsFrom r hx D E rho c b n (Nat.succ i)) := rfl
    rw [e, band_eq_true] at hL
    obtain ⟨h1, h2⟩ := rowsFrom_sound n (Nat.succ i) hL.2
    refine ⟨by simp only [List.length_cons]; omega, fun p hp hc => ?_⟩
    rcases p with _ | p
    · have h0 := hL.1
      rw [Nat.add_zero] at hc
      rw [bor_iff, bnot_eq, bit_eq, hc, band_eq_true, Nat.beq_eq, allN_iff] at h0
      rcases h0 with h0 | h0
      · exact absurd h0 (by decide)
      · simpa using h0
    · have := h2 p (by simpa using hp) (by rw [show Nat.succ i + p = i + (p + 1) by omega]; exact hc)
      rw [show i + (p + 1) = Nat.succ i + p by omega]
      simpa using this

theorem invRow_sum (K : KT) (B a bj : Nat) : ∀ (k : List Nat) (l : Nat),
    (invRow K B a bj k l : Int) = ∑ p ∈ Finset.range k.length,
      (ln2 B (8 * a + (l + p)) : Int) * ((prK K k[p]! bj : Int) + 1)
  | [], _ => by
    change ((0 : Nat) : Int) = _
    simp
  | kl :: k, l => by
    have e : invRow K B a bj (kl :: k) l =
        Nat.add (Nat.mul (ln2 B (Nat.add (Nat.mul 8 a) l)) (Nat.succ (prK K kl bj)))
          (invRow K B a bj k (Nat.succ l)) := rfl
    rw [e, List.length_cons, Finset.sum_range_succ', xk_add, xk_mul, xk_add, xk_mul,
      Int.natCast_add, Int.natCast_mul, invRow_sum K B a bj k (Nat.succ l)]
    simp only [List.getElem!_cons_succ, List.getElem!_cons_zero, Nat.add_zero, Nat.succ_eq_add_one]
    push_cast
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [show l + 1 + p = l + (p + 1) by omega]

theorem invCols_sound {K : KT} {B a : Nat} {k : List Nat} :
    ∀ (b : List Nat) (j : Nat), invCols K B a k b j = true →
      ∀ p < b.length, (invRow K B a b[p]! k 0 + (if a = j + p then 2 else 0)) % 3 = 0
  | [], _, _, p, hp => absurd hp (Nat.not_lt_zero p)
  | bj :: b, j, hL, p, hp => by
    have e : invCols K B a k (bj :: b) j = band
        (Nat.beq (Nat.mod (Nat.add (invRow K B a bj k 0) (nif (Nat.beq a j) 2 0)) 3) 0)
        (invCols K B a k b (Nat.succ j)) := rfl
    rw [e, band_eq_true, Nat.beq_eq] at hL
    rcases p with _ | p
    · have h0 := hL.1
      rw [nif_eq, nbeq_eq, xk_add, xk_mod] at h0
      simpa [beq_iff_eq] using h0
    · have := invCols_sound b (Nat.succ j) hL.2 p (by simpa using hp)
      rw [show j + (p + 1) = Nat.succ j + p by omega]
      simpa using this

theorem flatMap_single_map {α β : Type} (f : α → β) :
    ∀ l : List α, (l.flatMap fun a => [f a]) = l.map f
  | [] => rfl
  | a :: l => by
    rw [List.flatMap_cons, flatMap_single_map f l]
    rfl

theorem satK_sound {m : Fin 6} {K : KT} {fx hx fx' hx' : Nat} (h : TabsOK m K fx hx fx' hx')
    {c : Nat} {w : KSat} (hs : satK K hx' (dim (pairMode m)) c w = true) :
    Chk.satOK (tabsK m K) (nroots m) (dim (pairMode m)) (Parr m) c (decSat w) = true := by
  have hs' := hs
  unfold satK at hs'
  simp only [band_eq_true] at hs'
  obtain ⟨_, hb, hE, hrows, hklen, hk, hinv⟩ := hs'
  rw [Nat.beq_eq, lenK_eq, lenK_eq] at hklen
  have hE' : (w.E + 2) % 3 ≠ 0 := by
    intro h0
    change bnot (Nat.beq ((w.E + 2) % 3) 0) = true at hE
    rw [h0] at hE
    exact absurd hE (by decide)
  have hO : (offK : Int) = 4294967296 := rfl
  have hbs : (decSat w).b.size = w.b.length := by simp [decSat]
  have hbget : ∀ a, (decSat w).b[a]! = w.b[a]! := fun _ => List.getElem!_toArray
  have hkget : ∀ a, (decSat w).k[a]! = w.k[a]! := fun _ => List.getElem!_toArray
  have he : (decSat w).e = (w.E : Int) - offK := rfl
  have hbmem : ∀ a < w.b.length, w.b[a]! < nroots m ∧ c.testBit w.b[a]! = true := by
    intro a ha
    have hmem : w.b[a]! ∈ w.b := by
      rw [getElem!_pos w.b a ha]
      exact List.getElem_mem ha
    rw [← h.hr]
    exact bOK_sound hb _ hmem
  have hkmem : ∀ a < w.b.length, w.k[a]! < nroots m := by
    intro a ha
    have hmem : w.k[a]! ∈ w.k := by
      rw [getElem!_pos w.k a (by omega)]
      exact List.getElem_mem (by omega)
    rw [← h.hr]
    exact ltOK_sound hk _ hmem
  have hP : ∀ i kk, i < nroots m → kk < dim (pairMode m) →
      ((Parr m)[i]!)[kk]! = (plK hx' (dim (pairMode m)) i kk : Int) - 8 := by
    intro i kk hi hkk
    rw [Parr, getElem!_map_range _ hi, getElem!_map_range _ hkk, hN'_eq h hi hkk]
    rfl
  have hn : ∀ i a, i < w.n.length → a < w.n[i]!.length →
      ((decSat w).n[i]!)[a]! = (((w.n[i]!)[a]! : Nat) : Int) - offK := by
    intro i a hi ha
    have e1 : (decSat w).n[i]! = ((w.n[i]!).map fun N : Nat => (N : ℤ) - offK).toArray := by
      change (w.n.map fun row => (row.map fun N => (N : ℤ) - offK).toArray).toArray[i]! = _
      rw [List.getElem!_toArray, getElem!_pos (w.n.map _) i (by simpa using hi), List.getElem_map,
        getElem!_pos w.n i hi]
      congr 1
      simp [flatMap_single_map]
    rw [e1, List.getElem!_toArray,
      getElem!_pos ((w.n[i]!).map fun N : Nat => (N : ℤ) - offK) a (by simpa using ha), List.getElem_map,
      getElem!_pos (w.n[i]!) a ha]
  have hB : ∀ a a', a < w.b.length → a' < w.b.length →
      ((decSat w).B[a]!)[a']! = (ln2 w.B (8 * a + a') : Int) := by
    intro a a' ha ha'
    simp only [decSat]
    rw [getElem!_map_range _ (by rw [lenK_eq]; exact ha), getElem!_map_range _ (by rw [lenK_eq]; exact ha')]
  obtain ⟨hnlen, hR⟩ := rowsFrom_sound w.n 0 hrows
  rw [Nat.zero_add, h.hr] at hnlen
  simp only [Chk.satOK, Bool.and_eq_true, hbs, hbget, hkget]
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [ExcExtK.nat_all_iff]
    intro a ha
    obtain ⟨h1, h2⟩ := hbmem a ha
    rw [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨h1, h2⟩
  · rw [he, hO, bne_iff_ne, ne_eq]
    omega
  · rw [ExcExtK.nat_all_iff]
    intro i hi
    by_cases hc : c.testBit i = true
    · rw [hc, Bool.not_true, Bool.false_or, ExcExtK.nat_all_iff]
      intro kk hkk
      have hin : i < w.n.length := by omega
      obtain ⟨hl, hid⟩ := hR i hin (by rw [Nat.zero_add]; exact hc)
      rw [← getElem!_pos w.n i hin] at hl
      simp only [lenK_eq] at hl
      have hI := hid kk hkk
      rw [← getElem!_pos w.n i hin, Nat.zero_add] at hI
      unfold identK at hI
      rw [Nat.beq_eq] at hI
      simp only [xk_add, xk_mul, lenK_eq] at hI
      zify at hI
      rw [dotK_sum hx' (dim (pairMode m)) kk (w.n[i]!) w.b hl, sumL_sum, sumP_sum, hl] at hI
      rw [beq_iff_eq, hP i kk hi hkk, he, fold_range,
        Finset.sum_congr rfl (g := fun a => ((((w.n[i]!)[a]! : Nat) : Int) - offK) *
          ((plK hx' (dim (pairMode m)) w.b[a]! kk : Int) - 8)) fun a ha => by
            have ha' := Finset.mem_range.mp ha
            rw [hn i a hin (by omega), hP _ _ (hbmem a ha').1 hkk],
        sum_shift]
      simp only [hbs]
      linear_combination -hI
    · rw [Bool.not_eq_true] at hc
      rw [hc]
      rfl
  · rw [ExcExtK.nat_all_iff]
    intro a ha
    exact decide_eq_true (hkmem a ha)
  · rw [Chk.invOK, ExcExtK.nat_all_iff]
    intro a ha
    rw [ExcExtK.nat_all_iff]
    intro j hj
    have hc := invCols_sound w.b 0 (allN_iff.mp hinv a (by rw [lenK_eq]; exact ha)) j hj
    have hj' := hbmem j hj
    have hsum : ((invRow K w.B a w.b[j]! w.k 0 : Nat) : Int) =
        Nat.fold w.b.length (fun l _ s => s + ((decSat w).B[a]!)[l]! *
          ((tabsK m K).pair[w.k[l]!]!)[w.b[j]!]!) 0 +
          9 * ∑ l ∈ Finset.range w.b.length, (ln2 w.B (8 * a + l) : Int) := by
      rw [invRow_sum, fold_range, Finset.mul_sum, ← Finset.sum_add_distrib, ← hklen]
      refine Finset.sum_congr rfl fun l hl => ?_
      have hl' := Finset.mem_range.mp hl
      rw [hB a l ha (by omega), tabsK_pair (hkmem l (by omega)) hj'.1,
        prK_eq h (hkmem l (by omega)) hj'.1, Nat.zero_add]
      ring
    rw [beq_iff_eq]
    generalize Nat.fold w.b.length (fun l _ s => s + ((decSat w).B[a]!)[l]! *
      ((tabsK m K).pair[w.k[l]!]!)[w.b[j]!]!) 0 = S at hsum ⊢
    generalize ∑ l ∈ Finset.range w.b.length, (ln2 w.B (8 * a + l) : Int) = X at hsum
    generalize invRow K w.B a w.b[j]! w.k 0 = R at hc hsum
    by_cases haj : a = j
    · subst haj
      simp only [Nat.zero_add, if_true] at hc ⊢
      omega
    · simp only [Nat.zero_add, haj, if_false] at hc ⊢
      omega

theorem orthK_mask_eq {m : Fin 6} {K : KT} {fx hx fx' hx' : Nat} (h : TabsOK m K fx hx fx' hx')
    {k : Nat} (hk : k < nroots m) :
    ExcInsK.orthK K k = Chk.orthMaskN (tabsK m K) (nroots m) k := by
  rw [ExcInsK.orthK, Chk.orthMaskN, h.hr]
  apply maskK_eq
  intro i hi
  rw [band_eq_and, beq8 (prK_eq h hk hi), beq8 (prK_eq h hi hk), tabsK_pair hk hi, tabsK_pair hi hk]

theorem flagK_sound {m : Fin 6} {K : KT} {fx hx fx' hx' : Nat} (h : TabsOK m K fx hx fx' hx')
    {c k : Nat} (hf : flagK K c k = true) : Chk.flagE6N (tabsK m K) (nroots m) c = true := by
  have e1 : Nat.sub (Nat.shiftLeft 1 K.r) 1 = 2 ^ nroots m - 1 := by
    rw [h.hr]
    change 1 <<< nroots m - 1 = _
    rw [Nat.shiftLeft_eq, Nat.one_mul]
  have e2 : flagK K c k = bor (Nat.beq (Chk.trunc (nroots m) c) (2 ^ nroots m - 1))
      (band (Nat.blt k (nroots m)) (Nat.beq (Chk.trunc (nroots m) c) (ExcInsK.orthK K k))) := by
    rw [flagK, e1, truncK_eq, h.hr]
  rw [e2, bor_iff, band_eq_true, Nat.beq_eq, Nat.blt_eq, Nat.beq_eq] at hf
  rw [Chk.flagE6N, Bool.or_eq_true, beq_iff_eq]
  rcases hf with hf | ⟨hk, hf⟩
  · exact Or.inl hf
  · refine Or.inr ?_
    rw [Nat.any_eq_finRange_any, List.any_eq_true]
    exact ⟨⟨k, hk⟩, List.mem_finRange _, by rw [beq_iff_eq, hf, orthK_mask_eq h hk]⟩

theorem repK_sound {m : Fin 6} {K : KT} {fx hx fx' hx' : Nat} (h : TabsOK m K fx hx fx' hx')
    {e6 : Bool} (he6 : e6 = true → m.val = 2 ∨ m.val = 3) {c : Nat} {x : KRep}
    (hr : repK K hx' (dim (pairMode m)) e6 c x = true) :
    Nonempty (SatWitness m (ofMask m c)) ∨ ((m.val = 2 ∨ m.val = 3) ∧ (ofMask m c = Finset.univ ∨
      ∃ k, ofMask m c = Finset.univ.filter fun i => pairing m k i = 0 ∧ pairing m i k = 0)) := by
  cases x with
  | sat w =>
    exact Or.inl (nonempty_satWitness_of_satOK (tabsOK_tabsK h) (factorOK_tabsK m K)
      (satK_sound h hr))
  | flag k =>
    have e : repK K hx' (dim (pairMode m)) e6 c (.flag k) = band e6 (flagK K c k) := rfl
    rw [e, band_eq_true] at hr
    exact Or.inr ⟨he6 hr.1, flagE6N_sound (tabsOK_tabsK h) (flagK_sound h hr.2)⟩
  | a8 => exact absurd hr Bool.false_ne_true

end CFSG.ExcInsK

end
