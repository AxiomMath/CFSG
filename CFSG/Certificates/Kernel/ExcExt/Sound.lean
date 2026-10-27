module

public import Certificates.Data.CFSGNative.ExcCensus.ExtCore
public import Certificates.Data.Kernel.ExcExt.TabCheck

public section

noncomputable section

namespace CFSG.ExcExtK

open CFSG.StandardType.GGQ2Frame.ExcRaw

@[expose] def tabsK (m : Fin 6) (K : KT) : Chk.Tabs where
  f := (Array.range (nroots m)).map fun i => (Array.range (dim m)).map fun k => Chk.fN m i k
  h := (Array.range (nroots m)).map fun i => (Array.range (dim m)).map fun k => Chk.hN m i k
  pair := (Array.range (nroots m)).map fun i => (Array.range (nroots m)).map fun j => Chk.pairN m i j
  adj := (Array.range (nroots m)).map (adjK K)
  zm := (Array.range (3 ^ dim m)).map (zmK K)
  rt := (Array.range (nroots m)).map fun u => (Array.range (nroots m)).map (rtK K u)

@[expose] def pairMode (m : Fin 6) : Fin 6 := if m.val = 3 then 2 else m

structure TabsOK (m : Fin 6) (K : KT) (fx hx fx' hx' : Nat) : Prop where
  hm : K.m = m.val
  hd : K.d = dim m
  hr : K.r = nroots m
  hF : (tabF m == decI (dim m) (nroots m) fx) = true
  hH : (tabH m == decI (dim m) (nroots m) hx) = true
  hF' : (tabF (pairMode m) == decI (dim (pairMode m)) (nroots m) fx') = true
  hH' : (tabH (pairMode m) == decI (dim (pairMode m)) (nroots m) hx') = true
  hf3 : resOK (dim m * nroots m) fx K.f3 = true
  hh3 : resOK (dim m * nroots m) hx K.h3 = true
  hpair : pairOK K (dim (pairMode m)) fx' hx' = true
  hadj : adjOK K = true
  hzb : zmBoundOK K = true
  hzm : ∀ c < 3 ^ dim m, Nat.beq (zmK K c) (maskK K.r (zBitK K c)) = true
  hrt : rtOK K = true
  hlg : lgOK K tabFix1 = true

theorem band_eq_true {a b : Bool} : band a b = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> decide

theorem allN_iff {n : Nat} {p : Nat → Bool} : allN n p = true ↔ ∀ i < n, p i = true := by
  induction n with
  | zero => exact ⟨fun _ i hi => absurd hi (Nat.not_lt_zero i), fun _ => rfl⟩
  | succ n ih =>
    have e : allN (n + 1) p = band (p n) (allN n p) := rfl
    rw [e, band_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact h2 i hi
      · exact h1
    · intro h
      exact ⟨h n (Nat.lt_succ_self n), fun i hi => h i (by omega)⟩

theorem zm_of_range {K : KT} {lo n : Nat} (h : zmRangeOK K lo n = true) {c : Nat} (h1 : lo ≤ c)
    (h2 : c < lo + n) : Nat.beq (zmK K c) (maskK K.r (zBitK K c)) = true := by
  have h' : ∀ i < n, Nat.beq (zmK K (lo + i)) (maskK K.r (zBitK K (lo + i))) = true :=
    allN_iff.mp h
  have := h' (c - lo) (by omega)
  rwa [Nat.add_sub_of_le h1] at this

theorem zm_all_of_chunks {K : KT} {w q : Nat} (h : ∀ j < q, zmRangeOK K (w * j) w = true) :
    ∀ c < w * q, Nat.beq (zmK K c) (maskK K.r (zBitK K c)) = true := by
  intro c hc
  have hw : 0 < w := Nat.pos_of_ne_zero (by rintro rfl; simp at hc)
  have hj : c / w < q := (Nat.div_lt_iff_lt_mul hw).mpr (by rwa [Nat.mul_comm])
  refine zm_of_range (h (c / w) hj) (Nat.mul_div_le c w) ?_
  have := Nat.lt_mul_div_succ c hw
  rw [Nat.mul_succ] at this
  omega

theorem TabsOK.of_bool {m m' : Fin 6} (hm' : pairMode m = m') {K : KT} {fx hx fx' hx' : Nat}
    (hb : tabBool m.val (dim m) (nroots m) K (tabF m) (tabH m) (tabF m') (tabH m') (dim m') fx hx
      fx' hx' tabFix1 = true)
    (hz : ∀ c < 3 ^ dim m, Nat.beq (zmK K c) (maskK K.r (zBitK K c)) = true) :
    TabsOK m K fx hx fx' hx' := by
  subst hm'
  simp only [tabBool, band_eq_true, Nat.beq_eq] at hb
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := hb
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, hz, h13, h14⟩

theorem nat_all_iff {n : Nat} {f : (i : Nat) → i < n → Bool} :
    Nat.all n f = true ↔ ∀ i (h : i < n), f i h = true := by
  rw [Nat.all_eq_finRange_all, List.all_eq_true]
  constructor
  · intro h i hi
    exact h ⟨i, hi⟩ (List.mem_finRange _)
  · intro h x _
    exact h x.val x.isLt

theorem getElem!_map_range {α : Type} [Inhabited α] {n i : Nat} (g : Nat → α) (h : i < n) :
    ((Array.range n).map g)[i]! = g i := by
  rw [getElem!_pos ((Array.range n).map g) i (by simpa using h)]
  simp

theorem tabsK_f {m : Fin 6} {K : KT} {i k : Nat} (hi : i < nroots m) (hk : k < dim m) :
    (tabsK m K).f[i]![k]! = Chk.fN m i k := by
  simp only [tabsK]
  rw [getElem!_map_range _ hi, getElem!_map_range _ hk]

theorem tabsK_h {m : Fin 6} {K : KT} {i k : Nat} (hi : i < nroots m) (hk : k < dim m) :
    (tabsK m K).h[i]![k]! = Chk.hN m i k := by
  simp only [tabsK]
  rw [getElem!_map_range _ hi, getElem!_map_range _ hk]

theorem tabsK_pair {m : Fin 6} {K : KT} {i j : Nat} (hi : i < nroots m) (hj : j < nroots m) :
    (tabsK m K).pair[i]![j]! = Chk.pairN m i j := by
  simp only [tabsK]
  rw [getElem!_map_range _ hi, getElem!_map_range _ hj]

theorem tabsK_adj {m : Fin 6} {K : KT} {i : Nat} (hi : i < nroots m) :
    (tabsK m K).adj[i]! = adjK K i := by
  simp only [tabsK]
  rw [getElem!_map_range _ hi]

theorem tabsK_zm {m : Fin 6} {K : KT} {c : Nat} (hc : c < 3 ^ dim m) :
    (tabsK m K).zm[c]! = zmK K c := by
  simp only [tabsK]
  rw [getElem!_map_range _ hc]

theorem tabsK_rt {m : Fin 6} {K : KT} {u t : Nat} (hu : u < nroots m) (ht : t < nroots m) :
    (tabsK m K).rt[u]![t]! = rtK K u t := by
  simp only [tabsK]
  rw [getElem!_map_range _ hu, getElem!_map_range _ ht]

theorem xk_add (a b : Nat) : Nat.add a b = a + b := rfl

theorem xk_mul (a b : Nat) : Nat.mul a b = a * b := rfl

theorem xk_mod (a b : Nat) : Nat.mod a b = a % b := rfl

theorem bor_iff {a b : Bool} : bor a b = true ↔ a = true ∨ b = true := by
  cases a <;> cases b <;> decide

theorem bor_eq_or (a b : Bool) : bor a b = (a || b) := by
  cases a <;> rfl

theorem sumN_zero (f : Nat → Nat) : sumN 0 f = 0 := rfl

theorem maskK_eq {n : Nat} {p q : Nat → Bool} (h : ∀ t < n, p t = q t) :
    maskK n p = Chk.maskN n q := by
  induction n with
  | zero =>
    rw [Chk.maskN, Nat.fold_zero]
    rfl
  | succ n ih =>
    have e : maskK (n + 1) p = nif (p n) (Nat.lor (maskK n p) (Nat.shiftLeft 1 n)) (maskK n p) :=
      rfl
    rw [e, ih (fun t ht => h t (by omega)), h n (by omega)]
    simp only [Chk.maskN, Nat.fold_succ]
    cases q n <;> rfl

theorem sumN_cast (n : Nat) (f : Nat → Nat) :
    ((sumN n f : Nat) : Int) = Nat.fold n (fun k _ s => s + (f k : Int)) 0 := by
  induction n with
  | zero =>
    rw [Nat.fold_zero]
    rfl
  | succ n ih =>
    simp only [Nat.fold_succ]
    rw [← ih]
    change ((sumN n f + f n : Nat) : Int) = (sumN n f : Int) + (f n : Int)
    omega

theorem fold_congr {n : Nat} {a b : Nat → Int} (h : ∀ k < n, a k = b k) :
    Nat.fold n (fun k _ s => s + a k) 0 = Nat.fold n (fun k _ s => s + b k) 0 := by
  induction n with
  | zero => simp only [Nat.fold_zero]
  | succ n ih =>
    simp only [Nat.fold_succ]
    rw [ih (fun k hk => h k (by omega)), h n (by omega)]

theorem fold_dvd {n : Nat} {a b : Nat → Int} (h : ∀ k < n, (3 : Int) ∣ a k - b k) :
    (3 : Int) ∣ Nat.fold n (fun k _ s => s + a k) 0 - Nat.fold n (fun k _ s => s + b k) 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Nat.fold_succ]
    have h1 := ih (fun k hk => h k (by omega))
    have h2 := h n (by omega)
    omega

theorem fold_shift8 (n : Nat) (a b : Nat → Nat) :
    Nat.fold n (fun k _ s => s + ((a k : Int) - 8) * ((b k : Int) - 8)) 0 =
      ((sumN n fun k => a k * b k : Nat) : Int) - 8 * ((sumN n a : Nat) : Int) -
        8 * ((sumN n b : Nat) : Int) + 64 * (n : Int) := by
  induction n with
  | zero => simp [sumN_zero]
  | succ n ih =>
    simp only [Nat.fold_succ]
    rw [ih]
    change _ = (((sumN n fun k => a k * b k) + a n * b n : Nat) : Int) -
      8 * ((sumN n a + a n : Nat) : Int) - 8 * ((sumN n b + b n : Nat) : Int) +
        64 * ((n + 1 : Nat) : Int)
    simp only [Int.natCast_add, Int.natCast_mul]
    grind

theorem idx_lt_mul {d r t k : Nat} (ht : t < r) (hk : k < d) : d * t + k < d * r := by
  have : d * (t + 1) ≤ d * r := Nat.mul_le_mul_left d ht
  rw [Nat.mul_succ] at this
  omega

theorem decI_getD {d r x i k : Nat} (hi : i < r) (hk : k < d) :
    ((decI d r x).getD i []).getD k 0 = exI d x i k := by
  simp [decI, List.getD_eq_getElem?_getD, hi, hk]

theorem fN_eq {m : Fin 6} {K : KT} {fx hx fx' hx' : Nat} (h : TabsOK m K fx hx fx' hx') {i k : Nat}
    (hi : i < nroots m) (hk : k < dim m) : Chk.fN m i k = exI (dim m) fx i k := by
  rw [Chk.fN, beq_iff_eq.mp h.hF]
  exact decI_getD hi hk

theorem hN_eq {m : Fin 6} {K : KT} {fx hx fx' hx' : Nat} (h : TabsOK m K fx hx fx' hx') {i k : Nat}
    (hi : i < nroots m) (hk : k < dim m) : Chk.hN m i k = exI (dim m) hx i k := by
  rw [Chk.hN, beq_iff_eq.mp h.hH]
  exact decI_getD hi hk

theorem fN'_eq {m : Fin 6} {K : KT} {fx hx fx' hx' : Nat} (h : TabsOK m K fx hx fx' hx') {i k : Nat}
    (hi : i < nroots m) (hk : k < dim (pairMode m)) :
    Chk.fN (pairMode m) i k = exI (dim (pairMode m)) fx' i k := by
  rw [Chk.fN, beq_iff_eq.mp h.hF']
  exact decI_getD hi hk

theorem hN'_eq {m : Fin 6} {K : KT} {fx hx fx' hx' : Nat} (h : TabsOK m K fx hx fx' hx') {i k : Nat}
    (hi : i < nroots m) (hk : k < dim (pairMode m)) :
    Chk.hN (pairMode m) i k = exI (dim (pairMode m)) hx' i k := by
  rw [Chk.hN, beq_iff_eq.mp h.hH']
  exact decI_getD hi hk

theorem fK_dvd {m : Fin 6} {K : KT} {fx hx fx' hx' : Nat} (h : TabsOK m K fx hx fx' hx') {t k : Nat}
    (ht : t < nroots m) (hk : k < dim m) : (3 : Int) ∣ (fK K t k : Int) - Chk.fN m t k := by
  have e := allN_iff.mp h.hf3 (dim m * t + k) (idx_lt_mul ht hk)
  simp only [Nat.beq_eq] at e
  have e2 : fK K t k = ln2 K.f3 (dim m * t + k) := by
    rw [fK, h.hd]
    rfl
  rw [e2, e, fN_eq h ht hk]
  change (3 : Int) ∣ (((ln4 fx (dim m * t + k) + 1) % 3 : Nat) : Int) -
    ((ln4 fx (dim m * t + k) : Int) - 8)
  omega

theorem hK_dvd {m : Fin 6} {K : KT} {fx hx fx' hx' : Nat} (h : TabsOK m K fx hx fx' hx') {t k : Nat}
    (ht : t < nroots m) (hk : k < dim m) : (3 : Int) ∣ (hK K t k : Int) - Chk.hN m t k := by
  have e := allN_iff.mp h.hh3 (dim m * t + k) (idx_lt_mul ht hk)
  simp only [Nat.beq_eq] at e
  have e2 : hK K t k = ln2 K.h3 (dim m * t + k) := by
    rw [hK, h.hd]
    rfl
  rw [e2, e, hN_eq h ht hk]
  change (3 : Int) ∣ (((ln4 hx (dim m * t + k) + 1) % 3 : Nat) : Int) -
    ((ln4 hx (dim m * t + k) : Int) - 8)
  omega

theorem pairN_eq (m : Fin 6) (i j : Nat) : Chk.pairN m i j =
    Nat.fold (dim (pairMode m))
      (fun k _ s => s + Chk.fN (pairMode m) i k * Chk.hN (pairMode m) j k) 0 := by
  by_cases hm : m.val = 3
  · have e : pairMode m = 2 := by simp [pairMode, hm]
    rw [e, Chk.pairN, if_pos hm]
    rfl
  · have e : pairMode m = m := by simp [pairMode, hm]
    rw [e, Chk.pairN, if_neg hm]

theorem prK_eq {m : Fin 6} {K : KT} {fx hx fx' hx' : Nat} (h : TabsOK m K fx hx fx' hx') {i j : Nat}
    (hi : i < nroots m) (hj : j < nroots m) : (prK K i j : Int) = Chk.pairN m i j + 8 := by
  have hP := allN_iff.mp (allN_iff.mp h.hpair i (by rw [h.hr]; exact hi)) j
    (by rw [h.hr]; exact hj)
  simp only [pairLaneOK, Nat.beq_eq] at hP
  rw [pairN_eq, fold_congr (b := fun k => ((ln4 fx' (dim (pairMode m) * i + k) : Int) - 8) *
    ((ln4 hx' (dim (pairMode m) * j + k) : Int) - 8)) ?_, fold_shift8]
  · simp only [xk_add, xk_mul] at hP ⊢
    omega
  · intro k hk
    rw [fN'_eq h hi hk, hN'_eq h hj hk]
    rfl

theorem bnot_beq8 {P : Nat} {a : Int} (h : (P : Int) = a + 8) : bnot (Nat.beq P 8) = (a != 0) := by
  by_cases hp : P = 8
  · subst hp
    have ha : a = 0 := by omega
    subst ha
    rfl
  · have h1 : Nat.beq P 8 = false := by
      cases e : Nat.beq P 8
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true e) hp
    have h2 : a ≠ 0 := by omega
    rw [h1]
    change true = (a != 0)
    simp [h2]

theorem adj_sound {m : Fin 6} {K : KT} {fx hx fx' hx' : Nat} (h : TabsOK m K fx hx fx' hx') {i : Nat}
    (hi : i < nroots m) : adjK K i = Chk.adjA (tabsK m K) (nroots m) i := by
  have hA := h.hadj
  simp only [adjOK, band_eq_true] at hA
  have e := allN_iff.mp hA.2 i (by rw [h.hr]; exact hi)
  simp only [Nat.beq_eq] at e
  rw [e, h.hr, Chk.adjA]
  apply maskK_eq
  intro j hj
  rw [tabsK_pair hi hj, tabsK_pair hj hi, bor_eq_or, bnot_beq8 (prK_eq h hi hj),
    bnot_beq8 (prK_eq h hj hi)]

theorem dvd_term {x y : Nat} {e : Int} (h : (3 : Int) ∣ (x : Int) - e) :
    (3 : Int) ∣ ((Nat.mul x y : Nat) : Int) - e * (y : Int) := by
  have e1 : ((Nat.mul x y : Nat) : Int) = (x : Int) * (y : Int) := Int.natCast_mul x y
  rw [e1, ← Int.sub_mul]
  exact Int.dvd_trans h (Int.dvd_mul_right _ _)

theorem zm_sound {m : Fin 6} {K : KT} {fx hx fx' hx' : Nat} (h : TabsOK m K fx hx fx' hx') {c : Nat}
    (hc : c < 3 ^ dim m) : zmK K c = Chk.zmA (tabsK m K) (dim m) (nroots m) c := by
  have e := h.hzm c hc
  simp only [Nat.beq_eq] at e
  rw [e, h.hr, Chk.zmA]
  apply maskK_eq
  intro t ht
  simp only [zBitK, Chk.evA]
  rw [h.hd]
  have key : (3 : Int) ∣ ((sumN (dim m) fun k => Nat.mul (fK K t k) (digK c k) : Nat) : Int) -
      Nat.fold (dim m) (fun k _ s => s + (tabsK m K).f[t]![k]! * (Chk.dig c k : Int)) 0 := by
    rw [sumN_cast]
    apply fold_dvd
    intro k hk
    rw [tabsK_f ht hk]
    exact dvd_term (fK_dvd h ht hk)
  generalize (sumN (dim m) fun k => Nat.mul (fK K t k) (digK c k)) = S at key ⊢
  generalize Nat.fold (dim m) (fun k _ s => s + (tabsK m K).f[t]![k]! * (Chk.dig c k : Int)) 0 = F
    at key ⊢
  apply Bool.eq_iff_iff.mpr
  rw [Nat.beq_eq, beq_iff_eq, xk_mod]
  omega

theorem rt_entry {x' x y p : Nat} {F' F Y P : Int} (pos : Bool) (ε : Int)
    (hε : ε = if pos then 1 else -1) (h1 : (3 : Int) ∣ (x' : Int) - F')
    (h2 : (3 : Int) ∣ (x : Int) - F) (h3 : (3 : Int) ∣ (y : Int) - Y) (hP : (p : Int) = P + 8)
    (hb : Bool.rec (motive := fun _ => Bool)
      (Nat.beq (Nat.mod (Nat.add x' (Nat.add x (Nat.mul 2 (Nat.mul (Nat.succ p) y)))) 3) 0)
      (eq3 x' (Nat.add x (Nat.mul 2 (Nat.mul (Nat.succ p) y)))) pos = true) :
    ((F' - ε * (F - P * Y)) % 3 == 0) = true := by
  obtain ⟨q, hq⟩ := h3
  have hY : Y = (y : Int) - 3 * q := by omega
  have hP' : P = (p : Int) - 8 := by omega
  have h4 : (3 : Int) ∣ P * Y - ((p : Int) + 1) * (y : Int) :=
    ⟨-3 * (y : Int) - (p : Int) * q + 8 * q, by rw [hY, hP']; grind⟩
  have e5 : (((p + 1) * y : Nat) : Int) = ((p : Int) + 1) * (y : Int) := by
    rw [Int.natCast_mul, Int.natCast_add]
    rfl
  rw [beq_iff_eq]
  cases pos <;> simp only [eq3, Nat.beq_eq, xk_add, xk_mul, xk_mod, Nat.succ_eq_add_one] at hb <;>
    simp only [Bool.false_eq_true, if_false, if_true] at hε <;> subst hε <;>
    generalize P * Y = w at h4 ⊢ <;> generalize ((p : Int) + 1) * (y : Int) = w2 at h4 e5 <;>
    generalize (p + 1) * y = z at hb e5 <;> omega

theorem rtEq_of {m : Fin 6} {K : KT} {fx hx fx' hx' : Nat} (h : TabsOK m K fx hx fx' hx')
    {u t t' : Nat} (hu : u < nroots m) (ht : t < nroots m) (ht' : t' < nroots m) (pos : Bool)
    (ε : Int) (hε : ε = if pos then 1 else -1) (hR : rtEqK K t' u t pos = true) :
    Chk.rtEq (tabsK m K) (dim m) t' u t ε = true := by
  rw [Chk.rtEq, nat_all_iff]
  intro k hk
  have hR' := allN_iff.mp hR k (by rw [h.hd]; exact hk)
  simp only [band_eq_true] at hR'
  rw [Bool.and_eq_true, tabsK_f ht' hk, tabsK_f ht hk, tabsK_f hu hk, tabsK_pair ht hu,
    tabsK_h ht' hk, tabsK_h ht hk, tabsK_h hu hk, tabsK_pair hu ht]
  exact ⟨rt_entry pos ε hε (fK_dvd h ht' hk) (fK_dvd h ht hk) (fK_dvd h hu hk) (prK_eq h ht hu)
    hR'.1, rt_entry pos ε hε (hK_dvd h ht' hk) (hK_dvd h ht hk) (hK_dvd h hu hk)
    (prK_eq h hu ht) hR'.2⟩

theorem rt_sound {m : Fin 6} {K : KT} {fx hx fx' hx' : Nat} (h : TabsOK m K fx hx fx' hx') {u t : Nat}
    (hu : u < nroots m) (ht : t < nroots m) :
    rtK K u t < nroots m ∧ (Chk.rtEq (tabsK m K) (dim m) (rtK K u t) u t 1 = true ∨
      Chk.rtEq (tabsK m K) (dim m) (rtK K u t) u t (-1) = true) := by
  have hR := allN_iff.mp (allN_iff.mp h.hrt u (by rw [h.hr]; exact hu)) t
    (by rw [h.hr]; exact ht)
  simp only [band_eq_true, bor_iff, Nat.blt_eq] at hR
  obtain ⟨hlt, hR⟩ := hR
  rw [h.hr] at hlt
  refine ⟨hlt, ?_⟩
  rcases hR with hR | hR
  · exact Or.inl (rtEq_of h hu ht hlt true 1 rfl hR)
  · exact Or.inr (rtEq_of h hu ht hlt false (-1) rfl hR)

theorem tabsOK_tabsK {m : Fin 6} {K : KT} {fx hx fx' hx' : Nat} (h : TabsOK m K fx hx fx' hx') :
    Chk.tabsOK m (tabsK m K) = true := by
  simp only [Chk.tabsOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, nat_all_iff,
    Bool.or_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · simp [tabsK]
  · simp [tabsK]
  · simp [tabsK]
  · simp [tabsK]
  · simp [tabsK]
  · simp [tabsK]
  · intro i hi k hk
    exact ⟨tabsK_f hi hk, tabsK_h hi hk⟩
  · intro i hi j hj
    exact tabsK_pair hi hj
  · intro i hi
    rw [tabsK_adj hi]
    exact adj_sound h hi
  · intro c hc
    rw [tabsK_zm hc]
    exact zm_sound h hc
  · intro u hu t ht
    rw [tabsK_rt hu ht]
    exact rt_sound h hu ht

@[expose] def decLin (w : KLin) : Chk.LinW where
  tc := w.tc
  n := w.n
  nodes := (List.range w.nodes.len).map (ln7 w.nodes.P)
  neg := (List.range w.nodes.len).map (bit w.neg)
  a := w.a
  b := w.b

@[expose] def decDer (L : KL) : List (Nat × Nat) :=
  (List.range L.len).map fun i => (ln14 L.P i % 128, ln14 L.P i / 128)

@[expose] def decMat (B : Nat) : Array (Array Int) :=
  (Array.range 8).map fun i => (Array.range 8).map fun j => ((ln2 B (8 * i + j) : Nat) : Int)

@[expose] def decVec (x : Nat) : Array Int := (Array.range 8).map fun l => ((ln2 x l : Nat) : Int)

@[expose] def decPerm (p : KL) : List Nat := (List.range p.len).map (ln4 p.P)

@[expose] def decCoef (c : KL) : List (Nat × Nat) :=
  (List.range c.len).map fun i => (ln9 c.P i % 128, ln9 c.P i / 128)

@[expose] def decWit : KWit → Chk.ExtWit
  | .twoL => .twoL
  | .twoK => .twoK
  | .leaf w Ll Lk Bl Bk =>
    .leaf { w := decLin w, Lℓ := decDer Ll, Lk := decDer Lk, Bℓ := decMat Bl, Bk := decMat Bk }
  | .inner w L B Bi => .inner (decLin w) (decDer L) (decMat B) (decMat Bi)
  | .det w L B x => .det (decLin w) (decDer L) (decMat B) (decVec x) none
  | .ambD w Lk La Bk Bb p h =>
    .ambD { w := decLin w, Lk := decDer Lk, La := decDer La, Bk := decMat Bk, Bb := decMat Bb }
      (decPerm p) h
  | .d5 w Lk La Bk Bb Lj =>
    .d5 { w := decLin w, Lk := decDer Lk, La := decDer La, Bk := decMat Bk, Bb := decMat Bb }
      (decDer Lj)

@[expose] def decRefL : KRefL → Option Chk.RefL
  | .none => none
  | .zero => some .zero
  | .disc S => some (.disc S)
  | .cent w => some (.cent w)
  | .label => some .label
  | .q2 => some .q2
  | .ins c => some (.ins (decCoef c))

@[expose] def decRefP : KRefP → Option Chk.RefP
  | .none => none
  | .disc S => some (.disc S)
  | .cent w => some (.cent w)
  | .label => some .label

@[expose] def decRefC (e : Nat) : Option Chk.RefC :=
  match e % 8 with
  | 1 => some (.disc (e / 8))
  | 2 => some (.cent (e / 8))
  | 3 => some .label
  | 4 => some .inCent
  | _ => none

@[expose] def pick (d cv : Nat) : Nat → List KPlane → Nat → Option KPlane
  | 0, _, _ => none
  | n + 1, ps, cy =>
    if Chk.canonN d cv n then
      match ps with
      | [] => none
      | P :: tl => if cy = n then some P else pick d cv n tl cy
    else pick d cv n ps cy

@[expose] def searchOf (m : Fin 6) (L : KLine) : Chk.Search where
  line cv := if cv = L.cv then decRefL L.ref else none
  plane cv cy := (pick (dim m) cv (3 ^ dim m) L.planes cy).bind fun P => decRefP P.ref
  cand _ cz := decRefC (ln128 L.cref cz)

@[expose] def witOf (m : Fin 6) (L : KLine) (cv cy a b : Nat) : Chk.ExtWit :=
  match pick (dim m) cv (3 ^ dim m) L.planes cy with
  | some P => decWit (P.wits.getD (2 * a + (b - 1)) .twoL)
  | none => .twoL

@[expose] def ExtLineOK (m : Fin 6) (K : KT) (L : KLine) : Prop :=
  Chk.scanLineN (tabsK m K) m true true (searchOf m L)
    (fun cv cy => Chk.candScanN (tabsK m K) m (searchOf m L) cv cy fun a b =>
      Chk.extWitOK (tabsK m K) m cv cy (Chk.combN (dim m) cv cy a b) (witOf m L cv cy a b))
    L.cv = true

theorem digK_dig (c k : Nat) : digK c k = Chk.dig c k := rfl

theorem pivUp_eq (c n : Nat) :
    pivUp c n = ((List.range n).find? fun k => Chk.dig c k != 0).getD n := by
  induction n with
  | zero =>
    rw [List.range_zero, List.find?_nil, Option.getD_none]
    rfl
  | succ n ih =>
    have e : pivUp c (n + 1) =
        nif (Nat.blt (pivUp c n) n) (pivUp c n) (nif (bnot (Nat.beq (digK c n) 0)) n (n + 1)) :=
      rfl
    rw [e, List.range_succ, List.find?_append]
    cases hf : (List.range n).find? (fun k => Chk.dig c k != 0) with
    | some k =>
      rw [hf, Option.getD_some] at ih
      have hk : k < n := List.mem_range.mp (List.mem_of_find?_eq_some hf)
      rw [ih, Nat.blt_eq.mpr hk]
      rfl
    | none =>
      rw [hf, Option.getD_none] at ih
      rw [ih]
      have hb : Nat.blt n n = false := by
        cases e : Nat.blt n n
        · rfl
        · exact absurd (Nat.blt_eq.mp e) (Nat.lt_irrefl n)
      rw [hb, digK_dig]
      by_cases h0 : Chk.dig c n = 0
      · have h1 : Nat.beq (Chk.dig c n) 0 = true := by
          rw [h0]
          rfl
        rw [h1]
        simp [nif, bnot, h0]
      · have h1 : Nat.beq (Chk.dig c n) 0 = false := by
          cases e : Nat.beq (Chk.dig c n) 0
          · rfl
          · exact absurd (Nat.eq_of_beq_eq_true e) h0
        rw [h1]
        simp [nif, bnot, h0]

theorem pivK_eq (d c : Nat) : pivK d c = Chk.pivN d c := by
  rw [pivK, pivUp_eq, Chk.pivN]

theorem canonK_eq (d cv cy : Nat) : canonK d cv cy = Chk.canonN d cv cy := by
  rw [Bool.eq_iff_iff]
  simp only [canonK, Chk.canonN, band_eq_true, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq,
    decide_eq_true_eq, beq_iff_eq, pivK_eq, digK_dig, and_assoc]
  exact Iff.rfl

theorem ofDigK_ofDigits (d : Nat) (f g : Nat → Nat) (h : ∀ k, f k = g k) :
    ofDigK d f = Chk.ofDigits d g := by
  induction d with
  | zero =>
    rw [Chk.ofDigits, Nat.fold_zero]
    rfl
  | succ n ih =>
    have e : ofDigK (n + 1) f = ofDigK n f + f n % 3 * 3 ^ n := rfl
    rw [e, ih]
    simp only [Chk.ofDigits, Nat.fold_succ]
    rw [h n]

theorem combK_eq (d cv cy a b : Nat) : combK d cv cy a b = Chk.combN d cv cy a b :=
  ofDigK_ofDigits d _ _ fun _ => rfl

theorem xk_land (a b : Nat) : Nat.land a b = a &&& b := rfl

theorem xk_pow (a b : Nat) : Nat.pow a b = a ^ b := rfl

theorem band_eq_and (a b : Bool) : band a b = (a && b) := by
  cases a <;> rfl

theorem bnot_eq (a : Bool) : bnot a = !a := by
  cases a <;> rfl

theorem nbeq_eq (a b : Nat) : Nat.beq a b = (a == b) := by
  cases e : Nat.beq a b
  · have := Nat.ne_of_beq_eq_false e
    simp [this]
  · have := Nat.eq_of_beq_eq_true e
    simp [this]

theorem nbeq_false {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases e : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true e) h

theorem nblt_eq (a b : Nat) : Nat.blt a b = decide (a < b) := by
  rw [Bool.eq_iff_iff, Nat.blt_eq, decide_eq_true_eq]

theorem truncK_eq (r c : Nat) : truncK r c = Chk.trunc r c := rfl

theorem subK_eq (a b : Nat) : subK a b = Chk.subN a b := by
  rw [subK, nbeq_eq]
  rfl

theorem bit_eq (x i : Nat) : bit x i = x.testBit i := by
  have e : Nat.land x (Nat.shiftLeft 1 i) = x &&& 2 ^ i := by
    change x &&& (1 <<< i) = _
    rw [Nat.shiftLeft_eq, Nat.one_mul]
  unfold bit
  rw [e, nblt_eq]
  have hb : ∀ j, (x &&& 2 ^ i).testBit j = (x.testBit i && decide (i = j)) := by
    intro j
    rw [Nat.testBit_and, Nat.testBit_two_pow]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij]
  cases hx : x.testBit i
  · have h0 : x &&& 2 ^ i = 0 := Nat.eq_of_testBit_eq fun j => by
      rw [hb, hx, Nat.zero_testBit]
      rfl
    rw [h0]
    rfl
  · have hne : x &&& 2 ^ i ≠ 0 := by
      intro h0
      have := hb i
      rw [h0, Nat.zero_testBit, hx] at this
      simp at this
    simp only [decide_eq_true_eq]
    omega

theorem allN_eq_all {n : Nat} {p q : Nat → Bool} (h : ∀ i < n, p i = q i) :
    allN n p = Nat.all n (fun i _ => q i) := by
  rw [Bool.eq_iff_iff, allN_iff, nat_all_iff]
  constructor
  · intro H i hi
    rw [← h i hi]
    exact H i hi
  · intro H i hi
    rw [h i hi]
    exact H i hi

theorem zmK_eq {m : Fin 6} {K : KT} {fx hx fx' hx' : Nat} (hT : TabsOK m K fx hx fx' hx')
    (c : Nat) : zmK K c = (tabsK m K).zm[c]! := by
  by_cases hc : c < 3 ^ dim m
  · rw [tabsK_zm hc]
  · have hsz : (tabsK m K).zm.size = 3 ^ dim m := by simp [tabsK]
    rw [getElem!_neg (tabsK m K).zm c (by rw [hsz]; exact hc)]
    have hb := hT.hzb
    unfold zmBoundOK at hb
    rw [Nat.blt_eq, hT.hd] at hb
    have hb' : K.zm < 2 ^ (128 * 3 ^ dim m) := hb
    have hlt : K.zm < 2 ^ (128 * c) :=
      Nat.lt_of_lt_of_le hb' (Nat.pow_le_pow_right (by decide) (by omega))
    change K.zm >>> (128 * c) &&& 340282366920938463463374607431768211455 = 0
    rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hlt, Nat.zero_and]

theorem adjK_eq {m : Fin 6} {K : KT} {fx hx fx' hx' : Nat} (hT : TabsOK m K fx hx fx' hx')
    {t : Nat} (ht : t < nroots m) : adjK K t = (tabsK m K).adj[t]! := by
  rw [tabsK_adj ht]

theorem closedK_eq {m : Fin 6} {K : KT} {fx hx fx' hx' : Nat} (hT : TabsOK m K fx hx fx' hx')
    (c S : Nat) : closedK K c S = Chk.closedOK (tabsK m K) (nroots m) c S := by
  have hA : ∀ (c' S' : Nat),
      allN K.r (fun t => bor (bnot (bit S' t)) (subK (Nat.land (adjK K t) c') S')) =
        Nat.all (nroots m) (fun t _ => !S'.testBit t || Chk.subN ((tabsK m K).adj[t]! &&& c') S') := by
    intro c' S'
    rw [hT.hr]
    apply allN_eq_all
    intro t ht
    rw [bor_eq_or, bnot_eq, bit_eq, adjK_eq hT ht, subK_eq]
    rfl
  simp only [closedK]
  rw [hA]
  simp only [Chk.closedOK, band_eq_and, bnot_eq, nbeq_eq, truncK_eq, hT.hr, bne, Bool.and_assoc,
    xk_land]

theorem discK_eq {m : Fin 6} {K : KT} {fx hx fx' hx' : Nat} (hT : TabsOK m K fx hx fx' hx')
    (c S : Nat) : discK K c S = Chk.discOK (tabsK m K) (nroots m) c S := by
  rw [discK, Chk.discOK, bor_eq_or, nbeq_eq, truncK_eq, hT.hr, closedK_eq hT]

theorem offPlaneK_eq (d cv cy w : Nat) : offPlaneK d cv cy w = Chk.offPlane d cv cy w := by
  rw [offPlaneK, Chk.offPlane]
  apply allN_eq_all
  intro a _
  apply allN_eq_all
  intro b _
  rw [bnot_eq, nbeq_eq, combK_eq]
  rfl

theorem xk_div (a b : Nat) : Nat.div a b = a / b := rfl

theorem sumN_succ (n : Nat) (f : Nat → Nat) : sumN (n + 1) f = sumN n f + f n := rfl

theorem nble_eq (a b : Nat) : Nat.ble a b = decide (a ≤ b) := by
  rw [Bool.eq_iff_iff, Nat.ble_eq, decide_eq_true_eq]

theorem nif_eq (b : Bool) (x y : Nat) : nif b x y = if b then x else y := by
  cases b <;> rfl

theorem brec_eq (x y b : Bool) : Bool.rec (motive := fun _ => Bool) x y b = if b then y else x := by
  cases b <;> rfl

theorem labC_zero : labC 0 0 0 = 0 := rfl

theorem labF4K_eq (n : Nat) :
    labF4K n = labC (Chk.labF4N n).1 (Chk.labF4N n).2.1 (Chk.labF4N n).2.2 := by
  unfold labF4K Chk.labF4N
  split <;> simp_all [nif_eq, nbeq_eq, labC_zero]

theorem labE6K_eq (n l : Nat) :
    labE6K n l = labC (Chk.labE6RelN n l).1 (Chk.labE6RelN n l).2.1 (Chk.labE6RelN n l).2.2 := by
  unfold labE6K Chk.labE6RelN
  simp only [nif_eq, nbeq_eq, band_eq_and, Bool.and_eq_true, beq_iff_eq]
  repeat' split
  all_goals simp_all [labC_zero]

theorem labSLK_eq (n o : Nat) :
    labSLK n o = labC (Chk.labSLN n o).1 (Chk.labSLN n o).2.1 (Chk.labSLN n o).2.2 := by
  unfold labSLK Chk.labSLN
  split <;> (try split) <;> simp_all [nif_eq, nbeq_eq, labC_zero]

theorem labF4N_lt (n : Nat) : (Chk.labF4N n).1 < 32 ∧ (Chk.labF4N n).2.1 < 32 := by
  unfold Chk.labF4N
  split <;> decide

theorem labE6RelN_lt (n l : Nat) :
    (Chk.labE6RelN n l).1 < 32 ∧ (Chk.labE6RelN n l).2.1 < 32 := by
  unfold Chk.labE6RelN
  split <;> decide

theorem labSLN_lt (n o : Nat) : (Chk.labSLN n o).1 < 32 ∧ (Chk.labSLN n o).2.1 < 32 := by
  unfold Chk.labSLN
  split <;> (try split) <;> decide

theorem labelOf_lt (T : Chk.Tabs) (m : Fin 6) (c : Nat) :
    (Chk.labelOf T m c).1 < 32 ∧ (Chk.labelOf T m c).2.1 < 32 := by
  unfold Chk.labelOf Chk.labelN
  split
  · exact labF4N_lt _
  · exact labE6RelN_lt _ _
  · exact labSLN_lt _ _

theorem land_one_bit (c t : Nat) :
    Nat.land (Nat.shiftRight c t) 1 = if c.testBit t then 1 else 0 := by
  change c >>> t &&& 1 = _
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (c / 2 ^ t) with h | h <;> simp [h]

theorem cardK_eq (r c : Nat) : cardK r c = Chk.cardN r c := by
  induction r with
  | zero => simp [cardK, sumN_zero, Chk.cardN]
  | succ n ih =>
    have e : cardK (n + 1) c = cardK n c + Nat.land (Nat.shiftRight c n) 1 := rfl
    rw [e, ih, land_one_bit]
    simp only [Chk.cardN, List.range_succ, List.countP_append, List.countP_singleton]

theorem sumN_congr {n : Nat} {f g : Nat → Nat} (h : ∀ i < n, f i = g i) :
    sumN n f = sumN n g := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sumN_succ, sumN_succ, ih (fun i hi => h i (by omega)), h n (by omega)]

theorem fold_count (r : Nat) (P : Nat → Bool) (acc : Nat) :
    Nat.fold r (fun j _ a => if P j then a + 1 else a) acc =
      acc + sumN r (fun j => if P j then 1 else 0) := by
  induction r with
  | zero => simp [sumN_zero]
  | succ n ih =>
    simp only [Nat.fold_succ]
    rw [ih, sumN_succ]
    split <;> omega

theorem fold_sum_if (r : Nat) (Q : Nat → Bool) (S : Nat → Nat) (a : Nat) :
    Nat.fold r (fun i _ acc => if Q i then acc + S i else acc) a =
      a + sumN r (fun i => if Q i then S i else 0) := by
  induction r with
  | zero => simp [sumN_zero]
  | succ n ih =>
    simp only [Nat.fold_succ]
    rw [ih, sumN_succ]
    split <;> omega

theorem beq8 {P : Nat} {a : Int} (h : (P : Int) = a + 8) : Nat.beq P 8 = (a == 0) := by
  rw [nbeq_eq]
  by_cases hp : P = 8
  · subst hp
    have ha : a = 0 := by omega
    subst ha
    rfl
  · have ha : a ≠ 0 := by omega
    rw [beq_false_of_ne hp, beq_false_of_ne ha]

theorem orthK_eq {m : Fin 6} {K : KT} {fx hx fx' hx' : Nat} (hT : TabsOK m K fx hx fx' hx')
    (c : Nat) : orthK K c = Chk.orthN (tabsK m K) (nroots m) c := by
  simp only [Chk.orthN, fold_count, fold_sum_if, Nat.zero_add]
  unfold orthK
  rw [hT.hr]
  apply sumN_congr
  intro i hi
  have hin : ∀ j < nroots m, nif (band (bit c j) (Nat.beq (prK K i j) 8)) 1 0 =
      if (c.testBit j && (tabsK m K).pair[i]![j]! == 0) = true then 1 else 0 := by
    intro j hj
    rw [nif_eq, band_eq_and, bit_eq, tabsK_pair hi hj, beq8 (prK_eq hT hi hj)]
  rw [nif_eq, bit_eq, sumN_congr hin]

theorem countP_range_congr {r : Nat} {p q : Nat → Bool} (h : ∀ t < r, p t = q t) :
    (List.range r).countP p = (List.range r).countP q := by
  induction r with
  | zero => simp
  | succ n ih =>
    simp only [List.range_succ, List.countP_append, List.countP_singleton]
    rw [ih (fun t ht => h t (by omega)), h n (by omega)]

theorem lg_eq {m : Fin 6} {K : KT} {fx hx fx' hx' : Nat} (hT : TabsOK m K fx hx fx' hx') {t : Nat}
    (ht : t < nroots m) : K.lg.testBit t = tabFix1.getD t false := by
  have := allN_iff.mp hT.hlg t (by rw [hT.hr]; exact ht)
  rw [← bit_eq]
  revert this
  cases bit K.lg t <;> cases tabFix1.getD t false <;> decide

theorem labK_eq {m : Fin 6} {K : KT} {fx hx fx' hx' : Nat} (hT : TabsOK m K fx hx fx' hx')
    (c : Nat) : labK K c = labC (Chk.labelOf (tabsK m K) m c).1 (Chk.labelOf (tabsK m K) m c).2.1
      (Chk.labelOf (tabsK m K) m c).2.2 := by
  have hcard : cardK K.r c = Chk.cardN (nroots m) c := by rw [hT.hr, cardK_eq]
  have hlong : cardK K.r (Nat.land c K.lg) = Chk.longN (nroots m) c := by
    rw [hT.hr, cardK_eq, Chk.cardN, Chk.longN]
    apply countP_range_congr
    intro t ht
    rw [xk_land, Nat.testBit_and, lg_eq hT ht]
  unfold labK
  rw [hcard, hlong, orthK_eq hT, hT.hm]
  obtain ⟨_ | _ | k, hk⟩ := m
  · simp [nif_eq, nbeq_eq, Chk.labelOf, Chk.labelN, labF4K_eq]
  · simp [nif_eq, nbeq_eq, Chk.labelOf, Chk.labelN, labE6K_eq]
  · simp [nif_eq, nbeq_eq, Chk.labelOf, Chk.labelN, labSLK_eq]

theorem labC_parts {t r n : Nat} (ht : t < 32) (hr : r < 32) :
    labT (labC t r n) = t ∧ labR (labC t r n) = r ∧ labN (labC t r n) = n := by
  simp only [labT, labR, labN, labC, xk_add, xk_mul, xk_mod, xk_div]
  omega

theorem lam2P_eq (t r n : Nat) : lam2P t r n = Chk.lam2N (t, r, n) := by
  simp only [Chk.lam2N]
  unfold lam2P
  split <;> simp_all [band_eq_and, bor_eq_or, bnot_eq, nbeq_eq, nble_eq, brec_eq, bne, xk_mod,
    Bool.and_assoc]
  all_goals
    intro _
    repeat' split
    all_goals omega

theorem lam2K_labK {m : Fin 6} {K : KT} {fx hx fx' hx' : Nat} (hT : TabsOK m K fx hx fx' hx')
    (c : Nat) : lam2K (labK K c) = Chk.lam2N (Chk.labelOf (tabsK m K) m c) := by
  have hb := labelOf_lt (tabsK m K) m c
  rw [lam2K, labK_eq hT]
  generalize Chk.labelOf (tabsK m K) m c = x at hb ⊢
  obtain ⟨t, r, n⟩ := x
  dsimp only at hb ⊢
  obtain ⟨e1, e2, e3⟩ := labC_parts (n := n) hb.1 hb.2
  rw [e1, e2, e3, lam2P_eq]

theorem q2K_labK {m : Fin 6} {K : KT} {fx hx fx' hx' : Nat} (hT : TabsOK m K fx hx fx' hx')
    (c : Nat) : q2K (labK K c) = Chk.q2N (Chk.labelOf (tabsK m K) m c) := by
  have hb := labelOf_lt (tabsK m K) m c
  rw [q2K, labK_eq hT]
  generalize Chk.labelOf (tabsK m K) m c = x at hb ⊢
  obtain ⟨t, r, n⟩ := x
  dsimp only at hb ⊢
  obtain ⟨e1, e2, e3⟩ := labC_parts (n := n) hb.1 hb.2
  rw [e1, e2, e3]
  simp [Chk.q2N, bor_eq_or, band_eq_and, nblt_eq, nbeq_eq, Bool.and_assoc]

theorem all_map_range {α : Type} (n : Nat) (f : Nat → α) (p : α → Bool) :
    ((List.range n).map f).all p = allN n (fun i => p (f i)) := by
  rw [Bool.eq_iff_iff, List.all_eq_true, allN_iff]
  simp [List.mem_map, List.mem_range]

theorem foldl_map_range {α : Type} (n : Nat) (f : Nat → α) (g : α → Int) :
    ((List.range n).map f).foldl (fun s e => s + g e) 0 = Nat.fold n (fun i _ s => s + g (f i)) 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.foldl_append, ih]
    simp [Nat.fold_succ]

theorem dvd_term' {x y : Nat} {e : Int} (h : (3 : Int) ∣ (x : Int) - e) :
    (3 : Int) ∣ ((Nat.mul y x : Nat) : Int) - (y : Int) * e := by
  have e1 : ((Nat.mul y x : Nat) : Int) = (y : Int) * (x : Int) := Int.natCast_mul y x
  rw [e1, ← Int.mul_sub]
  exact Int.dvd_trans h (Int.dvd_mul_left _ _)

theorem inK_sound {m : Fin 6} {K : KT} {fx hx fx' hx' : Nat} (hT : TabsOK m K fx hx fx' hx')
    {c cv : Nat} {coef : KL} (h : inK K c coef cv = true) :
    Chk.inOK (tabsK m K) (dim m) (nroots m) c (decCoef coef) cv = true := by
  have h' : band (allN coef.len fun i =>
        band (Nat.blt (ln9 coef.P i % 128) K.r) (bit c (ln9 coef.P i % 128)))
      (allN K.d fun k => Nat.beq ((sumN coef.len (fun i =>
        (ln9 coef.P i / 128) * hK K (ln9 coef.P i % 128) k) + 2 * digK cv k) % 3) 0) = true := h
  rw [band_eq_true] at h'
  obtain ⟨hA, hB⟩ := h'
  have hA' : ∀ i < coef.len,
      ln9 coef.P i % 128 < nroots m ∧ c.testBit (ln9 coef.P i % 128) = true := by
    intro i hi
    have := allN_iff.mp hA i hi
    rw [band_eq_true, Nat.blt_eq, hT.hr, bit_eq] at this
    exact this
  rw [Chk.inOK, Bool.and_eq_true]
  constructor
  · rw [decCoef, all_map_range, allN_iff]
    intro i hi
    obtain ⟨h1, h2⟩ := hA' i hi
    simp [h1, h2]
  · rw [nat_all_iff]
    intro k hk
    have hk' := allN_iff.mp hB k (by rw [hT.hd]; exact hk)
    simp only [Nat.beq_eq] at hk'
    rw [decCoef, foldl_map_range, beq_iff_eq]
    dsimp only
    have key : (3 : Int) ∣ ((sumN coef.len (fun i =>
        (ln9 coef.P i / 128) * hK K (ln9 coef.P i % 128) k) : Nat) : Int) -
        Nat.fold coef.len (fun i _ s => s + ((ln9 coef.P i / 128 : Nat) : Int) *
          (tabsK m K).h[ln9 coef.P i % 128]![k]!) 0 := by
      rw [sumN_cast]
      apply fold_dvd
      intro i hi
      rw [tabsK_h (hA' i hi).1 hk]
      exact dvd_term' (hK_dvd hT (hA' i hi).1 hk)
    generalize (sumN coef.len (fun i => (ln9 coef.P i / 128) * hK K (ln9 coef.P i % 128) k)) = S
      at key hk'
    generalize Nat.fold coef.len (fun i _ s => s + ((ln9 coef.P i / 128 : Nat) : Int) *
      (tabsK m K).h[ln9 coef.P i % 128]![k]!) 0 = F at key ⊢
    simp only [digK_dig, xk_add, xk_mul, xk_mod] at hk'
    omega

theorem refLK_sound {m : Fin 6} {K : KT} {fx hx fx' hx' : Nat} (hT : TabsOK m K fx hx fx' hx')
    {cv : Nat} {e : KRefL} (h : refLK K cv e = true) :
    ∃ e', decRefL e = some e' ∧ Chk.refLOK (tabsK m K) m true true cv e' = true := by
  cases e with
  | none => exact Bool.noConfusion h
  | zero =>
    refine ⟨.zero, rfl, ?_⟩
    have h' : Nat.beq cv 0 = true := h
    rw [nbeq_eq] at h'
    exact h'
  | disc S =>
    refine ⟨.disc S, rfl, ?_⟩
    have h' : discK K (zmK K cv) S = true := h
    rw [discK_eq hT, zmK_eq hT] at h'
    exact h'
  | cent w =>
    refine ⟨.cent w, rfl, ?_⟩
    have h' : band (Nat.blt w (Nat.pow 3 K.d)) (band (subK (truncK K.r (zmK K cv)) (zmK K w))
        (offPlaneK K.d cv 0 w)) = true := h
    simp only [band_eq_and, nblt_eq, subK_eq, truncK_eq, offPlaneK_eq, zmK_eq hT, hT.hr, hT.hd,
      xk_pow, Bool.and_assoc] at h'
    simp only [Chk.refLOK, Bool.and_assoc]
    exact h'
  | label =>
    refine ⟨.label, rfl, ?_⟩
    have h' : bnot (lam2K (labK K (zmK K cv))) = true := h
    rw [bnot_eq, lam2K_labK hT, zmK_eq hT] at h'
    exact h'
  | q2 =>
    refine ⟨.q2, rfl, ?_⟩
    have h' : bnot (q2K (labK K (zmK K cv))) = true := h
    rw [bnot_eq, q2K_labK hT, zmK_eq hT] at h'
    simp only [Chk.refLOK, Bool.true_and]
    exact h'
  | ins coef =>
    refine ⟨.ins (decCoef coef), rfl, ?_⟩
    have h' : inK K (zmK K cv) coef cv = true := h
    rw [zmK_eq hT] at h'
    simp only [Chk.refLOK, Bool.true_and]
    exact inK_sound hT h'

theorem refPK_sound {m : Fin 6} {K : KT} {fx hx fx' hx' : Nat} (hT : TabsOK m K fx hx fx' hx')
    {cv cy : Nat} {e : KRefP} (h : refPK K cv cy e = true) :
    ∃ e', decRefP e = some e' ∧ Chk.refPOK (tabsK m K) m cv cy e' = true := by
  cases e with
  | none => exact Bool.noConfusion h
  | disc S =>
    refine ⟨.disc S, rfl, ?_⟩
    have h' : discK K (Nat.land (zmK K cv) (zmK K cy)) S = true := h
    rw [discK_eq hT, zmK_eq hT, zmK_eq hT, xk_land] at h'
    exact h'
  | cent w =>
    refine ⟨.cent w, rfl, ?_⟩
    have h' : band (Nat.blt w (Nat.pow 3 K.d)) (band (subK (truncK K.r (Nat.land (zmK K cv)
        (zmK K cy))) (zmK K w)) (offPlaneK K.d cv cy w)) = true := h
    simp only [band_eq_and, nblt_eq, subK_eq, truncK_eq, offPlaneK_eq, zmK_eq hT, hT.hr, hT.hd,
      xk_land, xk_pow, Bool.and_assoc] at h'
    simp only [Chk.refPOK, Bool.and_assoc]
    exact h'
  | label =>
    refine ⟨.label, rfl, ?_⟩
    have h' : bnot (lam2K (labK K (Nat.land (zmK K cv) (zmK K cy)))) = true := h
    rw [bnot_eq, lam2K_labK hT, zmK_eq hT, zmK_eq hT, xk_land] at h'
    exact h'

theorem refCK_sound {m : Fin 6} {K : KT} {fx hx fx' hx' : Nat} (hT : TabsOK m K fx hx fx' hx')
    {cv cz e : Nat} (h : refCK K cv cz e = true) :
    ∃ e', decRefC e = some e' ∧ Chk.refCOK (tabsK m K) m cv cz e' = true := by
  have h' : refCKAt K cv cz (e % 8) (e / 8) = true := h
  unfold refCKAt at h'
  by_cases h1 : e % 8 = 1
  · rw [h1] at h'
    have hk : discK K (zmK K cz) (e / 8) = true := h'
    refine ⟨.disc (e / 8), by simp [decRefC, h1], ?_⟩
    rw [discK_eq hT, zmK_eq hT] at hk
    exact hk
  rw [nbeq_false h1] at h'
  by_cases h2 : e % 8 = 2
  · rw [h2] at h'
    have hk : band (Nat.blt (e / 8) (Nat.pow 3 K.d)) (band (subK (truncK K.r (zmK K cz))
        (zmK K (e / 8))) (offPlaneK K.d cz 0 (e / 8))) = true := h'
    refine ⟨.cent (e / 8), by simp [decRefC, h2], ?_⟩
    simp only [band_eq_and, nblt_eq, subK_eq, truncK_eq, offPlaneK_eq, zmK_eq hT, hT.hr, hT.hd,
      xk_pow, Bool.and_assoc] at hk
    simp only [Chk.refCOK, Bool.and_assoc]
    exact hk
  rw [nbeq_false h2] at h'
  by_cases h3 : e % 8 = 3
  · rw [h3] at h'
    have hk : bnot (lam2K (labK K (zmK K cz))) = true := h'
    refine ⟨.label, by simp [decRefC, h3], ?_⟩
    rw [bnot_eq, lam2K_labK hT, zmK_eq hT] at hk
    exact hk
  rw [nbeq_false h3] at h'
  by_cases h4 : e % 8 = 4
  · rw [h4] at h'
    have hk : subK (truncK K.r (zmK K cz)) (zmK K cv) = true := h'
    refine ⟨.inCent, by simp [decRefC, h4], ?_⟩
    rw [subK_eq, truncK_eq, hT.hr, zmK_eq hT, zmK_eq hT] at hk
    exact hk
  rw [nbeq_false h4] at h'
  exact Bool.noConfusion h'

theorem xk_sub (a b : Nat) : Nat.sub a b = a - b := rfl

theorem twoNodeP_eq (xt xr xn jt jr jn : Nat) :
    twoNodeP xt xr xn jt jr jn = Chk.twoNodeN (xt, xr, xn) (jt, jr, jn) := by
  simp only [twoNodeP, Chk.twoNodeN, band_eq_and, bor_eq_or, nbeq_eq, xk_add, xk_mod, xk_pow,
    xk_sub, Bool.and_assoc, Bool.or_assoc]

theorem twoNodeK_labK {m : Fin 6} {K : KT} {fx hx fx' hx' : Nat} (hT : TabsOK m K fx hx fx' hx')
    (c c' : Nat) : twoNodeK (labK K c) (labK K c') =
      Chk.twoNodeN (Chk.labelOf (tabsK m K) m c) (Chk.labelOf (tabsK m K) m c') := by
  have hb := labelOf_lt (tabsK m K) m c
  have hb' := labelOf_lt (tabsK m K) m c'
  rw [twoNodeK, labK_eq hT, labK_eq hT]
  generalize Chk.labelOf (tabsK m K) m c = x at hb ⊢
  generalize Chk.labelOf (tabsK m K) m c' = y at hb' ⊢
  obtain ⟨t, r, n⟩ := x
  obtain ⟨t', r', n'⟩ := y
  dsimp only at hb hb' ⊢
  obtain ⟨e1, e2, e3⟩ := labC_parts (n := n) hb.1 hb.2
  obtain ⟨e1', e2', e3'⟩ := labC_parts (n := n') hb'.1 hb'.2
  rw [e1, e2, e3, e1', e2', e3', twoNodeP_eq]

theorem wk_dim_le : ∀ m : Fin 6, dim m ≤ 8 := by decide

theorem wk_nroots_le : ∀ m : Fin 6, nroots m ≤ 128 := by decide

theorem wk_ln2_le (x i : Nat) : ln2 x i ≤ 3 := Nat.and_le_right

theorem wk_ln4_le (x i : Nat) : ln4 x i ≤ 15 := Nat.and_le_right

theorem wk_nif_pos {b : Bool} {x y : Nat} (h : b = true) : nif b x y = x := by rw [h]; rfl

theorem wk_nif_neg {b : Bool} {x y : Nat} (h : b = false) : nif b x y = y := by rw [h]; rfl

theorem wk_dl_tc (w : KLin) : (decLin w).tc = w.tc := rfl

theorem wk_dl_n (w : KLin) : (decLin w).n = w.n := rfl

theorem wk_dl_a (w : KLin) : (decLin w).a = w.a := rfl

theorem wk_dl_b (w : KLin) : (decLin w).b = w.b := rfl

theorem wk_nodeK_lt {w : KLin} {i : Nat} (hi : i < w.nodes.len) : nodeK w i = ln7 w.nodes.P i := by
  rw [nodeK, nif_eq, nblt_eq, if_pos (decide_eq_true hi)]

theorem wk_nodeN (w : KLin) (i : Nat) : Chk.nodeN (decLin w) i = nodeK w i := by
  rw [Chk.nodeN, nodeK, nif_eq, nblt_eq]
  change ((List.range w.nodes.len).map (ln7 w.nodes.P)).getD i 0 = _
  by_cases hi : i < w.nodes.len <;> simp [List.getD_eq_getElem?_getD, hi]

theorem wk_sgn (w : KLin) (i : Nat) : Chk.sgnN (decLin w) i = if negK w i then -1 else 1 := by
  rw [Chk.sgnN, negK, band_eq_and, nblt_eq]
  change (if ((List.range w.nodes.len).map (bit w.neg)).getD i false then (-1 : Int) else 1) = _
  by_cases hi : i < w.nodes.len <;> simp [List.getD_eq_getElem?_getD, hi]

theorem wk_getD_map {n k : Nat} (f : Nat → Nat) (hk : k < n) :
    ((List.range n).map f).getD k 0 = f k := by
  simp [List.getD_eq_getElem?_getD, hk]

theorem wk_rk (tc n : Nat) : rkK tc n = Chk.rkN tc n := by
  unfold rkK Chk.rkN
  rcases tc with _ | _ | _ | _ | _ | _ | _ | _ | tc <;> simp [nif_eq, nblt_eq, nbeq_eq] <;> omega

theorem wk_rkW (w : KLin) : rkW w = Chk.rkN (decLin w).tc (decLin w).n := wk_rk w.tc w.n

theorem wk_valid (tc n : Nat) : validK tc n = Chk.validN tc n := by
  unfold validK Chk.validN
  rcases tc with _ | _ | _ | _ | _ | _ | _ | _ | _ | tc <;>
    simp [brec_eq, band_eq_and, nble_eq, nbeq_eq]

theorem wk_cart (tc n i j : Nat) : (cartK tc n i j : Int) = Chk.cartanN tc n i j + 8 := by
  unfold cartK Chk.cartanN
  by_cases hij : i = j
  · rw [if_pos hij, wk_nif_pos (b := Nat.beq i j) (by rw [hij, nbeq_eq]; simp)]
    rfl
  · rw [if_neg hij, wk_nif_neg (b := Nat.beq i j) (nbeq_false hij)]
    unfold cartOff
    rcases tc with _ | _ | _ | _ | _ | _ | _ | _ | tc
    all_goals simp only [nif_eq, nbeq_eq, bor_eq_or, band_eq_and, eqN, nble_eq, nblt_eq,
      Nat.succ_eq_add_one, xk_add, xk_sub]
    all_goals simp
    all_goals (repeat' split) <;> omega

theorem wk_countP (n : Nat) (p : Nat → Bool) :
    (List.range n).countP p = sumN n (fun c => nif (p c) 1 0) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.countP_append, List.countP_singleton, ih, sumN_succ, nif_eq]

theorem wk_leaf (tc n a : Nat) : leafK tc n a = Chk.leafN tc n a := by
  rw [leafK, Chk.leafN, ← List.countP_eq_length_filter, wk_countP, wk_rk, nbeq_eq]
  congr 1
  apply sumN_congr
  intro c _
  rw [band_eq_and, bnot_beq8 (wk_cart tc n a c), bnot_eq, nbeq_eq]
  rfl

theorem wk_inner (tc n : Nat) : innerK tc n = Chk.innerTypeN tc n := by
  simp only [innerK, Chk.innerTypeN, bor_eq_or, band_eq_and, nbeq_eq, nble_eq, xk_mod,
    Bool.or_assoc, Bool.and_assoc]

theorem wk_notB2 {m : Fin 6} {K : KT} {fx hx fx' hx' : Nat} (hT : TabsOK m K fx hx fx' hx')
    (c : Nat) : notB2K K c = Chk.notB2 m c := by
  rw [notB2K, Chk.notB2, bnot_eq, band_eq_and, nbeq_eq, nbeq_eq, cardK_eq, hT.hm, hT.hr]

theorem wk_type {m : Fin 6} {K : KT} {fx hx fx' hx' : Nat} (hT : TabsOK m K fx hx fx' hx')
    {w : KLin} (h : typeK K w = true) :
    Chk.typeOK (tabsK m K) (nroots m) (decLin w) = true ∧ ∀ i < rkW w, nodeK w i < nroots m := by
  simp only [typeK, band_eq_true] at h
  obtain ⟨hv, hl, hn, hc⟩ := h
  have hl' : w.nodes.len = rkW w := Nat.eq_of_beq_eq_true hl
  have hn' : ∀ i < rkW w, nodeK w i < nroots m := by
    intro i hi
    have := allN_iff.mp hn i (by omega)
    rwa [Nat.blt_eq, hT.hr] at this
  refine ⟨?_, hn'⟩
  unfold Chk.typeOK
  simp only [Bool.and_eq_true, beq_iff_eq, nat_all_iff]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · rw [← wk_valid]
    exact hv
  · change ((List.range w.nodes.len).map (ln7 w.nodes.P)).length = _
    rw [List.length_map, List.length_range, hl', wk_rkW]
  · change ((List.range w.nodes.len).map (ln7 w.nodes.P)).all _ = true
    rw [all_map_range, allN_iff]
    intro i hi
    have := hn' i (by omega)
    rw [wk_nodeK_lt hi] at this
    exact decide_eq_true this
  · intro i hi j hj
    rw [← wk_rkW] at hi hj
    have hij := allN_iff.mp (allN_iff.mp hc i hi) j hj
    rw [nbeq_eq, beq_iff_eq] at hij
    simp only [xk_sub] at hij
    rw [wk_sgn, wk_sgn, wk_nodeN, wk_nodeN, tabsK_pair (hn' i hi) (hn' j hj), wk_dl_tc, wk_dl_n]
    have hP := prK_eq hT (hn' i hi) (hn' j hj)
    have hC := wk_cart w.tc w.n i j
    have h15 : prK K (nodeK w i) (nodeK w j) ≤ 15 := wk_ln4_le _ _
    generalize prK K (nodeK w i) (nodeK w j) = P at hP hij h15
    generalize cartK w.tc w.n i j = C at hC hij
    generalize negK w i = s1 at hij ⊢
    generalize negK w j = s2 at hij ⊢
    cases s1 <;> cases s2 <;> simp at hij ⊢ <;> omega

theorem wk_lin {m : Fin 6} {K : KT} {fx hx fx' hx' : Nat} (hT : TabsOK m K fx hx fx' hx')
    {w : KLin} (h : linK K w = true) :
    Chk.linOK (tabsK m K) (nroots m) (decLin w) = true ∧ rkW w ≤ 8 ∧ w.a < rkW w ∧
      w.b < rkW w ∧ ∀ i < rkW w, nodeK w i < nroots m := by
  simp only [linK, band_eq_true] at h
  obtain ⟨hty, h8, ha, hb, hab, hleaf⟩ := h
  obtain ⟨hty', hn⟩ := wk_type hT hty
  rw [Nat.ble_eq] at h8
  rw [Nat.blt_eq] at ha hb
  refine ⟨?_, h8, ha, hb, hn⟩
  unfold Chk.linOK
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  rw [wk_dl_a, wk_dl_b, wk_dl_tc, wk_dl_n, ← wk_rk, ← wk_leaf]
  rw [bnot_eq, nbeq_eq] at hab
  exact ⟨⟨⟨⟨hty', ha⟩, hb⟩, hab⟩, hleaf⟩

theorem wk_nodeMask (w : KLin) {p q : Nat → Bool} (hpq : ∀ i, p i = q i) :
    nodeMaskK w p = Chk.nodeMask (decLin w) q := by
  unfold nodeMaskK Chk.nodeMask
  rw [← wk_rkW]
  generalize rkW w = n
  induction n with
  | zero =>
    rw [Nat.fold_zero]
    rfl
  | succ n ih =>
    have e : (Nat.rec (motive := fun _ => Nat) 0
        (fun i acc => nif (p i) (Nat.lor acc (Nat.shiftLeft 1 (nodeK w i))) acc) (n + 1) : Nat) =
        nif (p n) (Nat.lor (Nat.rec (motive := fun _ => Nat) 0
          (fun i acc => nif (p i) (Nat.lor acc (Nat.shiftLeft 1 (nodeK w i))) acc) n)
          (Nat.shiftLeft 1 (nodeK w n))) (Nat.rec (motive := fun _ => Nat) 0
          (fun i acc => nif (p i) (Nat.lor acc (Nat.shiftLeft 1 (nodeK w i))) acc) n) := rfl
    rw [e, ih, Nat.fold_succ, hpq, wk_nodeN, nif_eq]
    rfl

theorem wk_filter_ne {a : Nat} : ∀ {n : Nat}, a < n →
    (List.range n).filter (fun i => i != a) = (List.range (n - 1)).map (Chk.offN a)
  | 0, h => absurd h (Nat.not_lt_zero a)
  | n + 1, h => by
    rw [List.range_succ, List.filter_append, Nat.add_sub_cancel]
    by_cases ha : a < n
    · rw [wk_filter_ne ha]
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      rw [Nat.add_sub_cancel, List.range_succ, List.map_append]
      have h1 : ¬ k < a := by omega
      have h2 : (k + 1 != a) = true := by simp; omega
      simp [Chk.offN, h1, h2]
    · have han : a = n := by omega
      subst han
      have h1 : (List.range a).filter (fun i => i != a) = List.range a :=
        List.filter_eq_self.mpr fun i hi => by
          have := List.mem_range.mp hi
          simp
          omega
      have h2 : (List.range a).map (Chk.offN a) = List.range a := by
        conv => rhs; rw [← List.map_id (List.range a)]
        apply List.map_congr_left
        intro i hi
        have := List.mem_range.mp hi
        simp [Chk.offN, this]
      rw [h1, h2]
      simp

theorem wk_nodeList_true (w : KLin) :
    Chk.nodeList (decLin w) (fun _ => true) =
      (List.range (rkW w)).map fun i => nodeK w (idK i) := by
  rw [Chk.nodeList, (List.filter_eq_self (p := fun _ => true)).mpr (fun _ _ => rfl), ← wk_rkW]
  apply List.map_congr_left
  intro i _
  rw [wk_nodeN]
  rfl

theorem wk_nodeList_off (w : KLin) {a : Nat} (ha : a < rkW w) :
    Chk.nodeList (decLin w) (fun i => i != a) =
      (List.range (rkW w - 1)).map fun i => nodeK w (offK a i) := by
  rw [Chk.nodeList, ← wk_rkW, wk_filter_ne ha, List.map_map]
  apply List.map_congr_left
  intro i _
  simp only [Function.comp, wk_nodeN, offK, nif_eq, nblt_eq, Chk.offN, decide_eq_true_eq]

theorem wk_live : liveBit = 2 ^ 128 := rfl

theorem wk_bit_live {S t : Nat} (ht : t < 128) : bit (S ||| liveBit) t = S.testBit t := by
  rw [bit_eq, wk_live, Nat.testBit_or, Nat.testBit_two_pow]
  have : ¬ 128 = t := by omega
  simp [this]

theorem wk_and_live {x S : Nat} (hx : x < 2 ^ 128) : x &&& (S ||| liveBit) = x &&& S := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_and, wk_live, Nat.testBit_or, Nat.testBit_two_pow]
  by_cases hi : i = 128
  · subst hi
    rw [Nat.testBit_lt_two_pow hx]
    simp
  · have : ¬ 128 = i := fun e => hi e.symm
    simp [this]

theorem wk_trunc_lt (r c : Nat) (hr : r ≤ 128) : Chk.trunc r c < 2 ^ 128 := by
  have h1 : c &&& (2 ^ r - 1) ≤ 2 ^ r - 1 := Nat.and_le_right
  have h2 : 2 ^ r ≤ 2 ^ 128 := Nat.pow_le_pow_right (by decide) hr
  have h3 : 0 < 2 ^ r := Nat.two_pow_pos r
  change c &&& (2 ^ r - 1) < 2 ^ 128
  omega

theorem wk_deriv {m : Fin 6} {K : KT} {fx hx fx' hx' : Nat} (hT : TabsOK m K fx hx fx' hx')
    {gens : Nat} (hg : gens < 2 ^ 128) (P n : Nat) :
    (derivK K gens ⟨n, P⟩ = 0 ∧ Chk.derivN (tabsK m K) (nroots m) gens (decDer ⟨n, P⟩) = none) ∨
    ∃ S, S < 2 ^ 128 ∧ derivK K gens ⟨n, P⟩ = S ||| liveBit ∧
      Chk.derivN (tabsK m K) (nroots m) gens (decDer ⟨n, P⟩) = some S := by
  induction n with
  | zero => exact Or.inr ⟨gens, hg, rfl, rfl⟩
  | succ n ih =>
    have eK : derivK K gens ⟨n + 1, P⟩ =
        nif (band (Nat.blt (ln14 P n % 128) K.r) (band (Nat.blt (ln14 P n / 128) K.r)
          (band (bit gens (ln14 P n % 128)) (bit (derivK K gens ⟨n, P⟩) (ln14 P n / 128)))))
        (Nat.lor (derivK K gens ⟨n, P⟩) (Nat.shiftLeft 1 (rtK K (ln14 P n % 128) (ln14 P n / 128))))
        0 := rfl
    have eN : Chk.derivN (tabsK m K) (nroots m) gens (decDer ⟨n + 1, P⟩) =
        (Chk.derivN (tabsK m K) (nroots m) gens (decDer ⟨n, P⟩)).bind fun S =>
          if decide (ln14 P n % 128 < nroots m) && decide (ln14 P n / 128 < nroots m) &&
            gens.testBit (ln14 P n % 128) && S.testBit (ln14 P n / 128) then
            some (S ||| 1 <<< (tabsK m K).rt[ln14 P n % 128]![ln14 P n / 128]!)
          else none := by
      simp only [Chk.derivN, decDer, List.range_succ, List.map_append, List.foldl_append,
        List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
    generalize ln14 P n % 128 = u at eK eN
    generalize ln14 P n / 128 = t at eK eN
    rw [eK, eN]
    have hr := wk_nroots_le m
    rcases ih with ⟨h0, hN⟩ | ⟨S, hS, hK, hN⟩
    · rw [h0, hN]
      have : ∀ a b c : Bool, ∀ x : Nat, nif (band a (band b (band c false))) x 0 = 0 := by
        intro a b c x
        cases a <;> cases b <;> cases c <;> rfl
      have hb0 : bit 0 t = false := by rw [bit_eq, Nat.zero_testBit]
      rw [hb0]
      exact Or.inl ⟨this _ _ _ _, rfl⟩
    · rw [hK, hN, hT.hr]
      simp only [Option.bind]
      by_cases hc : u < nroots m ∧ t < nroots m ∧ gens.testBit u = true ∧ S.testBit t = true
      · obtain ⟨hu, ht, hgu, hSt⟩ := hc
        have hcK : band (Nat.blt u (nroots m)) (band (Nat.blt t (nroots m))
            (band (bit gens u) (bit (S ||| liveBit) t))) = true := by
          rw [band_eq_true, band_eq_true, band_eq_true, Nat.blt_eq, Nat.blt_eq, bit_eq,
            wk_bit_live (by omega)]
          exact ⟨hu, ht, hgu, hSt⟩
        have hrt := (rt_sound hT hu ht).1
        refine Or.inr ⟨S ||| 1 <<< rtK K u t, ?_, ?_, ?_⟩
        · apply Nat.or_lt_two_pow hS
          rw [Nat.shiftLeft_eq, Nat.one_mul]
          exact Nat.pow_lt_pow_right (by decide) (by omega)
        · rw [hcK]
          apply Nat.eq_of_testBit_eq
          intro i
          change ((S ||| liveBit) ||| 1 <<< rtK K u t).testBit i = _
          simp only [Nat.testBit_or]
          cases S.testBit i <;> cases liveBit.testBit i <;> cases (1 <<< rtK K u t).testBit i <;>
            rfl
        · rw [if_pos (by
              simp only [Bool.and_eq_true, decide_eq_true_eq]
              exact ⟨⟨⟨hu, ht⟩, hgu⟩, hSt⟩), tabsK_rt hu ht]
      · have hcK : band (Nat.blt u (nroots m)) (band (Nat.blt t (nroots m))
            (band (bit gens u) (bit (S ||| liveBit) t))) = false := by
          cases e : band (Nat.blt u (nroots m)) (band (Nat.blt t (nroots m))
              (band (bit gens u) (bit (S ||| liveBit) t)))
          · rfl
          · exfalso
            rw [band_eq_true, band_eq_true, band_eq_true, Nat.blt_eq, Nat.blt_eq] at e
            obtain ⟨hu, ht, hgu, hSt⟩ := e
            rw [bit_eq] at hgu
            rw [wk_bit_live (by omega)] at hSt
            exact hc ⟨hu, ht, hgu, hSt⟩
        refine Or.inl ⟨by rw [hcK]; rfl, ?_⟩
        rw [if_neg]
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        exact fun ⟨⟨⟨a, b⟩, c⟩, d⟩ => hc ⟨a, b, c, d⟩

theorem wk_gen {m : Fin 6} {K : KT} {fx hx fx' hx' : Nat} (hT : TabsOK m K fx hx fx' hx')
    {gens c : Nat} {L : KL} (h : genK K gens c L = true) :
    Chk.genOK (tabsK m K) (nroots m) gens c (decDer L) = true := by
  obtain ⟨n, P⟩ := L
  simp only [genK, band_eq_true] at h
  obtain ⟨hg, hsub, hS0, hcS⟩ := h
  rw [Nat.blt_eq, hT.hr, xk_pow] at hg
  have hr := wk_nroots_le m
  have hg' : gens < 2 ^ 128 :=
    Nat.lt_of_lt_of_le hg (Nat.pow_le_pow_right (by decide) hr)
  rcases wk_deriv hT hg' P n with ⟨h0, -⟩ | ⟨S, -, hK, hN⟩
  · rw [h0] at hS0
    exact Bool.noConfusion hS0
  · unfold Chk.genOK
    rw [hN]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    rw [subK_eq] at hsub
    refine ⟨⟨hg, hsub⟩, ?_⟩
    rw [hK, subK_eq, truncK_eq, hT.hr, Chk.subN, wk_and_live (wk_trunc_lt _ c hr)] at hcS
    exact hcS

theorem wk_join {m : Fin 6} {K : KT} {fx hx fx' hx' : Nat} (hT : TabsOK m K fx hx fx' hx')
    {l k t : Nat} {L : KL} (h : joinK K l k t L = true) :
    Chk.joinOK (tabsK m K) (nroots m) l k t (decDer L) = true := by
  obtain ⟨n, P⟩ := L
  simp only [joinK, band_eq_true] at h
  obtain ⟨ht, hS0, hbit⟩ := h
  rw [Nat.blt_eq, hT.hr] at ht
  rw [hT.hr] at hS0 hbit
  have hr := wk_nroots_le m
  rcases wk_deriv hT (gens := Nat.lor (truncK (nroots m) l) (truncK (nroots m) k))
    (Nat.or_lt_two_pow (wk_trunc_lt _ l hr) (wk_trunc_lt _ k hr)) P n with
    ⟨h0, -⟩ | ⟨S, -, hK, hN⟩
  · rw [h0] at hS0
    exact Bool.noConfusion hS0
  · have hN' : Chk.derivN (tabsK m K) (nroots m)
        (Chk.trunc (nroots m) l ||| Chk.trunc (nroots m) k) (decDer ⟨n, P⟩) = some S := hN
    unfold Chk.joinOK
    rw [hN']
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    rw [hK, wk_bit_live (by omega)] at hbit
    exact ⟨ht, hbit⟩

theorem wk_decMat {B i j : Nat} (hi : i < 8) (hj : j < 8) :
    (decMat B)[i]![j]! = ((ln2 B (8 * i + j) : Nat) : Int) := by
  rw [decMat, getElem!_map_range _ hi, getElem!_map_range _ hj]

theorem wk_decVec {x l : Nat} (hl : l < 8) : (decVec x)[l]! = ((ln2 x l : Nat) : Int) := by
  rw [decVec, getElem!_map_range _ hl]

theorem wk_anyN {n : Nat} {p : Nat → Bool} : anyN n p = true ↔ ∃ i < n, p i = true := by
  induction n with
  | zero => exact ⟨fun h => Bool.noConfusion h, fun ⟨i, hi, _⟩ => absurd hi (Nat.not_lt_zero i)⟩
  | succ n ih =>
    have e : anyN (n + 1) p = bor (p n) (anyN n p) := rfl
    rw [e, bor_iff, ih]
    constructor
    · rintro (h | ⟨i, hi, h⟩)
      · exact ⟨n, Nat.lt_succ_self n, h⟩
      · exact ⟨i, by omega, h⟩
    · rintro ⟨i, hi, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact Or.inr ⟨i, hi, h⟩
      · exact Or.inl h

theorem wk_ndel (i j : Nat) : (3 : Int) ∣ (ndel i j : Int) + (if i = j then 1 else 0) := by
  rw [ndel, nif_eq, nbeq_eq]
  by_cases h : i = j
  · rw [if_pos (by simp [h]), if_pos h]
    omega
  · rw [if_neg (by simp [h]), if_neg h]
    omega

theorem wk_fin {n e : Nat} {f : Nat → Nat} {g : Nat → Int} {δ : Int}
    (h : ∀ k < n, (3 : Int) ∣ (f k : Int) - g k) (he : (3 : Int) ∣ (e : Int) + δ)
    (hs : Nat.beq (Nat.mod (Nat.add (sumN n f) e) 3) 0 = true) :
    (Nat.fold n (fun k _ s => s + g k) 0 - δ) % 3 = 0 := by
  have key : (3 : Int) ∣ ((sumN n f : Nat) : Int) - Nat.fold n (fun k _ s => s + g k) 0 := by
    rw [sumN_cast]
    exact fold_dvd h
  simp only [Nat.beq_eq, xk_mod, xk_add] at hs
  generalize sumN n f = S at key hs
  generalize Nat.fold n (fun k _ s => s + g k) 0 = F at key ⊢
  omega

theorem wk_fin0 {n : Nat} {f : Nat → Nat} {g : Nat → Int}
    (h : ∀ k < n, (3 : Int) ∣ (f k : Int) - g k) (hs : Nat.beq (Nat.mod (sumN n f) 3) 0 = true) :
    Nat.fold n (fun k _ s => s + g k) 0 % 3 = 0 := by
  have key : (3 : Int) ∣ ((sumN n f : Nat) : Int) - Nat.fold n (fun k _ s => s + g k) 0 := by
    rw [sumN_cast]
    exact fold_dvd h
  simp only [Nat.beq_eq, xk_mod] at hs
  generalize sumN n f = S at key hs
  generalize Nat.fold n (fun k _ s => s + g k) 0 = F at key ⊢
  omega

theorem wk_line {m : Fin 6} {K : KT} {fx hx fx' hx' : Nat} (hT : TabsOK m K fx hx fx' hx')
    {w : KLin} {cnt : Nat} {pos : Nat → Nat} {cz B : Nat} (h : lineK K w cnt pos cz B = true) :
    Chk.lineOK (tabsK m K) (dim m) (nroots m) ((List.range cnt).map fun i => nodeK w (pos i)) cz
      (decMat B) = true := by
  simp only [lineK, band_eq_true] at h
  obtain ⟨hcz, hp, hcnt, hrows, hmat⟩ := h
  rw [Nat.blt_eq, hT.hd, xk_pow] at hcz
  rw [Nat.blt_eq, hT.hd, pivK_eq] at hp
  have hcnt' : cnt + 1 = dim m := by
    rw [← hT.hd]
    exact Nat.eq_of_beq_eq_true hcnt
  have hrows' : ∀ i < cnt, nodeK w (pos i) < nroots m ∧
      ((tabsK m K).zm[cz]!).testBit (nodeK w (pos i)) = true := by
    intro i hi
    have := allN_iff.mp hrows i hi
    rw [band_eq_true, Nat.blt_eq, hT.hr, bit_eq, zmK_eq hT] at this
    exact this
  have hd8 := wk_dim_le m
  unfold Chk.lineOK
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, nat_all_iff]
  refine ⟨⟨⟨⟨hcz, hp⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [List.length_map, List.length_range]
    exact hcnt'
  · rw [all_map_range, allN_iff]
    intro i hi
    obtain ⟨h1, h2⟩ := hrows' i hi
    simp [h1, h2]
  · intro i hi j hj
    have hij := allN_iff.mp (allN_iff.mp hmat i (by rw [hT.hd]; exact hi)) j
      (by rw [hT.hd]; exact hj)
    rw [hT.hd, pivK_eq] at hij
    refine wk_fin ?_ (wk_ndel i j) hij
    intro k hk
    rw [wk_decMat (by omega) (by omega)]
    apply dvd_term'
    unfold Chk.phiN
    by_cases hk1 : k + 1 < dim m
    · have hkc : k < cnt := by omega
      rw [wk_nif_pos (b := Nat.blt (Nat.succ k) (dim m)) (Nat.blt_eq.mpr hk1), if_pos hk1,
        wk_getD_map _ hkc, tabsK_f (hrows' k hkc).1 hj]
      exact fK_dvd hT (hrows' k hkc).1 hj
    · have e1 : Nat.blt (Nat.succ k) (dim m) = false := by
        rw [Bool.eq_false_iff]
        intro e
        exact hk1 (Nat.blt_eq.mp e)
      rw [wk_nif_neg e1, if_neg hk1, nif_eq, nbeq_eq]
      by_cases hjp : j = Chk.pivN (dim m) cz
      · rw [if_pos hjp, if_pos (beq_iff_eq.mpr hjp)]
        omega
      · rw [if_neg hjp, if_neg (fun e => hjp (beq_iff_eq.mp e))]
        omega

theorem wk_inv {tc n k B : Nat} (hk : k ≤ 8) (h : invCK tc n k idK B = true) :
    Chk.invOK k (Chk.cartanN tc n) (decMat B) = true := by
  unfold Chk.invOK
  rw [nat_all_iff]
  intro i hi
  rw [nat_all_iff]
  intro j hj
  have hij := allN_iff.mp (allN_iff.mp h i hi) j hj
  simp only [idK] at hij
  rw [beq_iff_eq]
  refine wk_fin ?_ (wk_ndel i j) hij
  intro l hl
  rw [wk_decMat (by omega) (by omega)]
  apply dvd_term'
  have := wk_cart tc n l j
  omega

theorem wk_sing {tc n k x : Nat} (hk : k ≤ 8) (h : singK tc n k x = true) :
    Chk.singOK k (Chk.cartanN tc n) (decVec x) = true := by
  simp only [singK, band_eq_true] at h
  obtain ⟨hany, hall⟩ := h
  unfold Chk.singOK
  rw [Bool.and_eq_true]
  constructor
  · obtain ⟨l, hl, hx⟩ := wk_anyN.mp hany
    rw [List.any_eq_true]
    refine ⟨l, List.mem_range.mpr hl, ?_⟩
    rw [wk_decVec (by omega)]
    rw [bnot_eq, nbeq_eq] at hx
    simp only [xk_mod, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq] at hx
    simp only [bne_iff_ne, ne_eq]
    omega
  · rw [nat_all_iff]
    intro i hi
    rw [beq_iff_eq]
    refine wk_fin0 ?_ (allN_iff.mp hall i hi)
    intro l hl
    rw [wk_decVec (by omega)]
    apply dvd_term
    have := wk_cart tc n i l
    omega

theorem wk_indep {m : Fin 6} {K : KT} {fx hx fx' hx' : Nat} (hT : TabsOK m K fx hx fx' hx')
    {w : KLin} {B : Nat} (h8 : rkW w ≤ 8) (hn : ∀ i < rkW w, nodeK w i < nroots m)
    (h : indepK K w B = true) : Chk.indepOK (tabsK m K) (dim m) (decLin w) (decMat B) = true := by
  unfold Chk.indepOK
  simp only [nat_all_iff]
  rw [← wk_rkW]
  intro i hi j hj
  have hij := allN_iff.mp (allN_iff.mp h i hi) j hj
  rw [hT.hd] at hij
  rw [beq_iff_eq]
  refine wk_fin ?_ (wk_ndel i j) hij
  intro l hl
  have hd8 := wk_dim_le m
  rw [wk_decMat (by omega) (by omega), wk_nodeN, tabsK_h (hn i hi) hl]
  exact dvd_term (hK_dvd hT (hn i hi) hl)

theorem wk_nbr {m : Fin 6} {K : KT} {fx hx fx' hx' : Nat} (hT : TabsOK m K fx hx fx' hx')
    {cz k : Nat} {w : KLin} {L : KL} {B : Nat} (h : nbrK K cz k w L B = true) :
    Chk.nbrOK (tabsK m K) m cz k (decLin w) (decDer L) (decMat B) = true ∧ rkW w ≤ 8 := by
  simp only [nbrK, band_eq_true] at h
  obtain ⟨hL, hg, hl, hb⟩ := h
  obtain ⟨hlin, h8, -, -, -⟩ := wk_lin hT hL
  refine ⟨?_, h8⟩
  unfold Chk.nbrOK
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨hlin, ?_⟩, ?_⟩, ?_⟩
  · rw [← wk_nodeMask w (p := fun _ => true) (q := fun _ => true) (fun _ => rfl)]
    exact wk_gen hT hg
  · rw [wk_nodeList_true]
    exact wk_line hT hl
  · rw [← wk_notB2 hT]
    exact hb

theorem wk_common {m : Fin 6} {K : KT} {fx hx fx' hx' : Nat} (hT : TabsOK m K fx hx fx' hx')
    {cv cz l k : Nat} {w : KLin} {Ll Lk : KL} {Bl Bk : Nat}
    (h : commonK K cv cz l k w Ll Lk Bl Bk = true) :
    Chk.commonOK (tabsK m K) m cv cz l k
      { w := decLin w, Lℓ := decDer Ll, Lk := decDer Lk, Bℓ := decMat Bl, Bk := decMat Bk } =
      true := by
  simp only [commonK, band_eq_true] at h
  obtain ⟨hL, hg1, hg2, hl1, hl2, hb1, hb2⟩ := h
  obtain ⟨hlin, -, ha, hb, -⟩ := wk_lin hT hL
  unfold Chk.commonOK
  simp only [Bool.and_eq_true, wk_dl_a, wk_dl_b]
  refine ⟨⟨⟨⟨⟨⟨hlin, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [← wk_nodeMask w (p := fun i => bnot (Nat.beq i w.a)) (q := fun i => i != w.a)
      (fun i => by rw [bnot_eq, nbeq_eq]; rfl)]
    exact wk_gen hT hg1
  · rw [← wk_nodeMask w (p := fun i => bnot (Nat.beq i w.b)) (q := fun i => i != w.b)
      (fun i => by rw [bnot_eq, nbeq_eq]; rfl)]
    exact wk_gen hT hg2
  · rw [wk_nodeList_off w ha]
    exact wk_line hT hl1
  · rw [wk_nodeList_off w hb]
    exact wk_line hT hl2
  · rw [← wk_notB2 hT]
    exact hb1
  · rw [← wk_notB2 hT]
    exact hb2

theorem wk_amb {m : Fin 6} {K : KT} {fx hx fx' hx' : Nat} (hT : TabsOK m K fx hx fx' hx')
    {cv cz l k : Nat} {w : KLin} {Lk La : KL} {Bk Bb : Nat}
    (h : ambK K cv cz l k w Lk La Bk Bb = true) :
    Chk.ambOK (tabsK m K) m cv cz l k
      { w := decLin w, Lk := decDer Lk, La := decDer La, Bk := decMat Bk, Bb := decMat Bb } =
      true := by
  simp only [ambK, band_eq_true] at h
  obtain ⟨hL, hg, hl, hj, hcv, hab, hd, hind, hb1, hb2⟩ := h
  obtain ⟨hlin, h8, ha, -, hn⟩ := wk_lin hT hL
  unfold Chk.ambOK
  simp only [Bool.and_eq_true, decide_eq_true_eq, wk_dl_a, wk_dl_b]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨hlin, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [← wk_nodeMask w (p := fun i => bnot (Nat.beq i w.a)) (q := fun i => i != w.a)
      (fun i => by rw [bnot_eq, nbeq_eq]; rfl)]
    exact wk_gen hT hg
  · rw [wk_nodeList_off w ha]
    exact wk_line hT hl
  · rw [wk_nodeN]
    exact wk_join hT hj
  · rwa [Nat.blt_eq, hT.hd, xk_pow] at hcv
  · rw [List.all_eq_true]
    intro t ht
    rw [Chk.nodeList, List.mem_map] at ht
    obtain ⟨i, hi, rfl⟩ := ht
    rw [List.mem_filter, List.mem_range] at hi
    obtain ⟨hi, hne⟩ := hi
    have hi' : i < rkW w := by rw [wk_rkW]; exact hi
    have := allN_iff.mp hab i hi'
    rw [bor_iff, bor_iff, bit_eq, zmK_eq hT, nbeq_eq, nbeq_eq] at this
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hne
    rw [wk_nodeN]
    rcases this with (h1 | h1) | h1
    · exact absurd (beq_iff_eq.mp h1) hne.1
    · exact absurd (beq_iff_eq.mp h1) hne.2
    · exact h1
  · unfold Chk.basisOK
    rw [Bool.and_eq_true, beq_iff_eq, ← wk_rkW]
    refine ⟨?_, wk_indep hT h8 hn hind⟩
    rw [hT.hd] at hd
    exact Nat.eq_of_beq_eq_true hd
  · rw [← wk_notB2 hT]
    exact hb1
  · rw [← wk_notB2 hT]
    exact hb2

theorem wk_nodup {p : KL}
    (h : allN p.len (fun i => allN i fun j => bnot (Nat.beq (ln4 p.P i) (ln4 p.P j))) = true) :
    (decPerm p).Nodup := by
  have hne : ∀ i < p.len, ∀ j < i, ln4 p.P i ≠ ln4 p.P j := by
    intro i hi j hj e
    have := allN_iff.mp (allN_iff.mp h i hi) j hj
    rw [e, bnot_eq, nbeq_eq, beq_self_eq_true] at this
    exact Bool.noConfusion this
  unfold decPerm List.Nodup
  rw [List.pairwise_map]
  refine (List.pairwise_lt_range (n := p.len)).imp_of_mem fun {a b} _ hb hab => ?_
  exact fun e => hne b (List.mem_range.mp hb) a hab e.symm

theorem wk_getD_perm {p : KL} {i : Nat} (hi : i < p.len) : (decPerm p).getD i 0 = ln4 p.P i :=
  wk_getD_map _ hi

theorem wk_ambD {m : Fin 6} {K : KT} {fx hx fx' hx' : Nat} (hT : TabsOK m K fx hx fx' hx')
    {cv cz l k : Nat} {w : KLin} {Lk La : KL} {Bk Bb : Nat} {perm : KL} {hh : Nat}
    (h : ambDK K cv cz l k w Lk La Bk Bb perm hh = true) :
    Chk.ambDOK (tabsK m K) m cv cz l k
      { w := decLin w, Lk := decDer Lk, La := decDer La, Bk := decMat Bk, Bb := decMat Bb }
      (decPerm perm) hh = true := by
  simp only [ambDK, band_eq_true] at h
  obtain ⟨hamb, h3, hrk, hlen, hnd, hrange, hcart⟩ := h
  have hlen' : perm.len = 2 * hh := Nat.eq_of_beq_eq_true hlen
  unfold Chk.ambDOK
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, nat_all_iff, wk_dl_a, wk_dl_tc,
    wk_dl_n]
  refine ⟨⟨⟨⟨⟨⟨wk_amb hT hamb, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · exact Nat.ble_eq.mp h3
  · rw [← wk_rk]
    exact Nat.eq_of_beq_eq_true hrk
  · rw [decPerm, List.length_map, List.length_range]
    exact hlen'
  · exact wk_nodup hnd
  · rw [decPerm, all_map_range, allN_iff]
    intro i hi
    have := allN_iff.mp hrange i hi
    rw [band_eq_true, Nat.blt_eq, bnot_eq, nbeq_eq, rkW, wk_rk] at this
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨decide_eq_true this.1, this.2⟩
  · intro i hi j hj
    have hij := allN_iff.mp (allN_iff.mp hcart i hi) j hj
    rw [nbeq_eq, beq_iff_eq] at hij
    simp only [xk_mul] at hij
    have e1 := wk_cart w.tc w.n (ln4 perm.P i) (ln4 perm.P j)
    have e2 := wk_cart 3 (2 * hh) i j
    rw [hij] at e1
    rw [wk_getD_perm (by omega), wk_getD_perm (by omega)]
    omega

theorem wk_lab {m : Fin 6} {K : KT} {fx hx fx' hx' : Nat} (hT : TabsOK m K fx hx fx' hx')
    {c t r n : Nat} (ht : t < 32) (hr : r < 32) (h : Nat.beq (labK K c) (labC t r n) = true) :
    Chk.labelOf (tabsK m K) m c = (t, r, n) := by
  have e := Nat.eq_of_beq_eq_true h
  rw [labK_eq hT] at e
  have hb := labelOf_lt (tabsK m K) m c
  generalize Chk.labelOf (tabsK m K) m c = x at e hb ⊢
  obtain ⟨x1, x2, x3⟩ := x
  dsimp only at e hb
  obtain ⟨a1, a2, a3⟩ := labC_parts (n := x3) hb.1 hb.2
  obtain ⟨b1, b2, b3⟩ := labC_parts (n := n) ht hr
  rw [e] at a1 a2 a3
  rw [a1] at b1
  rw [a2] at b2
  rw [a3] at b3
  rw [b1, b2, b3]

theorem wk_d5 {m : Fin 6} {K : KT} {fx hx fx' hx' : Nat} (hT : TabsOK m K fx hx fx' hx')
    {cv cz l j k : Nat} {w : KLin} {Lk La : KL} {Bk Bb : Nat} {Lj : KL}
    (h : d5K K cv cz l j k w Lk La Bk Bb Lj = true) :
    Chk.d5OK (tabsK m K) m cv cz l j k
      { w := decLin w, Lk := decDer Lk, La := decDer La, Bk := decMat Bk, Bb := decMat Bb }
      (decDer Lj) = true := by
  simp only [d5K, band_eq_true, bor_iff] at h
  obtain ⟨hamb, htc, hn, ha, hb, hg, hnb, hlab⟩ := h
  unfold Chk.d5OK
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, wk_dl_a, wk_dl_b, wk_dl_tc, wk_dl_n]
  refine ⟨⟨⟨⟨⟨⟨⟨wk_amb hT hamb, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · exact Nat.eq_of_beq_eq_true htc
  · exact Nat.eq_of_beq_eq_true hn
  · exact Nat.eq_of_beq_eq_true ha
  · rcases hb with hb | hb | hb
    · exact Or.inl (Or.inl (Nat.eq_of_beq_eq_true hb))
    · exact Or.inl (Or.inr (Nat.eq_of_beq_eq_true hb))
    · exact Or.inr (Nat.eq_of_beq_eq_true hb)
  · rw [← wk_nodeMask w (p := fun i => band (bnot (Nat.beq i w.a)) (bnot (Nat.beq i w.b)))
      (q := fun i => i != w.a && i != w.b)
      (fun i => by rw [band_eq_and, bnot_eq, bnot_eq, nbeq_eq, nbeq_eq]; rfl)]
    exact wk_gen hT hg
  · rw [← wk_notB2 hT]
    exact hnb
  · rcases hlab with hl | hl
    · exact Or.inl (wk_lab hT (by decide) (by decide) hl)
    · exact Or.inr (wk_lab hT (by decide) (by decide) hl)

theorem witK_sound {m : Fin 6} {K : KT} {fx hx fx' hx' : Nat} (hT : TabsOK m K fx hx fx' hx')
    {cv cy cz : Nat} {X : KWit} (h : witK K cv cy cz X = true) :
    Chk.extWitOK (tabsK m K) m cv cy cz (decWit X) = true := by
  cases X
  case twoL =>
    have h' : twoNodeK (labK K (zmK K cv)) (labK K (Nat.land (zmK K cv) (zmK K cy))) = true := h
    rw [twoNodeK_labK hT, zmK_eq hT, zmK_eq hT, xk_land] at h'
    exact h'
  case twoK =>
    have h' : twoNodeK (labK K (zmK K cz)) (labK K (Nat.land (zmK K cv) (zmK K cy))) = true := h
    rw [twoNodeK_labK hT, zmK_eq hT, zmK_eq hT, zmK_eq hT, xk_land] at h'
    exact h'
  case leaf w Ll Lk Bl Bk =>
    have h' : band (commonK K cv cz (zmK K cv) (zmK K cz) w Ll Lk Bl Bk)
        (leafK w.tc w.n w.b) = true := h
    rw [band_eq_true, zmK_eq hT, zmK_eq hT] at h'
    simp only [decWit, Chk.extWitOK, Chk.leafModelOK, Bool.and_eq_true]
    refine ⟨wk_common hT h'.1, ?_⟩
    rw [← wk_leaf]
    exact h'.2
  case inner w L B Bi =>
    have h' : band (nbrK K cz (zmK K cz) w L B)
        (band (invCK w.tc w.n (rkW w) idK Bi) (innerK w.tc w.n)) = true := h
    rw [band_eq_true, band_eq_true, zmK_eq hT] at h'
    obtain ⟨hn, hi, hin⟩ := h'
    obtain ⟨hn', h8⟩ := wk_nbr hT hn
    simp only [decWit, Chk.extWitOK, Bool.and_eq_true]
    rw [← wk_rkW, ← wk_inner]
    exact ⟨⟨hn', wk_inv h8 hi⟩, hin⟩
  case det w L B x =>
    have h' : band (nbrK K cz (zmK K cz) w L B)
        (band (singK w.tc w.n (rkW w) x) (Nat.beq K.d (Nat.succ (rkW w)))) = true := h
    rw [band_eq_true, band_eq_true, zmK_eq hT] at h'
    obtain ⟨hn, hs, hd⟩ := h'
    obtain ⟨hn', h8⟩ := wk_nbr hT hn
    simp only [decWit, Chk.extWitOK, Bool.and_eq_true, Chk.detCondN, decide_eq_true_eq]
    rw [← wk_rkW]
    refine ⟨⟨hn', wk_sing h8 hs⟩, ?_⟩
    rw [← hT.hd]
    exact Nat.eq_of_beq_eq_true hd
  case ambD w Lk La Bk Bb p hh =>
    have h' : ambDK K cv cz (zmK K cv) (zmK K cz) w Lk La Bk Bb p hh = true := h
    rw [zmK_eq hT, zmK_eq hT] at h'
    simp only [decWit, Chk.extWitOK]
    exact wk_ambD hT h'
  case d5 w Lk La Bk Bb Lj =>
    have h' : d5K K cv cz (zmK K cv) (Nat.land (zmK K cv) (zmK K cy)) (zmK K cz) w Lk La Bk Bb
        Lj = true := h
    rw [zmK_eq hT, zmK_eq hT, zmK_eq hT, xk_land] at h'
    simp only [decWit, Chk.extWitOK]
    exact wk_d5 hT h'

theorem walkK_succ (T : KT) (cv cref n : Nat) (ps : List KPlane) :
    walkK T cv cref (n + 1) ps = Bool.rec (motive := fun _ => Bool) (walkK T cv cref n ps)
      (List.rec (motive := fun _ => Bool) false
        (fun P tl _ => band (Nat.beq P.cy n) (band (planeK T cv cref P) (walkK T cv cref n tl))) ps)
      (canonK T.d cv n) := rfl

theorem pick_succ (d cv n : Nat) (ps : List KPlane) (cy : Nat) :
    pick d cv (n + 1) ps cy = if Chk.canonN d cv n then
      (match ps with
        | [] => none
        | P :: tl => if cy = n then some P else pick d cv n tl cy)
    else pick d cv n ps cy := rfl

theorem walk_sound {K : KT} {d : Nat} (hd : K.d = d) {cv cref : Nat} :
    ∀ {n : Nat} {ps : List KPlane}, walkK K cv cref n ps = true → ∀ cy < n,
      Chk.canonN d cv cy = true →
      ∃ P, pick d cv n ps cy = some P ∧ P.cy = cy ∧ planeK K cv cref P = true := by
  intro n
  induction n with
  | zero =>
    intro ps _ cy hcy
    exact absurd hcy (Nat.not_lt_zero cy)
  | succ n ih =>
    intro ps hw cy hcy hc
    rw [walkK_succ, hd, canonK_eq] at hw
    rw [pick_succ]
    cases hcn : Chk.canonN d cv n
    · rw [hcn] at hw
      have hne : cy ≠ n := by
        rintro rfl
        rw [hc] at hcn
        exact Bool.noConfusion hcn
      rw [if_neg (by simp)]
      exact ih hw cy (by omega) hc
    · rw [hcn] at hw
      rw [if_pos rfl]
      cases ps with
      | nil => exact Bool.noConfusion hw
      | cons P tl =>
        have hw' : band (Nat.beq P.cy n) (band (planeK K cv cref P) (walkK K cv cref n tl)) = true :=
          hw
        simp only [band_eq_true, Nat.beq_eq] at hw'
        obtain ⟨h1, h2, h3⟩ := hw'
        by_cases hcn' : cy = n
        · subst hcn'
          exact ⟨P, by simp, h1, h2⟩
        · obtain ⟨Q, hQ, hQ1, hQ2⟩ := ih h3 cy (by omega) hc
          exact ⟨Q, by simp [hcn', hQ], hQ1, hQ2⟩

theorem candsK_sound {K : KT} {cv cy cref : Nat} :
    ∀ {ws : List KWit} {i : Nat}, candsK K cv cy cref ws i = true →
      ∀ j, i ≤ j → j < 6 →
        bor (refCK K cv (combK K.d cv cy (j / 2) (j % 2 + 1))
            (ln128 cref (combK K.d cv cy (j / 2) (j % 2 + 1))))
          (witK K cv cy (combK K.d cv cy (j / 2) (j % 2 + 1)) (ws.getD (j - i) .twoL)) = true := by
  intro ws
  induction ws with
  | nil =>
    intro i h j hij hj
    have h' : Nat.beq i 6 = true := h
    rw [Nat.beq_eq] at h'
    omega
  | cons X tl ih =>
    intro i h j hij hj
    have h' : band (bor (refCK K cv (combK K.d cv cy (i / 2) (i % 2 + 1))
          (ln128 cref (combK K.d cv cy (i / 2) (i % 2 + 1))))
        (witK K cv cy (combK K.d cv cy (i / 2) (i % 2 + 1)) X))
        (candsK K cv cy cref tl (i + 1)) = true := h
    rw [band_eq_true] at h'
    by_cases hji : j = i
    · subst hji
      rw [Nat.sub_self]
      exact h'.1
    · have := ih h'.2 j (by omega) hj
      have e : j - i = (j - (i + 1)) + 1 := by omega
      rw [e]
      exact this

theorem scanLineK_sound {m : Fin 6} {K : KT} {fx hx fx' hx' : Nat} (hT : TabsOK m K fx hx fx' hx')
    {L : KLine} (hL : scanLineK K L = true) : ExtLineOK m K L := by
  have hd := hT.hd
  unfold ExtLineOK
  have hL' : bor (refLK K L.cv L.ref) (walkK K L.cv L.cref (Nat.pow 3 K.d) L.planes) = true := hL
  rw [bor_iff] at hL'
  rw [Chk.scanLineN, Bool.or_eq_true]
  rcases hL' with hL' | hL'
  · left
    obtain ⟨e, he, hok⟩ := refLK_sound hT hL'
    simp only [searchOf, if_pos rfl, he]
    exact hok
  · right
    rw [nat_all_iff]
    intro cy hcy
    rw [Bool.or_eq_true, Bool.or_eq_true]
    by_cases hc : Chk.canonN (dim m) L.cv cy = true
    · rw [hd] at hL'
      obtain ⟨P, hP, hPcy, hpl⟩ := walk_sound hd hL' cy hcy hc
      have hP' : pick (dim m) L.cv (3 ^ dim m) L.planes cy = some P := hP
      have hpl' : bor (refPK K L.cv P.cy P.ref) (candsK K L.cv P.cy L.cref P.wits 0) = true := hpl
      rw [bor_iff, hPcy] at hpl'
      rcases hpl' with hr | hr
      · left
        right
        obtain ⟨e, he, hok⟩ := refPK_sound hT hr
        simp only [searchOf, hP', Option.bind_some, he]
        exact hok
      · right
        rw [Chk.candScanN, nat_all_iff]
        intro a ha
        rw [nat_all_iff]
        intro b' hb'
        rw [Bool.or_eq_true]
        have hj := candsK_sound hr (2 * a + b') (Nat.zero_le _) (by omega)
        have e1 : (2 * a + b') / 2 = a := by omega
        have e2 : (2 * a + b') % 2 = b' := by omega
        rw [e1, e2, Nat.sub_zero, bor_iff, hd, combK_eq] at hj
        rcases hj with hj | hj
        · left
          obtain ⟨e, he, hok⟩ := refCK_sound hT hj
          simp only [searchOf, he]
          exact hok
        · right
          have hw := witK_sound hT hj
          simp only [witOf, hP', Nat.add_sub_cancel]
          exact hw
    · left
      left
      simp [hc]

end CFSG.ExcExtK

end

end
