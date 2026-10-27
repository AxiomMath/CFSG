module

public import Certificates.Data.Kernel.WE6OffK
public import Certificates.Data.WE6Offender
public import CFSG.Certificates.Kernel.TwD5ReflKSound
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Bool
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.KC.WE6K

open CFSG.KC.TwD5R Certificates.WE6Offender
open scoped Matrix

theorem allK_eq_true {n : Nat} {p : Nat → Bool} : allK n p = true ↔ ∀ k < n, p k = true := by
  induction n with
  | zero => exact ⟨fun _ k hk => absurd hk (Nat.not_lt_zero _), fun _ => rfl⟩
  | succ n ih =>
    change andB (allK n p) (p n) = true ↔ _
    rw [andB_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ k hk
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
      · exact h1 k hk
      · exact h2
    · intro h
      exact ⟨fun k hk => h k (Nat.lt_succ_of_lt hk), h n (Nat.lt_succ_self n)⟩

theorem sumK_eq (n : Nat) (f : Nat → Nat) : sumK n f = ∑ k ∈ Finset.range n, f k := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Nat.add (sumK n f) (f n) = _
    rw [Finset.sum_range_succ, ← ih]
    rfl

theorem sumK_congr {n : Nat} {f g : Nat → Nat} (h : ∀ k < n, f k = g k) : sumK n f = sumK n g := by
  rw [sumK_eq, sumK_eq]
  exact Finset.sum_congr rfl fun k hk => h k (Finset.mem_range.mp hk)

theorem eqB_eq_true {a b : Bool} : eqB a b = true ↔ a = b := by
  cases a <;> cases b <;> decide

theorem beq_false_iff {a b : Nat} : Nat.beq a b = false ↔ a ≠ b := by
  rw [← Bool.not_eq_true, Nat.beq_eq]

theorem bit_eq (m i : Nat) : bit m i = m.testBit i := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  change Nat.beq ((m >>> i) &&& 1) 1 = _
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  by_cases h : m / 2 ^ i % 2 = 1
  · rw [h]
    decide
  · rw [decide_eq_false h]
    exact beq_false_iff.mpr h

theorem bit_land (A B a : Nat) : bit (Nat.land A B) a = (bit A a && bit B a) := by
  rw [bit_eq, bit_eq, bit_eq]
  exact Nat.testBit_and A B a

theorem rngK_iff {lo n : Nat} {q : Nat → Bool} :
    rngK lo n q = true ↔ ∀ i, lo ≤ i → i < lo + n → q i = true := by
  rw [rngK, allK_eq_true]
  constructor
  · intro h i h1 h2
    have := h (i - lo) (by omega)
    have e : lo + (i - lo) = i := by omega
    rw [← e]
    exact this
  · intro h t ht
    exact h (lo + t) (by omega) (by omega)

theorem all81 {q : Nat → Bool} (h0 : rngK 0 27 q = true) (h1 : rngK 27 27 q = true)
    (h2 : rngK 54 27 q = true) : ∀ i < 81, q i = true := by
  intro i hi
  rcases (by omega : i < 27 ∨ (27 ≤ i ∧ i < 54) ∨ 54 ≤ i) with h | h | h
  · exact rngK_iff.mp h0 i (by omega) (by omega)
  · exact rngK_iff.mp h1 i h.1 (by omega)
  · exact rngK_iff.mp h2 i h (by omega)

theorem getN_eq (l : List Nat) (i : Nat) : getN l i = l.getD i 0 := by
  induction l generalizing i with
  | nil => rfl
  | cons a t ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i

theorem getLL_eq (l : List (List Nat)) (i : Nat) : getLL l i = l.getD i [] := by
  induction l generalizing i with
  | nil => rfl
  | cons a t ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i

theorem memK_eq_true {a : Nat} {l : List Nat} : memK a l = true ↔ a ∈ l := by
  induction l with
  | nil => exact ⟨fun h => (Bool.false_ne_true h).elim, fun h => absurd h List.not_mem_nil⟩
  | cons b t ih =>
    change orB (Nat.beq a b) (memK a t) = true ↔ _
    rw [orB_eq_true, ih, List.mem_cons, Nat.beq_eq]

theorem nodupK_nodup {l : List Nat} (h : nodupK l = true) : l.Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons a t ih =>
    change andB (notB (memK a t)) (nodupK t) = true at h
    obtain ⟨h1, h2⟩ := andB_eq_true.mp h
    rw [notB_eq_true] at h1
    refine List.nodup_cons.mpr ⟨fun ha => ?_, ih h2⟩
    rw [← memK_eq_true, h1] at ha
    cases ha

theorem bit_maskOf {l : List Nat} {a : Nat} : bit (maskOf l) a = true ↔ a ∈ l := by
  rw [bit_eq]
  induction l with
  | nil =>
    change Nat.testBit 0 a = true ↔ _
    simp
  | cons b t ih =>
    change ((1 <<< b) ||| maskOf t).testBit a = true ↔ _
    rw [List.mem_cons, ← ih, Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow,
      Bool.or_eq_true, decide_eq_true_eq, eq_comm]

theorem countIn_eq (l : List Nat) (M : Nat) :
    countIn l M = (l.filter fun a => bit M a).length := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    change Nat.add (selN (bit M a) 1 0) (countIn t M) = _
    rw [List.filter_cons, ih]
    cases h : bit M a
    · simp only [selN, Bool.false_eq_true, if_false]
      exact Nat.zero_add _
    · simp only [selN, if_true, List.length_cons]
      exact Nat.add_comm _ _

theorem card_inter_le (li lj : List Nat) :
    (li.toFinset ∩ lj.toFinset).card ≤ countIn lj (maskOf li) := by
  rw [countIn_eq]
  have e : li.toFinset ∩ lj.toFinset = (lj.filter fun a => bit (maskOf li) a).toFinset := by
    ext a
    simp only [Finset.mem_inter, List.mem_toFinset, List.mem_filter, bit_maskOf]
    tauto
  rw [e]
  exact List.toFinset_card_le _

theorem card_inter3_le (li lj lk : List Nat) :
    (li.toFinset ∩ lj.toFinset ∩ lk.toFinset).card ≤
      countIn lk (Nat.land (maskOf li) (maskOf lj)) := by
  rw [countIn_eq]
  have e : li.toFinset ∩ lj.toFinset ∩ lk.toFinset =
      (lk.filter fun a => bit (Nat.land (maskOf li) (maskOf lj)) a).toFinset := by
    ext a
    simp only [Finset.mem_inter, List.mem_toFinset, List.mem_filter, bit_land, Bool.and_eq_true,
      bit_maskOf]
    tauto
  rw [e]
  exact List.toFinset_card_le _

theorem fld_eq (c k : Nat) : fld c k = c / 4 ^ k % 4 := by
  change (c >>> (2 * k)) &&& (2 ^ 2 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, pow_mul]
  norm_num

theorem ofCode_apply (c : Nat) (i j : Fin 6) :
    ofCode c i j = ((fld c (6 * i.val + j.val) : Nat) : ZMod 3) := by
  rw [ofCode, fld_eq, Nat.shiftRight_eq_div_pow, pow_mul]
  norm_num

theorem psum_digits (f : Nat → Nat) (n : Nat) (hf : ∀ k < n, f k < 4) :
    (∑ k ∈ Finset.range n, f k * 4 ^ k) < 4 ^ n ∧
      ∀ k < n, (∑ k ∈ Finset.range n, f k * 4 ^ k) / 4 ^ k % 4 = f k := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨hb, hd⟩ := ih fun k hk => hf k (by omega)
    have hfn := hf n (by omega)
    rw [Finset.sum_range_succ]
    set S := ∑ k ∈ Finset.range n, f k * 4 ^ k
    have hpos : 0 < 4 ^ n := by positivity
    refine ⟨?_, fun k hk => ?_⟩
    · have h3 : f n * 4 ^ n ≤ 3 * 4 ^ n := Nat.mul_le_mul_right _ (by omega)
      rw [pow_succ]
      omega
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
      · have hsplit : f n * 4 ^ n = 4 ^ k * (f n * 4 ^ (n - k)) := by
          rw [mul_left_comm, ← pow_add, Nat.add_sub_cancel' hk.le]
        have hpk : 0 < 4 ^ k := by positivity
        rw [hsplit, Nat.add_mul_div_left _ _ hpk]
        have h4 : 4 ∣ f n * 4 ^ (n - k) :=
          Dvd.dvd.mul_left (dvd_pow_self 4 (by omega)) _
        obtain ⟨m, hm⟩ := h4
        rw [hm, Nat.add_mul_mod_self_left]
        exact hd k hk
      · rw [Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hb, zero_add, Nat.mod_eq_of_lt hfn]

theorem pack_eq (f : Nat → Nat) : pack f = ∑ k ∈ Finset.range 36, f k * 4 ^ k := by
  rw [pack, sumK_eq]
  rfl

theorem fld_pack {f : Nat → Nat} (hf : ∀ k < 36, f k < 4) {k : Nat} (hk : k < 36) :
    fld (pack f) k = f k := by
  rw [fld_eq, pack_eq]
  exact (psum_digits f 36 hf).2 k hk

theorem pack_congr {f g : Nat → Nat} (h : ∀ k < 36, f k = g k) : pack f = pack g :=
  sumK_congr fun k hk => by rw [h k hk]

theorem canonC_spec {c : Nat} (h : canonC c = true) :
    c = pack (fun k => fld c k) ∧ ∀ k < 36, fld c k < 3 := by
  obtain ⟨h1, h2⟩ := andB_eq_true.mp h
  refine ⟨Nat.eq_of_beq_eq_true h1, fun k hk => ?_⟩
  have := allK_eq_true.mp h2 k hk
  simpa using this

theorem canonC_pack {f : Nat → Nat} (hf : ∀ k < 36, f k < 3) : canonC (pack f) = true := by
  have hf4 : ∀ k < 36, f k < 4 := fun k hk => by have := hf k hk; omega
  refine andB_eq_true.mpr ⟨?_, allK_eq_true.mpr fun k hk => ?_⟩
  · rw [Nat.beq_eq]
    exact pack_congr fun k hk => (fld_pack hf4 hk).symm
  · rw [fld_pack hf4 hk]
    simpa using hf k hk

theorem ofCode_inj {a b : Nat} (ha : canonC a = true) (hb : canonC b = true)
    (h : ofCode a = ofCode b) : a = b := by
  obtain ⟨ea, la⟩ := canonC_spec ha
  obtain ⟨eb, lb⟩ := canonC_spec hb
  have key : ∀ k < 36, fld a k = fld b k := by
    intro k hk
    have e := congrFun (congrFun h ⟨k / 6, by omega⟩) ⟨k % 6, by omega⟩
    rw [ofCode_apply, ofCode_apply] at e
    have hk' : 6 * (k / 6) + k % 6 = k := Nat.div_add_mod k 6
    simp only [hk'] at e
    rw [ZMod.natCast_eq_natCast_iff'] at e
    have := la k hk
    have := lb k hk
    omega
  rw [ea, eb]
  exact pack_congr key

theorem ent_lt (a b k : Nat) : ent a b k < 3 := Nat.mod_lt _ (by norm_num)

theorem ent_eq (a b : Nat) {i j : Nat} (hj : j < 6) :
    ent a b (6 * i + j) = (∑ t ∈ Finset.range 6, fld a (6 * i + t) * fld b (6 * t + j)) % 3 := by
  have h1 : (6 * i + j) / 6 = i := by omega
  have h2 : (6 * i + j) % 6 = j := by omega
  change Nat.mod (sumK 6 fun t => Nat.mul (fld a (Nat.add (Nat.mul 6 ((6 * i + j) / 6)) t))
    (fld b (Nat.add (Nat.mul 6 t) ((6 * i + j) % 6)))) 3 = _
  rw [h1, h2, sumK_eq]
  rfl

theorem canonC_mulC (a b : Nat) : canonC (mulC a b) = true :=
  canonC_pack fun k _ => ent_lt a b k

theorem ofCode_mulC (a b : Nat) : ofCode (mulC a b) = ofCode a * ofCode b := by
  ext i j
  rw [ofCode_apply, Matrix.mul_apply, mulC,
    fld_pack (fun k _ => by have := ent_lt a b k; omega) (by omega), ent_eq a b j.isLt,
    ZMod.natCast_mod, Nat.cast_sum, Finset.sum_range (fun t => ((fld a (6 * i.val + t) *
      fld b (6 * t + j.val) : Nat) : ZMod 3))]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [ofCode_apply, ofCode_apply, Nat.cast_mul]

theorem ofCode_idC : ofCode idC = 1 := by
  ext i j
  rw [ofCode_apply]
  fin_cases i <;> fin_cases j <;> decide

theorem canonC_idC : canonC idC = true := by decide +kernel

theorem ofCode_powC (c p : Nat) : ofCode (powC c p) = ofCode c ^ p := by
  induction p with
  | zero => exact ofCode_idC
  | succ p ih =>
    change ofCode (mulC (powC c p) c) = _
    rw [ofCode_mulC, ih, pow_succ]

theorem ofCode_eq_one {c : Nat} (hc : canonC c = true) : ofCode c = 1 ↔ c = idC := by
  rw [← ofCode_idC]
  exact ⟨ofCode_inj hc canonC_idC, fun h => h ▸ rfl⟩

theorem mulC_eq_iff (a b c d : Nat) : mulC a b = mulC c d ↔ ofCode (mulC a b) = ofCode (mulC c d) :=
  ⟨fun h => h ▸ rfl, ofCode_inj (canonC_mulC a b) (canonC_mulC c d)⟩

theorem g1_eq : g1 = ofCode g1C := by
  unfold g1
  ext i j
  rw [ofCode_apply]
  fin_cases i <;> fin_cases j <;> decide

theorem g2_eq : g2 = ofCode g2C := by
  unfold g2
  ext i j
  rw [ofCode_apply]
  fin_cases i <;> fin_cases j <;> decide

theorem mem_subL {a b c : Nat} (h : c ∈ subL a b) :
    ∃ p q : Fin 3, ofCode c = ofCode a ^ p.val * ofCode b ^ q.val := by
  change c ∈ [mulC (powC a 0) (powC b 0), mulC (powC a 0) (powC b 1), mulC (powC a 0) (powC b 2),
    mulC (powC a 1) (powC b 0), mulC (powC a 1) (powC b 1), mulC (powC a 1) (powC b 2),
    mulC (powC a 2) (powC b 0), mulC (powC a 2) (powC b 1), mulC (powC a 2) (powC b 2)] at h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, 0, by rw [ofCode_mulC, ofCode_powC, ofCode_powC]; rfl⟩
  · exact ⟨0, 1, by rw [ofCode_mulC, ofCode_powC, ofCode_powC]; rfl⟩
  · exact ⟨0, 2, by rw [ofCode_mulC, ofCode_powC, ofCode_powC]; rfl⟩
  · exact ⟨1, 0, by rw [ofCode_mulC, ofCode_powC, ofCode_powC]; rfl⟩
  · exact ⟨1, 1, by rw [ofCode_mulC, ofCode_powC, ofCode_powC]; rfl⟩
  · exact ⟨1, 2, by rw [ofCode_mulC, ofCode_powC, ofCode_powC]; rfl⟩
  · exact ⟨2, 0, by rw [ofCode_mulC, ofCode_powC, ofCode_powC]; rfl⟩
  · exact ⟨2, 1, by rw [ofCode_mulC, ofCode_powC, ofCode_powC]; rfl⟩
  · exact ⟨2, 2, by rw [ofCode_mulC, ofCode_powC, ofCode_powC]; rfl⟩

theorem dx_lt (x s : Nat) : dx x s < 3 := by
  change selN (Nat.beq s 0) 0 _ < 3
  cases Nat.beq s 0
  · exact Nat.mod_lt _ (by norm_num)
  · exact Nat.zero_lt_succ _

theorem decode_apply (x : Nat) (s : Fin 6) : decode x s = ((dx x s.val : Nat) : ZMod 3) := by
  rw [decode]
  by_cases hs : s = 0
  · subst hs
    simp only [if_true]
    rfl
  · rw [if_neg hs]
    have hs' : Nat.beq s.val 0 = false := beq_false_iff.mpr fun h => hs (Fin.ext h)
    change _ = ((selN (Nat.beq s.val 0) 0 _ : Nat) : ZMod 3)
    rw [hs']
    rfl

theorem decode_zero (x : Nat) : decode x 0 = 0 := by
  simp [decode]

theorem mulVec_decode (c x : Nat) (r : Fin 6) :
    (ofCode c *ᵥ decode x) r = ((sumK 6 fun s =>
      Nat.mul (fld c (Nat.add (Nat.mul 6 r.val) s)) (dx x s) : Nat) : ZMod 3) := by
  rw [Matrix.mulVec, dotProduct, sumK_eq, Nat.cast_sum, Finset.sum_range]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [ofCode_apply, decode_apply, ← Nat.cast_mul]
  rfl

theorem fixC_iff (c x : Nat) : fixC c x = true ↔ ofCode c *ᵥ decode x = decode x := by
  rw [fixC, allK_eq_true, funext_iff]
  constructor
  · intro h r
    rw [mulVec_decode, decode_apply, ZMod.natCast_eq_natCast_iff',
      Nat.mod_eq_of_lt (dx_lt x r.val)]
    exact Nat.eq_of_beq_eq_true (h r.val r.isLt)
  · intro h r hr
    have e := h ⟨r, hr⟩
    rw [mulVec_decode, decode_apply, ZMod.natCast_eq_natCast_iff',
      Nat.mod_eq_of_lt (dx_lt x r)] at e
    rw [Nat.beq_eq]
    exact e

theorem decode_inj {a b : Nat} (ha : a < 243) (hb : b < 243) (h : decode a = decode b) :
    a = b := by
  have e : ∀ s : Fin 6, dx a s.val = dx b s.val := fun s => by
    have := congrFun h s
    rw [decode_apply, decode_apply, ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (dx_lt _ _),
      Nat.mod_eq_of_lt (dx_lt _ _)] at this
    exact this
  have e1 : a / 1 % 3 = b / 1 % 3 := e 1
  have e2 : a / 3 % 3 = b / 3 % 3 := e 2
  have e3 : a / 9 % 3 = b / 9 % 3 := e 3
  have e4 : a / 27 % 3 = b / 27 % 3 := e 4
  have e5 : a / 81 % 3 = b / 81 % 3 := e 5
  omega

theorem exists_decode {v : Vec6} (hv : v 0 = 0) : ∃ x < 243, decode x = v := by
  have h1 := ZMod.val_lt (v 1)
  have h2 := ZMod.val_lt (v 2)
  have h3 := ZMod.val_lt (v 3)
  have h4 := ZMod.val_lt (v 4)
  have h5 := ZMod.val_lt (v 5)
  refine ⟨(v 1).val + 3 * (v 2).val + 9 * (v 3).val + 27 * (v 4).val + 81 * (v 5).val,
    by omega, ?_⟩
  funext s
  rw [decode_apply]
  rcases s with ⟨k, hk⟩
  interval_cases k
  · change ((0 : Nat) : ZMod 3) = v 0
    rw [hv, Nat.cast_zero]
  · change ((((v 1).val + 3 * (v 2).val + 9 * (v 3).val + 27 * (v 4).val + 81 * (v 5).val) / 1
      % 3 : Nat) : ZMod 3) = v 1
    rw [show ((v 1).val + 3 * (v 2).val + 9 * (v 3).val + 27 * (v 4).val + 81 * (v 5).val) / 1
      % 3 = (v 1).val by omega, ZMod.natCast_zmod_val]
  · change ((((v 1).val + 3 * (v 2).val + 9 * (v 3).val + 27 * (v 4).val + 81 * (v 5).val) / 3
      % 3 : Nat) : ZMod 3) = v 2
    rw [show ((v 1).val + 3 * (v 2).val + 9 * (v 3).val + 27 * (v 4).val + 81 * (v 5).val) / 3
      % 3 = (v 2).val by omega, ZMod.natCast_zmod_val]
  · change ((((v 1).val + 3 * (v 2).val + 9 * (v 3).val + 27 * (v 4).val + 81 * (v 5).val) / 9
      % 3 : Nat) : ZMod 3) = v 3
    rw [show ((v 1).val + 3 * (v 2).val + 9 * (v 3).val + 27 * (v 4).val + 81 * (v 5).val) / 9
      % 3 = (v 3).val by omega, ZMod.natCast_zmod_val]
  · change ((((v 1).val + 3 * (v 2).val + 9 * (v 3).val + 27 * (v 4).val + 81 * (v 5).val) / 27
      % 3 : Nat) : ZMod 3) = v 4
    rw [show ((v 1).val + 3 * (v 2).val + 9 * (v 3).val + 27 * (v 4).val + 81 * (v 5).val) / 27
      % 3 = (v 4).val by omega, ZMod.natCast_zmod_val]
  · change ((((v 1).val + 3 * (v 2).val + 9 * (v 3).val + 27 * (v 4).val + 81 * (v 5).val) / 81
      % 3 : Nat) : ZMod 3) = v 5
    rw [show ((v 1).val + 3 * (v 2).val + 9 * (v 3).val + 27 * (v 4).val + 81 * (v 5).val) / 81
      % 3 = (v 5).val by omega, ZMod.natCast_zmod_val]

theorem image_decode_eq {c : Nat} {l : List Nat} (h1 : ∀ x ∈ l, x < 243 ∧ fixC c x = true)
    (h2 : ∀ x < 243, fixC c x = true → x ∈ l) : l.toFinset.image decode = fixedB1 (ofCode c) := by
  ext v
  simp only [Finset.mem_image, List.mem_toFinset, fixedB1, Finset.mem_filter, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨decode_zero x, (fixC_iff c x).mp (h1 x hx).2⟩
  · rintro ⟨hv0, hfix⟩
    obtain ⟨x, hx, rfl⟩ := exists_decode hv0
    exact ⟨x, h2 x hx ((fixC_iff c x).mpr hfix), rfl⟩

theorem baseOK_spec {L : List Nat} (h : baseOK L = true) :
    (∀ c ∈ L, canonC c = true) ∧ L.Nodup ∧ L.length = 81 ∧ getN L 0 = idC ∧
      (∀ i < 81, mulC (getN L i) g1C ∈ L ∧ mulC (getN L i) g2C ∈ L) ∧
      mulC g1C g2C ≠ mulC g2C g1C := by
  unfold baseOK at h
  obtain ⟨h1, h⟩ := andB_eq_true.mp h
  obtain ⟨h2, h⟩ := andB_eq_true.mp h
  obtain ⟨h3, h⟩ := andB_eq_true.mp h
  obtain ⟨h4, h⟩ := andB_eq_true.mp h
  obtain ⟨h5, h6⟩ := andB_eq_true.mp h
  refine ⟨allL_eq_true.mp h1, nodupK_nodup h2, ?_, Nat.eq_of_beq_eq_true h4, fun i hi => ?_, ?_⟩
  · rw [← lenN_eq]
    exact Nat.eq_of_beq_eq_true h3
  · obtain ⟨a, b⟩ := andB_eq_true.mp (allK_eq_true.mp h5 i hi)
    exact ⟨memK_eq_true.mp a, memK_eq_true.mp b⟩
  · exact beq_false_iff.mp (notB_eq_true.mp h6)

theorem ordRow_spec {L : List Nat} {om i : Nat} (h : ordRow L om i = true) :
    bit om i = andB (Nat.beq (mulC (mulC (getN L i) (getN L i)) (getN L i)) idC)
      (notB (Nat.beq (getN L i) idC)) :=
  eqB_eq_true.mp h

theorem commRow_spec {L CM : List Nat} {i : Nat} (h : commRow L CM i = true) :
    ∀ j < 81, bit (getN CM i) j =
      Nat.beq (mulC (getN L i) (getN L j)) (mulC (getN L j) (getN L i)) :=
  fun j hj => by
    unfold commRow letN at h
    exact eqB_eq_true.mp (allK_eq_true.mp h j hj)

theorem fixRow_spec {L : List Nat} {FC : List (List Nat)} {i : Nat} (h : fixRow L FC i = true) :
    (∀ x ∈ getLL FC i, x < 243 ∧ fixC (getN L i) x = true) ∧
      ∀ x < 243, fixC (getN L i) x = true → x ∈ getLL FC i := by
  unfold fixRow letN letL at h
  obtain ⟨h1, h2⟩ := andB_eq_true.mp h
  refine ⟨fun x hx => ?_, fun x hx hf => ?_⟩
  · obtain ⟨a, b⟩ := andB_eq_true.mp (allL_eq_true.mp h1 x hx)
    exact ⟨by simpa using a, b⟩
  · rcases orB_eq_true.mp (allK_eq_true.mp h2 x hx) with h3 | h3
    · rw [notB_eq_true, hf] at h3
      cases h3
    · exact bit_maskOf.mp h3

theorem boundRow_spec {L CM : List Nat} {FC : List (List Nat)} {om i : Nat}
    (h : boundRow L CM FC om i = true) (hi : bit om i = true) :
    (getLL FC i).length ≤ 27 ∧ ∀ j < 81, bit om j = true → bit (getN CM i) j = true → j ≠ i →
      getN L j ≠ mulC (getN L i) (getN L i) →
      countIn (getLL FC j) (maskOf (getLL FC i)) ≤ 9 ∧
      ∀ k < 81, bit om k = true → bit (getN CM i) k = true → bit (getN CM j) k = true →
        countIn (getLL FC k) (Nat.land (maskOf (getLL FC i)) (maskOf (getLL FC j))) ≤ 3 ∨
          getN L k ∈ subL (getN L i) (getN L j) := by
  unfold boundRow letN letL at h
  rcases orB_eq_true.mp h with h0 | h0
  · rw [notB_eq_true, hi] at h0
    cases h0
  obtain ⟨hl, hr⟩ := andB_eq_true.mp h0
  refine ⟨by rw [← lenN_eq]; simpa using hl, fun j hj hoj hmj hji hsq => ?_⟩
  rcases orB_eq_true.mp (allK_eq_true.mp hr j hj) with h1 | h1
  · exfalso
    rw [notB_eq_true] at h1
    have : andB (bit om j) (andB (bit (getN CM i) j) (andB (notB (Nat.beq j i))
        (notB (Nat.beq (getN L j) (mulC (getN L i) (getN L i)))))) = true := by
      rw [hoj, hmj, notB_eq_true.mpr (beq_false_iff.mpr hji),
        notB_eq_true.mpr (beq_false_iff.mpr hsq)]
      rfl
    rw [h1] at this
    cases this
  obtain ⟨h2, h3⟩ := andB_eq_true.mp h1
  refine ⟨by simpa using h2, fun k hk hok hik hjk => ?_⟩
  rcases orB_eq_true.mp (allK_eq_true.mp h3 k hk) with h4 | h4
  · exfalso
    rw [notB_eq_true, hok, hik, hjk] at h4
    cases h4
  rcases orB_eq_true.mp h4 with h5 | h5
  · exact Or.inl (by simpa using h5)
  · exact Or.inr (memK_eq_true.mp h5)

theorem nodup_eraseDups_nat : ∀ l : List Nat, l.eraseDups.Nodup
  | [] => List.nodup_nil
  | a :: as => by
    rw [List.eraseDups_cons]
    refine List.nodup_cons.mpr ⟨fun h => ?_, nodup_eraseDups_nat _⟩
    rw [List.mem_eraseDups, List.mem_filter] at h
    simp at h
termination_by l => l.length
decreasing_by
  have := List.length_filter_le (fun b => !b == a) as
  simp only [List.length_cons]
  omega

theorem check_of (hb : baseOK LCode = true) (ho : ∀ i < 81, ordRow LCode ordMask i = true)
    (hc : ∀ i < 81, commRow LCode commMasks i = true)
    (hf : ∀ i < 81, fixRow LCode fixCodes i = true)
    (hB : ∀ i < 81, boundRow LCode commMasks fixCodes ordMask i = true) : check () = true := by
  obtain ⟨hcan, hnd, hlen, h0, hcl, hne⟩ := baseOK_spec hb
  have hL : L = LCode.map ofCode := by rw [L]
  have hLAt : ∀ i : Fin 81, LAt i = ofCode (getN LCode i.val) := by
    intro i
    have hi : i.val < LCode.length := by rw [hlen]; exact i.isLt
    rw [getN_eq, List.getD_eq_getElem _ _ hi]
    simp only [LAt, List.get_eq_getElem, hL, List.getElem_map]
  have hmem : ∀ i < 81, getN LCode i ∈ LCode := fun i hi => by
    rw [getN_eq, List.getD_eq_getElem _ _ (by omega)]
    exact List.getElem_mem _
  have hcanAt : ∀ i < 81, canonC (getN LCode i) = true := fun i hi => hcan _ (hmem i hi)
  have hidx : ∀ c ∈ LCode, ∃ j : Fin 81, getN LCode j.val = c := by
    intro c hc
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hc
    exact ⟨⟨j, by omega⟩, by rw [getN_eq, List.getD_eq_getElem _ _ hj]⟩
  have hordAt : ∀ i : Fin 81, ordAt i = bit ordMask i.val := fun i => by
    rw [bit_eq]
    rfl
  have hcommAt : ∀ i j : Fin 81, commAt i j = bit (getN commMasks i.val) j.val := fun i j => by
    rw [bit_eq, getN_eq]
    rfl
  have hfixAt : ∀ i : Fin 81, fixSetAt i = (getLL fixCodes i.val).toFinset := fun i => by
    rw [getLL_eq, List.getD_eq_getElem _ _ (by rw [fixCodes_length]; exact i.isLt)]
    simp only [fixSetAt, List.get_eq_getElem]
  have hP1 : LAt 0 = 1 := by
    rw [hLAt]
    change ofCode (getN LCode 0) = 1
    rw [h0, ofCode_idC]
  have hP2 : L.Nodup := by
    rw [hL]
    exact hnd.map_on fun x hx y hy e => ofCode_inj (hcan x hx) (hcan y hy) e
  have hmul : ∀ (g : Mat6) (gc : Nat), g = ofCode gc →
      (∀ i < 81, mulC (getN LCode i) gc ∈ LCode) → ∀ i : Fin 81, ∃ j : Fin 81, LAt j = LAt i * g := by
    intro g gc hg h i
    obtain ⟨j, hj⟩ := hidx _ (h i.val i.isLt)
    exact ⟨j, by rw [hLAt, hLAt, hj, ofCode_mulC, hg]⟩
  have hP4 := hmul g1 g1C g1_eq fun i hi => (hcl i hi).1
  have hP5 := hmul g2 g2C g2_eq fun i hi => (hcl i hi).2
  have hP6 : ordOK := by
    intro i
    rw [hordAt, ordRow_spec (ho i.val i.isLt), andB_eq_true, notB_eq_true, beq_false_iff,
      Nat.beq_eq, hLAt, ← ofCode_eq_one (canonC_mulC _ _), ofCode_mulC, ofCode_mulC, ne_eq,
      ne_eq, ofCode_eq_one (hcanAt i.val i.isLt), pow_three, mul_assoc]
  have hP7 : commOK := by
    intro i j
    rw [hcommAt, commRow_spec (hc i.val i.isLt) j.val j.isLt, Nat.beq_eq, mulC_eq_iff,
      ofCode_mulC, ofCode_mulC, hLAt, hLAt]
  have hfr : ∀ i : Fin 81, (fixSetAt i).image decode = fixedB1 (LAt i) := fun i => by
    obtain ⟨h1, h2⟩ := fixRow_spec (hf i.val i.isLt)
    rw [hfixAt, hLAt]
    exact image_decode_eq h1 h2
  have hP8 : fixOK := by
    refine ⟨hfr, ?_⟩
    have hlt : ∀ x ∈ fixCodes.flatten, x < 243 := by
      intro x hx
      obtain ⟨l, hl, hxl⟩ := List.mem_flatten.mp hx
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hl
      have hi' : i < 81 := by rwa [fixCodes_length] at hi
      have := (fixRow_spec (hf i hi')).1 x
      rw [getLL_eq, List.getD_eq_getElem _ _ hi] at this
      exact (this hxl).1
    exact (nodup_eraseDups_nat _).map_on fun x hx y hy e =>
      decode_inj (hlt x (List.mem_eraseDups.mp hx)) (hlt y (List.mem_eraseDups.mp hy)) e
  have hbr : ∀ i : Fin 81, ordAt i = true → _ := fun i hoi =>
    boundRow_spec (hB i.val i.isLt) (by rw [← hordAt]; exact hoi)
  have hsq : ∀ i j : Fin 81, LAt j ≠ LAt i * LAt i →
      getN LCode j.val ≠ mulC (getN LCode i.val) (getN LCode i.val) := by
    intro i j h e
    apply h
    rw [hLAt, hLAt, e, ofCode_mulC]
  have hP9 : (ordList ()).all singleFast = true := by
    rw [List.all_eq_true]
    intro i _
    rw [singleFast_eq_true_iff]
    intro hoi
    rw [hfixAt]
    exact (List.toFinset_card_le _).trans (hbr i hoi).1
  have hP10 : (ordList ()).all (fun i => (ordList ()).all fun j =>
      pairFastWith ((fixSets ()).getD i.val ∅) ((fixSets ()).getD j.val ∅) i j) = true := by
    rw [List.all_eq_true]
    intro i _
    rw [List.all_eq_true]
    intro j _
    rw [fixSets_getD, fixSets_getD, pairFastWith_eq_true_iff, pairCond_eq_true_iff]
    rintro ⟨hoi, hoj, hij, hji, hs⟩
    rw [hfixAt, hfixAt]
    refine (card_inter_le _ _).trans ((hbr i hoi).2 j.val j.isLt (by rw [← hordAt]; exact hoj)
      (by rw [← hcommAt]; exact hij) (fun e => hji (Fin.ext e)) (hsq i j hs)).1
  have hP11 : (ordList ()).all (fun i => (ordList ()).all fun j => (ordList ()).all fun k =>
      tripleFastWith ((fixSets ()).getD i.val ∅) ((fixSets ()).getD j.val ∅)
        ((fixSets ()).getD k.val ∅) i j k) = true := by
    rw [List.all_eq_true]
    intro i _
    rw [List.all_eq_true]
    intro j _
    rw [List.all_eq_true]
    intro k _
    rw [fixSets_getD, fixSets_getD, fixSets_getD, tripleFastWith_eq_true_iff,
      tripleCond_eq_true_iff, pairCond_eq_true_iff]
    rintro ⟨⟨hoi, hoj, hij, hji, hs⟩, hok, hik, hjk, hsub⟩
    rw [hfixAt, hfixAt, hfixAt]
    rcases ((hbr i hoi).2 j.val j.isLt (by rw [← hordAt]; exact hoj)
      (by rw [← hcommAt]; exact hij) (fun e => hji (Fin.ext e)) (hsq i j hs)).2 k.val k.isLt
      (by rw [← hordAt]; exact hok) (by rw [← hcommAt]; exact hik)
      (by rw [← hcommAt]; exact hjk) with h3 | h3
    · exact (card_inter3_le _ _ _).trans h3
    · exfalso
      obtain ⟨p, q, e⟩ := mem_subL h3
      apply hsub p q
      rw [hLAt, hLAt, hLAt, e]
  have hP12 : g1 * g2 ≠ g2 * g1 := by
    rw [g1_eq, g2_eq, ← ofCode_mulC, ← ofCode_mulC]
    exact fun e => hne (ofCode_inj (canonC_mulC _ _) (canonC_mulC _ _) e)
  rw [check, List.all_eq_true]
  intro b hb
  rw [checkParts] at hb
  obtain h | hb := List.mem_cons.mp hb
  · rw [h]
    rw [id_eq, decide_eq_true_eq]
    exact hP1
  obtain h | hb := List.mem_cons.mp hb
  · rw [h]
    rw [id_eq, decide_eq_true_eq]
    exact hP2
  obtain h | hb := List.mem_cons.mp hb
  · rw [h]
    rw [id_eq, decide_eq_true_eq]
    exact L_length
  obtain h | hb := List.mem_cons.mp hb
  · rw [h]
    rw [id_eq, decide_eq_true_eq]
    exact hP4
  obtain h | hb := List.mem_cons.mp hb
  · rw [h]
    rw [id_eq, decide_eq_true_eq]
    exact hP5
  obtain h | hb := List.mem_cons.mp hb
  · rw [h]
    rw [id_eq, decide_eq_true_eq]
    exact hP6
  obtain h | hb := List.mem_cons.mp hb
  · rw [h]
    rw [id_eq, decide_eq_true_eq]
    exact hP7
  obtain h | hb := List.mem_cons.mp hb
  · rw [h]
    rw [id_eq, decide_eq_true_eq]
    exact hP8
  obtain h | hb := List.mem_cons.mp hb
  · rw [h, id_eq]
    exact hP9
  obtain h | hb := List.mem_cons.mp hb
  · rw [h, id_eq]
    exact hP10
  obtain h | hb := List.mem_cons.mp hb
  · rw [h, id_eq]
    exact hP11
  obtain h | hb := List.mem_cons.mp hb
  · rw [h]
    rw [id_eq, decide_eq_true_eq]
    exact hP12
  exact absurd hb List.not_mem_nil

end CFSG.KC.WE6K
