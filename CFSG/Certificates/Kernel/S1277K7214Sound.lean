module

public import Certificates.Data.Kernel.S1277K7214
public import CFSG.Certificates.Kernel.S1277KMLPrim
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.KS.C7214

open CFSG.Quasithin.H13.S127.Mod CFSG.KC.S1277ML CFSG.KC.S1277Gm CFSG.KC.C7214 CFSG.KS.S1277ML
  CFSG.KS.S1277Gm

theorem allG_eq {α : Type} (f : α → Bool) (l : List α) : allG f l = l.all f := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    change andB (f x) (allG f l) = _
    rw [andB_eq, ih, List.all_cons]

theorem anyG_eq {α : Type} (f : α → Bool) (l : List α) : anyG f l = l.any f := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    change orB (f x) (anyG f l) = _
    rw [orB_eq, ih, List.any_cons]

theorem cntG_eq {α : Type} (f : α → Bool) (l : List α) : cntG f l = l.countP f := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    change Bool.rec (motive := fun _ => ℕ) (cntG f l) (Nat.succ (cntG f l)) (f x) = _
    rw [ih, List.countP_cons]
    cases f x
    · rfl
    · rfl

theorem allG_true {α : Type} {f : α → Bool} {l : List α} (h : allG f l = true) :
    ∀ x ∈ l, f x = true := by
  rw [allG_eq, List.all_eq_true] at h
  exact h

theorem anyG_true {α : Type} {f : α → Bool} {l : List α} (h : anyG f l = true) :
    ∃ x ∈ l, f x = true := by
  rw [anyG_eq, List.any_eq_true] at h
  exact h

theorem allG_of {α : Type} {f : α → Bool} {l : List α} (h : ∀ x ∈ l, f x = true) :
    allG f l = true := by
  rw [allG_eq, List.all_eq_true]
  exact h

theorem anyG_of {α : Type} {f : α → Bool} {l : List α} {x : α} (hx : x ∈ l) (h : f x = true) :
    anyG f l = true := by
  rw [anyG_eq, List.any_eq_true]
  exact ⟨x, hx, h⟩

theorem allL_true {f : ℕ → Bool} {l : List ℕ} (h : allL f l = true) : ∀ x ∈ l, f x = true := by
  rw [allL_eq, List.all_eq_true] at h
  exact h

theorem anyL_true {f : ℕ → Bool} {l : List ℕ} (h : anyL f l = true) : ∃ x ∈ l, f x = true := by
  rw [anyL_eq, List.any_eq_true] at h
  exact h

theorem andB_true {a b : Bool} (h : andB a b = true) : a = true ∧ b = true := by
  rw [andB_eq, Bool.and_eq_true] at h
  exact h

theorem orB_true {a b : Bool} (h : orB a b = true) : a = true ∨ b = true := by
  rw [orB_eq, Bool.or_eq_true] at h
  exact h

theorem imp_of_orB {a b : Bool} (h : orB (notB a) b = true) (ha : a = true) : b = true := by
  rw [ha] at h
  exact h

theorem right_of_orB {a b : Bool} (h : orB a b = true) (ha : a = false) : b = true := by
  rw [ha] at h
  exact h

theorem nbeq (a b : ℕ) : Nat.beq a b = (a == b) := by
  rw [Bool.eq_iff_iff, Nat.beq_eq, beq_iff_eq]

theorem beq_false_of_ne {a b : ℕ} (h : a ≠ b) : Nat.beq a b = false := by
  cases e : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true e) h

theorem memN_iff (c : ℕ) (l : List ℕ) : memN c l = true ↔ c ∈ l := by
  unfold memN
  rw [anyL_eq, List.any_eq_true]
  simp [Nat.beq_eq]

theorem appK_eq (B : B6) (v : ℕ) : appK B v = B.app v := by
  unfold appK B6.app
  rw [land1, bit1_eq, bit1_eq, bit1_eq, bit1_eq, bit1_eq, ← bit_mul0, ← bit_mul, ← bit_mul,
    ← bit_mul, ← bit_mul, ← bit_mul]
  rfl

theorem appK_fun (B : B6) : (fun v => appK B v) = B.app := funext (appK_eq B)

theorem compK_eq (B C : B6) : compK B C = B.comp C := by
  simp only [compK, B6.comp, appK_eq]

theorem powK_eq (B : B6) (n : ℕ) : powK B n = B.pow n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change compK B (powK B n) = _
    rw [compK_eq, ih]
    rfl

theorem beqB_iff (B C : B6) : beqB B C = true ↔ B = C := by
  obtain ⟨b0, b1, b2, b3, b4, b5⟩ := B
  obtain ⟨c0, c1, c2, c3, c4, c5⟩ := C
  simp only [beqB, andB_eq, Bool.and_eq_true, Nat.beq_eq, B6.mk.injEq]

theorem beqB_true {B C : B6} (h : beqB B C = true) : B = C := (beqB_iff B C).1 h

theorem beqB_false {B C : B6} (h : B ≠ C) : beqB B C = false := by
  cases hb : beqB B C
  · rfl
  · exact absurd (beqB_true hb) h

theorem memB_iff (B : B6) (L : List B6) : memB B L = true ↔ B ∈ L := by
  unfold memB
  rw [anyG_eq, List.any_eq_true]
  simp only [beqB_iff, exists_eq_right']

theorem invoB_of {B : B6} (h1 : B.comp B = B6.id) (h2 : B ≠ B6.id) : invoB B = true := by
  unfold invoB
  rw [compK_eq, (beqB_iff _ _).2 h1, beqB_false h2]
  rfl

theorem rec_cnt (f : ℕ → Bool) : ∀ n,
    Nat.rec (motive := fun _ => ℕ) 0 (fun c r => Bool.rec (motive := fun _ => ℕ) r (Nat.succ r)
      (f c)) n = ((List.range n).filter f).length := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.filter_append, List.length_append, ← ih]
    change Bool.rec (motive := fun _ => ℕ) _ _ (f n) = _
    cases h : f n <;> simp [h]

theorem fixK_eq (B : B6) : fixK B = fixCount B := by
  have e := rec_cnt (fun c => Nat.beq (appK B c) c) 64
  unfold fixK fixCount
  refine e.trans ?_
  congr 2
  funext c
  rw [nbeq, appK_eq]

theorem testBit_fixMK (B : B6) {c : ℕ} (hc : c < 64) :
    (fixMK B).testBit c = (B.app c == c) := by
  unfold fixMK
  rw [testBit_maskBelow]
  change (decide (c < 64) && _) = _
  rw [decide_eq_true hc, Bool.true_and, nbeq, appK_eq]

theorem presvK_eq (l : List ℕ) (B : B6) : presvK l B = presv l B := by
  unfold presvK presv
  rw [allL_eq]
  congr 1
  funext c
  rw [Bool.eq_iff_iff, anyL_eq, List.any_eq_true]
  simp [Nat.beq_eq, appK_eq]

theorem s0pK_eq : s0pK = s0p := by
  simp only [s0pK, s0p, compK_eq]

theorem prodK_eq (l : List B6) : prodK l = l.flatMap fun a => s0p.map fun s => a.comp s := by
  simp only [prodK, s0pK_eq, compK_eq]

theorem ofW_lt (w s : ℕ) : fldN w s < 64 := by
  rw [fldN_eq]
  exact Nat.mod_lt _ (by norm_num)

theorem bitV_xor (a b i x : ℕ) : bitV (a ^^^ b) i x = bitV a i x ^^^ bitV b i x := by
  unfold bitV
  rw [Nat.testBit_xor]
  cases a.testBit i <;> cases b.testBit i <;> simp

theorem app_xor (B : B6) (a b : ℕ) : B.app (a ^^^ b) = B.app a ^^^ B.app b := by
  unfold B6.app
  rw [bitV_xor, bitV_xor, bitV_xor, bitV_xor, bitV_xor, bitV_xor]
  ac_rfl

theorem app_zero (B : B6) : B.app 0 = 0 := by simp [B6.app, bitV]

theorem app_bitV (B : B6) (v i x : ℕ) : B.app (bitV v i x) = bitV v i (B.app x) := by
  unfold bitV
  by_cases h : v.testBit i = true <;> simp [h, app_zero]

theorem app_comp (B C : B6) (v : ℕ) : (B.comp C).app v = B.app (C.app v) := by
  have e : C.app v = bitV v 0 C.c0 ^^^ bitV v 1 C.c1 ^^^ bitV v 2 C.c2 ^^^ bitV v 3 C.c3 ^^^
      bitV v 4 C.c4 ^^^ bitV v 5 C.c5 := rfl
  rw [e, app_xor, app_xor, app_xor, app_xor, app_xor, app_bitV, app_bitV, app_bitV, app_bitV,
    app_bitV, app_bitV]
  rfl

theorem comp_assoc (A B C : B6) : (A.comp B).comp C = A.comp (B.comp C) := by
  rw [B6.comp.eq_1 (A.comp B) C]
  simp only [app_comp]
  rfl

theorem valid_app {B : B6} (hB : B.Valid) (v : ℕ) : B.app v < 64 := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hB
  have h64 : (64 : ℕ) = 2 ^ 6 := by norm_num
  have hb : ∀ i x, x < 64 → bitV v i x < 2 ^ 6 := by
    intro i x hx
    unfold bitV
    split <;> omega
  unfold B6.app
  rw [h64]
  exact Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (Nat.xor_lt_two_pow
    (Nat.xor_lt_two_pow (hb 0 _ h0) (hb 1 _ h1)) (hb 2 _ h2)) (hb 3 _ h3)) (hb 4 _ h4)) (hb 5 _ h5)

theorem valid_comp {B : B6} (hB : B.Valid) (C : B6) : (B.comp C).Valid :=
  ⟨valid_app hB _, valid_app hB _, valid_app hB _, valid_app hB _, valid_app hB _, valid_app hB _⟩

theorem id_app : ∀ x < 64, B6.id.app x = x := by decide +kernel

theorem id_comp {X : B6} (hX : X.Valid) : B6.id.comp X = X := by
  obtain ⟨c0, c1, c2, c3, c4, c5⟩ := X
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hX
  simp only [B6.comp, id_app _ h0, id_app _ h1, id_app _ h2, id_app _ h3, id_app _ h4, id_app _ h5]

theorem pow_valid {B : B6} (hB : B.Valid) (n : ℕ) : (B.pow n).Valid := by
  cases n with
  | zero => exact (by decide : B6.id.Valid)
  | succ n => exact valid_comp hB _

theorem pow_add {B : B6} (hB : B.Valid) (m n : ℕ) : B.pow (m + n) = (B.pow m).comp (B.pow n) := by
  induction m with
  | zero =>
    rw [Nat.zero_add]
    exact (id_comp (pow_valid hB n)).symm
  | succ m ih =>
    rw [Nat.succ_add]
    change B.comp (B.pow (m + n)) = (B.comp (B.pow m)).comp (B.pow n)
    rw [ih, comp_assoc]

theorem forceB_eq (X : B6) (k : B6 → Bool) : forceB X k = k X := by
  unfold forceB
  simp only [strictB_ml]

theorem validB_valid {B : B6} (h : validB B = true) : B.Valid := by
  obtain ⟨b0, b1, b2, b3, b4, b5⟩ := B
  simp only [validB, andB_eq, Bool.and_eq_true, Nat.blt_eq] at h
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := h
  exact ⟨h0, h1, h2, h3, h4, h5⟩

theorem pow15B_eq {B : B6} (hB : B.Valid) (k : B6 → B6 → Bool) :
    pow15B B k = k (B.pow 3) (B.pow 12) := by
  unfold pow15B
  simp only [forceB_eq, compK_eq]
  have h3 : B.comp (B.comp (B.comp B6.id)) = B.pow 3 := rfl
  rw [h3, ← pow_add hB 3 3, ← pow_add hB 6 6]

theorem eq15B_iff {B : B6} (hB : B.Valid) : eq15B B = true ↔ B.pow 15 = B6.id := by
  unfold eq15B
  rw [pow15B_eq hB, compK_eq, ← pow_add hB 3 12, beqB_iff]

theorem eq60B_true {B : B6} (hB : B.Valid) (h : eq60B B = true) : B.pow 60 = B6.id := by
  unfold eq60B at h
  rw [pow15B_eq hB] at h
  simp only [forceB_eq, compK_eq] at h
  rw [← pow_add hB 3 12, ← pow_add hB 15 15, ← pow_add hB 30 30] at h
  exact beqB_true h

theorem xor_lt64 {x g : ℕ} (hg : g < 64) : x ^^^ g < 64 ↔ x < 64 := by
  have h64 : (64 : ℕ) = 2 ^ 6 := by norm_num
  rw [h64] at hg ⊢
  constructor
  · intro h
    have := Nat.xor_lt_two_pow h hg
    rwa [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero] at this
  · intro h
    exact Nat.xor_lt_two_pow h hg

def SpInv (acc : List ℕ) (m : ℕ) : Prop := ∀ x, x ∈ acc ↔ x < 64 ∧ m.testBit x = true

theorem SpInv.step {acc : List ℕ} {m g : ℕ} (h : SpInv acc m) (hg : g < 64) :
    SpInv (if acc.contains g then acc else acc ++ acc.map (· ^^^ g)) (addSp m g) := by
  by_cases hc : acc.contains g = true
  · have hb : bitN m g = true := by
      rw [bitN_eq]
      exact ((h g).1 (by simpa using hc)).2
    rw [if_pos hc]
    unfold addSp
    rw [hb]
    exact h
  · have hb : bitN m g = false := by
      rw [bitN_eq]
      cases e : m.testBit g
      · rfl
      · exact absurd (by simpa using (h g).2 ⟨hg, e⟩) hc
    rw [if_neg hc]
    unfold addSp
    rw [hb]
    intro x
    change x ∈ acc ++ acc.map (· ^^^ g) ↔ x < 64 ∧ (m ||| maskBelow _ 64).testBit x = true
    rw [List.mem_append, List.mem_map, Nat.testBit_or, testBit_maskBelow, bitN_eq]
    have hy : (∃ y ∈ acc, y ^^^ g = x) ↔ x ^^^ g ∈ acc := by
      constructor
      · rintro ⟨y, hy, rfl⟩
        rwa [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
      · intro hx
        exact ⟨x ^^^ g, hx, by rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]⟩
    rw [hy, h x, h (x ^^^ g), xor_lt64 hg]
    change _ ↔ x < 64 ∧ (m.testBit x || (decide (x < 64) && m.testBit (Nat.xor x g))) = true
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    change _ ↔ x < 64 ∧ (m.testBit x = true ∨ x < 64 ∧ m.testBit (x ^^^ g) = true)
    tauto

theorem spanChk_aux (ds : List ℕ) (hds : ∀ d ∈ ds, d < 64) : ∀ (l acc : List ℕ) (m : ℕ),
    SpInv acc m →
    List.rec (motive := fun _ => ℕ → Bool) (fun m => allL (fun d => bitN m d) ds)
      (fun g _ r m => andB (Nat.blt g (nat_lit 64)) (strictB (addSp m g) r)) l m = true →
    (ds.all fun d => (l.foldl (fun acc g => if acc.contains g then acc else
      acc ++ acc.map (· ^^^ g)) acc).contains d) = true := by
  intro l
  induction l with
  | nil =>
    intro acc m hi h
    rw [List.all_eq_true]
    intro d hd
    have e := allL_true h d hd
    rw [bitN_eq] at e
    simpa using (hi d).2 ⟨hds d hd, e⟩
  | cons g l ih =>
    intro acc m hi h
    change andB (Nat.blt g 64) (strictB (addSp m g) _) = true at h
    obtain ⟨hg, h⟩ := andB_true h
    rw [strictB_ml] at h
    rw [List.foldl_cons]
    exact ih _ _ (hi.step (by simpa only [Nat.blt_eq] using hg)) h

theorem spanHas_of (l : List ℕ) (h : spanChk l (List.range 64) = true) :
    spanHas l (List.range 64) = true := by
  unfold spanHas spanX
  refine spanChk_aux _ (fun d hd => List.mem_range.1 hd) l [0] 1 (fun x => ?_) h
  have h1 : (1 : ℕ) = 2 ^ 0 := rfl
  rw [List.mem_singleton, h1, Nat.testBit_two_pow, decide_eq_true_eq]
  constructor
  · rintro rfl
    exact ⟨by norm_num, rfl⟩
  · rintro ⟨-, hx⟩
    exact hx.symm

theorem sound1 (G : List B6) (h : chk1 G = true) : ∀ c ∈ oVecL, ∃ g ∈ G, g.app c = 1 := by
  intro c hc
  obtain ⟨g, hg, e⟩ := anyG_true (allL_true h c hc)
  exact ⟨g, hg, by rw [← appK_eq]; exact Nat.eq_of_beq_eq_true e⟩

theorem sound2 (G : List B6) (h : chk2 G = true) :
    ∀ c ∈ List.range 64, c ≠ 0 → c ∉ oVecL → ∀ d ∈ p1c, d ≠ 0 → ∃ g ∈ G, g.app c = d := by
  intro c hc h0 ho d hd hd0
  have h1 := right_of_orB (allL_true h c hc) (beq_false_of_ne h0)
  have h2 := right_of_orB h1 (by
    cases e : memN c oVecL
    · rfl
    · exact absurd ((memN_iff _ _).1 e) ho)
  have h3 := right_of_orB (allL_true h2 d hd) (beq_false_of_ne hd0)
  obtain ⟨g, hg, e⟩ := anyG_true h3
  exact ⟨g, hg, by rw [← appK_eq]; exact Nat.eq_of_beq_eq_true e⟩

theorem sound3 (G : List B6) (h : chk3 G = true) : (G.filter (presv pt1)).length = 180 := by
  have e := Nat.eq_of_beq_eq_true h
  rw [cntG_eq] at e
  rw [← List.countP_eq_length_filter, ← e]
  congr 1
  funext g
  rw [presvK_eq]

theorem sound5 (G : List B6) (h : chk5 G = true) :
    ∀ g ∈ G, presv pt1 g = true → blkC g = [1, 0, 0, 1] → g = B6.id := by
  intro g hg hp hb
  have h1 := imp_of_orB (allG_true h g hg) (by rw [presvK_eq]; exact hp)
  simp only [blkC, List.cons.injEq, and_true] at hb
  obtain ⟨e1, e2, e3, e4⟩ := hb
  refine beqB_true (imp_of_orB h1 ?_)
  simp only [Bool.and_eq_true, Nat.beq_eq]
  exact ⟨⟨⟨e1, e2⟩, e3⟩, e4⟩

theorem sound6 (T : List B6) (h : chk6 T = true) : ∀ g ∈ T, det2 g = 1 :=
  fun g hg => Nat.eq_of_beq_eq_true (allG_true h g hg)

theorem sound7 (T : List B6) (h : chk7 T = true) : ∀ c ∈ List.range 64, c ∉ pt1 →
    spanHas (pt1 ++ T.map (·.app c)) (List.range 64) = true := by
  intro c hc hp
  have h1 := right_of_orB (allL_true h c hc) (by
    cases e : memN c pt1
    · rfl
    · exact absurd ((memN_iff _ _).1 e) hp)
  exact spanHas_of _ (by simpa only [appK_eq] using h1)

theorem sound8 (T : List B6) (h : chk8 T = true) :
    spanHas (T.flatMap fun g => (List.range 64).map fun c => c ^^^ g.app c) (List.range 64) =
      true :=
  spanHas_of _ (by simpa only [chk8, appK_eq] using h)

theorem cube_of {a : B6} (h : cubeB a = true) : a.pow 3 = B6.id := by
  rw [← powK_eq]
  exact beqB_true h

theorem sound9 (T : List B6) (h : chk9 T = true) : ∀ g ∈ T, ∃ a ∈ T, ∃ b ∈ T,
    a.pow 3 = B6.id ∧ b.pow 3 = B6.id ∧ g = a.comp b := by
  intro g hg
  obtain ⟨a, ha, e⟩ := anyG_true (allG_true h g hg)
  obtain ⟨e1, e⟩ := andB_true e
  obtain ⟨e2, e⟩ := andB_true e
  obtain ⟨e3, e4⟩ := andB_true e
  refine ⟨a, ha, _, (memB_iff _ _).1 e2, cube_of e1, cube_of e3, ?_⟩
  rw [← compK_eq]
  exact beqB_true e4

theorem sound10 (T : List B6) (W : List ℕ) (h : chk10 T W = true) :
    ∀ g ∈ T, ∃ a ∈ T, ∃ b ∈ T, g = ((a.comp b).comp (inv6 a)).comp (inv6 b) := by
  intro g hg
  obtain ⟨h1, h2⟩ := andB_true h
  obtain ⟨w, hw, eg⟩ := anyL_true (allG_true h1 g hg)
  obtain ⟨e1, e⟩ := andB_true (allL_true h2 w hw)
  obtain ⟨e2, e3⟩ := andB_true e
  refine ⟨_, (memB_iff _ _).1 e1, _, (memB_iff _ _).1 e2, ?_⟩
  rw [beqB_true eg, beqB_true e3]
  simp only [compK_eq, powK_eq, inv6]

theorem sound11 (N : List B6) (h : chk11 N = true) :
    ∀ B ∈ N, B.comp B = B6.id → B ≠ B6.id → fixCount B ≤ 16 := by
  intro B hB h1 h2
  have e := imp_of_orB (allG_true h B hB) (invoB_of h1 h2)
  rw [← fixK_eq]
  exact Nat.le_of_ble_eq_true e

theorem sound12 (N : List B6) (h : chk12 N = true) :
    ∀ B ∈ N, B.pow 15 = B6.id → B ≠ B6.id → fixCount B < 8 := by
  intro B hB h1 h2
  obtain ⟨hv, e⟩ := andB_true (allG_true h B hB)
  have e := imp_of_orB e ((eq15B_iff (validB_valid hv)).2 h1)
  have e := right_of_orB e (beqB_false h2)
  rw [← fixK_eq]
  simpa only [Nat.blt_eq] using e

theorem sound13 (N : List B6) (h : chk13 N = true) :
    ∀ B ∈ N, B.comp B = B6.id → B ≠ B6.id → 16 ≤ fixCount B → ∃ c ∈ oVecL, B.app c = c := by
  intro B hB h1 h2 h3
  have e := imp_of_orB (allG_true h B hB) (invoB_of h1 h2)
  have e := right_of_orB e (by
    rw [fixK_eq]
    cases e : Nat.blt (fixCount B) 16
    · rfl
    · rw [Nat.blt_eq] at e
      omega)
  obtain ⟨c, hc, e⟩ := anyL_true e
  exact ⟨c, hc, by rw [← appK_eq]; exact Nat.eq_of_beq_eq_true e⟩

theorem sound14 (G : List B6) (h : chk14 G = true) : ∀ B ∈ G, B.comp B = B6.id → B ≠ B6.id →
    ∃ g ∈ G, ∀ c ∈ List.range 64, (B.app c = c ↔ g.app c ∈ l2c) := by
  intro B hB h1 h2
  have e := imp_of_orB (allG_true h B hB) (invoB_of h1 h2)
  rw [strictB_ml] at e
  obtain ⟨g, hg, e⟩ := anyG_true e
  refine ⟨g, hg, fun c hc => ?_⟩
  have hc' := List.mem_range.1 hc
  have e := allBelow_true _ 64 e c hc'
  have e' : (B.app c == c) = Nat.blt (appK g c) 16 := by
    rwa [eqB_eq, beq_iff_eq, bitN_eq, testBit_fixMK B hc'] at e
  have hl : l2c = List.range 16 := rfl
  rw [hl, List.mem_range, ← appK_eq g, ← Nat.blt_eq, ← e', beq_iff_eq]

theorem sound15 (N : List B6) (h : chk15 N = true) :
    ∀ B ∈ N, 8 ≤ (l2c.filter fun c => B.app c == c).length → B ∈ r2 := by
  intro B hB h1
  refine (memB_iff _ _).1 (right_of_orB (allG_true h B hB) ?_)
  rw [cntL_eq, List.countP_eq_length_filter]
  have e : (fun c => Nat.beq (appK B c) c) = fun c => B.app c == c := by
    funext c
    rw [nbeq, appK_eq]
  rw [e]
  cases e : Nat.blt _ 8
  · rfl
  · rw [Nat.blt_eq] at e
    omega

theorem sound16 (S N : List B6) (Y : List ℕ) (h : chk16 S N Y = true) :
    ∀ y ∈ S, y.comp y = B6.id → ∀ B ∈ N,
      (∀ c ∈ List.range 64, y.app c = c → B.app c = c) → B = B6.id ∨ B = y := by
  intro y hy h1 B hB hf
  obtain ⟨h2, h3⟩ := andB_true h
  have e := imp_of_orB (allG_true h2 y hy) (by rw [compK_eq]; exact (beqB_iff _ _).2 h1)
  obtain ⟨w, hw, ew⟩ := anyL_true e
  have hyw := beqB_true ew
  have e := allL_true h3 w hw
  simp only [strictB_ml] at e
  obtain ⟨f1, e⟩ := andB_true e
  obtain ⟨f2, e⟩ := andB_true e
  obtain ⟨f3, e⟩ := andB_true e
  have hfix : ∀ s, Nat.beq (appK (ofW w 0) (fldN w s)) (fldN w s) = true →
      Nat.beq (appK B (fldN w s)) (fldN w s) = true := by
    intro s hs
    have := hf (fldN w s) (List.mem_range.2 (ofW_lt w s))
      (by rw [hyw, ← appK_eq]; exact Nat.eq_of_beq_eq_true hs)
    rw [appK_eq, this]
    exact Nat.beq_refl _
  have e := imp_of_orB (allG_true e B hB) (by rw [hfix _ f1, hfix _ f2, hfix _ f3]; rfl)
  rcases orB_true e with e | e
  · exact Or.inl (beqB_true e)
  · exact Or.inr (by rw [hyw]; exact beqB_true e)

theorem sound17 (S : List B6) (h : chk17 S = true) :
    ∀ y ∈ S, y.comp y = B6.id → fixCount y = 8 := by
  intro y hy h1
  have e := imp_of_orB (allG_true h y hy) (by rw [compK_eq]; exact (beqB_iff _ _).2 h1)
  rw [← fixK_eq]
  exact Nat.eq_of_beq_eq_true e

theorem sound18 (S : List B6) (h : chk18 S = true) : ∀ y ∈ S, y.comp y = B6.id →
    ∀ p ∈ oPts, presv (ptOf p) y = true → ∃ c ∈ oVecL, y.app c = c := by
  intro y hy h1 p hp h2
  have e := imp_of_orB (allG_true h y hy) (by rw [compK_eq]; exact (beqB_iff _ _).2 h1)
  have e := imp_of_orB (allL_true e p hp) (by rw [presvK_eq]; exact h2)
  obtain ⟨c, hc, e⟩ := anyL_true e
  exact ⟨c, hc, by rw [← appK_eq]; exact Nat.eq_of_beq_eq_true e⟩

theorem sound19 (S : List B6) (h : chk19 S = true) : ∀ τ ∈ S,
    (∀ s ∈ s0, ∃ s' ∈ s0, τ.comp s = s'.comp τ) → two6 τ = true →
      ∃ k ∈ zs6, ∃ u ∈ s0p, k.comp τ = u.comp k := by
  intro t ht h1 h2
  have e := imp_of_orB (allG_true h t ht) (allG_of fun s hs => by
    obtain ⟨s', hs', e⟩ := h1 s hs
    exact anyG_of hs' (by rw [compK_eq, compK_eq]; exact (beqB_iff _ _).2 e))
  have e := imp_of_orB e (by
    rw [powK_eq]
    exact (beqB_iff _ _).2 (beq_iff_eq.1 h2))
  obtain ⟨k, hk, e⟩ := anyG_true e
  obtain ⟨u, hu, e⟩ := anyG_true e
  refine ⟨k, hk, u, by rw [← s0pK_eq]; exact hu, ?_⟩
  rw [← compK_eq, ← compK_eq]
  exact beqB_true e

theorem soundCl (L D : List B6) (h : chkCl L D = true) : ∀ x ∈ L, ∀ y ∈ L, x.comp y ∈ L := by
  intro x hx y hy
  obtain ⟨h1, h⟩ := andB_true h
  obtain ⟨h2, h3⟩ := andB_true h
  have hxD := (memB_iff _ _).1 (allG_true h1 x hx)
  have hyD := (memB_iff _ _).1 (allG_true h1 y hy)
  have e := (memB_iff _ _).1 (allG_true (allG_true h3 x hxD) y hyD)
  rw [compK_eq] at e
  exact (memB_iff _ _).1 (allG_true h2 _ e)

theorem soundZ (L C : List B6) (i : B6) (h : chkZ L C i = true) :
    ∀ B ∈ L, (∀ D ∈ C, B.comp D = D.comp B) → B = B6.id ∨ B = i := by
  intro B hB h1
  have e := imp_of_orB (allG_true h B hB) (allG_of fun D hD => by
    rw [compK_eq, compK_eq]
    exact (beqB_iff _ _).2 (h1 D hD))
  rcases orB_true e with e | e
  · exact Or.inl (beqB_true e)
  · exact Or.inr (beqB_true e)

theorem sound24 (S N : List B6) (h : chk24 S N = true) : ∀ y ∈ S, y.comp y = B6.id →
    ∃ m ∈ N, y.comp m = m.comp i1 ∨ y.comp m = m.comp i2 := by
  intro y hy h1
  have e := imp_of_orB (allG_true h y hy) (by rw [compK_eq]; exact (beqB_iff _ _).2 h1)
  obtain ⟨m, hm, e⟩ := anyG_true e
  refine ⟨m, hm, ?_⟩
  rw [← compK_eq, ← compK_eq, ← compK_eq]
  rcases orB_true e with e | e
  · exact Or.inl (beqB_true e)
  · exact Or.inr (beqB_true e)

theorem sound25 (N : List B6) (h : chk25 N = true) : ∀ m ∈ N, i2.comp m ≠ m.comp i1 := by
  intro m hm e
  have e2 := allG_true h m hm
  rw [compK_eq, compK_eq, (beqB_iff _ _).2 e] at e2
  exact absurd e2 (by decide)

theorem sound26 (G N : List B6) (h : chk26 G N = true) : i1 ∈ N ∧ i1 ∉ G ∧ i2 ∈ N ∧ i2 ∉ G := by
  obtain ⟨h1, h⟩ := andB_true h
  obtain ⟨h2, h⟩ := andB_true h
  obtain ⟨h3, h4⟩ := andB_true h
  rw [notB_eq, Bool.not_eq_true'] at h2 h4
  refine ⟨(memB_iff _ _).1 h1, fun e => ?_, (memB_iff _ _).1 h3, fun e => ?_⟩
  · rw [(memB_iff _ _).2 e] at h2
    exact absurd h2 (by decide)
  · rw [(memB_iff _ _).2 e] at h4
    exact absurd h4 (by decide)

theorem sound27 (h : chk27 = true) : i1 ∈ l1s0p ∧ i2 ∈ l2s0p := by
  obtain ⟨h1, h2⟩ := andB_true h
  rw [memB_iff, prodK_eq] at h1 h2
  exact ⟨h1, h2⟩

theorem sound28 (N : List B6) (h : chk28 N = true) : ∀ B ∈ N, B.pow 60 = B6.id := by
  intro B hB
  obtain ⟨hv, e⟩ := andB_true (allG_true h B hB)
  exact eq60B_true (validB_valid hv) e

end CFSG.KS.C7214

end
