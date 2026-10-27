module

public import CFSG.LocalAnalysis.ComponentClassification.J2CoverModelsSylow

public section

namespace CFSG.ComponentClassification.J2Cover.Models

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

@[expose] def IsNormCocycle {G : Type*} [Group G] (g : G → G → ZMod 2) : Prop :=
  (∀ b, g 1 b = 0) ∧ (∀ a, g a 1 = 0) ∧ ∀ a b c, g a b + g (a * b) c = g b c + g a (b * c)

@[expose] def cob {G : Type*} [Group G] (b : G → ZMod 2) (x y : G) : ZMod 2 :=
  b x + b y + b (x * y)

theorem zmod_two_add_self (v : ZMod 2) : v + v = 0 := by grind

theorem isNormCocycle_cob {G : Type*} [Group G] {b : G → ZMod 2} (hb : b 1 = 0) :
    IsNormCocycle (cob b) := by
  refine ⟨fun c => ?_, fun a => ?_, fun a c d => ?_⟩
  · simp only [cob, one_mul, hb, zero_add, zmod_two_add_self]
  · simp only [cob, mul_one, hb, add_zero, zmod_two_add_self]
  · simp only [cob, mul_assoc]
    grind

theorem IsNormCocycle.add {G : Type*} [Group G] {g g' : G → G → ZMod 2} (hg : IsNormCocycle g)
    (hg' : IsNormCocycle g') : IsNormCocycle fun a b => g a b + g' a b := by
  refine ⟨fun b => ?_, fun a => ?_, fun a b c => ?_⟩
  · change g 1 b + g' 1 b = 0
    rw [hg.1, hg'.1, add_zero]
  · change g a 1 + g' a 1 = 0
    rw [hg.2.1, hg'.2.1, add_zero]
  · change g a b + g' a b + (g (a * b) c + g' (a * b) c) =
      g b c + g' b c + (g a (b * c) + g' a (b * c))
    have h1 := hg.2.2 a b c
    have h2 := hg'.2.2 a b c
    grind

theorem IsNormCocycle.smul {G : Type*} [Group G] {g : G → G → ZMod 2} (hg : IsNormCocycle g)
    (e : ZMod 2) : IsNormCocycle fun a b => e * g a b := by
  refine ⟨fun b => ?_, fun a => ?_, fun a b c => ?_⟩
  · change e * g 1 b = 0
    rw [hg.1, mul_zero]
  · change e * g a 1 = 0
    rw [hg.2.1, mul_zero]
  · change e * g a b + e * g (a * b) c = e * g b c + e * g a (b * c)
    rw [← mul_add, ← mul_add, hg.2.2 a b c]

theorem IsNormCocycle.sum {G : Type*} [Group G] {ι : Type*} (s : Finset ι)
    {g : ι → G → G → ZMod 2} (hg : ∀ j ∈ s, IsNormCocycle (g j)) :
    IsNormCocycle fun a b => ∑ j ∈ s, g j a b := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨fun _ => by simp, fun _ => by simp, fun _ _ _ => by simp⟩
  | insert j s hj ih =>
    have hs := ih fun i hi => hg i (Finset.mem_insert_of_mem hi)
    have hj' := hg j (Finset.mem_insert_self j s)
    simp only [Finset.sum_insert hj]
    exact hj'.add hs

@[expose] noncomputable def tbl (rows : Array ℕ) (s t : S) : ZMod 2 :=
  if bitAt rows (idx s) (idx t) then 1 else 0

@[expose] noncomputable def mk1 (m : ℕ) (s : S) : ZMod 2 := if maskBit m (idx s) then 1 else 0

theorem tbl_elt (rows : Array ℕ) {x y : ℕ} (hx : x < 128) (hy : y < 128) :
    tbl rows (elt x) (elt y) = if bitAt rows x y then 1 else 0 := by
  rw [tbl, idx_elt hx, idx_elt hy]

theorem mk1_elt (m : ℕ) {x : ℕ} (hx : x < 128) :
    mk1 m (elt x) = if maskBit m x then 1 else 0 := by
  rw [mk1, idx_elt hx]

@[expose] noncomputable def hCoc (j : ℕ) : S → S → ZMod 2 := tbl (hRowsT j)

@[expose] noncomputable def fCoc : S → S → ZMod 2 := tbl fRows

@[expose] noncomputable def bCoch (j : ℕ) : S → ZMod 2 := mk1 (bMask j)

@[expose] noncomputable def eFlag (j : ℕ) : ZMod 2 := if eBit j then 1 else 0

@[expose] noncomputable def chi (k : ℕ) : S → ZMod 2 := mk1 (chiMask k)

@[expose] noncomputable def dd (g : S → S → ZMod 2) (x v w : S) : ZMod 2 :=
  g x v + g (x * v) w + g v w + g x (v * w)

theorem dd_mul (g : S → S → ZMod 2) (y p v w : S) :
    dd g (y * p) v w = dd g p v w + dd g y p v + dd g y (p * v) w + dd g y p (v * w) := by
  simp only [dd, mul_assoc]
  grind

theorem isNormCocycle_of_gen {g : S → S → ZMod 2} (hl : ∀ b, g 1 b = 0) (hr : ∀ a, g a 1 = 0)
    (hgen : ∀ k < 3, ∀ v w : S, g (yS k) v + g (yS k * v) w = g v w + g (yS k) (v * w)) :
    IsNormCocycle g := by
  have hdd : ∀ k < 3, ∀ v w : S, dd g (yS k) v w = 0 := fun k hk v w => by
    rw [dd, add_assoc, hgen k hk v w]
    grind
  have key : ∀ n, n < 128 → ∀ v w : S, dd g (elt n) v w = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn v w
      by_cases hn0 : n = 0
      · subst hn0
        rw [elt_zero, dd, one_mul, hl, hl, zero_add, add_zero, zmod_two_add_self]
      · have hp := par_lt hn0
        rw [elt_cons hn0 hn, dd_mul, ih _ hp (hp.trans hn), hdd _ (gen_lt n), hdd _ (gen_lt n),
          hdd _ (gen_lt n)]
        simp
  refine ⟨hl, hr, fun a b c => ?_⟩
  have := key (idx a) (idx_lt a) b c
  rw [elt_idx, dd] at this
  grind

theorem eq_zero_of_gen {c : S → S → ZMod 2} (hc : IsNormCocycle c)
    (h : ∀ k < 3, ∀ t, c (yS k) t = 0) (s t : S) : c s t = 0 := by
  have key : ∀ n, n < 128 → ∀ t : S, c (elt n) t = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn t
      by_cases hn0 : n = 0
      · subst hn0
        rw [elt_zero, hc.1]
      · have hp := par_lt hn0
        have hcc := hc.2.2 (yS (gen n)) (elt (par n)) t
        rw [h _ (gen_lt n), h _ (gen_lt n), ih _ hp (hp.trans hn), zero_add] at hcc
        rw [elt_cons hn0 hn, hcc, add_zero]
  rw [← elt_idx s]
  exact key _ (idx_lt s) t

theorem normCocOK_parts {rows : Array ℕ} (h : normCocOK rows = true) :
    (∀ x < 128, bitAt rows 0 x = false ∧ bitAt rows x 0 = false) ∧
    allLt 3 (fun k => allLt 128 fun b => allLt 128 fun c =>
      !(bitAt rows (k + 1) b ^^ bitAt rows (lmulTab[k]!)[b]! c ^^ bitAt rows b c ^^
        bitAt rows (k + 1) (mulTab[b]!)[c]!)) = true := by
  rw [normCocOK, Bool.and_eq_true] at h
  refine ⟨fun x hx => ?_, h.2⟩
  have := allLt_spec h.1 hx
  simpa [Bool.and_eq_true] using this

theorem isNormCocycle_tbl {rows : Array ℕ} (h : normCocOK rows = true) :
    IsNormCocycle (tbl rows) := by
  have h0 := (normCocOK_parts h).1
  have h1 := (normCocOK_parts h).2
  refine isNormCocycle_of_gen (fun b => ?_) (fun a => ?_) (fun k hk v w => ?_)
  · rw [← elt_idx b, ← elt_zero, tbl_elt rows (by norm_num) (idx_lt b), (h0 _ (idx_lt b)).1]
    rfl
  · rw [← elt_idx a, ← elt_zero, tbl_elt rows (idx_lt a) (by norm_num), (h0 _ (idx_lt a)).2]
    rfl
  · have hkb := allLt_spec (allLt_spec (allLt_spec h1 hk) (idx_lt v)) (idx_lt w)
    obtain ⟨hl1, hl2⟩ := lmul_spec hk (idx_lt v)
    obtain ⟨hm1, hm2⟩ := mulIdx_spec (a := idx v) (idx_lt w)
    rw [lmulTab_get hk (idx_lt v), mulTab_get (idx_lt v) (idx_lt w)] at hkb
    have e1 : yS k = elt (k + 1) := (elt_succ hk).symm
    have e2 : yS k * v = elt (lmul k (idx v)) := by rw [hl2, elt_idx]
    have e3 : v * w = elt (mulIdx (idx v) (idx w)) := by rw [hm2, elt_idx, elt_idx]
    rw [e2, e3, e1, ← elt_idx v, ← elt_idx w, idx_elt (idx_lt v), idx_elt (idx_lt w),
      tbl_elt rows (by omega) (idx_lt v), tbl_elt rows hl1 (idx_lt w),
      tbl_elt rows (idx_lt v) (idx_lt w), tbl_elt rows (by omega) hm1]
    revert hkb
    cases bitAt rows (k + 1) (idx v) <;> cases bitAt rows (lmul k (idx v)) (idx w) <;>
      cases bitAt rows (idx v) (idx w) <;> cases bitAt rows (k + 1) (mulIdx (idx v) (idx w)) <;>
      decide

theorem cocycleCheck_parts :
    normCocOK fRows = true ∧
    (∀ j < 6, normCocOK (hRowsT j) = true ∧ treeNormOK (hRowsT j) = true ∧
      ∀ l < 6, qPos l < 384 ∧ bitAt (hRowsT j) (qPos l / 128 + 1) (qPos l % 128) = (j == l)) ∧
    (∀ k < 3, (∀ m < 3, maskBit (chiMask k) (m + 1) = (k == m)) ∧
      ∀ a < 128, ∀ d < 128,
        maskBit (chiMask k) ((mulTab[a]!)[d]!) =
          (maskBit (chiMask k) a ^^ maskBit (chiMask k) d)) := by
  have h := cocycleCheck_eq
  simp only [cocycleCheck, Bool.and_eq_true, allLt_iff, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  exact ⟨h1, fun j hj => ⟨(h2 j hj).1.1, (h2 j hj).1.2, fun l hl => (h2 j hj).2 l hl⟩,
    fun k hk => ⟨(h3 k hk).1, (h3 k hk).2⟩⟩

theorem isNormCocycle_fCoc : IsNormCocycle fCoc := isNormCocycle_tbl cocycleCheck_parts.1

theorem isNormCocycle_hCoc {j : ℕ} (hj : j < 6) : IsNormCocycle (hCoc j) :=
  isNormCocycle_tbl (cocycleCheck_parts.2.1 j hj).1

theorem hCoc_tree {j : ℕ} (hj : j < 6) {x : ℕ} (hx0 : x ≠ 0) (hx : x < 128) :
    hCoc j (yS (gen x)) (elt (par x)) = 0 := by
  have h := allLt_spec (cocycleCheck_parts.2.1 j hj).2.1 hx
  simp only [Bool.or_eq_true, beq_iff_eq, hx0, false_or, Bool.not_eq_true'] at h
  rw [hCoc, ← elt_succ (gen_lt x), tbl_elt _ (by have := gen_lt x; omega)
    ((par_lt hx0).trans hx), h]
  rfl

theorem hCoc_free {j l : ℕ} (hj : j < 6) (hl : l < 6) :
    hCoc j (yS (qPos l / 128)) (elt (qPos l % 128)) = if j = l then 1 else 0 := by
  obtain ⟨hq, h⟩ := (cocycleCheck_parts.2.1 j hj).2.2 l hl
  have hk : qPos l / 128 < 3 := by omega
  rw [hCoc, ← elt_succ hk, tbl_elt _ (by omega) (Nat.mod_lt _ (by norm_num)), h]
  by_cases hjl : j = l <;> simp [hjl]

theorem chi_hom {k : ℕ} (hk : k < 3) (s t : S) : chi k (s * t) = chi k s + chi k t := by
  have h := (cocycleCheck_parts.2.2 k hk).2 (idx s) (idx_lt s) (idx t) (idx_lt t)
  obtain ⟨hm1, hm2⟩ := mulIdx_spec (a := idx s) (idx_lt t)
  rw [elt_idx, elt_idx] at hm2
  rw [chi, ← hm2, mk1_elt _ hm1, ← elt_idx s, ← elt_idx t, mk1_elt _ (idx_lt _),
    mk1_elt _ (idx_lt _), idx_elt (idx_lt s), idx_elt (idx_lt t), ← mulTab_get (idx_lt s)
    (idx_lt t), h]
  cases maskBit (chiMask k) (idx s) <;> cases maskBit (chiMask k) (idx t) <;> decide

theorem chi_gen {k m : ℕ} (hk : k < 3) (hm : m < 3) : chi k (yS m) = if k = m then 1 else 0 := by
  have h := (cocycleCheck_parts.2.2 k hk).1 m hm
  rw [chi, ← elt_succ hm, mk1_elt _ (by omega), h]
  by_cases hkm : k = m <;> simp [hkm]

section Tree

variable (g : S → S → ZMod 2)

@[expose] noncomputable def val (k : ℕ) : ZMod 2 := g (yS (k / 128)) (elt (k % 128))

@[expose] noncomputable def eval (m : ℕ) : ZMod 2 :=
  ∑ k ∈ Finset.range 384, if m.testBit k then val g k else 0

theorem val_eq {i m : ℕ} (hm : m < 128) : val g (128 * i + m) = g (yS i) (elt m) := by
  rw [val, show (128 * i + m) / 128 = i by omega, show (128 * i + m) % 128 = m by omega]

theorem eval_xor (m m' : ℕ) : eval g (m ^^^ m') = eval g m + eval g m' := by
  rw [eval, eval, eval, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Nat.testBit_xor]
  cases m.testBit k <;> cases m'.testBit k <;> simp [zmod_two_add_self]

theorem eval_two_pow {j : ℕ} (hj : j < 384) : eval g (2 ^ j) = val g j := by
  simp only [eval, Nat.testBit_two_pow, decide_eq_true_eq]
  rw [Finset.sum_ite_eq]
  simp [hj]

theorem eval_and_eq_zero {K : ℕ} (hK : ∀ k < 384, K.testBit k = true → val g k = 0) (m : ℕ) :
    eval g (m &&& K) = 0 := by
  refine Finset.sum_eq_zero fun k hk => ?_
  rw [Nat.testBit_and]
  cases h : K.testBit k
  · simp
  · simp [hK k (Finset.mem_range.1 hk) h]

theorem eval_eq_zero (h : ∀ k < 384, val g k = 0) (m : ℕ) : eval g m = 0 :=
  Finset.sum_eq_zero fun k hk => by simp [h k (Finset.mem_range.1 hk)]

@[expose] def wmask (x h : ℕ) : ℕ :=
  (path x).foldr (fun z acc => 2 ^ (128 * gen z + mulIdx (par z) h) ^^^ acc) 0

theorem wmask_zero (h : ℕ) : wmask 0 h = 0 := by simp [wmask, path_zero]

theorem wmask_cons {x : ℕ} (hx0 : x ≠ 0) (hx : x < 128) (h : ℕ) :
    wmask x h = 2 ^ (128 * gen x + mulIdx (par x) h) ^^^ wmask (par x) h := by
  rw [wmask, path_cons hx0 hx, List.foldr_cons]
  rfl

inductive Step
  | edge (x : ℕ)
  | free (l : ℕ)
  | coc (i b h j : ℕ)

@[expose] def Step.mask : Step → ℕ
  | .edge x => 2 ^ (128 * gen x + par x)
  | .free l => 2 ^ qPos l
  | .coc i b h _ =>
    2 ^ (128 * i + b) ^^^ wmask (lmul i b) h ^^^ wmask b h ^^^ 2 ^ (128 * i + mulIdx b h)

@[expose] def Step.pivot : Step → ℕ
  | .edge x => 128 * gen x + par x
  | .free l => qPos l
  | .coc _ _ _ j => j

@[expose] def Step.valid : Step → Bool
  | .edge x => x != 0 && decide (x < 128)
  | .free l => decide (l < 6)
  | .coc i b h _ => decide (i < 3) && decide (b < 128) && decide (h < 128)

@[expose] def peel : ℕ → List Step → Bool
  | K, [] => K == 2 ^ 384 - 1
  | K, s :: l => s.valid && decide (s.pivot < 384) &&
      (s.mask ^^^ (s.mask &&& K) == 2 ^ s.pivot) && peel (K ||| 2 ^ s.pivot) l

@[expose] def certSteps : List Step :=
  [.coc 0 7 2 140, .coc 0 7 7 40, .coc 0 9 9 48, .coc 0 14 5 181, .coc 0 16 6 311, .coc 0 19 1 33,
   .coc 0 19 2 164, .coc 0 19 3 51, .coc 0 19 4 58, .coc 0 19 6 74, .coc 0 19 12 228,
   .coc 0 20 8 86, .coc 0 32 1 57, .coc 0 32 11 11, .coc 0 33 4 97, .coc 0 34 98 355,
   .coc 0 37 1 62, .coc 0 37 2 71, .coc 0 37 5 109, .coc 0 37 17 91, .coc 0 37 26 354,
   .coc 0 51 4 112, .coc 0 70 1 108, .coc 0 78 2 246, .coc 1 2 1 133, .coc 1 2 3 138,
   .coc 1 2 6 145, .coc 1 2 7 146, .coc 1 2 8 149, .coc 1 2 9 150, .coc 1 2 11 154, .coc 1 2 13 159,
   .coc 1 2 14 160, .coc 1 2 15 163, .coc 1 2 19 170, .coc 1 2 20 171, .coc 1 2 23 177,
   .coc 1 2 24 178, .coc 1 2 27 184, .coc 1 2 28 185, .coc 1 2 29 188, .coc 1 2 30 189,
   .coc 1 2 33 194, .coc 1 2 34 195, .coc 1 2 37 200, .coc 1 2 38 201, .coc 1 2 40 168,
   .coc 1 2 41 206, .coc 1 2 44 211, .coc 1 2 45 212, .coc 1 2 47 216, .coc 1 2 48 217,
   .coc 1 2 51 222, .coc 1 2 52 223, .coc 1 2 54 227, .coc 1 2 58 232, .coc 1 2 59 233,
   .coc 1 2 62 238, .coc 1 2 63 239, .coc 1 2 65 242, .coc 1 2 68 245, .coc 1 2 71 248,
   .coc 1 2 74 251, .coc 1 2 75 252, .coc 1 40 2 7, .coc 1 40 5 14, .coc 1 40 12 28,
   .coc 1 40 14 53, .coc 1 77 7 205, .coc 1 77 11 76, .coc 1 77 12 226, .coc 1 77 26 65,
   .coc 1 98 2 103, .coc 1 116 57 90, .coc 2 55 2 356, .coc 2 55 5 68, .coc 2 55 12 106,
   .coc 2 55 26 87, .coc 2 55 28 82, .coc 2 55 32 81, .coc 2 78 2 334, .coc 2 78 28 80,
   .coc 2 78 57 113, .coc 2 88 53 344, .coc 2 88 57 373, .coc 2 99 26 370, .coc 2 114 18 127,
   .coc 2 117 32 376, .coc 2 123 10 94, .coc 0 7 37 72, .coc 0 7 48 89, .coc 0 7 62 110,
   .coc 0 11 25 52, .coc 0 11 39 75, .coc 0 19 15 119, .coc 0 19 27 357, .coc 0 32 10 220,
   .coc 0 32 17 73, .coc 0 32 21 84, .coc 0 32 31 111, .coc 0 72 2 120, .coc 0 73 11 225,
   .coc 0 80 10 348, .coc 0 80 11 124, .coc 0 105 112 350, .coc 0 108 66 353, .coc 0 108 72 304,
   .coc 0 108 112 293, .coc 0 109 33 61, .coc 0 111 90 330, .coc 0 112 33 324, .coc 0 114 13 269,
   .coc 0 114 18 333, .coc 0 115 13 115, .coc 0 115 18 153, .coc 0 115 32 167, .coc 0 115 53 208,
   .coc 0 115 97 9, .coc 0 117 2 117, .coc 0 117 5 209, .coc 0 117 12 244, .coc 0 117 18 88,
   .coc 0 117 26 361, .coc 0 117 32 237, .coc 0 117 40 210, .coc 0 117 50 345, .coc 0 117 57 85,
   .coc 0 117 61 336, .coc 0 117 97 100, .coc 0 118 53 118, .coc 0 118 54 310, .coc 0 118 94 327,
   .coc 0 118 103 359, .coc 0 119 1 363, .coc 0 119 4 382, .coc 0 119 5 347, .coc 0 119 24 24,
   .coc 0 119 32 335, .coc 0 119 50 93, .coc 0 119 54 204, .coc 0 119 57 66, .coc 0 119 103 339,
   .coc 0 120 10 259, .coc 0 120 18 234, .coc 0 120 31 36, .coc 0 120 76 381, .coc 0 121 10 121,
   .coc 0 121 13 367, .coc 0 121 17 219, .coc 0 121 18 307, .coc 0 121 26 107, .coc 0 121 29 235,
   .coc 0 121 30 30, .coc 0 121 31 249, .coc 0 121 32 38, .coc 0 121 33 116, .coc 0 121 37 279,
   .coc 0 121 50 275, .coc 0 121 53 79, .coc 0 121 56 366, .coc 0 121 65 372, .coc 0 121 66 207,
   .coc 0 121 100 55, .coc 0 121 106 314, .coc 0 122 7 122, .coc 0 122 9 218, .coc 0 122 11 229,
   .coc 0 122 12 104, .coc 0 122 23 22, .coc 0 122 28 340, .coc 0 122 30 379, .coc 0 122 32 78,
   .coc 0 122 37 360, .coc 0 122 41 297, .coc 0 122 42 302, .coc 0 122 48 318, .coc 0 122 51 69,
   .coc 0 122 58 303, .coc 0 122 62 95, .coc 0 122 67 67, .coc 0 122 70 326, .coc 0 122 74 264,
   .coc 0 122 76 332, .coc 0 122 77 77, .coc 0 122 80 371, .coc 0 122 91 369, .coc 0 122 108 364,
   .coc 0 122 109 365, .coc 0 122 113 281, .coc 0 122 114 255, .coc 0 122 115 351,
   .coc 0 122 124 380, .coc 0 122 125 125, .coc 0 123 2 123, .coc 0 123 3 346, .coc 0 123 5 221,
   .coc 0 123 10 98, .coc 0 123 12 250, .coc 0 123 13 241, .coc 0 123 21 213, .coc 0 123 22 289,
   .coc 0 123 23 253, .coc 0 123 24 192, .coc 0 123 25 224, .coc 0 123 26 92, .coc 0 123 27 368,
   .coc 0 123 32 374, .coc 0 123 33 375, .coc 0 123 34 34, .coc 0 123 43 43, .coc 0 123 47 343,
   .coc 0 123 50 358, .coc 0 123 52 320, .coc 0 123 53 247, .coc 0 123 59 59, .coc 0 123 60 285,
   .coc 0 123 62 321, .coc 0 123 65 126, .coc 0 123 66 16, .coc 0 123 77 341, .coc 0 123 81 63,
   .coc 0 123 84 338, .coc 0 123 85 352, .coc 0 123 86 214, .coc 0 123 88 254, .coc 0 123 89 243,
   .coc 0 123 94 271, .coc 0 123 95 96, .coc 0 123 96 377, .coc 0 123 99 300, .coc 0 123 101 101,
   .coc 0 123 105 105, .coc 0 123 107 174, .coc 0 123 108 236, .coc 0 123 109 45,
   .coc 0 123 111 295, .coc 0 123 115 383, .coc 0 123 116 262, .coc 0 123 122 349,
   .coc 0 123 126 198, .coc 0 124 16 283, .coc 0 124 17 231, .coc 0 124 18 230, .coc 0 124 20 20,
   .coc 0 124 25 342, .coc 0 124 33 362, .coc 0 124 37 215, .coc 0 124 54 378, .coc 0 124 62 83,
   .coc 0 124 74 337, .coc 0 124 85 240]

@[expose] def allSteps : List Step :=
  (List.range 127).map (fun k => Step.edge (k + 1)) ++ (List.range 6).map Step.free ++ certSteps

theorem peel_allSteps : peel 0 allSteps = true := by decide +kernel

variable {g}

theorem peel_sound (hs : ∀ s : Step, s.valid = true → eval g s.mask = 0) :
    ∀ (l : List Step) (K : ℕ), (∀ k < 384, K.testBit k = true → val g k = 0) →
      peel K l = true → ∀ k < 384, val g k = 0
  | [], K, hK, hp, k, hk => by
    rw [peel, beq_iff_eq] at hp
    exact hK k hk (by rw [hp, Nat.testBit_two_pow_sub_one]; simpa using hk)
  | s :: l, K, hK, hp, k, hk => by
    simp only [peel, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hp
    obtain ⟨⟨⟨hv, hj⟩, hm⟩, hp⟩ := hp
    refine peel_sound hs l _ (fun k' hk' hb => ?_) hp k hk
    rw [Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true, decide_eq_true_eq] at hb
    rcases hb with hb | rfl
    · exact hK k' hk' hb
    · have hsplit : s.mask = (s.mask &&& K) ^^^ (s.mask ^^^ (s.mask &&& K)) := by
        rw [← Nat.xor_assoc, Nat.xor_comm (s.mask &&& K) s.mask, Nat.xor_assoc, Nat.xor_self,
          Nat.xor_zero]
      have := hs s hv
      rw [hsplit, eval_xor, eval_and_eq_zero g hK, hm, eval_two_pow g hj, zero_add] at this
      exact this

variable (hl : ∀ b, g 1 b = 0) (hc : ∀ a b c, g a b + g (a * b) c = g b c + g a (b * c))
  (ht : ∀ x, x ≠ 0 → x < 128 → g (yS (gen x)) (elt (par x)) = 0)
include hl hc ht

theorem eval_wmask : ∀ x, x < 128 → ∀ h, h < 128 → eval g (wmask x h) = g (elt x) (elt h) := by
  intro x
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    intro hx h hh
    by_cases hx0 : x = 0
    · subst hx0
      rw [wmask_zero, elt_zero, hl, eval, Finset.sum_eq_zero]
      intro k _
      simp
    · have hp := par_lt hx0
      have hpx : par x < 128 := hp.trans hx
      obtain ⟨hm, hm'⟩ := mulIdx_spec (a := par x) hh
      rw [wmask_cons hx0 hx, eval_xor, eval_two_pow g (by have := gen_lt x; omega), val_eq g hm,
        hm', ih _ hp hpx h hh, elt_cons hx0 hx]
      have := hc (yS (gen x)) (elt (par x)) (elt h)
      rw [ht x hx0 hx, zero_add] at this
      rw [this]
      grind

theorem eval_step_mask (hq : ∀ l < 6, val g (qPos l) = 0) (s : Step) (hv : s.valid = true) :
    eval g s.mask = 0 := by
  cases s with
  | edge x =>
    simp only [Step.valid, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hv
    obtain ⟨hx0, hx⟩ := hv
    have hp := par_lt hx0
    have hg := gen_lt x
    rw [Step.mask, eval_two_pow g (by omega), val_eq g (by omega), ht x hx0 hx]
  | free l =>
    simp only [Step.valid, decide_eq_true_eq] at hv
    have hq' := (cocycleCheck_parts.2.1 0 (by norm_num)).2.2 l hv
    rw [Step.mask, eval_two_pow g hq'.1, hq l hv]
  | coc i b h j =>
    simp only [Step.valid, Bool.and_eq_true, decide_eq_true_eq] at hv
    obtain ⟨⟨hi, hb⟩, hh⟩ := hv
    obtain ⟨hl1, hl2⟩ := lmul_spec hi hb
    obtain ⟨hm1, hm2⟩ := mulIdx_spec (a := b) hh
    rw [Step.mask, eval_xor, eval_xor, eval_xor, eval_two_pow g (by omega),
      eval_two_pow g (by omega), val_eq g hb, val_eq g hm1, eval_wmask hl hc ht _ hl1 h hh,
      eval_wmask hl hc ht _ hb h hh, hl2, hm2]
    have := hc (yS i) (elt b) (elt h)
    grind

theorem eq_zero_of_tree (hq : ∀ l < 6, val g (qPos l) = 0) (a b : S) : g a b = 0 := by
  have hval := peel_sound (eval_step_mask hl hc ht hq) allSteps 0 (by simp) peel_allSteps
  rw [← elt_idx a, ← elt_idx b, ← eval_wmask hl hc ht _ (idx_lt a) _ (idx_lt b),
    eval_eq_zero g hval]

end Tree


theorem sum_fin_six_delta (ε : Fin 6 → ZMod 2) {m : ℕ} (hm : m < 6) :
    ∑ j : Fin 6, ε j * (if (j : ℕ) = m then 1 else 0) = ε ⟨m, hm⟩ := by
  have : ∀ j : Fin 6, ε j * (if (j : ℕ) = m then 1 else 0) =
      if j = ⟨m, hm⟩ then ε j else 0 := fun j => by
    by_cases hj : (j : ℕ) = m
    · rw [ite_eq_left hj, ite_eq_left (Fin.ext hj), mul_one]
    · rw [ite_eq_right hj, ite_eq_right (fun h => hj (by rw [h])), mul_zero]
  rw [Finset.sum_congr rfl fun j _ => this j, Finset.sum_ite_eq']
  simp

@[expose] noncomputable def lamPath (g : S → S → ZMod 2) (x : ℕ) : ZMod 2 :=
  ((path x).map fun z => g (yS (gen z)) (elt (par z))).sum

theorem lamPath_zero (g : S → S → ZMod 2) : lamPath g 0 = 0 := by
  simp [lamPath, path_zero]

theorem lamPath_cons (g : S → S → ZMod 2) {x : ℕ} (hx0 : x ≠ 0) (hx : x < 128) :
    lamPath g x = g (yS (gen x)) (elt (par x)) + lamPath g (par x) := by
  simp only [lamPath, path_cons hx0 hx, List.map_cons, List.sum_cons]

theorem tree_cob (g : S → S → ZMod 2) (hg : IsNormCocycle g) {x : ℕ} (hx0 : x ≠ 0)
    (hx : x < 128) :
    g (yS (gen x)) (elt (par x)) + cob (fun s => lamPath g (idx s)) (yS (gen x)) (elt (par x)) =
      0 := by
  have hg3 := gen_lt x
  have hp := par_lt hx0
  have hy : lamPath g (idx (yS (gen x))) = 0 := by
    rw [← elt_succ hg3, idx_elt (by omega), lamPath_cons g (by omega) (by omega),
      (gen_par_succ hg3).1, (gen_par_succ hg3).2, elt_zero, hg.2.1, lamPath_zero, add_zero]
  rw [cob, hy, ← elt_cons hx0 hx, idx_elt (hp.trans hx), idx_elt hx, lamPath_cons g hx0 hx]
  grind

theorem exists_eq_cob_add_sum (g : S → S → ZMod 2) (hg : IsNormCocycle g) :
    ∃ (b : S → ZMod 2) (ε : Fin 6 → ZMod 2), ∀ s t, g s t = cob b s t + ∑ j, ε j * hCoc j s t := by
  set μ : S → ZMod 2 := fun s => lamPath g (idx s) with hμ
  have hμ1 : μ 1 = 0 := by
    rw [hμ]
    simp only
    rw [← elt_zero, idx_elt (by norm_num), lamPath_zero]
  set g1 : S → S → ZMod 2 := fun s t => g s t + cob μ s t with hg1
  have hc1 : IsNormCocycle g1 := hg.add (isNormCocycle_cob hμ1)
  set ε : Fin 6 → ZMod 2 := fun l => val g1 (qPos l) with hε
  set g2 : S → S → ZMod 2 := fun s t => g1 s t + ∑ j : Fin 6, ε j * hCoc j s t with hg2
  have hc2 : IsNormCocycle g2 :=
    hc1.add (IsNormCocycle.sum _ fun j _ => (isNormCocycle_hCoc j.isLt).smul (ε j))
  have ht2 : ∀ x, x ≠ 0 → x < 128 → g2 (yS (gen x)) (elt (par x)) = 0 := by
    intro x hx0 hx
    rw [hg2]
    simp only
    rw [hg1]
    simp only
    rw [tree_cob g hg hx0 hx, zero_add]
    exact Finset.sum_eq_zero fun j _ => by rw [hCoc_tree j.isLt hx0 hx, mul_zero]
  have hq2 : ∀ l < 6, val g2 (qPos l) = 0 := by
    intro l hl
    rw [val, hg2]
    simp only
    have : ∀ j : Fin 6, ε j * hCoc j (yS (qPos l / 128)) (elt (qPos l % 128)) =
        ε j * (if (j : ℕ) = l then 1 else 0) := fun j => by rw [hCoc_free j.isLt hl]
    rw [Finset.sum_congr rfl fun j _ => this j, sum_fin_six_delta ε hl]
    exact zmod_two_add_self _
  refine ⟨μ, ε, fun s t => ?_⟩
  have h0 := eq_zero_of_tree (g := g2) hc2.1 hc2.2.2 ht2 hq2 s t
  rw [hg2, hg1] at h0
  simp only at h0
  grind

theorem eq_zero_of_sum_eq_cob (ε : Fin 6 → ZMod 2) (b : S → ZMod 2)
    (h : ∀ s t, ∑ j, ε j * hCoc j s t = cob b s t) : ε = 0 := by
  have hb1 : b 1 = 0 := by
    have := h 1 1
    rw [Finset.sum_eq_zero fun j _ => by rw [(isNormCocycle_hCoc j.isLt).1, mul_zero], cob,
      mul_one] at this
    grind
  have htree : ∀ x, x ≠ 0 → x < 128 → b (elt x) = b (yS (gen x)) + b (elt (par x)) := by
    intro x hx0 hx
    have := h (yS (gen x)) (elt (par x))
    rw [Finset.sum_eq_zero fun j _ => by rw [hCoc_tree j.isLt hx0 hx, mul_zero], cob,
      ← elt_cons hx0 hx] at this
    grind
  set χ : S → ZMod 2 := fun s => ∑ k : Fin 3, b (yS k) * chi k s with hχ
  have hχm : ∀ s t, χ (s * t) = χ s + χ t := fun s t => by
    rw [hχ]
    simp only
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by rw [chi_hom k.isLt, mul_add]
  have hχy : ∀ m < 3, χ (yS m) = b (yS m) := fun m hm => by
    rw [hχ]
    simp only
    have : ∀ k : Fin 3, b (yS k) * chi k (yS m) = if k = ⟨m, hm⟩ then b (yS k) else 0 :=
      fun k => by
        rw [chi_gen k.isLt hm]
        by_cases hk : (k : ℕ) = m
        · rw [ite_eq_left hk, ite_eq_left (Fin.ext hk), mul_one]
        · rw [ite_eq_right hk, ite_eq_right (fun h => hk (by rw [h])), mul_zero]
    rw [Finset.sum_congr rfl fun k _ => this k, Finset.sum_ite_eq']
    simp
  have hχ1 : χ 1 = 0 := by
    have := hχm 1 1
    rw [mul_one] at this
    grind
  have hbχ : ∀ n, n < 128 → b (elt n) = χ (elt n) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn
      by_cases hn0 : n = 0
      · subst hn0
        rw [elt_zero, hb1, hχ1]
      · have hp := par_lt hn0
        rw [htree n hn0 hn, elt_cons hn0 hn, hχm, hχy _ (gen_lt n), ih _ hp (hp.trans hn)]
  have hcob : ∀ s t, cob b s t = 0 := fun s t => by
    rw [cob, ← elt_idx s, ← elt_idx t, ← (mulIdx_spec (a := idx s) (idx_lt t)).2,
      hbχ _ (idx_lt s), hbχ _ (idx_lt t), hbχ _ (mulIdx_spec (a := idx s) (idx_lt t)).1,
      (mulIdx_spec (a := idx s) (idx_lt t)).2, hχm]
    grind
  funext m
  have := h (yS (qPos m / 128)) (elt (qPos m % 128))
  have hs : ∀ j : Fin 6, ε j * hCoc j (yS (qPos m / 128)) (elt (qPos m % 128)) =
      ε j * (if (j : ℕ) = m then 1 else 0) := fun j => by rw [hCoc_free j.isLt m.isLt]
  rw [Finset.sum_congr rfl fun j _ => hs j, sum_fin_six_delta ε m.isLt, hcob] at this
  simpa using this

end CFSG.ComponentClassification.J2Cover.Models
