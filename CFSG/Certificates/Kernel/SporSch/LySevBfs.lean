module

public import CFSG.Certificates.Kernel.SporSch.LyKeyLemmas
public import CFSG.Sporadic.Schreier.LyCheckSeven
import CFSG.Certificates.Kernel.SporSch.LyLoop

public section

namespace CFSG.KS.SporSch.LySvB

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch.LySev CFSG.KS.SporSch.LyLoop CFSG.KS.SporSch.LyM
open CFSG.Sporadic.LySchreier.Native CFSG.Sporadic.Th.Native

@[expose] noncomputable def dec7B (x : Nat) : Array Nat := Array.ofFn (n := 7) fun r => d3 x r.val

@[expose] noncomputable def dec49B (x : Nat) : Array Nat := Array.ofFn (n := 49) fun t => d3 x t.val

theorem d3_eq (x t : Nat) : d3 x t = x / 2 ^ (3 * t) % 8 := by
  unfold d3
  change (x >>> (3 * t)) &&& (2 ^ 3 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

theorem getD7 {x r : Nat} (hr : r < 7) : (dec7B x)[r]! = d3 x r := by
  unfold dec7B
  rw [ofFn_getP (fun r => d3 x r) hr]

theorem getD49 {x t : Nat} (ht : t < 49) : (dec49B x)[t]! = d3 x t := by
  unfold dec49B
  rw [ofFn_getP (fun t => d3 x t) ht]

theorem foldr_sum (g : Nat → Nat) : ∀ (n a : Nat),
    (List.range n).foldr (fun c s => Nat.add s (g c)) a = a + ∑ c ∈ Finset.range n, g c
  | 0, a => by simp
  | n + 1, a => by
    rw [List.range_succ, List.foldr_append, List.foldr_cons, List.foldr_nil, foldr_sum g n,
      Finset.sum_range_succ]
    change a + g n + _ = _
    omega

theorem place_fld {w n : Nat} {val : Nat → Nat} (hw : 0 < w) (hv : ∀ r < n, val r < 2 ^ w) {r : Nat}
    (hr : r < n) :
    CFSG.KS.SporSch.LyK.placeF val (fun r => w * r) n / 2 ^ (w * r) % 2 ^ w = val r := by
  have hn : 0 < n := by omega
  have hspec := CFSG.KS.SporSch.LyK.placeF_spec (d := n) (w := w) (S := w * n) (N := n) le_rfl
    (pl := fun p => p) (val := val) (sh := fun r => w * r)
    (fun p hp => by nlinarith) (fun p hp q hq h => h) hv
    (fun p hp => by rw [Nat.div_eq_of_lt hp, Nat.mod_eq_of_lt hp]; omega) n le_rfl
  have e := hspec.1 r hr
  unfold CFSG.KS.SporSch.LyM.entL at e
  rw [Nat.div_eq_of_lt hr, Nat.mod_eq_of_lt hr, Nat.mul_zero, Nat.zero_add] at e
  exact e

theorem mv7K_place (R x : Nat) : mv7K R x = CFSG.KS.SporSch.LyK.placeF
    (fun r => (∑ c ∈ Finset.range 7, d3 R (7 * r + c) * d3 x c) % 5) (fun r => 3 * r) 7 := by
  unfold mv7K CFSG.KS.SporSch.LyK.placeF
  rw [foldN_eqP]
  congr 1
  funext r acc
  rw [foldN_eqP, foldr_sum (fun c => Nat.mul (d3 R (Nat.add (Nat.mul 7 r) c)) (d3 x c)) 7 0,
    Nat.zero_add]
  rfl

theorem d3_mv7K (R x : Nat) {r : Nat} (hr : r < 7) :
    d3 (mv7K R x) r = (∑ c ∈ Finset.range 7, d3 R (7 * r + c) * d3 x c) % 5 := by
  rw [d3_eq, mv7K_place]
  exact place_fld (w := 3) (by norm_num) (fun r _ => Nat.lt_of_lt_of_le (Nat.mod_lt _ (by norm_num))
    (by norm_num)) hr

theorem d3_mv7K_lt (R x : Nat) {r : Nat} (hr : r < 7) : d3 (mv7K R x) r < 5 := by
  rw [d3_mv7K R x hr]
  exact Nat.mod_lt _ (by norm_num)

theorem mv7_dec (R x : Nat) : mv7 (dec49B R) (dec7B x) = dec7B (mv7K R x) := by
  unfold mv7
  conv_rhs => unfold dec7B
  refine congrArg Array.ofFn (funext fun r => ?_)
  rw [d3_mv7K R x r.isLt, fold_sum]
  refine congrArg (· % 5) (Finset.sum_congr rfl fun c hc => ?_)
  have hc' := Finset.mem_range.1 hc
  rw [getD49 (by omega), getD7 hc']

theorem code7K_sum (x : Nat) : code7K x = ∑ r ∈ Finset.range 7, d3 x r * 5 ^ r := by
  unfold code7K
  rw [foldN_eqP, foldr_sum (fun r => Nat.mul (d3 x r) (Nat.pow 5 r)) 7 0, Nat.zero_add]
  rfl

theorem code7_dec (x : Nat) : code7 (dec7B x) = code7K x := by
  unfold code7
  rw [fold_sum, code7K_sum]
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [getD7 (Finset.mem_range.1 hr)]

theorem digits_lt : ∀ (n : Nat) (a : Nat → Nat), (∀ r < n, a r < 5) →
    ∑ r ∈ Finset.range n, a r * 5 ^ r < 5 ^ n
  | 0, _, _ => by simp
  | n + 1, a, h => by
    rw [Finset.sum_range_succ, Nat.pow_succ]
    have h1 := digits_lt n a fun r hr => h r (by omega)
    have h2 := h n (by omega)
    have : a n * 5 ^ n ≤ 4 * 5 ^ n := Nat.mul_le_mul_right _ (by omega)
    omega

theorem digits_inj : ∀ (n : Nat) (a b : Nat → Nat), (∀ r < n, a r < 5) → (∀ r < n, b r < 5) →
    ∑ r ∈ Finset.range n, a r * 5 ^ r = ∑ r ∈ Finset.range n, b r * 5 ^ r → ∀ r < n, a r = b r
  | 0, _, _, _, _, _ => fun r hr => absurd hr (Nat.not_lt_zero r)
  | n + 1, a, b, ha, hb, h => by
    rw [Finset.sum_range_succ', Finset.sum_range_succ'] at h
    have e1 : ∀ c : Nat → Nat, ∑ r ∈ Finset.range n, c (r + 1) * 5 ^ (r + 1) =
        5 * ∑ r ∈ Finset.range n, c (r + 1) * 5 ^ r := by
      intro c
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [Nat.pow_succ]
      ring
    rw [e1 a, e1 b, Nat.pow_zero, Nat.mul_one, Nat.mul_one] at h
    have ha0 := ha 0 (by omega)
    have hb0 := hb 0 (by omega)
    have h0 : a 0 = b 0 := by omega
    have hrest : ∑ r ∈ Finset.range n, a (r + 1) * 5 ^ r = ∑ r ∈ Finset.range n, b (r + 1) * 5 ^ r := by
      omega
    have ih := digits_inj n (fun r => a (r + 1)) (fun r => b (r + 1)) (fun r hr => ha _ (by omega))
      (fun r hr => hb _ (by omega)) hrest
    intro r hr
    rcases r with _ | r
    · exact h0
    · exact ih r (by omega)

theorem code7K_lt {x : Nat} (h : ∀ r < 7, d3 x r < 5) : code7K x < 78125 := by
  rw [code7K_sum]
  exact digits_lt 7 (d3 x) h

theorem dec7B_inj {x y : Nat} (hx : ∀ r < 7, d3 x r < 5) (hy : ∀ r < 7, d3 y r < 5)
    (h : code7K x = code7K y) : dec7B x = dec7B y := by
  rw [code7K_sum, code7K_sum] at h
  have := digits_inj 7 (d3 x) (d3 y) hx hy h
  unfold dec7B
  exact congrArg Array.ofFn (funext fun r => this r.val r.isLt)

theorem code7K_of_dec {x y : Nat} (h : dec7B x = dec7B y) : code7K x = code7K y := by
  rw [← code7_dec, ← code7_dec, h]

theorem allIn_iff' {lo hi : Nat} {p : Nat → Bool} :
    allIn lo hi p = true ↔ ∀ k, lo ≤ k → k < hi → p k = true := by
  unfold allIn
  rw [Nat.all_eq_finRange_all, List.all_eq_true]
  constructor
  · intro h k hk1 hk2
    have := h ⟨k - lo, by omega⟩ (List.mem_finRange _)
    simp only at this
    rwa [Nat.add_sub_cancel' hk1] at this
  · intro h i _
    exact h _ (Nat.le_add_right _ _) (by have := i.isLt; omega)

theorem index_fold {α : Type} [BEq α] [Hashable α] [LawfulBEq α] [Inhabited α] (pts : Array α) :
    ∀ n, (∀ a < n, ∀ b < n, pts[a]! = pts[b]! → a = b) →
      ∀ k < n, ((List.range n).foldl (fun m k => m.insert pts[k]! k) (∅ : Std.HashMap α Nat))[pts[k]!]? =
        some k
  | 0, _ => fun k hk => absurd hk (Nat.not_lt_zero k)
  | n + 1, hinj => by
    intro k hk
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      Std.HashMap.getElem?_insert]
    by_cases hkn : k = n
    · subst hkn
      rw [if_pos (beq_self_eq_true _)]
    · have hne : (pts[n]! == pts[k]!) = false := by
        rw [beq_eq_false_iff_ne]
        intro e
        exact hkn (hinj k hk n (by omega) e.symm)
      rw [hne]
      exact index_fold pts n (fun a ha b hb e => hinj a (by omega) b (by omega) e) k (by omega)

theorem index_getD {α : Type} [BEq α] [Hashable α] [LawfulBEq α] [Inhabited α] (pts : Array α) {n : Nat}
    (hinj : ∀ a < n, ∀ b < n, pts[a]! = pts[b]! → a = b) {k : Nat} (hk : k < n) :
    ((List.range n).foldl (fun m k => m.insert pts[k]! k) (∅ : Std.HashMap α Nat)).getD pts[k]! n = k := by
  rw [Std.HashMap.getD_eq_getD_getElem?, index_fold pts n hinj k hk]
  rfl

theorem hasBit_iff (M k : Nat) : hasBit M k = M.testBit k := by
  unfold hasBit
  change Nat.blt 0 (M &&& 1 <<< k) = _
  rw [Nat.shiftLeft_eq, Nat.one_mul]
  cases h : M.testBit k
  · have e : M &&& 2 ^ k = 0 := by
      apply Nat.eq_of_testBit_eq
      intro i
      rw [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit]
      by_cases hi : k = i
      · subst hi
        rw [h]
        rfl
      · simp [hi]
    rw [e]
    rfl
  · have e : (M &&& 2 ^ k).testBit k = true := by
      rw [Nat.testBit_and, Nat.testBit_two_pow, h]
      simp
    have hpos : 0 < M &&& 2 ^ k := by
      rcases Nat.eq_zero_or_pos (M &&& 2 ^ k) with h0 | h0
      · rw [h0, Nat.zero_testBit] at e
        exact absurd e (by decide)
      · exact h0
    exact Eq.mpr Nat.blt_eq hpos

theorem enc_cnt {cnt M : Nat} (h : cnt < 2 ^ 20) : Nat.land (cnt + 2 ^ 20 * M) 1048575 = cnt := by
  change (cnt + 2 ^ 20 * M) &&& (2 ^ 20 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h]

theorem enc_msk {cnt M : Nat} (h : cnt < 2 ^ 20) : Nat.shiftRight (cnt + 2 ^ 20 * M) 20 = M := by
  change (cnt + 2 ^ 20 * M) >>> 20 = _
  rw [Nat.shiftRight_eq_div_pow, Nat.add_mul_div_left _ _ (by norm_num), Nat.div_eq_of_lt h,
    Nat.zero_add]

theorem vStep_enc (GP E PL : Nat → Nat) (c h j cnt M : Nat) (hcnt : cnt < 2 ^ 20) :
    vStep GP E PL c h j (cnt + 2 ^ 20 * M) =
      if h < cnt then
        (if M.testBit (code7K (mv7K (GP j) (E h))) = true then cnt + 2 ^ 20 * M
         else if cnt < c ∧ E cnt = mv7K (GP j) (E h) ∧ PL cnt = h + 2 ^ 20 * j then
           (cnt + 1) + 2 ^ 20 * (M ||| 2 ^ code7K (mv7K (GP j) (E h)))
         else vFail)
      else cnt + 2 ^ 20 * M := by
  unfold vStep
  simp only [strictN_eqP, nIf_eqP, bAnd_eqP, enc_cnt hcnt, enc_msk hcnt, hasBit_iff,
    Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq]
  have e1 : Nat.shiftLeft j 20 = 2 ^ 20 * j := by
    change j <<< 20 = _
    rw [Nat.shiftLeft_eq, Nat.mul_comm]
  have e2 : Nat.shiftLeft 1 (code7K (mv7K (GP j) (E h))) = 2 ^ code7K (mv7K (GP j) (E h)) := by
    change 1 <<< _ = _
    rw [Nat.shiftLeft_eq, Nat.one_mul]
  have e3 : ∀ X : Nat, Nat.shiftLeft X 20 = 2 ^ 20 * X := fun X => by
    change X <<< 20 = _
    rw [Nat.shiftLeft_eq, Nat.mul_comm]
  rw [e1, e2, e3]
  rfl

theorem vFail_eq : vFail = 1048575 + 2 ^ 20 * 0 := rfl

theorem vStep_fail (GP E PL : Nat → Nat) {c : Nat} (hc : c ≤ 78125) (h j : Nat) :
    vStep GP E PL c h j vFail = vFail := by
  rw [vFail_eq, vStep_enc GP E PL c h j 1048575 0 (by norm_num)]
  simp only [Nat.zero_testBit, Bool.false_eq_true, ↓reduceIte]
  split_ifs with h1 h2
  · omega
  · rfl
  · rfl

theorem vStep_skip (GP E PL : Nat → Nat) (c h j st : Nat) (hh : Nat.land st 1048575 ≤ h) :
    vStep GP E PL c h j st = st := by
  unfold vStep
  rw [strictN_eqP, strictN_eqP, nIf_eqP, if_neg (by rw [Nat.blt_eq]; exact Nat.not_lt.2 hh)]

theorem fold_fix {α σ : Type} (f : α → σ → σ) (F : σ) (hB : ∀ x, f x F = F) :
    ∀ l : List α, l.foldl (fun s x => f x s) F = F
  | [] => rfl
  | x :: l => by rw [List.foldl_cons, hB, fold_fix f F hB l]

theorem range_splitG {σ : Type} (f : Nat → σ → σ) (s : σ) {a b : Nat} (hab : a ≤ b) :
    (List.range b).foldl (fun s x => f x s) s =
      (List.range' a (b - a)).foldl (fun s x => f x s) ((List.range a).foldl (fun s x => f x s) s) := by
  have e : b = a + (b - a) := by omega
  conv_lhs => rw [e, List.range_add, List.foldl_append]
  rw [List.range'_eq_map_range]

@[expose] def cO (st : Nat) : Nat := st % 2 ^ 20

@[expose] def mO (st : Nat) : Nat := st / 2 ^ 20

theorem st_dec (st : Nat) : st = cO st + 2 ^ 20 * mO st := (Nat.mod_add_div st (2 ^ 20)).symm

theorem cO_lt (st : Nat) : cO st < 2 ^ 20 := Nat.mod_lt _ (by norm_num)

theorem cO_enc {cnt M : Nat} (h : cnt < 2 ^ 20) : cO (cnt + 2 ^ 20 * M) = cnt := by
  unfold cO
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h]

theorem mO_enc {cnt M : Nat} (h : cnt < 2 ^ 20) : mO (cnt + 2 ^ 20 * M) = M := by
  unfold mO
  rw [Nat.add_mul_div_left _ _ (by norm_num), Nat.div_eq_of_lt h, Nat.zero_add]

theorem land_cO (st : Nat) : Nat.land st 1048575 = cO st := by
  change st &&& (2 ^ 20 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod]
  rfl

@[expose] def AV (kg c : Nat) (GP E PL : Nat → Nat) (st : Nat) : Prop :=
  1 ≤ cO st ∧ cO st ≤ c ∧
  (∀ k, (mO st).testBit k = true ↔ ∃ i < cO st, code7K (E i) = k) ∧
  (∀ i < cO st, ∀ r < 7, d3 (E i) r < 5) ∧
  (∀ i < cO st, 0 < i → Nat.land (PL i) 1048575 < i ∧ Nat.shiftRight (PL i) 20 < kg ∧
    E i = mv7K (GP (Nat.shiftRight (PL i) 20)) (E (Nat.land (PL i) 1048575))) ∧
  (∀ a < cO st, ∀ b < cO st, code7K (E a) = code7K (E b) → a = b)

@[expose] def NV (E PL : Nat → Nat) (st : Nat)
    (s : Array Bool × Array (Array Nat) × Array Nat × Array Nat) : Prop :=
  s.1.size = 78125 ∧ (∀ k < 78125, s.1[k]! = (mO st).testBit k) ∧
  s.2.1 = (Array.ofFn (n := cO st) fun i => dec7B (E i.val)) ∧
  s.2.2.1 = (Array.ofFn (n := cO st) fun i => Nat.land (PL i.val) 1048575) ∧
  s.2.2.2 = (Array.ofFn (n := cO st) fun i => Nat.shiftRight (PL i.val) 20)

theorem land_enc {h j : Nat} (hh : h < 2 ^ 20) : Nat.land (h + 2 ^ 20 * j) 1048575 = h := by
  rw [land_cO, cO_enc hh]

theorem shr_enc {h j : Nat} (hh : h < 2 ^ 20) : Nat.shiftRight (h + 2 ^ 20 * j) 20 = j := by
  change (h + 2 ^ 20 * j) >>> 20 = _
  rw [Nat.shiftRight_eq_div_pow]
  exact mO_enc hh

theorem set_get {k k' : Nat} {a : Array Bool} (hk : k < a.size) (hk' : k' < a.size) :
    (a.set! k true)[k']! = if k = k' then true else a[k']! := by
  rw [Array.set!_eq_setIfInBounds]
  rw [getElem!_pos _ k' (by simpa using hk'), getElem!_pos a k' hk', Array.getElem_setIfInBounds]

theorem vstep_sim {kg c : Nat} {GP E PL : Nat → Nat} {gens : Array (Array Nat)}
    (hg : gens.size = kg ∧ ∀ j < kg, gens[j]! = dec49B (GP j)) (hc : c ≤ 78125) {h j st : Nat}
    {s : Array Bool × Array (Array Nat) × Array Nat × Array Nat} (hj : j < kg)
    (hav : AV kg c GP E PL st) (hnv : NV E PL st s) (hh : h < cO st)
    (hnf : vStep GP E PL c h j st ≠ vFail) :
    AV kg c GP E PL (vStep GP E PL c h j st) ∧ cO st ≤ cO (vStep GP E PL c h j st) ∧
      NV E PL (vStep GP E PL c h j st)
        (if (!s.1[code7 (mv7 gens[j]! (dec7B (E h)))]!) = true then
          (s.1.set! (code7 (mv7 gens[j]! (dec7B (E h)))) true, s.2.1.push (mv7 gens[j]! (dec7B (E h))),
            s.2.2.1.push h, s.2.2.2.push j)
        else (s.1, s.2.1, s.2.2.1, s.2.2.2)) := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hav
  obtain ⟨n1, n2, n3, n4, n5⟩ := hnv
  have hcnt := cO_lt st
  set cnt := cO st with hcntdef
  set M := mO st with hMdef
  have hst : st = cnt + 2 ^ 20 * M := st_dec st
  have hEh : ∀ r < 7, d3 (E h) r < 5 := a4 h hh
  set Y := mv7K (GP j) (E h) with hY
  have hYd : ∀ r < 7, d3 Y r < 5 := fun r hr => d3_mv7K_lt _ _ hr
  have hy : mv7 gens[j]! (dec7B (E h)) = dec7B Y := by rw [hg.2 j hj, mv7_dec]
  have hk : code7 (mv7 gens[j]! (dec7B (E h))) = code7K Y := by rw [hy, code7_dec]
  have hk5 : code7K Y < 78125 := code7K_lt hYd
  rw [hy, code7_dec]
  have hseen : s.1[code7K Y]! = M.testBit (code7K Y) := n2 _ hk5
  rw [hst, vStep_enc GP E PL c h j cnt M hcnt, if_pos hh] at hnf ⊢
  by_cases hb : M.testBit (code7K Y) = true
  · rw [if_pos hb, hseen, hb]
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [← hst]
    exact ⟨⟨a1, a2, a3, a4, a5, a6⟩, le_rfl, n1, n2, n3, n4, n5⟩
  · rw [if_neg hb] at hnf ⊢
    by_cases hn : cnt < c ∧ E cnt = Y ∧ PL cnt = h + 2 ^ 20 * j
    · rw [if_pos hn]
      have hb' : M.testBit (code7K Y) = false := by simpa using hb
      rw [hseen, hb']
      simp only [Bool.not_false, ↓reduceIte]
      obtain ⟨hn1, hn2, hn3⟩ := hn
      have hc1 : cnt + 1 < 2 ^ 20 := by omega
      have hh20 : h < 2 ^ 20 := by omega
      rw [← hY]
      unfold AV NV
      rw [cO_enc hc1, mO_enc hc1]
      refine ⟨⟨by omega, hn1, fun k => ?_, fun i hi r hr => ?_, fun i hi hi0 => ?_, fun a ha b hb2 e => ?_⟩,
        by omega, ?_, fun k hk' => ?_, ?_, ?_, ?_⟩
      · rw [Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true, a3, decide_eq_true_eq]
        constructor
        · rintro (⟨i, hi, e⟩ | e)
          · exact ⟨i, by omega, e⟩
          · exact ⟨cnt, by omega, by rw [hn2, e]⟩
        · rintro ⟨i, hi, e⟩
          rcases Nat.lt_or_ge i cnt with h' | h'
          · exact Or.inl ⟨i, h', e⟩
          · have : i = cnt := by omega
            subst this
            exact Or.inr (by rw [← e, hn2])
      · rcases Nat.lt_or_ge i cnt with h' | h'
        · exact a4 i h' r hr
        · have : i = cnt := by omega
          subst this
          rw [hn2]
          exact hYd r hr
      · rcases Nat.lt_or_ge i cnt with h' | h'
        · exact a5 i h' hi0
        · have : i = cnt := by omega
          subst this
          rw [hn3, land_enc hh20, shr_enc hh20, hn2]
          exact ⟨hh, hj, rfl⟩
      · have hnew : ∀ i < cnt, code7K (E i) ≠ code7K Y := fun i hi e =>
          hb ((a3 _).2 ⟨i, hi, e⟩)
        rcases Nat.lt_or_ge a cnt with ha' | ha'
        · rcases Nat.lt_or_ge b cnt with hb' | hb'
          · exact a6 a ha' b hb' e
          · have : b = cnt := by omega
            subst this
            rw [hn2] at e
            exact absurd e (hnew a ha')
        · have : a = cnt := by omega
          subst this
          rcases Nat.lt_or_ge b cnt with hb' | hb'
          · rw [hn2] at e
            exact absurd e.symm (hnew b hb')
          · omega
      · change (s.1.set! (code7K Y) true).size = 78125
        rw [Array.size_set!, n1]
      · change (s.1.set! (code7K Y) true)[k]! = _
        rw [set_get (by rw [n1]; exact hk5) (by rw [n1]; exact hk'), Nat.testBit_or,
          Nat.testBit_two_pow, n2 k hk']
        by_cases e : code7K Y = k
        · rw [if_pos e, e]
          simp
        · rw [if_neg e]
          simp [e]
      · change s.2.1.push (dec7B Y) = _
        rw [n3, ← hn2]
        exact ofFn_push (fun i => dec7B (E i)) cnt
      · change s.2.2.1.push h = _
        have : h = Nat.land (PL cnt) 1048575 := by rw [hn3, land_enc hh20]
        rw [n4, this]
        exact ofFn_push (fun i => Nat.land (PL i) 1048575) cnt
      · change s.2.2.2.push j = _
        have : j = Nat.shiftRight (PL cnt) 20 := by rw [hn3, shr_enc hh20]
        rw [n5, this]
        exact ofFn_push (fun i => Nat.shiftRight (PL i) 20) cnt
    · rw [if_neg hn] at hnf
      exact absurd rfl hnf

theorem foldl_skip (f : Nat → Nat → Nat) (hskip : ∀ h st, cO st ≤ h → f h st = st) :
    ∀ (l : List Nat) (st : Nat), (∀ x ∈ l, cO st ≤ x) → l.foldl (fun st h => f h st) st = st
  | [], _, _ => rfl
  | x :: l, st, hl => by
    rw [List.foldl_cons, hskip _ _ (hl x List.mem_cons_self)]
    exact foldl_skip f hskip l st fun y hy => hl y (List.mem_cons_of_mem _ hy)

theorem vStep_mono (GP E PL : Nat → Nat) {c : Nat} (hc : c ≤ 78125) (h j st : Nat) :
    cO st ≤ cO (vStep GP E PL c h j st) := by
  have hcnt := cO_lt st
  conv_rhs => rw [st_dec st]
  rw [vStep_enc GP E PL c h j _ _ hcnt]
  split_ifs with h1 h2 h3
  · rw [← st_dec]
  · rw [cO_enc (by omega)]
    omega
  · rw [vFail_eq, cO_enc (by norm_num)]
    omega
  · rw [← st_dec]

theorem fold_mono (f : Nat → Nat → Nat) (hm : ∀ x st, cO st ≤ cO (f x st)) :
    ∀ (l : List Nat) (st : Nat), cO st ≤ cO (l.foldl (fun st x => f x st) st)
  | [], _ => le_rfl
  | x :: l, st => by
    rw [List.foldl_cons]
    exact Nat.le_trans (hm x st) (fold_mono f hm l _)

theorem vRun_eq (GP E PL : Nat → Nat) (kg c h₀ len st : Nat) :
    vRun GP E PL kg c h₀ len st = (List.range len).foldl (fun st i =>
      (List.range kg).foldl (fun st j => vStep GP E PL c (h₀ + i) j st) st) st := by
  unfold vRun
  rw [foldUp_eqP]
  congr 1
  funext st i
  rw [foldUp_eqP]
  rfl

theorem vbfs_soundL {kg c nS Hh : Nat} {GP E PL C : Nat → Nat} {root : Array Nat}
    {gens : Array (Array Nat)} (hg : gens.size = kg ∧ ∀ j < kg, gens[j]! = dec49B (GP j))
    (hroot : root = dec7B (E 0)) (hE0 : ∀ r < 7, d3 (E 0) r < 5) (hPL0 : PL 0 = 0)
    (hc : c ≤ 78125) (hcov : c ≤ nS * Hh)
    (hC0 : C 0 = 1 + 2 ^ 20 * 2 ^ code7K (E 0))
    (hrun : ∀ q < nS, vRun GP E PL kg c (q * Hh) Hh (C q) = C (q + 1))
    (hCn : Nat.land (C nS) 1048575 = c) :
    vecBFS root gens = (Array.ofFn (n := c) fun i => dec7B (E i.val),
        Array.ofFn (n := c) fun i => Nat.land (PL i.val) 1048575,
        Array.ofFn (n := c) fun i => Nat.shiftRight (PL i.val) 20) ∧
      vecTreeOK root gens (Array.ofFn (n := c) fun i => dec7B (E i.val),
        Array.ofFn (n := c) fun i => Nat.land (PL i.val) 1048575,
        Array.ofFn (n := c) fun i => Nat.shiftRight (PL i.val) 20) = true := by
  let sV := fun h st => (List.range kg).foldl (fun st j => vStep GP E PL c h j st) st
  let stG := fun t => (List.range t).foldl (fun st h => sV h st) (C 0)
  have hGs : ∀ t, stG (t + 1) = sV t (stG t) := by
    intro t
    change (List.range (t + 1)).foldl _ _ = _
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hCq : ∀ q ≤ nS, C q = stG (q * Hh) := by
    intro q
    induction q with
    | zero => intro _; rw [Nat.zero_mul]; rfl
    | succ q ih =>
      intro hq
      rw [← hrun q (by omega), vRun_eq, ih (by omega)]
      have e := range_splitG (fun h st => sV h st) (C 0) (a := q * Hh) (b := (q + 1) * Hh)
        (Nat.mul_le_mul_right Hh (Nat.le_succ q))
      have e2 : (q + 1) * Hh - q * Hh = Hh := by rw [Nat.succ_mul]; omega
      rw [e2, List.range'_eq_map_range, List.foldl_map] at e
      exact e.symm
  set N := nS * Hh with hN
  have hGN : cO (stG N) = c := by
    rw [← hCq nS le_rfl, ← land_cO, hCn]
  have hskip1 : ∀ h st, cO st ≤ h → sV h st = st := by
    intro h st hh
    change (List.range kg).foldl _ st = st
    generalize List.range kg = l
    induction l with
    | nil => rfl
    | cons j l ih => rw [List.foldl_cons, vStep_skip GP E PL c h j st (by rw [land_cO]; exact hh), ih]
  have hskipN : ∀ t, stG (N + t) = stG N := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih =>
      rw [← Nat.add_assoc, hGs, ih]
      exact hskip1 _ _ (by omega)
  have hfixV : ∀ h, sV h vFail = vFail := fun h => fold_fix (fun j st => vStep GP E PL c h j st) vFail
    (fun j => vStep_fail GP E PL hc h j) _
  have hFne : cO vFail ≠ c := by
    rw [vFail_eq, cO_enc (by norm_num)]
    omega
  have hnf : ∀ t, stG t ≠ vFail := by
    intro t ht
    have e : stG (N + t) = (List.range' t N).foldl (fun s x => sV x s) (stG t) := by
      have := range_splitG (fun h st => sV h st) (C 0) (a := t) (b := N + t) (by omega)
      rw [Nat.add_sub_cancel] at this
      exact this
    rw [hskipN, ht, fold_fix _ _ hfixV] at e
    exact hFne (e ▸ hGN)
  let sI := fun h j => (List.range j).foldl (fun st j => vStep GP E PL c h j st) (stG h)
  have hIs : ∀ h j, sI h (j + 1) = vStep GP E PL c h j (sI h j) := by
    intro h j
    change (List.range (j + 1)).foldl _ _ = _
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hInf : ∀ h, ∀ j ≤ kg, sI h j ≠ vFail := by
    intro h j hj hf
    have e := range_splitG (fun j st => vStep GP E PL c h j st) (stG h) hj
    change sV h (stG h) = _ at e
    rw [← hGs] at e
    change _ = (List.range' j (kg - j)).foldl _ (sI h j) at e
    rw [hf, fold_fix _ _ (fun j => vStep_fail GP E PL hc h j)] at e
    exact hnf _ e
  have hIk : ∀ h, sI h kg = stG (h + 1) := fun h => (hGs h).symm
  let R := fun t s => AV kg c GP E PL (stG t) ∧ NV E PL (stG t) s
  have hc0 : cO (C 0) = 1 := by
    rw [hC0, cO_enc (by norm_num)]
  have hm0 : mO (C 0) = 2 ^ code7K (E 0) := by
    rw [hC0, mO_enc (by norm_num)]
  have hk0 : code7K (E 0) < 78125 := code7K_lt hE0
  have hc1 : 1 ≤ c := by
    have := fold_mono (fun h st => sV h st) (fun h st => fold_mono
      (fun j st => vStep GP E PL c h j st) (fun j st => vStep_mono GP E PL hc h j st) (List.range kg) st)
      (List.range N) (C 0)
    change cO (C 0) ≤ cO (stG N) at this
    rw [hc0, hGN] at this
    exact this
  have hex : ∃ s, vecBFS root gens = (s.2.1, s.2.2.1, s.2.2.2) ∧ R 78125 s := by
    unfold vecBFS
    refine ⟨_, rfl, forIn_range_spec (fun t s => R t s) 78125 _ _ ?_ ?_⟩
    ·
      change AV kg c GP E PL (C 0) ∧ NV E PL (C 0) _
      unfold AV NV
      rw [hc0, hm0]
      refine ⟨⟨Nat.le_refl 1, by omega, fun k => ?_, fun i hi => ?_, fun i hi hi0 => by omega,
        fun a ha b hb _ => by omega⟩, ?_, fun k hk => ?_, ?_, ?_, ?_⟩
      · rw [Nat.testBit_two_pow, decide_eq_true_eq]
        constructor
        · rintro rfl
          exact ⟨0, by omega, rfl⟩
        · rintro ⟨i, hi, rfl⟩
          have : i = 0 := by omega
          rw [this]
      · have : i = 0 := by omega
        rw [this]
        exact hE0
      · simp
      · dsimp only
        have hsz : (Array.replicate 78125 false).size = 78125 := Array.size_replicate
        rw [hroot, code7_dec, set_get (by rw [hsz]; exact hk0) (by rw [hsz]; exact hk),
          Nat.testBit_two_pow]
        by_cases e : code7K (E 0) = k
        · rw [if_pos e, decide_eq_true e]
        · rw [if_neg e, getElem!_pos _ k (by rw [hsz]; exact hk), Array.getElem_replicate,
            decide_eq_false e]
      · change #[root] = _
        rw [hroot]
        rfl
      · apply Array.ext
        · simp
        · intro i h1 h2
          have : i = 0 := by simpa using h1
          subst this
          simp [hPL0]
      · apply Array.ext
        · simp
        · intro i h1 h2
          have : i = 0 := by simpa using h1
          subst this
          simp [hPL0]
    ·
      intro h b hh hb
      obtain ⟨hav, hnv⟩ := hb
      have hsz : b.2.1.size = cO (stG h) := by rw [hnv.2.2.1]; simp
      dsimp only
      split
      · rename_i hlt
        rw [hsz] at hlt
        refine ⟨_, rfl, ?_⟩
        have hx : b.2.1[h]! = dec7B (E h) := by rw [hnv.2.2.1]; exact ofFn_getP (fun i => dec7B (E i)) hlt
        have hfin : ∀ s, (AV kg c GP E PL (sI h gens.size) ∧ NV E PL (sI h gens.size) s ∧
            cO (stG h) ≤ cO (sI h gens.size)) → R (h + 1) (s.1, s.2.1, s.2.2.1, s.2.2.2) := by
          intro s hs
          rw [hg.1, hIk h] at hs
          exact ⟨hs.1, hs.2.1⟩
        refine hfin _ (forIn_range_spec (fun j s => AV kg c GP E PL (sI h j) ∧ NV E PL (sI h j) s ∧
          cO (stG h) ≤ cO (sI h j)) gens.size _ _ ⟨hav, hnv, le_rfl⟩ ?_)
        intro j s hj hs
        rw [hg.1] at hj
        obtain ⟨hs1, hs2, hs3⟩ := hs
        refine ⟨_, (apply_ite (fun z => (pure (ForInStep.yield z) : Id _)) _ _ _).symm, ?_⟩
        have hsim := vstep_sim hg hc hj hs1 hs2 (Nat.lt_of_lt_of_le hlt hs3)
          (by rw [← hIs]; exact hInf h (j + 1) (by omega))
        rw [← hIs] at hsim
        rw [hx]
        exact ⟨hsim.1, hsim.2.2, Nat.le_trans hs3 hsim.2.1⟩
      · rename_i hge
        rw [hsz] at hge
        refine ⟨_, rfl, ?_⟩
        change R (h + 1) b
        have e : stG (h + 1) = stG h := by rw [hGs]; exact hskip1 _ _ (by omega)
        change AV kg c GP E PL (stG (h + 1)) ∧ NV E PL (stG (h + 1)) b
        rw [e]
        exact ⟨hav, hnv⟩
  obtain ⟨s, hs, hav, hnv⟩ := hex
  have hG78 : stG 78125 = stG N := by
    rcases Nat.le_total N 78125 with h1 | h1
    · have := hskipN (78125 - N)
      rw [Nat.add_sub_cancel' h1] at this
      exact this
    · have e : stG N = (List.range' 78125 (N - 78125)).foldl (fun s x => sV x s) (stG 78125) :=
        range_splitG (fun h st => sV h st) (C 0) h1
      rw [e]
      refine (foldl_skip sV hskip1 _ _ fun x hx => ?_).symm
      have := List.mem_range'.1 hx
      have := hav.2.1
      omega
  have hcF : cO (stG 78125) = c := by rw [hG78, hGN]
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hav
  obtain ⟨n1, n2, n3, n4, n5⟩ := hnv
  rw [hcF] at a1 a4 a5 a6 n3 n4 n5
  refine ⟨by rw [hs, n3, n4, n5], ?_⟩
  unfold vecTreeOK
  dsimp only
  simp only [Bool.and_eq_true]
  have hpts : ∀ k < c, (Array.ofFn (n := c) fun i => dec7B (E i.val))[k]! = dec7B (E k) :=
    fun k hk => ofFn_getP (fun i => dec7B (E i)) hk
  refine ⟨⟨⟨⟨⟨by simp, by simp⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [hpts 0 (by omega), hroot]
    exact beq_self_eq_true _
  · rw [Array.all_eq_true]
    intro i hi
    rw [Array.size_ofFn] at hi
    rw [Array.getElem_ofFn]
    simp only [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true]
    refine ⟨by simp [dec7B], fun r hr => ?_⟩
    have hr' : r < 7 := by simpa [dec7B] using hr
    rw [← getElem!_pos _ r hr, getD7 hr']
    exact decide_eq_true (a4 i hi r hr')
  · rw [allIn_iff']
    intro k hk1 hk2
    rw [Array.size_ofFn] at hk2
    have hpar := ofFn_getP (fun i => Nat.land (PL i) 1048575) hk2
    have hlab := ofFn_getP (fun i => Nat.shiftRight (PL i) 20) hk2
    obtain ⟨t1, t2, t3⟩ := a5 k hk2 (by omega)
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    rw [hpar, hlab, hg.1]
    refine ⟨⟨t1, t2⟩, ?_⟩
    rw [hg.2 _ t2, hpts _ (by omega), mv7_dec, hpts k hk2, ← t3]
  · rw [allIn_iff']
    intro k _ hk2
    rw [beq_iff_eq]
    rw [Array.size_ofFn] at hk2 ⊢
    refine index_getD _ (fun a ha b hb e => ?_) hk2
    rw [hpts a ha, hpts b hb] at e
    exact a6 a ha b hb (code7K_of_dec e)

end CFSG.KS.SporSch.LySvB

end
