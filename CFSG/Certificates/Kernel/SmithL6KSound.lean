module

public import Certificates.Data.Kernel.SmithL6K
public import CFSG.Certificates.Kernel.SmithL6RankSound

public section

namespace CFSG.SmithL6.K

open CFSG.SmithL6 CFSG.SmithL6.Kernel
open CFSG.SmithE (tri applyCols)

theorem foldl_xor_false (g : Nat → Bool) (l : List Nat) (c : Bool) :
    l.foldl (fun b i => b ^^ g i) c = (c ^^ l.foldl (fun b i => b ^^ g i) false) := by
  induction l generalizing c with
  | nil => simp
  | cons i l ih =>
    simp only [List.foldl_cons]
    rw [ih, ih (false ^^ g i)]
    cases c <;> cases g i <;> simp

theorem foldl_xor_split (f g : Nat → Bool) (l : List Nat) (c : Bool) :
    l.foldl (fun b i => b ^^ (f i ^^ g i)) c =
      (l.foldl (fun b i => b ^^ f i) c ^^ l.foldl (fun b i => b ^^ g i) false) := by
  induction l generalizing c with
  | nil => simp
  | cons i l ih =>
    simp only [List.foldl_cons]
    rw [ih, foldl_xor_false f l (c ^^ (f i ^^ g i)), foldl_xor_false f l (c ^^ f i),
      foldl_xor_false g l (false ^^ g i)]
    cases c <;> cases f i <;> cases g i <;>
      simp [Bool.xor_assoc, Bool.xor_comm, Bool.xor_left_comm]

theorem eq_of_xor_eq_zero {a b : Nat} (h : a ^^^ b = 0) : a = b := by
  have e := congrArg (· ^^^ b) h
  simp only [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero, Nat.zero_xor] at e
  exact e

theorem par_xor (a b : Nat) : par (a ^^^ b) = (par a ^^ par b) := by
  unfold par
  simp only [Nat.testBit_xor]
  exact foldl_xor_split _ _ _ false

theorem form_xor_left (φ ψ x : Nat) : form (φ ^^^ ψ) x = (form φ x ^^ form ψ x) := by
  unfold form
  rw [← par_xor, Nat.and_xor_distrib_right]

theorem form_xor_right (φ x y : Nat) : form φ (x ^^^ y) = (form φ x ^^ form φ y) := by
  unfold form
  rw [← par_xor, Nat.and_xor_distrib_left]

@[expose] def TvP (p : Nat × Nat) : Prop :=
  p.1 < 64 ∧ p.2 < 64 ∧ p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ form p.2 p.1 = false

@[expose] def conjP (p q : Nat × Nat) : Nat × Nat :=
  (if form p.2 q.1 then q.1 ^^^ p.1 else q.1, if form q.2 p.1 then q.2 ^^^ p.2 else q.2)

theorem xor_lt64 {a b : Nat} (ha : a < 64) (hb : b < 64) : a ^^^ b < 64 :=
  Nat.xor_lt_two_pow (n := 6) ha hb

theorem conjP_tvP {p q : Nat × Nat} (hp : TvP p) (hq : TvP q) : TvP (conjP p q) := by
  obtain ⟨w, ψ⟩ := p
  obtain ⟨v, φ⟩ := q
  obtain ⟨hw, hψ, hw0, hψ0, hψw⟩ := hp
  obtain ⟨hv, hφ, hv0, hφ0, hφv⟩ := hq
  simp only at hw hψ hw0 hψ0 hψw hv hφ hv0 hφ0 hφv
  unfold conjP TvP
  simp only
  cases h1 : form ψ v <;> cases h2 : form φ w <;>
    simp only [Bool.false_eq_true, ↓reduceIte, if_true]
  · exact ⟨hv, hφ, hv0, hφ0, hφv⟩
  · refine ⟨hv, xor_lt64 hφ hψ, hv0, fun h => ?_, ?_⟩
    · rw [eq_of_xor_eq_zero h, hψw] at h2
      exact Bool.false_ne_true h2
    · rw [form_xor_left, hφv, h1]
      rfl
  · refine ⟨xor_lt64 hv hw, hφ, fun h => ?_, hφ0, ?_⟩
    · rw [eq_of_xor_eq_zero h, hψw] at h1
      exact Bool.false_ne_true h1
    · rw [form_xor_right, hφv, h2]
      rfl
  · refine ⟨xor_lt64 hv hw, xor_lt64 hφ hψ, fun h => ?_, fun h => ?_, ?_⟩
    · rw [eq_of_xor_eq_zero h, hψw] at h1
      exact Bool.false_ne_true h1
    · rw [eq_of_xor_eq_zero h, hψw] at h2
      exact Bool.false_ne_true h2
    · rw [form_xor_left, form_xor_right, form_xor_right, hφv, h1, h2, hψw]
      rfl

theorem conjP_conjP {p q : Nat × Nat} (hp : TvP p) : conjP p (conjP p q) = q := by
  obtain ⟨w, ψ⟩ := p
  obtain ⟨v, φ⟩ := q
  obtain ⟨-, -, -, -, hψw⟩ := hp
  simp only at hψw
  unfold conjP
  simp only
  cases h1 : form ψ v <;> cases h2 : form φ w <;>
    simp only [Bool.false_eq_true, ↓reduceIte, if_true, h1, h2, form_xor_left, form_xor_right,
      hψw, Bool.xor_false, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

@[expose] def lastIdx (f : Nat → Nat) (x d : Nat) : Nat → Nat
  | 0 => d
  | N + 1 => if f N = x then N else lastIdx f x d N

theorem foldl_set_size (f : Nat → Nat) (M d N : Nat) :
    ((List.range N).foldl (fun A j => A.set! (f j) j) (Array.replicate M d)).size = M := by
  induction N with
  | zero => simp
  | succ N ih => rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      Array.set!_eq_setIfInBounds, Array.size_setIfInBounds, ih]

theorem foldl_set_get (f : Nat → Nat) (M d N x : Nat) (hx : x < M) :
    ((List.range N).foldl (fun A j => A.set! (f j) j) (Array.replicate M d))[x]! =
      lastIdx f x d N := by
  induction N with
  | zero =>
    simp only [List.range_zero, List.foldl_nil, lastIdx]
    rw [getElem!_pos _ x (by simpa using hx), Array.getElem_replicate]
  | succ N ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      Array.set!_eq_setIfInBounds]
    have hs := foldl_set_size f M d N
    rw [getElem!_pos _ x (by rw [Array.size_setIfInBounds, hs]; exact hx),
      Array.getElem_setIfInBounds (by rw [hs]; exact hx), lastIdx]
    by_cases h : f N = x
    · simp [h]
    · rw [if_neg h, if_neg h, ← ih, getElem!_pos _ x (by rw [hs]; exact hx)]

theorem lastIdx_none {f : Nat → Nat} {x d N : Nat} (h : ∀ j < N, f j ≠ x) : lastIdx f x d N = d := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [lastIdx, if_neg (h N (Nat.lt_succ_self N))]
    exact ih fun j hj => h j (by omega)

theorem lastIdx_last {f : Nat → Nat} {x d N j : Nat} (hj : j < N) (hf : f j = x)
    (hl : ∀ j', j < j' → j' < N → f j' ≠ x) : lastIdx f x d N = j := by
  induction N with
  | zero => omega
  | succ N ih =>
    rw [lastIdx]
    by_cases hN : j = N
    · subst hN
      rw [if_pos hf]
    · rw [if_neg (hl N (by omega) (Nat.lt_succ_self N))]
      exact ih (by omega) fun j' h1 h2 => hl j' h1 (by omega)

theorem foldl_set_none {f : Nat → Nat} {M d N x : Nat} (hx : x < M) (h : ∀ j < N, f j ≠ x) :
    ((List.range N).foldl (fun A j => A.set! (f j) j) (Array.replicate M d))[x]! = d := by
  rw [foldl_set_get f M d N x hx, lastIdx_none h]

theorem foldl_set_last {f : Nat → Nat} {M d N x j : Nat} (hx : x < M) (hj : j < N) (hf : f j = x)
    (hl : ∀ j', j < j' → j' < N → f j' ≠ x) :
    ((List.range N).foldl (fun A j => A.set! (f j) j) (Array.replicate M d))[x]! = j := by
  rw [foldl_set_get f M d N x hx, lastIdx_last hj hf hl]

theorem tvList_toList : tvList.toList = (List.range 4096).filterMap fun n =>
    if n / 64 ≠ 0 ∧ n % 64 ≠ 0 ∧ form (n % 64) (n / 64) = false then some (n / 64, n % 64)
    else none := by
  unfold tvList
  rw [List.toList_toArray]

theorem tvP_of_mem {p : Nat × Nat} (h : p ∈ tvList.toList) : TvP p := by
  rw [tvList_toList, List.mem_filterMap] at h
  obtain ⟨n, hn, he⟩ := h
  have hn' := List.mem_range.mp hn
  split at he
  · rename_i hc
    cases he
    exact ⟨by omega, Nat.mod_lt _ (by omega), hc.1, hc.2.1, hc.2.2⟩
  · cases he

theorem codeOf_lt {p : Nat × Nat} (hp : TvP p) : codeOf p < 4096 := by
  unfold codeOf
  have := hp.1
  have := hp.2.1
  omega

theorem codeOf_div {p : Nat × Nat} (hp : TvP p) : codeOf p / 64 = p.1 := by
  unfold codeOf
  have := hp.2.1
  omega

theorem codeOf_mod {p : Nat × Nat} (hp : TvP p) : codeOf p % 64 = p.2 := by
  unfold codeOf
  have := hp.2.1
  omega

theorem mem_of_tvP {p : Nat × Nat} (hp : TvP p) : p ∈ tvList.toList := by
  rw [tvList_toList, List.mem_filterMap]
  refine ⟨codeOf p, List.mem_range.mpr (codeOf_lt hp), ?_⟩
  rw [codeOf_div hp, codeOf_mod hp, if_pos ⟨hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2⟩]

theorem tvList_codes_sorted : (tvList.toList.map codeOf).Pairwise (· < ·) := by
  rw [tvList_toList, List.map_filterMap]
  refine List.Pairwise.filterMap _ ?_ (List.pairwise_lt_range (n := 4096))
  intro a a' haa' b hb b' hb'
  simp only [Option.map_eq_some_iff] at hb hb'
  obtain ⟨p, hp, rfl⟩ := hb
  obtain ⟨p', hp', rfl⟩ := hb'
  split at hp
  · split at hp'
    · cases hp
      cases hp'
      unfold codeOf
      simp only
      omega
    · cases hp'
  · cases hp

theorem tvPair_get {k : Nat} (hk : k < 1953) :
    tvPair k = tvList.toList[k]'(by rw [Array.length_toList, tvList_size]; exact hk) := by
  unfold tvPair
  rw [getElem!_pos tvList k (by rw [tvList_size]; exact hk), Array.getElem_toList]

theorem tvP_tvPair {k : Nat} (hk : k < 1953) : TvP (tvPair k) := by
  rw [tvPair_get hk]
  exact tvP_of_mem (List.getElem_mem _)

theorem tvPair_surj {p : Nat × Nat} (hp : TvP p) : ∃ k < 1953, tvPair k = p := by
  obtain ⟨k, hk, he⟩ := List.getElem_of_mem (mem_of_tvP hp)
  have hk' : k < 1953 := by rw [Array.length_toList, tvList_size] at hk; exact hk
  exact ⟨k, hk', by rw [tvPair_get hk']; exact he⟩

theorem codeOf_tvPair_lt {j k : Nat} (hjk : j < k) (hk : k < 1953) :
    codeOf (tvPair j) < codeOf (tvPair k) := by
  have hl : (tvList.toList.map codeOf).length = 1953 := by
    rw [List.length_map, Array.length_toList, tvList_size]
  have h := List.pairwise_iff_getElem.mp tvList_codes_sorted j k (by omega) (by omega) hjk
  simp only [List.getElem_map] at h
  rw [tvPair_get (by omega), tvPair_get hk]
  exact h

theorem codeOf_tvPair_inj {j k : Nat} (hj : j < 1953) (hk : k < 1953)
    (h : codeOf (tvPair j) = codeOf (tvPair k)) : j = k := by
  rcases Nat.lt_trichotomy j k with hjk | hjk | hjk
  · exact absurd h (Nat.ne_of_lt (codeOf_tvPair_lt hjk hk))
  · exact hjk
  · exact absurd h.symm (Nat.ne_of_lt (codeOf_tvPair_lt hjk hj))

theorem tvIdxTab_eq : tvIdxTab =
    (List.range 1953).foldl (fun A j => A.set! ((fun k => codeOf (tvPair k)) j) j)
      (Array.replicate 4096 1953) := rfl

theorem tvIdxTab_code {k : Nat} (hk : k < 1953) : tvIdxTab[codeOf (tvPair k)]! = k := by
  rw [tvIdxTab_eq]
  exact foldl_set_last (codeOf_lt (tvP_tvPair hk)) hk rfl fun j' h1 h2 h =>
    absurd (codeOf_tvPair_inj h2 hk h) (by omega)

theorem tvIdxTab_none {n : Nat} (hn : n < 4096) (h : ∀ k < 1953, codeOf (tvPair k) ≠ n) :
    tvIdxTab[n]! = 1953 := by
  rw [tvIdxTab_eq]
  exact foldl_set_none hn h

theorem tvImg_eq (j a : Nat) : tvImg j a = tvIdxTab[codeOf (conjP (tvPair j) (tvPair a))]! := rfl

theorem tvPair_tvImg_aux {j a : Nat} (hj : j < 1953) (ha : a < 1953) :
    tvImg j a < 1953 ∧ tvPair (tvImg j a) = conjP (tvPair j) (tvPair a) := by
  obtain ⟨k, hk, he⟩ := tvPair_surj (conjP_tvP (tvP_tvPair hj) (tvP_tvPair ha))
  rw [tvImg_eq, ← he, tvIdxTab_code hk]
  exact ⟨hk, rfl⟩

theorem tvImg_lt {j a : Nat} (hj : j < 1953) (ha : a < 1953) : tvImg j a < 1953 :=
  (tvPair_tvImg_aux hj ha).1

theorem tvPair_tvImg {j a : Nat} (hj : j < 1953) (ha : a < 1953) :
    tvPair (tvImg j a) = conjP (tvPair j) (tvPair a) :=
  (tvPair_tvImg_aux hj ha).2

theorem tvImg_tvImg {j a : Nat} (hj : j < 1953) (ha : a < 1953) : tvImg j (tvImg j a) = a := by
  rw [tvImg_eq, tvPair_tvImg hj ha, conjP_conjP (tvP_tvPair hj), tvIdxTab_code ha]

theorem tvTab_get {j a : Nat} (hj : j < 1953) (ha : a < 1953) : tvTab[j]![a]! = tvImg j a := by
  unfold tvTab
  rw [ofFn_get! _ hj]
  exact ofFn_get! (fun a : Fin 1953 => tvImg j a.val) ha

theorem conjC_codeOf {p q : Nat × Nat} (hp : TvP p) (hq : TvP q) :
    conjC (codeOf p) (codeOf q) = codeOf (conjP p q) := by
  unfold conjC
  rw [codeOf_div hp, codeOf_mod hp, codeOf_div hq, codeOf_mod hq]
  rfl

theorem tvImgP_eq {C I : Nat} (hC : ∀ k < 1953, fldW 12 C k = codeOf (tvPair k))
    (hI : ∀ n < 4096, fldW 11 I n = tvIdxTab[n]!) {j a : Nat} (hj : j < 1953) (ha : a < 1953) :
    tvImgP C I j a = tvImg j a := by
  have hpj := tvP_tvPair hj
  have hpa := tvP_tvPair ha
  unfold tvImgP
  rw [hC j hj, hC a ha, conjC_codeOf hpj hpa, hI _ (codeOf_lt (conjP_tvP hpj hpa)), tvImg_eq]

theorem idx_of_pinIdx {C I : Nat} (hC : ∀ k < 1953, fldW 12 C k = codeOf (tvPair k))
    (h : pinIdx C I = true) {n : Nat} (hn : n < 4096) : fldW 11 I n = tvIdxTab[n]! := by
  have h1 := List.all_eq_true.mp h n (List.mem_range.mpr hn)
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true',
    decide_eq_true_eq] at h1
  rcases h1 with ⟨hk, hv⟩ | ⟨hk, hc⟩
  · rw [hk, tvIdxTab_none hn]
    intro k hk' he
    have hp := tvP_tvPair hk'
    have : validP n = true := by
      rw [← he]
      unfold validP
      rw [codeOf_div hp, codeOf_mod hp]
      simp [hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2]
    rw [hv] at this
    exact Bool.false_ne_true this
  · rw [hC _ hk] at hc
    have e := tvIdxTab_code hk
    rw [hc] at e
    exact e.symm

theorem pinF_get {f : Nat → Nat} {a : Nat} {l : List Nat} (h : pinF f a l = true) {s : Nat}
    (hs : s < l.length) : f (a + s) = l[s] := by
  induction l generalizing a s with
  | nil => simp at hs
  | cons x l ih =>
    have h' : (f a == x && pinF f (a + 1) l) = true := h
    rw [Bool.and_eq_true, beq_iff_eq] at h'
    cases s with
    | zero => simpa using h'.1
    | succ s =>
      rw [List.getElem_cons_succ, ← ih h'.2 (by simp at hs; omega)]
      congr 1
      omega

theorem pinMapR_get {β α : Type} [BEq α] [LawfulBEq α] [Inhabited α] {f : β → α} {src : List β}
    {dst : List α} {a n : Nat} (h : pinMapR f src dst a n = true) {i : Nat} (h1 : a ≤ i)
    (h2 : i < a + n) (h3 : i < src.length) : f src[i] = dst.getD i default := by
  unfold pinMapR at h
  rw [beq_iff_eq] at h
  have hl := congrArg List.length h
  simp only [List.length_map, List.length_take, List.length_drop] at hl
  have hi : i - a < (((src.drop a).take n).map f).length := by
    simp only [List.length_map, List.length_take, List.length_drop]
    omega
  have e := List.getElem_of_eq h hi
  simp only [List.getElem_map, List.getElem_take, List.getElem_drop] at e
  have hd : i < dst.length := by omega
  rw [getD_of_lt hd]
  have ea : a + (i - a) = i := by omega
  simp only [ea] at e
  exact e

theorem Reach.mono {n m m' : Nat} {isRoot : Nat → Bool} {edge edge' : Nat → Nat → Nat → Bool}
    (h : Reach n m isRoot edge)
    (he : ∀ g < m, ∀ u < n, ∀ v < n, edge g u v = true → ∃ g' < m', edge' g' u v = true) :
    Reach n m' isRoot edge' := by
  intro Q hroot hstep
  refine h Q hroot fun g hg u hu v hv huv hQ => ?_
  obtain ⟨g', hg', h'⟩ := he g hg u hu v hv huv
  exact hstep g' hg' u hu v hv h' hQ

theorem maskOf_testBit (l : List Nat) (S x : Nat) :
    (l.foldl (fun S r => S ||| 2 ^ r) S).testBit x = (S.testBit x || l.contains x) := by
  induction l generalizing S with
  | nil => simp
  | cons r l ih =>
    rw [List.foldl_cons, ih, Nat.testBit_or, Nat.testBit_two_pow, List.contains_cons]
    by_cases h : r = x
    · subst h
      simp
    · have h' : (x == r) = false := by simp [Ne.symm h]
      simp [h, h']

theorem maskOf_lt {l : List Nat} {n : Nat} (h : ∀ r ∈ l, r < n) (S : Nat) (hS : S < 2 ^ n) :
    l.foldl (fun S r => S ||| 2 ^ r) S < 2 ^ n := by
  induction l generalizing S with
  | nil => exact hS
  | cons r l ih =>
    rw [List.foldl_cons]
    refine ih (fun r' hr' => h r' (List.mem_cons_of_mem r hr')) _ ?_
    exact Nat.or_lt_two_pow hS (Nat.pow_lt_pow_right (by omega) (h r (List.mem_cons_self ..)))

theorem walkT_sound {n m : Nat} {edge : Nat → Nat → Nat → Bool} (Q : Nat → Prop)
    (hstep : ∀ g < m, ∀ u < n, ∀ v < n, edge g u v = true → Q u → Q v) :
    ∀ (recs : List (Nat × Nat × Nat)) (S : Nat), S < 2 ^ n → (∀ x, S.testBit x = true → Q x) →
      walkT n m edge recs S = true → ∀ v < n, Q v := by
  intro recs
  induction recs with
  | nil =>
    intro S hS hQ h v hv
    have h' : (S == 2 ^ n - 1) = true := h
    rw [beq_iff_eq] at h'
    apply hQ
    rw [h', Nat.testBit_two_pow_sub_one]
    exact decide_eq_true hv
  | cons r recs ih =>
    intro S hS hQ h
    have h' : (S.testBit r.2.1 && decide (r.2.2 < m) && decide (r.1 < n) &&
        edge r.2.2 r.2.1 r.1 && walkT n m edge recs (S ||| 2 ^ r.1)) = true := h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h'
    obtain ⟨⟨⟨⟨hp, hg⟩, hv⟩, he⟩, hw⟩ := h'
    have hpn : r.2.1 < n := by
      rcases Nat.lt_or_ge r.2.1 n with hc | hc
      · exact hc
      · have : S.testBit r.2.1 = false :=
          Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hS (Nat.pow_le_pow_right (by omega) hc))
        rw [this] at hp
        exact absurd hp Bool.false_ne_true
    refine ih (S ||| 2 ^ r.1) (Nat.or_lt_two_pow hS (Nat.pow_lt_pow_right (by omega) hv)) ?_ hw
    intro x hx
    rw [Nat.testBit_or, Bool.or_eq_true, Nat.testBit_two_pow] at hx
    rcases hx with hx | hx
    · exact hQ x hx
    · have hx' : r.1 = x := of_decide_eq_true hx
      subst hx'
      exact hstep _ hg _ hpn _ hv he (hQ _ hp)

theorem reach_of_treeK {n m : Nat} {isRoot : Nat → Bool} {edge : Nat → Nat → Nat → Bool}
    {roots : List Nat} {recs : List (Nat × Nat × Nat)} (h : treeK n m isRoot edge roots recs = true) :
    Reach n m isRoot edge := by
  intro Q hroot hstep
  unfold treeK at h
  rw [Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨hr, hw⟩ := h
  have hr' : ∀ r ∈ roots, r < n ∧ isRoot r = true := fun r hm => by
    have := hr r hm
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact this
  refine walkT_sound Q hstep recs (maskOf roots)
    (maskOf_lt (fun r hm => (hr' r hm).1) 0 (Nat.two_pow_pos n)) ?_ hw
  intro x hx
  unfold maskOf at hx
  rw [maskOf_testBit, Nat.zero_testBit, Bool.false_or, List.contains_iff_mem] at hx
  exact hroot x (hr' x hx).1 (hr' x hx).2

end CFSG.SmithL6.K
