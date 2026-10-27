module

public import Certificates.Data.Kernel.BfsPinBase
import CFSG.Certificates.Kernel.BfsPinSetSound
import all CFSG.Certificates.Kernel.Spor.PrimSound
import CFSG.Certificates.Kernel.Spor.PcompFacts
public import CFSG.Certificates.Kernel.BfsPinUnpack

public section

namespace CFSG.KC.BfsPin

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.Monster.B.Co2.Native
open CFSG.RankThree.Native CFSG.Monster.B.Fischer CFSG.KC.Bfs
open CFSG.KLie.CT (fget pw2 maskN orN)

theorem allBlk_intro {b : Nat} {f : Nat → Bool} : ∀ {len : Nat},
    (∀ l < len, f (Nat.add b l) = true) → allBlk b f len = true
  | 0, _ => rfl
  | len + 1, h => by
    change Bool.rec (motive := fun _ => Bool) false (allBlk b f len) (f (Nat.add b len)) = true
    rw [h len (Nat.lt_succ_self len), allBlk_intro fun l hl => h l (by omega)]

theorem rec_blocks_intro {f : Nat → Bool} : ∀ {q : Nat},
    (∀ h < q, allBlk (Nat.shiftLeft h (nat_lit 6)) f (nat_lit 64) = true) →
    Nat.rec (motive := fun _ => Bool) true
      (fun h ih => Bool.rec (motive := fun _ => Bool) false ih
        (allBlk (Nat.shiftLeft h (nat_lit 6)) f (nat_lit 64))) q = true
  | 0, _ => rfl
  | q + 1, h => by
    change Bool.rec (motive := fun _ => Bool) false
      (Nat.rec (motive := fun _ => Bool) true
        (fun h ih => Bool.rec (motive := fun _ => Bool) false ih
          (allBlk (Nat.shiftLeft h (nat_lit 6)) f (nat_lit 64))) q)
      (allBlk (Nat.shiftLeft q (nat_lit 6)) f (nat_lit 64)) = true
    rw [h q (Nat.lt_succ_self q), rec_blocks_intro fun l hl => h l (by omega)]

theorem allN_intro {n : Nat} {f : Nat → Bool} (h : ∀ i < n, f i = true) : allN n f = true := by
  have e6 : ∀ x : Nat, Nat.shiftLeft x (nat_lit 6) = x * 64 := fun x => by
    change x <<< 6 = x * 64
    rw [Nat.shiftLeft_eq]
  have e64 : Nat.shiftRight n (nat_lit 6) = n / 64 := by
    change n >>> 6 = n / 64
    rw [Nat.shiftRight_eq_div_pow]
  have er : Nat.land n (nat_lit 63) = n % 64 := by
    change n &&& (2 ^ 6 - 1) = n % 2 ^ 6
    exact Nat.and_two_pow_sub_one_eq_mod n 6
  change Bool.rec (motive := fun _ => Bool) false
      (Nat.rec (motive := fun _ => Bool) true
        (fun h ih => Bool.rec (motive := fun _ => Bool) false ih
          (allBlk (Nat.shiftLeft h (nat_lit 6)) f (nat_lit 64))) (Nat.shiftRight n (nat_lit 6)))
      (allBlk (Nat.shiftLeft (Nat.shiftRight n (nat_lit 6)) (nat_lit 6)) f
        (Nat.land n (nat_lit 63))) = true
  have h1 : allBlk (Nat.shiftLeft (Nat.shiftRight n (nat_lit 6)) (nat_lit 6)) f
      (Nat.land n (nat_lit 63)) = true := by
    refine allBlk_intro fun l hl => h _ ?_
    rw [er] at hl
    rw [e6, e64]
    simp only [Nat.add_eq]
    omega
  have h2 := rec_blocks_intro (f := f) (q := Nat.shiftRight n (nat_lit 6)) fun q hq => by
    refine allBlk_intro fun l hl => h _ ?_
    rw [e64] at hq
    rw [e6]
    simp only [Nat.add_eq]
    have : l < 64 := hl
    omega
  rw [h1, h2]

private theorem testBit_pw2 (s i : Nat) : (pw2 s).testBit i = decide (s = i) := by
  change (1 <<< s).testBit i = _
  rw [Nat.one_shiftLeft, Nat.testBit_two_pow]

private theorem keysRun_spec {n w : Nat} {ps : List Nat} {N : Nat} {T : Nat → Nat} :
    ∀ (L : List Nat) (lo acc : Nat), keysRun n w ps N T L lo acc ≠ 0 →
      L.Pairwise (fun a b => keyK n w ps (T a) < keyK n w ps (T b)) ∧
        (∀ s ∈ L, lo ≤ keyK n w ps (T s)) ∧
        ∀ i, (keysRun n w ps N T L lo acc).testBit i = true → acc.testBit i = true ∨ i ∈ L
  | [], _, _, _ => ⟨List.Pairwise.nil, fun _ h => absurd h List.not_mem_nil,
      fun _ h => Or.inl h⟩
  | s :: L, lo, acc, h => by
    have e : keysRun n w ps N T (s :: L) lo acc =
        nIf(bAnd(Nat.blt s N, Nat.ble lo (keyK n w ps (T s))),
          keysRun n w ps N T L (Nat.succ (keyK n w ps (T s))) (Nat.lor acc (pw2 s)), nat_lit 0) :=
      strictN_app _ (fun key => nIf(bAnd(Nat.blt s N, Nat.ble lo key),
        keysRun n w ps N T L (Nat.succ key) (Nat.lor acc (pw2 s)), nat_lit 0))
    rw [e, nIf_ite] at h ⊢
    by_cases hc : bAnd(Nat.blt s N, Nat.ble lo (keyK n w ps (T s))) = true
    · rw [ite_eq_left hc] at h ⊢
      have hlo : lo ≤ keyK n w ps (T s) := Nat.le_of_ble_eq_true ((bAnd_iff _ _).1 hc).2
      obtain ⟨hp, hk, hb⟩ := keysRun_spec L _ _ h
      refine ⟨List.pairwise_cons.2 ⟨fun b hb' => hk b hb', hp⟩, fun t ht => ?_, fun i hi => ?_⟩
      · rcases List.mem_cons.1 ht with rfl | ht
        · exact hlo
        · exact le_trans hlo (Nat.le_of_succ_le (hk t ht))
      · rcases hb i hi with h' | h'
        · have e2 : (Nat.lor acc (pw2 s)).testBit i = (acc.testBit i || (pw2 s).testBit i) :=
            Nat.testBit_or acc (pw2 s) i
          rw [e2, testBit_pw2, Bool.or_eq_true, decide_eq_true_iff] at h'
          rcases h' with h' | rfl
          · exact Or.inl h'
          · exact Or.inr List.mem_cons_self
        · exact Or.inr (List.mem_cons_of_mem s h')
    · rw [ite_eq_right hc] at h
      exact absurd rfl h

private theorem pairwise_lt_inj {f : Nat → Nat} : ∀ {L : List Nat},
    L.Pairwise (fun a b => f a < f b) → ∀ a ∈ L, ∀ b ∈ L, f a = f b → a = b
  | [], _, a, ha, _, _, _ => absurd ha List.not_mem_nil
  | x :: L, h, a, ha, b, hb, e => by
    rw [List.pairwise_cons] at h
    rcases List.mem_cons.1 ha with ha' | ha'
    · rcases List.mem_cons.1 hb with hb' | hb'
      · rw [ha', hb']
      · rw [ha'] at e
        exact absurd e (Nat.ne_of_lt (h.1 b hb'))
    · rcases List.mem_cons.1 hb with hb' | hb'
      · rw [hb'] at e
        exact absurd e.symm (Nat.ne_of_lt (h.1 a ha'))
      · exact pairwise_lt_inj h.2 a ha' b hb' e

theorem keysSK_spec {n w : Nat} {ps : List Nat} {N : Nat} {T : Nat → Nat} {SK : List Nat}
    (h : keysSK n w ps N T SK = true) :
    ∀ i < N, ∀ j < N, keyK n w ps (T i) = keyK n w ps (T j) → i = j := by
  unfold keysSK at h
  simp only [bAnd_iff] at h
  obtain ⟨-, hN, hm⟩ := h
  have hm' := Nat.eq_of_beq_eq_true hm
  have hmask : ∀ i < N, (maskN N).testBit i = true := by
    intro i hi
    have e : maskN N = 2 ^ N - 1 := by
      change Nat.sub (1 <<< N) 1 = 2 ^ N - 1
      rw [Nat.one_shiftLeft]
      rfl
    rw [e, Nat.testBit_two_pow_sub_one, decide_eq_true_iff]
    exact hi
  have h0 : keysRun n w ps N T SK 0 0 ≠ 0 := by
    rw [hm']
    intro e
    have := hmask 0 (Nat.blt_eq.mp hN)
    rw [e, Nat.zero_testBit] at this
    exact Bool.false_ne_true this
  obtain ⟨hp, -, hb⟩ := keysRun_spec SK 0 0 h0
  have hmem : ∀ i < N, i ∈ SK := by
    intro i hi
    have h1 := hmask i hi
    rw [← hm'] at h1
    rcases hb i h1 with h2 | h2
    · rw [Nat.zero_testBit] at h2
      exact absurd h2 Bool.false_ne_true
    · exact h2
  intro i hi j hj e
  exact pairwise_lt_inj hp i (hmem i hi) j (hmem j hj) e

private theorem keysK_of_inj {n w : Nat} {ps : List Nat} {N : Nat} {T : Nat → Nat}
    (hi : ∀ i < N, ∀ j < N, pkeyK n w ps (T i) = pkeyK n w ps (T j) → i = j) :
    keysK n w ps N T = true := by
  refine allN_intro fun i hiN => ?_
  rw [strictB_app]
  refine allN_intro fun j hj => ?_
  cases e : Nat.beq (pkeyK n w ps (T i)) (pkeyK n w ps (T j))
  · rfl
  · exact absurd (hi i hiN j (by omega) (Nat.eq_of_beq_eq_true e)) (by omega)

private theorem keysK_of_keysSK {n w : Nat} {ps : List Nat} {N : Nat} {T : Nat → Nat}
    {SK : List Nat} (h : keysSK n w ps N T SK = true) : keysK n w ps N T = true :=
  keysK_of_inj (keysSK_spec h)

theorem distinctK_inj {N : Nat} {T S : Nat → Nat} (h : distinctK N T S = true) :
    ∀ a < N, ∀ b < N, T a = T b → a = b := by
  unfold distinctK at h
  simp only [bAnd_iff] at h
  obtain ⟨hlt, -, hm⟩ := h
  have hstep : ∀ k, k + 1 < N → T (S k) < T (S (k + 1)) :=
    fun k hk => Nat.blt_eq.mp (allN_spec hlt k (by change k < N - 1; omega))
  have hmono : ∀ k l, k < l → l < N → T (S k) < T (S l) := by
    intro k l
    induction l with
    | zero => intro h1; omega
    | succ l ih =>
      intro hkl hl
      rcases Nat.lt_or_ge k l with h1 | h1
      · exact Nat.lt_trans (ih h1 (by omega)) (hstep l hl)
      · have e : k = l := by omega
        rw [e]
        exact hstep l hl
  have hor : ∀ i M, (orN M fun k => pw2 (S k)).testBit i = true → ∃ k < M, S k = i := by
    intro i M
    induction M with
    | zero => intro h1; simp [orN] at h1
    | succ M ih =>
      intro h1
      have e : (orN (M + 1) fun k => pw2 (S k)) = (pw2 (S M) ||| orN M fun k => pw2 (S k)) :=
        rfl
      rw [e, Nat.testBit_or, Bool.or_eq_true, testBit_pw2, decide_eq_true_iff] at h1
      rcases h1 with h1 | h1
      · exact ⟨M, Nat.lt_succ_self M, h1⟩
      · obtain ⟨k, hk, e2⟩ := ih h1
        exact ⟨k, by omega, e2⟩
  have hsurj : ∀ a < N, ∃ k < N, S k = a := by
    intro a ha
    refine hor a N ?_
    have e : maskN N = 2 ^ N - 1 := by
      change Nat.sub (1 <<< N) 1 = 2 ^ N - 1
      rw [Nat.one_shiftLeft]
      rfl
    rw [Nat.eq_of_beq_eq_true hm, e, Nat.testBit_two_pow_sub_one, decide_eq_true_iff]
    exact ha
  intro a ha b hb e
  obtain ⟨k, hk, rfl⟩ := hsurj a ha
  obtain ⟨l, hl, rfl⟩ := hsurj b hb
  rcases Nat.lt_trichotomy k l with h1 | h1 | h1
  · exact absurd e (Nat.ne_of_lt (hmono k l h1 hl))
  · rw [h1]
  · exact absurd e.symm (Nat.ne_of_lt (hmono l k h1 hk))

theorem keyA_range_inj {n w p q : Nat} (hp : canonK n w (mask w) (n * w) p = true)
    (hq : canonK n w (mask w) (n * w) q = true)
    (h : keyA n (List.range n) (unpack n w p) = keyA n (List.range n) (unpack n w q)) : p = q := by
  obtain ⟨-, -, -, hp1⟩ := CFSG.KS.PF.canon_facts hp
  obtain ⟨-, -, -, hq1⟩ := CFSG.KS.PF.canon_facts hq
  unfold keyA at h
  have hl : ∀ i ∈ List.range n, (unpack n w p)[i]! = (unpack n w q)[i]! := by
    rcases Nat.lt_or_ge 1 n with hn | hn
    · have hlt : ∀ r : Nat, canonK n w (mask w) (n * w) r = true →
          ∀ l ∈ (List.range n).map fun i => (unpack n w r)[i]!, l < n := by
        intro r hr l hl
        obtain ⟨-, -, -, hr1⟩ := CFSG.KS.PF.canon_facts hr
        obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hl
        rw [List.mem_range] at hi
        rw [unpack_get' hi]
        exact hr1 i hi
      exact List.map_inj_left.1 (Nat.ofDigits_inj_of_len_eq hn (by simp) (hlt p hp) (hlt q hq) h)
    · intro i hi
      rw [List.mem_range] at hi
      rw [unpack_get' hi, unpack_get' hi]
      have := hp1 i hi
      have := hq1 i hi
      omega
  obtain ⟨-, hw, hp0, -⟩ := CFSG.KS.PF.canon_facts hp
  obtain ⟨-, -, hq0, -⟩ := CFSG.KS.PF.canon_facts hq
  refine CFSG.KS.PF.eq_of_fields (CFSG.KS.PF.w_pos hw) hp0 hq0 fun i hi => ?_
  have e := hl i (List.mem_range.2 hi)
  rw [unpack_get' hi, unpack_get' hi] at e
  exact e

private theorem range_keys_inj {n w ng N : Nat} {G T E S : Nat → Nat}
    (hk : bfsK n w ng G N T E S = true) :
    ∀ a < N, ∀ b < N, keyA n (List.range n) (unpack n w (T a)) =
      keyA n (List.range n) (unpack n w (T b)) → a = b := by
  have hc := bfsK_canon hk
  unfold bfsK at hk
  simp only [bAnd_iff] at hk
  intro a ha b hb e
  exact distinctK_inj hk.2.2.2.2.1 a ha b hb (keyA_range_inj (hc a ha) (hc b hb) e)

theorem idK_of_szOK {n w : Nat} (h : szOK n w = true) : idK n w (mask w) = true := by
  obtain ⟨hn, hw⟩ := szOK_facts h
  refine allN_intro fun i hi => ?_
  rw [pg_pidn hn hw hi]
  exact Nat.beq_refl i

private def StOK (key : Array Nat → Nat) (U : Nat → Array Nat) (c : Nat) (pts : Array (Array Nat))
    (idx : Std.HashMap Nat Nat) : Prop :=
  pts.size = c ∧ (∀ j < c, pts[j]! = U j) ∧ (∀ j < c, idx[key (U j)]? = some j) ∧
    ∀ m j, idx[m]? = some j → j < c ∧ key (U j) = m

section Search

variable {act : Nat → Array Nat → Array Nat} {key : Array Nat → Nat} {U : Nat → Array Nat}
  {N : Nat}

private theorem gF_st (hinj : ∀ a < N, ∀ b < N, key (U a) = key (U b) → a = b)
    {c i k r : Nat} {pts : Array (Array Nat)} {par lab row : Array Nat} {idx : Std.HashMap Nat Nat}
    (hs : StOK key U c pts idx) (hi : i < c)
    (hr : ((∃ j < c, act k (U i) = U j) ∧ r = c) ∨ (act k (U i) = U c ∧ r = c + 1))
    (hrN : r ≤ N) :
    StOK key U r (gF act key i (pts, par, lab, idx, row) k).1
      (gF act key i (pts, par, lab, idx, row) k).2.2.2.1 := by
  have hpi : pts[i]! = U i := hs.2.1 i hi
  simp only [gF]
  split
  · next j heq =>
    rw [Std.HashMap.get?_eq_getElem?, hpi] at heq
    obtain ⟨hj, hkj⟩ := hs.2.2.2 _ _ heq
    rcases hr with ⟨-, rfl⟩ | ⟨e, rfl⟩
    · exact hs
    · rw [e] at hkj
      exact absurd (hinj j (by omega) c (by omega) hkj) (by omega)
  · next heq =>
    rw [Std.HashMap.get?_eq_getElem?, hpi] at heq
    rcases hr with ⟨⟨j, hj, e⟩, -⟩ | ⟨e, rfl⟩
    · rw [e, hs.2.2.1 j hj] at heq
      exact absurd heq (by simp)
    · dsimp only
      rw [hpi, e]
      have hne : ∀ j < c, key (U c) ≠ key (U j) := fun j hj h' => by
        have := hinj c (by omega) j (by omega) h'
        omega
      refine ⟨by rw [Array.size_push, hs.1], fun j hj => ?_, fun j hj => ?_, fun m j h => ?_⟩
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · rw [push_get_lt _ _ (by rw [hs.1]; exact hj)]
          exact hs.2.1 j hj
        · exact push_get_of_eq _ _ hs.1
      · rw [Std.HashMap.getElem?_insert]
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · simp only [beq_iff_eq, hne j hj, ↓reduceIte]
          exact hs.2.2.1 j hj
        · simp only [beq_self_eq_true, ↓reduceIte, hs.1]
      · rw [Std.HashMap.getElem?_insert] at h
        split at h
        · next e' =>
          rw [beq_iff_eq] at e'
          cases h
          have := hs.1
          exact ⟨by omega, by rw [hs.1, e']⟩
        · obtain ⟨hj, e'⟩ := hs.2.2.2 m j h
          exact ⟨by omega, e'⟩

private theorem foldl_zero {g : Nat → Nat → Nat} (hz : ∀ k, g k 0 = 0) :
    ∀ L : List Nat, L.foldl (fun c k => g k c) 0 = 0
  | [] => rfl
  | k :: L => by rw [List.foldl_cons, hz, foldl_zero hz L]

private theorem foldl_mono {g : Nat → Nat → Nat} (hz : ∀ k, g k 0 = 0) {P : Nat → Prop}
    (hg : ∀ k, P k → ∀ c, g k c ≠ 0 → c ≤ g k c) :
    ∀ L : List Nat, (∀ k ∈ L, P k) → ∀ c, L.foldl (fun c k => g k c) c ≠ 0 →
      c ≤ L.foldl (fun c k => g k c) c
  | [], _, _, _ => le_rfl
  | k :: L, hL, c, h => by
    rw [List.foldl_cons] at h ⊢
    have h1 : g k c ≠ 0 := fun e => h (by rw [e, foldl_zero hz])
    exact le_trans (hg k (hL k List.mem_cons_self) c h1)
      (foldl_mono hz hg L (fun k' hk' => hL k' (List.mem_cons_of_mem k hk')) _ h)

private theorem fold_st (hinj : ∀ a < N, ∀ b < N, key (U a) = key (U b) → a = b)
    {g : Nat → Nat → Nat} {i ng : Nat} (hz : ∀ k, g k 0 = 0)
    (hg : ∀ k < ng, ∀ c, g k c ≠ 0 →
      ((∃ j < c, act k (U i) = U j) ∧ g k c = c) ∨ (act k (U i) = U c ∧ g k c = c + 1)) :
    ∀ (L : List Nat), (∀ k ∈ L, k < ng) → ∀ (c : Nat) (pts : Array (Array Nat))
      (par lab row : Array Nat) (idx : Std.HashMap Nat Nat), StOK key U c pts idx → i < c →
      L.foldl (fun c k => g k c) c ≠ 0 → L.foldl (fun c k => g k c) c ≤ N →
      StOK key U (L.foldl (fun c k => g k c) c) (L.foldl (gF act key i) (pts, par, lab, idx, row)).1
        (L.foldl (gF act key i) (pts, par, lab, idx, row)).2.2.2.1
  | [], _, _, _, _, _, _, _, hs, _, _, _ => hs
  | k :: L, hL, c, pts, par, lab, row, idx, hs, hi, h0, hN => by
    rw [List.foldl_cons] at h0 hN ⊢
    have hk := hL k List.mem_cons_self
    have hL' : ∀ k' ∈ L, k' < ng := fun k' hk' => hL k' (List.mem_cons_of_mem k hk')
    have h1 : g k c ≠ 0 := fun e => h0 (by rw [e, foldl_zero hz])
    have hmono : ∀ k < ng, ∀ c, g k c ≠ 0 → c ≤ g k c := fun k hk c h => by
      rcases hg k hk c h with ⟨-, e⟩ | ⟨-, e⟩ <;> omega
    have hc1 := hmono k hk c h1
    have hle := foldl_mono hz hmono L hL' (g k c) h0
    have hs1 := gF_st (row := row) (par := par) (lab := lab) hinj hs hi (hg k hk c h1) (by omega)
    exact fold_st hinj hz hg L hL' (g k c) _ (gF act key i (pts, par, lab, idx, row) k).2.1
      (gF act key i (pts, par, lab, idx, row) k).2.2.1
      (gF act key i (pts, par, lab, idx, row) k).2.2.2.2
      (gF act key i (pts, par, lab, idx, row) k).2.2.2.1 hs1 (by omega) h0 hN

end Search

private theorem genStep_cases {n w m : Nat} {T : Nat → Nat} {t row g k c : Nat}
    (h0 : genStep n w m T t row g k c ≠ 0) :
    ((∃ j < c, T j = pcomp n w m g t) ∧ genStep n w m T t row g k c = c) ∨
      (T c = pcomp n w m g t ∧ genStep n w m T t row g k c = c + 1) := by
  have hv := genStep_eq n w m T t row g k c
  generalize genStep n w m T t row g k c = r at h0 hv ⊢
  by_cases h1 : c = 0
  · simp only [h1, ↓reduceIte] at hv
    exact absurd hv h0
  simp only [h1, ↓reduceIte] at hv
  by_cases h2 : fget row k 16 < c
  · simp only [h2, ↓reduceIte] at hv
    by_cases h3 : T (fget row k 16) = pcomp n w m g t
    · simp only [h3, ↓reduceIte] at hv
      exact Or.inl ⟨⟨_, h2, h3⟩, hv⟩
    · simp only [h3, ↓reduceIte] at hv
      exact absurd hv h0
  · simp only [h2, ↓reduceIte] at hv
    by_cases h4 : fget row k 16 = c
    · by_cases h5 : T c = pcomp n w m g t
      · simp only [h4, h5, ↓reduceIte] at hv
        exact Or.inr ⟨h5, hv⟩
      · simp only [h4, h5, ↓reduceIte] at hv
        exact absurd hv h0
    · simp only [h4, ↓reduceIte] at hv
      exact absurd hv h0

private theorem pointF_foldl {n w m : Nat} {G T E : Nat → Nat} (i : Nat) : ∀ len lo c,
    pointF n w m G T E i len lo c =
      (List.range' lo len).foldl (fun c k => genStep n w m T (T i) (E i) (G k) k c) c
  | 0, _, _ => rfl
  | len + 1, lo, c => by
    rw [List.range'_succ, List.foldl_cons]
    exact pointF_foldl i len (lo + 1) _

private theorem pointStep_foldl {n w m ng : Nat} {G T E : Nat → Nat} (i c : Nat) :
    pointStep n w m ng G T E i c =
      (List.range ng).foldl (fun c k => genStep n w m T (T i) (E i) (G k) k c) c := by
  rw [pointStep_eq, pointF_foldl, List.range_eq_range']

private theorem pointStep_mono {n w m ng : Nat} {G T E : Nat → Nat} {i c : Nat}
    (h : pointStep n w m ng G T E i c ≠ 0) : c ≤ pointStep n w m ng G T E i c := by
  rw [pointStep_foldl] at h ⊢
  exact foldl_mono (P := fun _ => True) (fun k => genStep_zero n w m T (T i) (E i) (G k) k)
    (fun k _ c' h' => by rcases genStep_cases h' with ⟨-, e⟩ | ⟨-, e⟩ <;> omega)
    _ (fun _ _ => trivial) c h

private theorem runF_mono {n w m ng : Nat} {G T E : Nat → Nat} : ∀ len lo c,
    runF n w m ng G T E len lo c ≠ 0 → c ≤ runF n w m ng G T E len lo c
  | 0, _, _, _ => le_rfl
  | len + 1, lo, c, h => by
    rw [runF_succ] at h ⊢
    cases hb : Nat.blt lo c
    · rw [hb] at h
      exact absurd (runF_zero len _) h
    · rw [hb] at h
      have h1 := runF_mono len (Nat.succ lo) _ h
      have hp : pointStep n w m ng G T E lo c ≠ 0 := fun e => by
        change runF n w m ng G T E len (Nat.succ lo) (pointStep n w m ng G T E lo c) ≠ 0 at h
        rw [e, runF_zero] at h
        exact h rfl
      exact le_trans (pointStep_mono hp) h1

private theorem loop_st {n w ng N : Nat} {G T E : Nat → Nat} {gs : Array (Array Nat)}
    {ps : List Nat} (hs : gs.size = ng)
    (hinj : ∀ a < N, ∀ b < N, keyA n ps (unpack n w (T a)) = keyA n ps (unpack n w (T b)) → a = b)
    (hstep : ∀ i < N, ∀ k < ng,
      leftA n gs k (unpack n w (T i)) = unpack n w (pcomp n w (mask w) (G k) (T i))) :
    ∀ len lo c f (pts : Array (Array Nat)) (edges : Array (Array Nat)) (par lab : Array Nat)
      (idx : Std.HashMap Nat Nat), StOK (keyA n ps) (fun j => unpack n w (T j)) c pts idx →
      len ≤ f → runF n w (mask w) ng G T E len lo c ≠ 0 → runF n w (mask w) ng G T E len lo c ≤ N →
      ∃ (pts' : Array (Array Nat)) (edges' : Array (Array Nat)) (par' lab' : Array Nat)
        (idx' : Std.HashMap Nat Nat),
        StOK (keyA n ps) (fun j => unpack n w (T j)) (runF n w (mask w) ng G T E len lo c) pts'
          idx' ∧
        gLoop (leftA n gs) gs.size (keyA n ps) f lo pts edges par lab idx =
          gLoop (leftA n gs) gs.size (keyA n ps) (f - len) (lo + len) pts' edges' par' lab' idx'
  | 0, lo, c, f, pts, edges, par, lab, idx, hst, _, _, _ =>
    ⟨pts, edges, par, lab, idx, hst, rfl⟩
  | len + 1, lo, c, f, pts, edges, par, lab, idx, hst, hf, h0, hN => by
    obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    rw [runF_succ] at h0 hN ⊢
    cases hb : Nat.blt lo c
    · rw [hb] at h0
      exact absurd (runF_zero len _) h0
    · rw [hb] at h0 hN
      change runF n w (mask w) ng G T E len (Nat.succ lo) (pointStep n w (mask w) ng G T E lo c) ≠ 0
        at h0
      change runF n w (mask w) ng G T E len (Nat.succ lo) (pointStep n w (mask w) ng G T E lo c) ≤ N
        at hN
      change ∃ (pts' : Array (Array Nat)) (edges' : Array (Array Nat)) (par' lab' : Array Nat)
        (idx' : Std.HashMap Nat Nat),
        StOK (keyA n ps) (fun j => unpack n w (T j))
          (runF n w (mask w) ng G T E len (Nat.succ lo) (pointStep n w (mask w) ng G T E lo c))
          pts' idx' ∧
        gLoop (leftA n gs) gs.size (keyA n ps) (f + 1) lo pts edges par lab idx =
          gLoop (leftA n gs) gs.size (keyA n ps) (f + 1 - (len + 1)) (lo + (len + 1)) pts' edges'
            par' lab' idx'
      have hlo : lo < c := Nat.blt_eq.mp hb
      have hp0 : pointStep n w (mask w) ng G T E lo c ≠ 0 := fun e => by
        rw [e, runF_zero] at h0
        exact h0 rfl
      have hpN : pointStep n w (mask w) ng G T E lo c ≤ N :=
        le_trans (runF_mono len _ _ h0) hN
      have hloN : lo < N := by
        have := pointStep_mono hp0
        omega
      have hg : ∀ k < ng, ∀ c', genStep n w (mask w) T (T lo) (E lo) (G k) k c' ≠ 0 →
          ((∃ j < c', leftA n gs k (unpack n w (T lo)) = unpack n w (T j)) ∧
            genStep n w (mask w) T (T lo) (E lo) (G k) k c' = c') ∨
          (leftA n gs k (unpack n w (T lo)) = unpack n w (T c') ∧
            genStep n w (mask w) T (T lo) (E lo) (G k) k c' = c' + 1) := by
        intro k hk c' h'
        rw [hstep lo hloN k hk]
        rcases genStep_cases h' with ⟨⟨j, hj, e⟩, e2⟩ | ⟨e, e2⟩
        · exact Or.inl ⟨⟨j, hj, by rw [e]⟩, e2⟩
        · exact Or.inr ⟨by rw [e], e2⟩
      rw [pointStep_foldl] at hp0 hpN h0 hN ⊢
      have hfold := fold_st (act := leftA n gs) (key := keyA n ps) (U := fun j => unpack n w (T j))
        hinj (fun k => genStep_zero n w (mask w) T (T lo) (E lo) (G k) k) hg (List.range ng)
        (fun k hk => List.mem_range.1 hk) c pts par lab #[] idx hst hlo hp0 hpN
      have hst1 := hst
      rw [gLoop, ite_eq_left (by rw [hst1.1]; exact hlo)]
      have e1 : gStep (leftA n gs) gs.size (keyA n ps) lo (pts, par, lab, idx) =
          (List.range ng).foldl (gF (leftA n gs) (keyA n ps) lo) (pts, par, lab, idx, #[]) := by
        unfold gStep
        rw [hs]
      rw [e1]
      generalize (List.range ng).foldl (gF (leftA n gs) (keyA n ps) lo) (pts, par, lab, idx, #[]) =
        s at hfold
      obtain ⟨a, b, l, d, r⟩ := s
      obtain ⟨pts', edges', par', lab', idx', hst', heq⟩ :=
        loop_st hs hinj hstep len (Nat.succ lo) _ f a (edges.push r) b l d hfold (by omega) h0 hN
      refine ⟨pts', edges', par', lab', idx', hst', ?_⟩
      have e2 : f + 1 - (len + 1) = f - len := by omega
      have e3 : lo + (len + 1) = Nat.succ lo + len := by omega
      rw [e2, e3]
      exact heq

private theorem gLoop_done {act : Nat → Array Nat → Array Nat} {ngen : Nat} {key : Array Nat → Nat}
    {N : Nat} (f : Nat) (pts : Array (Array Nat)) (edges : Array (Array Nat)) (par lab : Array Nat)
    (idx : Std.HashMap Nat Nat) (h : pts.size = N) :
    (gLoop act ngen key f N pts edges par lab idx).1 = pts := by
  cases f with
  | zero => rfl
  | succ f =>
    rw [gLoop, ite_eq_right (by omega)]

theorem enumBfs_pts_of_inj {n w ng N fuel : Nat} {G T E S : Nat → Nat} {gs : Array (Array Nat)}
    {ps : List Nat} (hs : gs.size = ng) (hg : ∀ k < ng, gs[k]! = unpack n w (G k))
    (hk : bfsK n w ng G N T E S = true)
    (hinj : ∀ a < N, ∀ b < N, keyA n ps (unpack n w (T a)) = keyA n ps (unpack n w (T b)) → a = b)
    (hf : N ≤ fuel) :
    (enumBfs n gs ps fuel).pts = Array.ofFn (n := N) fun i => unpack n w (T i.val) := by
  have hk' := hk
  unfold bfsK at hk'
  simp only [bAnd_iff] at hk'
  obtain ⟨hsz, hcG', hcT', hT0, -, hrun⟩ := hk'
  have hcG : ∀ k < ng, canonK n w (mask w) (n * w) (G k) = true := allN_spec hcG'
  have hcT : ∀ i < N, canonK n w (mask w) (n * w) (T i) = true := allN_spec hcT'
  have hstep : ∀ i < N, ∀ k < ng,
      leftA n gs k (unpack n w (T i)) = unpack n w (pcomp n w (mask w) (G k) (T i)) := by
    intro i hi k hk1
    unfold leftA
    rw [hg k hk1, compA_unpack (hcG k hk1) (hcT i hi)]
  have hR : runF n w (mask w) ng G T E N 0 1 = N := by
    rw [← runK_eq]
    exact Nat.eq_of_beq_eq_true hrun
  have hN : N ≠ 0 := by
    intro e
    subst e
    have e1 : runF n w (mask w) ng G T E 0 0 1 = 1 := rfl
    omega
  have hU0 : unpack n w (T 0) = idA n := by
    obtain ⟨hn, hw⟩ := szOK_facts hsz
    rw [Nat.eq_of_beq_eq_true hT0, unpack_pidn hn hw]
  have hst0 : StOK (keyA n ps) (fun j => unpack n w (T j)) 1 #[idA n]
      ((∅ : Std.HashMap Nat Nat).insert (keyA n ps (idA n)) 0) := by
    refine ⟨rfl, fun j hj => ?_, fun j hj => ?_, fun m j h => ?_⟩
    · have e : j = 0 := by omega
      subst e
      dsimp only
      rw [hU0]
      simp
    · have e : j = 0 := by omega
      subst e
      dsimp only
      rw [hU0]
      simp
    · rw [Std.HashMap.getElem?_insert] at h
      split at h
      · next e =>
        rw [beq_iff_eq] at e
        cases h
        exact ⟨by omega, by dsimp only; rw [hU0, e]⟩
      · rw [Std.HashMap.getElem?_empty] at h
        exact absurd h (by simp)
  obtain ⟨pts', edges', par', lab', idx', hst', heq⟩ :=
    loop_st hs hinj hstep N 0 1 fuel #[idA n] #[] #[0] #[0] _ hst0 hf (by rw [hR]; exact hN)
      (by rw [hR])
  rw [hR] at hst'
  unfold enumBfs
  rw [arrBfs_eq]
  change (gLoop (leftA n gs) gs.size (keyA n ps) fuel 0 #[idA n] #[] #[0] #[0]
    ((∅ : Std.HashMap Nat Nat).insert (keyA n ps (idA n)) 0)).1 = _
  rw [heq, Nat.zero_add, gLoop_done _ _ _ _ _ _ hst'.1]
  apply Array.ext
  · rw [hst'.1, Array.size_ofFn]
  · intro i h1 h2
    rw [Array.getElem_ofFn, ← getElem!_pos pts' i h1]
    exact hst'.2.1 i (by rw [hst'.1] at h1; exact h1)

theorem enumBfs_pts_base {n w ng N fuel : Nat} {G T E S : Nat → Nat} {SK : List Nat}
    {gs : Array (Array Nat)}
    {ps : List Nat} (hs : gs.size = ng) (hg : ∀ k < ng, gs[k]! = unpack n w (G k))
    (hk : bfsK n w ng G N T E S = true) (hps : ∀ p ∈ ps, p < n)
    (hK : keysSK n w ps N T SK = true) (hf : N ≤ fuel) :
    (enumBfs n gs ps fuel).pts = Array.ofFn (n := N) fun i => unpack n w (T i.val) := by
  refine enumBfs_pts_of_inj hs hg hk (fun a ha b hb e => keysSK_spec hK a ha b hb ?_) hf
  rw [keyA_unpack hps, keyA_unpack hps] at e
  exact e

theorem enumBfs_pts {n w ng N fuel : Nat} {G T E S : Nat → Nat} {gs : Array (Array Nat)}
    (hs : gs.size = ng) (hg : ∀ k < ng, gs[k]! = unpack n w (G k))
    (hk : bfsK n w ng G N T E S = true) (hf : N ≤ fuel) :
    (enumBfs n gs (List.range n) fuel).pts = Array.ofFn (n := N) fun i => unpack n w (T i.val) :=
  enumBfs_pts_of_inj hs hg hk (range_keys_inj hk) hf

theorem enumOK_of_bfsK {n w ng N fuel : Nat} {G T E S : Nat → Nat} {gs : Array (Array Nat)}
    (hs : gs.size = ng) (hg : ∀ k < ng, gs[k]! = unpack n w (G k))
    (hp : ∀ k < ng, permOK n w (mask w) (n * w) (G k) (pinvS n w (mask w) (G k)) = true)
    (hk : bfsK n w ng G N T E S = true) (hf : N ≤ fuel) :
    enumOK n gs (List.range n) (enumBfs n gs (List.range n) fuel) = true := by
  have hk' := hk
  unfold bfsK at hk'
  simp only [bAnd_iff] at hk'
  obtain ⟨hsz, -, hcT', hT0, -, -⟩ := hk'
  obtain ⟨hN, -, -, -⟩ := bfsK_points (fun _ => True) trivial (fun _ _ _ _ => trivial) hk
  have hpid : canonK n w (mask w) (n * w) (pidn n w) = true := by
    rw [← Nat.eq_of_beq_eq_true hT0]
    exact allN_spec hcT' 0 hN
  have hps : ∀ p ∈ List.range n, p < n := fun p hp => List.mem_range.1 hp
  have hkey : keysK n w (List.range n) N T = true := keysK_of_inj fun i hi j hj e => by
    rw [← keyA_unpack hps, ← keyA_unpack hps] at e
    exact range_keys_inj hk i hi j hj e
  exact (enumBfs_of_bfsK_set hs hg hp (idK_of_szOK hsz) hpid hk hps hkey hf).1

theorem enumOK_of_bfsK_base {n w ng N fuel : Nat} {G T E S : Nat → Nat} {SK : List Nat}
    {gs : Array (Array Nat)} {ps : List Nat}
    (hs : gs.size = ng) (hg : ∀ k < ng, gs[k]! = unpack n w (G k))
    (hp : ∀ k < ng, permOK n w (mask w) (n * w) (G k) (pinvS n w (mask w) (G k)) = true)
    (hk : bfsK n w ng G N T E S = true) (hps : ∀ p ∈ ps, p < n)
    (hK : keysSK n w ps N T SK = true) (hf : N ≤ fuel) :
    enumOK n gs ps (enumBfs n gs ps fuel) = true := by
  have hk' := hk
  unfold bfsK at hk'
  simp only [bAnd_iff] at hk'
  obtain ⟨hsz, -, hcT', hT0, -, -⟩ := hk'
  obtain ⟨hN, -, -, -⟩ := bfsK_points (fun _ => True) trivial (fun _ _ _ _ => trivial) hk
  have hpid : canonK n w (mask w) (n * w) (pidn n w) = true := by
    rw [← Nat.eq_of_beq_eq_true hT0]
    exact allN_spec hcT' 0 hN
  exact (enumBfs_of_bfsK_set hs hg hp (idK_of_szOK hsz) hpid hk hps (keysK_of_keysSK hK) hf).1

end CFSG.KC.BfsPin

end
