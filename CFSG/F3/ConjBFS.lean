module

public import Certificates.Data.CFSGNative.F3.Conj
public import Certificates.Data.Kernel.F3Bfs
import CFSG.F3.Spec
import CFSG.Sporadic.Th.TableSpec
import CFSG.Certificates.Kernel.SporSch.LyLoop
public import Mathlib.Data.Nat.Notation

public section

namespace CFSG.F3.Native.BfsSpec

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.KC.F3Bfs CFSG.KC.Enum CFSG.KS.SporSch.LyLoop

theorem eq_of_beqV {a b : V} (h : a.beq b = true) : a = b := by
  obtain ⟨p, m⟩ := a
  obtain ⟨p', m'⟩ := b
  obtain ⟨h1, h2⟩ := V.beq_iff.1 h
  simp only at h1 h2
  rw [h1, h2]

theorem eq_of_eqM {d : ℕ} {X Y : Array V} (h : eqM d X Y = true) : X = Y := by
  unfold eqM at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hX, hY⟩, hall⟩ := h
  rw [Nat.all_eq_finRange_all, List.all_eq_true] at hall
  refine Array.ext (by rw [hX, hY]) fun i hi1 hi2 => ?_
  have hi : i < d := hX ▸ hi1
  have hb : X[i]!.beq Y[i]! = true := hall ⟨i, hi⟩ (List.mem_finRange _)
  have e := eq_of_beqV hb
  rwa [getElem!_pos X i hi1, getElem!_pos Y i hi2] at e

theorem get!_push_lt' {α : Type} [Inhabited α] (xs : Array α) (x : α) {i : ℕ}
    (h : i < xs.size) : (xs.push x)[i]! = xs[i]! := by
  rw [getElem!_pos (xs.push x) i (by rw [Array.size_push]; omega), getElem!_pos xs i h,
    Array.getElem_push_lt h]

theorem get!_push_eq' {α : Type} [Inhabited α] (xs : Array α) (x : α) :
    (xs.push x)[xs.size]! = x := by
  rw [getElem!_pos _ _ (by rw [Array.size_push]; omega), Array.getElem_push_eq]

theorem ofNat_ap (t : Table) (p : ℕ) : UInt32.ofNat (ap t p) = t[p]! := by
  unfold ap
  exact UInt32.ofNat_toNat

def LoopStep {β : Type} (I Q : β → Prop) : ForInStep β → Prop
  | .yield b => I b
  | .done b => Q b

theorem forIn_range'_loop {β : Type} (I : ℕ → β → Prop) (Q : β → Prop)
    (f : ℕ → β → Id (ForInStep β)) : ∀ (m s : ℕ) (b : β),
    (∀ q b, s ≤ q → q < s + m → I q b → LoopStep (I (q + 1)) Q (f q b)) →
    (∀ b, I (s + m) b → Q b) → I s b → Q (forIn (List.range' s m) b f)
  | 0, s, b, _, hend, h0 => hend b (by simpa using h0)
  | m + 1, s, b, hstep, hend, h0 => by
    rw [List.range'_succ, List.forIn_cons]
    have hs := hstep s b (Nat.le_refl _) (by omega) h0
    cases hf : f s b with
    | done b' =>
      rw [hf] at hs
      exact hs
    | yield b' =>
      rw [hf] at hs
      have e : s + (m + 1) = s + 1 + m := by omega
      exact forIn_range'_loop I Q f m (s + 1) b'
        (fun q b h1 h2 h3 => hstep q b (by omega) (by omega) h3)
        (fun b hb => hend b (by rwa [e])) hs

theorem forIn_range_loop {β : Type} (I : ℕ → β → Prop) (Q : β → Prop)
    (f : ℕ → β → Id (ForInStep β)) (n : ℕ) (b : β)
    (hstep : ∀ q b, q < n → I q b → LoopStep (I (q + 1)) Q (f q b))
    (hend : ∀ b, I n b → Q b) (h0 : I 0 b) : Q (forIn [:n] b f) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  have hs : Std.Legacy.Range.size [:n] = n := by simp [Std.Legacy.Range.size]
  simp only [hs]
  exact forIn_range'_loop I Q f n 0 b (fun q b _ h2 h3 => hstep q b (by omega) h3)
    (fun b hb => hend b (by simpa using hb)) h0

@[expose] noncomputable def cnt (fa fb fp fl : ℕ → ℕ) (h : ℕ) : ℕ :=
  (List.range h).foldl (fun s i => bfsStep fa fb fp fl i s) 1

theorem cnt_succ (fa fb fp fl : ℕ → ℕ) (h : ℕ) :
    cnt fa fb fp fl (h + 1) = bfsStep fa fb fp fl h (cnt fa fb fp fl h) := by
  unfold cnt
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem bfsHit_zero (fp fl : ℕ → ℕ) (h l x : ℕ) : bfsHit fp fl h l x 0 = 0 := by
  simp [bfsHit, nIf_eqP]

theorem bfsHit_spec {fp fl : ℕ → ℕ} {h l x n : ℕ} (hne : bfsHit fp fl h l x n ≠ 0) :
    (x < n ∧ bfsHit fp fl h l x n = n) ∨
      (x = n ∧ fp n = h ∧ fl n = l ∧ bfsHit fp fl h l x n = n + 1) := by
  revert hne
  simp only [bfsHit, nIf_eqP, Nat.beq_eq, Nat.blt_eq]
  split_ifs <;> omega

theorem bfsStep_eq (fa fb fp fl : ℕ → ℕ) (h n : ℕ) : bfsStep fa fb fp fl h n =
    if h < n then bfsHit fp fl h 2 (fb h) (bfsHit fp fl h 1 (fa h) n) else 0 := by
  simp only [bfsStep, nIf_eqP, strictN_eqP, Nat.blt_eq]

theorem bfsStep_zero (fa fb fp fl : ℕ → ℕ) (h : ℕ) : bfsStep fa fb fp fl h 0 = 0 := by
  rw [bfsStep_eq, if_neg (Nat.not_lt_zero h)]

def KInv (O : COrbit) (n : ℕ) (keys : Array (Array V)) (index : Std.HashMap (Array (ℕ × ℕ)) ℕ)
    (par lab : Table) : Prop :=
  keys.size = n ∧ (∀ i < n, keys[i]! = O.keys[i]!) ∧
    (∀ i < n, index[keyOf O.keys[i]!]? = some i) ∧
    (∀ Z i, index[Z]? = some i → i < n ∧ keyOf O.keys[i]! = Z) ∧
    par.size = n ∧ (∀ i < n, par[i]! = O.par[i]!) ∧ lab.size = n ∧ (∀ i < n, lab[i]! = O.lab[i]!)

def TInv (T a : Table) (h : ℕ) : Prop := a.size = h ∧ ∀ i < h, a[i]! = T[i]!

theorem tinv_push {T a : Table} {h : ℕ} (H : TInv T a h) {v : UInt32} (hv : T[h]! = v) :
    TInv T (a.push v) (h + 1) := by
  refine ⟨by rw [Array.size_push, H.1], fun i hi => ?_⟩
  rcases Nat.lt_or_ge i h with h1 | h1
  · rw [get!_push_lt' _ _ (by rw [H.1]; exact h1), H.2 i h1]
  · have e : i = a.size := by rw [H.1]; omega
    rw [e, get!_push_eq', ← hv, H.1]

theorem kinv_found {O : COrbit} {n : ℕ} {keys : Array (Array V)}
    {index : Std.HashMap (Array (ℕ × ℕ)) ℕ} {par lab : Table} (H : KInv O n keys index par lab)
    (hinj : ∀ i < O.keys.size, ∀ j < O.keys.size, keyOf O.keys[i]! = keyOf O.keys[j]! → i = j)
    (hn : n ≤ O.keys.size) {x k : ℕ} (hx : x < O.keys.size)
    (hk : index[keyOf O.keys[x]!]? = some k) : k = x ∧ x < n := by
  obtain ⟨h1, h2⟩ := H.2.2.2.1 _ _ hk
  have := hinj k (by omega) x hx h2
  exact ⟨this, this ▸ h1⟩

theorem kinv_absent {O : COrbit} {n : ℕ} {keys : Array (Array V)}
    {index : Std.HashMap (Array (ℕ × ℕ)) ℕ} {par lab : Table} (H : KInv O n keys index par lab)
    {x : ℕ} (hx : x < n) (hk : index[keyOf O.keys[x]!]? = none) : False := by
  rw [H.2.2.1 x hx] at hk
  simp at hk

theorem kinv_new {O : COrbit} {n : ℕ} {keys : Array (Array V)}
    {index : Std.HashMap (Array (ℕ × ℕ)) ℕ} {par lab : Table} (H : KInv O n keys index par lab)
    (hinj : ∀ i < O.keys.size, ∀ j < O.keys.size, keyOf O.keys[i]! = keyOf O.keys[j]! → i = j)
    (hn : n < O.keys.size) {p l : UInt32} (hp : O.par[n]! = p) (hl : O.lab[n]! = l) :
    KInv O (n + 1) (keys.push O.keys[n]!) (index.insert (keyOf O.keys[n]!) keys.size)
      (par.push p) (lab.push l) := by
  obtain ⟨hs, hk, hi1, hi2, hps, hpk, hls, hlk⟩ := H
  have hne : ∀ i < n, (keyOf O.keys[n]! == keyOf O.keys[i]!) = false := by
    intro i hi
    rw [beq_eq_false_iff_ne]
    intro e
    have := hinj n hn i (by omega) e
    omega
  refine ⟨by rw [Array.size_push, hs], fun i hi => ?_, fun i hi => ?_, fun Z i hZ => ?_,
    by rw [Array.size_push, hps], fun i hi => ?_, by rw [Array.size_push, hls], fun i hi => ?_⟩
  · rcases Nat.lt_or_ge i n with h1 | h1
    · rw [get!_push_lt' _ _ (by rw [hs]; exact h1), hk i h1]
    · have e : i = keys.size := by rw [hs]; omega
      rw [e, get!_push_eq', hs]
  · rw [Std.HashMap.getElem?_insert]
    rcases Nat.lt_or_ge i n with h1 | h1
    · rw [hne i h1]
      exact hi1 i h1
    · have e : i = n := by omega
      rw [e, beq_self_eq_true, if_pos rfl, hs]
  · rw [Std.HashMap.getElem?_insert] at hZ
    split_ifs at hZ with hz
    · rw [beq_iff_eq] at hz
      rw [hs] at hZ
      cases hZ
      exact ⟨by omega, hz⟩
    · have := hi2 Z i hZ
      exact ⟨by omega, this.2⟩
  · rcases Nat.lt_or_ge i n with h1 | h1
    · rw [get!_push_lt' _ _ (by rw [hps]; exact h1), hpk i h1]
    · have e : i = par.size := by rw [hps]; omega
      rw [e, get!_push_eq', hps, hp]
  · rcases Nat.lt_or_ge i n with h1 | h1
    · rw [get!_push_lt' _ _ (by rw [hls]; exact h1), hlk i h1]
    · have e : i = lab.size := by rw [hls]; omega
      rw [e, get!_push_eq', hls, hl]

theorem conjBFS_eq_of {d cap c : ℕ} {A Ai B Bi : Array V} {O : COrbit} {fa fb fp fl : ℕ → ℕ}
    (hok : conjOrbitOK d A Ai B Bi O c = true) (hcap : O.keys.size ≤ cap)
    (hsa : O.alpha.size = O.keys.size) (hsb : O.beta.size = O.keys.size)
    (hsp : O.par.size = O.keys.size) (hsl : O.lab.size = O.keys.size)
    (ha : ∀ i < O.keys.size, ap O.alpha i = fa i) (hb : ∀ i < O.keys.size, ap O.beta i = fb i)
    (hp : ∀ i < O.keys.size, ap O.par i = fp i) (hl : ∀ i < O.keys.size, ap O.lab i = fl i)
    (hbfs : bfsOrderOK fa fb fp fl O.keys.size = true) :
    conjBFS d A Ai B Bi cap = O := by
  unfold conjOrbitOK at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨hpos, -⟩, hroot⟩, hall⟩ := hok
  have hat := parAll_eq_true hall
  have hk : ∀ k < O.keys.size, (indexOf O.keys).getD (keyOf O.keys[k]!) O.keys.size = k ∧
      ap O.alpha k < O.keys.size ∧ conjM d A Ai O.keys[k]! = O.keys[ap O.alpha k]! ∧
      ap O.beta k < O.keys.size ∧ conjM d B Bi O.keys[k]! = O.keys[ap O.beta k]! := by
    intro k hk
    have := hat k hk
    simp only [conjCheckAt, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.or_eq_true]
      at this
    obtain ⟨⟨⟨⟨⟨⟨-, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, -⟩ := this
    exact ⟨h2, h3, eq_of_eqM h4, h5, eq_of_eqM h6⟩
  have hinj : ∀ i < O.keys.size, ∀ j < O.keys.size, keyOf O.keys[i]! = keyOf O.keys[j]! →
      i = j := by
    intro i hi j hj e
    rw [← (hk i hi).1, ← (hk j hj).1, e]
  have hA0 : O.keys[0]! = A := eq_of_eqM hroot
  simp only [bfsOrderOK, bAnd_eqP, Bool.and_eq_true, Nat.beq_eq] at hbfs
  obtain ⟨hp0, hl0, hfold⟩ := hbfs
  have hCN : cnt fa fb fp fl O.keys.size = O.keys.size := by
    rw [foldUp_eqP] at hfold
    exact hfold
  have hCz : ∀ t h, cnt fa fb fp fl h = 0 → cnt fa fb fp fl (h + t) = 0 := by
    intro t
    induction t with
    | zero => intro h e; exact e
    | succ t ih =>
      intro h e
      rw [← Nat.add_assoc, cnt_succ, ih h e]
      exact bfsStep_zero _ _ _ _ _
  have hCne : ∀ h ≤ O.keys.size, cnt fa fb fp fl h ≠ 0 := by
    intro h hh e
    have := hCz (O.keys.size - h) h e
    rw [Nat.add_sub_cancel' hh, hCN] at this
    omega
  have hpar : ∀ n < O.keys.size, ∀ q, fp n = q → O.par[n]! = UInt32.ofNat q := by
    intro n hn q e
    rw [← e, ← hp n hn, ofNat_ap]
  have hlab : ∀ n < O.keys.size, ∀ l, fl n = l → O.lab[n]! = UInt32.ofNat l := by
    intro n hn l e
    rw [← e, ← hl n hn, ofNat_ap]
  obtain ⟨s, hs, hK, hTa, hTb⟩ : ∃ s : Array (Array V) × Std.HashMap (Array (ℕ × ℕ)) ℕ × Table ×
      Table × Table × Table, conjBFS d A Ai B Bi cap =
        ⟨s.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2.1, s.2.2.2.2.2⟩ ∧
      KInv O O.keys.size s.1 s.2.1 s.2.2.2.2.1 s.2.2.2.2.2 ∧ TInv O.alpha s.2.2.1 O.keys.size ∧
      TInv O.beta s.2.2.2.1 O.keys.size := by
    unfold conjBFS
    refine ⟨_, rfl, ?_⟩
    refine forIn_range_loop (fun q (s : Array (Array V) × Std.HashMap (Array (ℕ × ℕ)) ℕ × Table ×
        Table × Table × Table) => q ≤ O.keys.size ∧ cnt fa fb fp fl q ≤ O.keys.size ∧
        KInv O (cnt fa fb fp fl q) s.1 s.2.1 s.2.2.2.2.1 s.2.2.2.2.2 ∧ TInv O.alpha s.2.2.1 q ∧
        TInv O.beta s.2.2.2.1 q)
      (fun (s : Array (Array V) × Std.HashMap (Array (ℕ × ℕ)) ℕ × Table × Table × Table × Table) =>
        KInv O O.keys.size s.1 s.2.1 s.2.2.2.2.1 s.2.2.2.2.2 ∧
        TInv O.alpha s.2.2.1 O.keys.size ∧ TInv O.beta s.2.2.2.1 O.keys.size) _ cap _ ?_ ?_ ?_
    ·
      intro q s hq hI
      obtain ⟨hqN, hcN, hKs, hTas, hTbs⟩ := hI
      rcases Nat.lt_or_ge q O.keys.size with hlt | hge
      · have hn0 : cnt fa fb fp fl (q + 1) ≠ 0 := hCne (q + 1) (by omega)
        have hCs := cnt_succ fa fb fp fl q
        rw [bfsStep_eq] at hCs
        by_cases hqn : q < cnt fa fb fp fl q
        swap
        · rw [if_neg hqn] at hCs
          exact absurd hCs hn0
        rw [if_pos hqn] at hCs
        have hn1z : bfsHit fp fl q 1 (fa q) (cnt fa fb fp fl q) ≠ 0 := by
          intro e
          rw [e, bfsHit_zero] at hCs
          exact hn0 hCs
        have hA := bfsHit_spec hn1z
        rw [hCs] at hn0
        have hB := bfsHit_spec hn0
        obtain ⟨-, haN, hcA, hbN, hcB⟩ := hk q hlt
        have hqs : q < s.1.size := by rw [hKs.1]; exact hqn
        have hX : s.1[q]! = O.keys[q]! := hKs.2.1 q hqn
        simp only [hqs, ↓reduceIte, hX, hcA, hcB]
        have hx := ha q hlt
        have hy := hb q hlt
        rw [← hx] at hA hB hCs
        rw [← hy] at hB hCs
        set n := cnt fa fb fp fl q with hn
        set n1 := bfsHit fp fl q 1 (ap O.alpha q) n with hn1
        have hTa1 : ∀ v, O.alpha[q]! = v → TInv O.alpha (s.2.2.1.push v) (q + 1) :=
          fun v hv => tinv_push hTas hv
        have hTb1 : ∀ v, O.beta[q]! = v → TInv O.beta (s.2.2.2.1.push v) (q + 1) :=
          fun v hv => tinv_push hTbs hv
        have hsz : s.1.size = n := hKs.1
        split
        ·
          rename_i k hka
          obtain ⟨hkx, hxn⟩ := kinv_found hKs hinj hcN haN hka
          subst hkx
          have hn1e : n1 = n := by
            rcases hA with h | h
            · exact h.2
            · omega
          split
          · rename_i k' hkb
            obtain ⟨hky, hyn⟩ := kinv_found hKs hinj hcN hbN hkb
            subst hky
            have hc : cnt fa fb fp fl (q + 1) = n := by
              rcases hB with h | h
              · rw [hCs, h.2, hn1e]
              · omega
            exact ⟨by omega, by omega, hc ▸ hKs, hTa1 _ (ofNat_ap _ _).symm,
              hTb1 _ (ofNat_ap _ _).symm⟩
          · rename_i hkb
            have hB2 : ap O.beta q = n ∧ fp n = q ∧ fl n = 2 ∧
                cnt fa fb fp fl (q + 1) = n + 1 := by
              rcases hB with h | h
              · exact absurd (kinv_absent hKs (by omega) hkb) id
              · exact ⟨by omega, hn1e ▸ h.2.1, hn1e ▸ h.2.2.1, by rw [hCs, h.2.2.2, hn1e]⟩
            obtain ⟨hye, hfp, hfl, hc⟩ := hB2
            have hnN : n < O.keys.size := by omega
            have hK1 := kinv_new hKs hinj hnN (hpar n hnN q hfp)
              ((hlab n hnN 2 hfl).trans rfl)
            rw [hc]
            refine ⟨by omega, by omega, ?_, hTa1 _ (ofNat_ap _ _).symm, hTb1 _ ?_⟩
            · rw [hye]
              exact hK1
            · rw [hsz, ← hye, ofNat_ap]
        ·
          rename_i hka
          have hA2 : ap O.alpha q = n ∧ fp n = q ∧ fl n = 1 ∧ n1 = n + 1 := by
            rcases hA with h | h
            · exact absurd (kinv_absent hKs h.1 hka) id
            · exact h
          obtain ⟨hxe, hfp, hfl, hn1e⟩ := hA2
          have hnN : n < O.keys.size := by omega
          have hK1 := kinv_new hKs hinj hnN (hpar n hnN q hfp) ((hlab n hnN 1 hfl).trans rfl)
          have hTa2 : TInv O.alpha (s.2.2.1.push (UInt32.ofNat s.1.size)) (q + 1) :=
            hTa1 _ (by rw [hsz, ← hxe, ofNat_ap])
          rw [hxe]
          rw [hxe] at hka
          split
          · rename_i k' hkb
            obtain ⟨hky, hyn⟩ := kinv_found hK1 hinj (by omega) hbN hkb
            subst hky
            have hc : cnt fa fb fp fl (q + 1) = n + 1 := by
              rcases hB with h | h
              · rw [hCs, h.2, hn1e]
              · omega
            exact ⟨by omega, by omega, hc ▸ hK1, hTa2, hTb1 _ (ofNat_ap _ _).symm⟩
          · rename_i hkb
            have hB2 : ap O.beta q = n + 1 ∧ fp (n + 1) = q ∧ fl (n + 1) = 2 ∧
                cnt fa fb fp fl (q + 1) = n + 2 := by
              rcases hB with h | h
              · exact absurd (kinv_absent hK1 (by omega) hkb) id
              · exact ⟨by omega, hn1e ▸ h.2.1, hn1e ▸ h.2.2.1, by rw [hCs, h.2.2.2, hn1e]⟩
            obtain ⟨hye, hfp2, hfl2, hc⟩ := hB2
            have hnN2 : n + 1 < O.keys.size := by omega
            have hK2 := kinv_new hK1 hinj hnN2 (hpar (n + 1) hnN2 q hfp2)
              ((hlab (n + 1) hnN2 2 hfl2).trans rfl)
            rw [hc]
            refine ⟨by omega, by omega, ?_, hTa2, hTb1 _ ?_⟩
            · rw [hye]
              exact hK2
            · rw [Array.size_push, hsz, ← hye, ofNat_ap]
      ·
        have e : q = O.keys.size := by omega
        have hqs : ¬ q < s.1.size := by rw [hKs.1, e, hCN]; omega
        simp only [hqs, ↓reduceIte]
        rw [e, hCN] at hKs
        rw [e] at hTas hTbs
        clear hcN
        exact ⟨hKs, hTas, hTbs⟩
    ·
      intro b hb
      have e : cap = O.keys.size := by omega
      rw [e, hCN] at hb
      exact hb.2.2
    ·
      have hc0 : cnt fa fb fp fl 0 = 1 := rfl
      refine ⟨Nat.zero_le _, by rw [hc0]; omega, ⟨rfl, fun i hi => ?_, fun i hi => ?_,
        fun Z i hZ => ?_, rfl, fun i hi => ?_, rfl, fun i hi => ?_⟩,
        ⟨rfl, fun i hi => absurd hi (Nat.not_lt_zero _)⟩,
        ⟨rfl, fun i hi => absurd hi (Nat.not_lt_zero _)⟩⟩
      all_goals dsimp only at *
      · have hi0 : i = 0 := by rw [hc0] at hi; omega
        subst hi0
        simp [hA0]
      · have hi0 : i = 0 := by rw [hc0] at hi; omega
        subst hi0
        simp [hA0]
      · simp only [Std.HashMap.getElem?_insert, Std.HashMap.getElem?_empty] at hZ
        split_ifs at hZ with hz
        simp only [Option.some.injEq] at hZ
        subst hZ
        refine ⟨by rw [hc0]; omega, ?_⟩
        rw [hA0]
        exact beq_iff_eq.1 hz
      · have hi0 : i = 0 := by rw [hc0] at hi; omega
        subst hi0
        rw [hpar 0 hpos 0 hp0]
        rfl
      · have hi0 : i = 0 := by rw [hc0] at hi; omega
        subst hi0
        rw [hlab 0 hpos 0 hl0]
        rfl
  have hkeys : s.1 = O.keys := by
    refine Array.ext hK.1 fun i h1 h2 => ?_
    have := hK.2.1 i (by rw [← hK.1]; exact h1)
    rwa [getElem!_pos _ i h1, getElem!_pos _ i h2] at this
  have htab : ∀ (T a : Table), T.size = O.keys.size → TInv T a O.keys.size → a = T := by
    intro T a hT H
    refine Array.ext (by rw [H.1, hT]) fun i h1 h2 => ?_
    have := H.2 i (by rw [← H.1]; exact h1)
    rwa [getElem!_pos _ i h1, getElem!_pos _ i h2] at this
  rw [hs, hkeys, htab _ _ hsa hTa, htab _ _ hsb hTb,
    htab _ _ hsp ⟨hK.2.2.2.2.1, hK.2.2.2.2.2.1⟩, htab _ _ hsl ⟨hK.2.2.2.2.2.2.1, hK.2.2.2.2.2.2.2⟩]

end CFSG.F3.Native.BfsSpec
