module

public import Certificates.Data.CFSGNative.Suz.W64
public import CFSG.F3.ConjBFS
import CFSG.Certificates.Kernel.SporSch.LyLoop

public section

namespace CFSG.Sporadic.Suz.Native.BfsSpec

open CFSG.Sporadic.Suz.Native CFSG.Sporadic.Th.Native CFSG.KC.F3Bfs CFSG.F3.Native.BfsSpec
  CFSG.KC.Enum CFSG.KS.SporSch.LyLoop

theorem ofNat_ne_none32 {v : Nat} (hv : v < 4294967295) : (UInt32.ofNat v == none32) = false := by
  rw [beq_eq_false_iff_ne]
  intro e
  have h := congrArg UInt32.toNat e
  rw [UInt32.toNat_ofNat_of_lt' (by change v < 4294967296; omega)] at h
  have h2 : (none32 ()).toNat = 4294967295 := rfl
  omega

theorem getT_push_lt {t : Table} {v : UInt32} {i : Nat} (h : i < t.size) :
    getT (t.push v) i = getT t i := by
  unfold getT
  rw [Array.getElem?_push, if_neg (by omega)]

theorem getT_push_none (t : Table) (i : Nat) :
    getT (t.push none32) i = if i < t.size then getT t i else none := by
  split
  · exact getT_push_lt (by assumption)
  · rename_i hi
    unfold getT
    by_cases e : i = t.size
    · rw [Array.getElem?_push, if_pos e]
      simp
    · rw [Array.getElem?_push, if_neg e, Array.getElem?_eq_none (by omega)]

theorem getT_set {t : Table} {i v k : Nat} (h : i < t.size) (hv : v < 4294967295) :
    getT (t.set! i (UInt32.ofNat v)) k = if i = k then some v else getT t k := by
  unfold getT
  rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  by_cases e : i = k
  · rw [if_pos e, if_pos h, if_pos e]
    simp only [ofNat_ne_none32 hv, Bool.false_eq_true, ↓reduceIte]
    rw [UInt32.toNat_ofNat_of_lt' (by change v < 4294967296; omega)]
  · rw [if_neg e, if_neg e]

theorem size_set' (t : Table) (i : Nat) (v : UInt32) : (t.set! i v).size = t.size := by
  rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]

theorem getT_lt {t : Table} {i v : Nat} (h : getT t i = some v) : i < t.size := by
  unfold getT at h
  split at h
  · rename_i x hx
    exact (Array.getElem?_eq_some_iff.1 hx).1
  · simp at h

theorem getT_isSome_lt {t : Table} {i : Nat} (h : (getT t i).isSome) : i < t.size := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 h
  exact getT_lt hv

theorem getT_set_some {t : Table} {i k v : Nat} (hi : i < t.size) (hv : v < 4294967295)
    (h : (getT t k).isSome) : (getT (t.set! i (UInt32.ofNat v)) k).isSome := by
  rw [getT_set hi hv]
  split
  · rfl
  · exact h

theorem getT_push_some {t : Table} {k : Nat} (v : UInt32) (h : (getT t k).isSome) :
    (getT (t.push v) k).isSome := by
  rw [getT_push_lt (getT_isSome_lt h)]
  exact h

theorem tab_eq {t T : Table} (hs : t.size = T.size) (h : ∀ k < T.size, getT t k = some (ap T k)) :
    t = T := by
  refine Array.ext hs fun i h1 h2 => ?_
  have e := h i h2
  unfold getT at e
  rw [Array.getElem?_eq_getElem h1] at e
  simp only at e
  split at e
  · simp at e
  · have e' : t[i].toNat = T[i]!.toNat := Option.some.inj e
    rw [getElem!_pos T i h2] at e'
    exact UInt32.toNat_inj.1 e'

@[expose] def LoopStepW {β : Type} (I Q : β → Prop) : ForInStep β → Prop
  | .yield b => I b
  | .done b => Q b

theorem forIn_range'_loopW {β : Type} (I : Nat → β → Prop) (Q : β → Prop)
    (f : Nat → β → Id (ForInStep β)) : ∀ (m s : Nat) (b : β),
    (∀ q b, s ≤ q → q < s + m → I q b → LoopStepW (I (q + 1)) Q (f q b)) →
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
      exact forIn_range'_loopW I Q f m (s + 1) b'
        (fun q b h1 h2 h3 => hstep q b (by omega) (by omega) h3)
        (fun b hb => hend b (by rwa [e])) hs

theorem forIn_range_loopW {β : Type} (I : Nat → β → Prop) (Q : β → Prop)
    (f : Nat → β → Id (ForInStep β)) (n : Nat) (b : β)
    (hstep : ∀ q b, q < n → I q b → LoopStepW (I (q + 1)) Q (f q b))
    (hend : ∀ b, I n b → Q b) (h0 : I 0 b) : Q (forIn [:n] b f) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  have hs : Std.Legacy.Range.size [:n] = n := by simp [Std.Legacy.Range.size]
  simp only [hs]
  exact forIn_range'_loopW I Q f n 0 b (fun q b _ h2 h3 => hstep q b (by omega) h3)
    (fun b hb => hend b (by simpa using hb)) h0

theorem parMapRange_eq {α : Type} (lo hi chunks : Nat) (f : Nat → α) :
    parMapRange lo hi chunks f = (Array.range (hi - lo)).map fun i => f (lo + i) := by
  unfold parMapRange
  simp only [List.foldl_map]
  have key : ∀ m, (List.range m).foldl (fun acc t => acc ++ (Array.range
      (min hi (lo + t * ((hi - lo + (chunks + 1) - 1) / (chunks + 1)) +
        (hi - lo + (chunks + 1) - 1) / (chunks + 1)) - (lo + t * ((hi - lo + (chunks + 1) - 1) /
          (chunks + 1))))).map (fun i => f (lo + t * ((hi - lo + (chunks + 1) - 1) /
            (chunks + 1)) + i))) #[] =
      (Array.range (min hi (lo + m * ((hi - lo + (chunks + 1) - 1) / (chunks + 1))) - lo)).map
        fun i => f (lo + i) := by
    intro m
    induction m with
    | zero =>
      simp
      omega
    | succ m ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih]
      generalize (hi - lo + (chunks + 1) - 1) / (chunks + 1) = per
      rcases Nat.lt_or_ge hi (lo + m * per) with h | h
      · have e1 : min hi (lo + m * per + per) - (lo + m * per) = 0 := by omega
        have e2 : min hi (lo + (m + 1) * per) - lo = min hi (lo + m * per) - lo := by
          rw [Nat.succ_mul]
          omega
        rw [e1, e2]
        simp
      · have e2 : min hi (lo + (m + 1) * per) - lo = min hi (lo + m * per) - lo +
            (min hi (lo + m * per + per) - (lo + m * per)) := by
          rw [Nat.succ_mul]
          omega
        have e3 : min hi (lo + m * per) - lo = m * per := by omega
        rw [e2, Array.range_add, Array.map_append, Array.map_map, e3]
        congr 1
        congr 1
        funext i
        simp only [Function.comp, Nat.add_assoc]
  have hk := key (chunks + 1)
  have hc : hi - lo ≤ (chunks + 1) * ((hi - lo + (chunks + 1) - 1) / (chunks + 1)) := by
    have h1 := Nat.div_add_mod (hi - lo + (chunks + 1) - 1) (chunks + 1)
    have h2 := Nat.mod_lt (hi - lo + (chunks + 1) - 1) (by omega : 0 < chunks + 1)
    omega
  have e : min hi (lo + (chunks + 1) * ((hi - lo + (chunks + 1) - 1) / (chunks + 1))) - lo =
      hi - lo := by omega
  rw [e] at hk
  exact hk

def KW (O : WOrbit) (n : Nat) (keys : Array (Array W)) (index : Std.HashMap (Array W) Nat)
    (par lab : Table) : Prop :=
  keys.size = n ∧ (∀ i < n, keys[i]! = O.keys[i]!) ∧ (∀ i < n, index[O.keys[i]!]? = some i) ∧
    (∀ Z i, index[Z]? = some i → i < n ∧ O.keys[i]! = Z) ∧
    par.size = n ∧ (∀ i < n, par[i]! = O.par[i]!) ∧ lab.size = n ∧ (∀ i < n, lab[i]! = O.lab[i]!)

theorem kw_found {O : WOrbit} {n : Nat} {keys : Array (Array W)}
    {index : Std.HashMap (Array W) Nat} {par lab : Table} (H : KW O n keys index par lab)
    (hinj : ∀ i < O.keys.size, ∀ j < O.keys.size, O.keys[i]! = O.keys[j]! → i = j)
    (hn : n ≤ O.keys.size) {x k : Nat} (hx : x < O.keys.size)
    (hk : index[O.keys[x]!]? = some k) : k = x ∧ x < n := by
  obtain ⟨h1, h2⟩ := H.2.2.2.1 _ _ hk
  have := hinj k (by omega) x hx h2
  exact ⟨this, this ▸ h1⟩

theorem kw_absent {O : WOrbit} {n : Nat} {keys : Array (Array W)}
    {index : Std.HashMap (Array W) Nat} {par lab : Table} (H : KW O n keys index par lab)
    {x : Nat} (hx : x < n) (hk : index[O.keys[x]!]? = none) : False := by
  rw [H.2.2.1 x hx] at hk
  simp at hk

theorem kw_new {O : WOrbit} {n : Nat} {keys : Array (Array W)}
    {index : Std.HashMap (Array W) Nat} {par lab : Table} (H : KW O n keys index par lab)
    (hinj : ∀ i < O.keys.size, ∀ j < O.keys.size, O.keys[i]! = O.keys[j]! → i = j)
    (hn : n < O.keys.size) {p l : UInt32} (hp : O.par[n]! = p) (hl : O.lab[n]! = l) :
    KW O (n + 1) (keys.push O.keys[n]!) (index.insert O.keys[n]! keys.size)
      (par.push p) (lab.push l) := by
  obtain ⟨hs, hk, hi1, hi2, hps, hpk, hls, hlk⟩ := H
  have hne : ∀ i < n, (O.keys[n]! == O.keys[i]!) = false := by
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
    by_cases hz : (O.keys[n]! == Z) = true
    · rw [if_pos hz] at hZ
      rw [beq_iff_eq] at hz
      rw [hs] at hZ
      cases hZ
      exact ⟨by omega, hz⟩
    · rw [if_neg hz] at hZ
      have := hi2 Z i hZ
      exact ⟨by omega, this.2⟩
  · rcases Nat.lt_or_ge i n with h1 | h1
    · rw [get!_push_lt' _ _ (by rw [hps]; exact h1), hpk i h1]
    · have e : i = par.size := by rw [hps]; omega
      rw [e, get!_push_eq', hps, hp]
  · rcases Nat.lt_or_ge i n with h1 | h1
    · rw [get!_push_lt' _ _ (by rw [hls]; exact h1), hlk i h1]
    · have e : i = lab.size := by rw [hls]; omega
      rw [e, get!_push_eq', hls, hl]

def SInv (O : WOrbit) (qa qb n : Nat) (al bi : Table) (keys : Array (Array W))
    (index : Std.HashMap (Array W) Nat) (alpha beta binv par lab : Table) : Prop :=
  KW O n keys index par lab ∧ alpha.size = n ∧
    (∀ k < n, getT alpha k = none ∨ (getT alpha k = some (ap O.alpha k) ∧ ap O.alpha k < n)) ∧
    (∀ k < qa, getT alpha k = some (ap O.alpha k)) ∧
    beta.size = n ∧ (∀ k < qb, getT beta k = some (ap O.beta k)) ∧
    binv.size = n ∧ (∀ k p, getT binv k = some p → p < qb ∧ ap O.beta p = k) ∧
    (∀ k, (getT al k).isSome → (getT alpha k).isSome) ∧
    (∀ k p, getT bi k = some p → getT binv k = some p)

structure Hyp (O : WOrbit) : Prop where
  hN : O.keys.size < 4294967295
  inv : ∀ k < O.keys.size, ap O.alpha (ap O.alpha k) = k
  ord : ∀ k < O.keys.size, ap O.beta (ap O.beta (ap O.beta k)) = k
  inj : ∀ i < O.keys.size, ∀ j < O.keys.size, O.keys[i]! = O.keys[j]! → i = j
  alt : ∀ k < O.keys.size, ap O.alpha k < O.keys.size
  blt : ∀ k < O.keys.size, ap O.beta k < O.keys.size

theorem Hyp.binj {O : WOrbit} (hO : Hyp O) {a b : Nat} (ha : a < O.keys.size)
    (hb : b < O.keys.size) (e : ap O.beta a = ap O.beta b) : a = b := by
  rw [← hO.ord a ha, ← hO.ord b hb, e]

theorem sinv_reset {O : WOrbit} {qa qb n : Nat} {al bi : Table} {keys : Array (Array W)}
    {index : Std.HashMap (Array W) Nat} {alpha beta binv par lab : Table}
    (H : SInv O qa qb n al bi keys index alpha beta binv par lab) :
    SInv O qa qb n alpha binv keys index alpha beta binv par lab :=
  ⟨H.1, H.2.1, H.2.2.1, H.2.2.2.1, H.2.2.2.2.1, H.2.2.2.2.2.1, H.2.2.2.2.2.2.1,
    H.2.2.2.2.2.2.2.1, fun _ h => h, fun _ _ h => h⟩

theorem getT_some_of_isSome {t : Table} {k : Nat} (h : (getT t k).isSome) :
    ∃ v, getT t k = some v := Option.isSome_iff_exists.1 h

theorem stepA_skip {O : WOrbit} {h n : Nat} {al bi : Table} {keys : Array (Array W)}
    {index : Std.HashMap (Array W) Nat} {alpha beta binv par lab : Table}
    (H : SInv O h h n al bi keys index alpha beta binv par lab) (hhn : h < n)
    (hs : (getT alpha h).isSome) :
    SInv O (h + 1) h n al bi keys index alpha beta binv par lab ∧ ap O.alpha h < n := by
  obtain ⟨hK, hsa, ha3, ha4, hrest⟩ := H
  have e : getT alpha h = some (ap O.alpha h) ∧ ap O.alpha h < n := by
    rcases ha3 h hhn with e | e
    · rw [e] at hs
      simp at hs
    · exact e
  refine ⟨⟨hK, hsa, ha3, fun k hk => ?_, hrest⟩, e.2⟩
  rcases Nat.lt_or_ge k h with h1 | h1
  · exact ha4 k h1
  · have : k = h := by omega
    rw [this]
    exact e.1

theorem stepA_found {O : WOrbit} (hO : Hyp O) {h n : Nat} {al bi : Table}
    {keys : Array (Array W)} {index : Std.HashMap (Array W) Nat} {alpha beta binv par lab : Table}
    (H : SInv O h h n al bi keys index alpha beta binv par lab) (hhn : h < n)
    (hn : n ≤ O.keys.size) (hfa : ap O.alpha h < n) :
    SInv O (h + 1) h n al bi keys index
      ((alpha.set! h (UInt32.ofNat (ap O.alpha h))).set! (ap O.alpha h) (UInt32.ofNat h))
      beta binv par lab := by
  obtain ⟨hK, hsa, ha3, ha4, hb1, hb2, hc1, hc2, hm1, hm2⟩ := H
  have hN := hO.hN
  have hinv := hO.inv h (by omega)
  have hs1 : (alpha.set! h (UInt32.ofNat (ap O.alpha h))).size = n := by rw [size_set', hsa]
  have hget : ∀ k, getT ((alpha.set! h (UInt32.ofNat (ap O.alpha h))).set! (ap O.alpha h)
      (UInt32.ofNat h)) k = if ap O.alpha h = k then some h else
        if h = k then some (ap O.alpha h) else getT alpha k := by
    intro k
    rw [getT_set (by rw [hs1]; exact hfa) (by omega), getT_set (by rw [hsa]; exact hhn) (by omega)]
  refine ⟨hK, by rw [size_set', hs1], fun k hk => ?_, fun k hk => ?_, hb1, hb2, hc1, hc2,
    fun k hk => ?_, hm2⟩
  · rw [hget]
    by_cases e1 : ap O.alpha h = k
    · rw [if_pos e1]
      subst e1
      exact Or.inr ⟨by rw [hinv], by rw [hinv]; exact hhn⟩
    · rw [if_neg e1]
      by_cases e2 : h = k
      · rw [if_pos e2]
        subst e2
        exact Or.inr ⟨rfl, hfa⟩
      · rw [if_neg e2]
        exact ha3 k hk
  · rw [hget]
    by_cases e1 : ap O.alpha h = k
    · rw [if_pos e1]
      subst e1
      rw [hinv]
    · rw [if_neg e1]
      by_cases e2 : h = k
      · rw [if_pos e2]
        subst e2
        rfl
      · rw [if_neg e2]
        exact ha4 k (by omega)
  · rw [hget]
    by_cases e1 : ap O.alpha h = k
    · rw [if_pos e1]
      rfl
    · rw [if_neg e1]
      by_cases e2 : h = k
      · rw [if_pos e2]
        rfl
      · rw [if_neg e2]
        exact hm1 k hk

theorem stepA_new {O : WOrbit} (hO : Hyp O) {h n : Nat} {al bi : Table}
    {keys : Array (Array W)} {index : Std.HashMap (Array W) Nat} {alpha beta binv par lab : Table}
    (H : SInv O h h n al bi keys index alpha beta binv par lab) (hhn : h < n)
    (hnN : n < O.keys.size) (hfa : ap O.alpha h = n) (hp : O.par[n]! = UInt32.ofNat h)
    (hl : O.lab[n]! = 1) :
    SInv O (h + 1) h (n + 1) al bi (keys.push O.keys[n]!) (index.insert O.keys[n]! keys.size)
      (((alpha.push none32).set! h (UInt32.ofNat keys.size)).set! keys.size (UInt32.ofNat h))
      (beta.push none32) (binv.push none32) (par.push (UInt32.ofNat h)) (lab.push 1) := by
  obtain ⟨hK, hsa, ha3, ha4, hb1, hb2, hc1, hc2, hm1, hm2⟩ := H
  have hN := hO.hN
  have hks : keys.size = n := hK.1
  have hinv := hO.inv h (by omega)
  rw [hfa] at hinv
  rw [hks]
  have hs1 : ((alpha.push none32).set! h (UInt32.ofNat n)).size = n + 1 := by
    rw [size_set', Array.size_push, hsa]
  have hget : ∀ k, getT (((alpha.push none32).set! h (UInt32.ofNat n)).set! n
      (UInt32.ofNat h)) k = if n = k then some h else
        if h = k then some n else if k < n then getT alpha k else none := by
    intro k
    rw [getT_set (by rw [hs1]; omega) (by omega),
      getT_set (by rw [Array.size_push, hsa]; omega) (by omega), getT_push_none, hsa]
  have hK1 := kw_new hK hO.inj hnN hp hl
  rw [hks] at hK1
  refine ⟨hK1, by rw [size_set', hs1], fun k hk => ?_, fun k hk => ?_,
    by rw [Array.size_push, hb1], fun k hk => ?_, by rw [Array.size_push, hc1], fun k p hkp => ?_,
    fun k hk => ?_, fun k p hkp => ?_⟩
  · rw [hget]
    by_cases e1 : n = k
    · rw [if_pos e1]
      subst e1
      exact Or.inr ⟨by rw [hinv], by rw [hinv]; omega⟩
    · rw [if_neg e1]
      by_cases e2 : h = k
      · rw [if_pos e2]
        subst e2
        exact Or.inr ⟨by rw [hfa], by rw [hfa]; omega⟩
      · rw [if_neg e2, if_pos (by omega : k < n)]
        rcases ha3 k (by omega) with e | e
        · exact Or.inl e
        · exact Or.inr ⟨e.1, by omega⟩
  · rw [hget, if_neg (by omega : ¬ n = k)]
    by_cases e2 : h = k
    · rw [if_pos e2]
      subst e2
      rw [hfa]
    · rw [if_neg e2, if_pos (by omega : k < n)]
      exact ha4 k (by omega)
  · rw [getT_push_lt (by rw [hb1]; omega)]
    exact hb2 k hk
  · rw [getT_push_none] at hkp
    by_cases e : k < binv.size
    · rw [if_pos e] at hkp
      exact hc2 k p hkp
    · rw [if_neg e] at hkp
      simp at hkp
  · rw [hget]
    by_cases e1 : n = k
    · rw [if_pos e1]
      rfl
    · rw [if_neg e1]
      by_cases e2 : h = k
      · rw [if_pos e2]
        rfl
      · have := getT_isSome_lt (hm1 k hk)
        rw [if_neg e2, if_pos (by omega : k < n)]
        exact hm1 k hk
  · have e := hm2 k p hkp
    rw [getT_push_lt (getT_lt e)]
    exact e

theorem stepB_derived {O : WOrbit} (hO : Hyp O) {h n : Nat} {al bi : Table}
    {keys : Array (Array W)} {index : Std.HashMap (Array W) Nat} {alpha beta binv par lab : Table}
    (H : SInv O (h + 1) h n al bi keys index alpha beta binv par lab) (hhn : h < n)
    (hn : n ≤ O.keys.size) {p r : Nat} (hp : getT binv h = some p) (hr : getT binv p = some r) :
    SInv O (h + 1) (h + 1) n al bi keys index alpha (beta.set! h (UInt32.ofNat r)) binv par lab ∧
      ap O.beta h = r ∧ r < h := by
  obtain ⟨hK, hsa, ha3, ha4, hb1, hb2, hc1, hc2, hm1, hm2⟩ := H
  have hN := hO.hN
  obtain ⟨hp1, hp2⟩ := hc2 h p hp
  obtain ⟨hr1, hr2⟩ := hc2 p r hr
  have hbr : ap O.beta h = r := by
    have := hO.ord r (by omega)
    rw [hr2, hp2] at this
    exact this
  refine ⟨⟨hK, hsa, ha3, ha4, by rw [size_set', hb1], fun k hk => ?_, hc1,
    fun k q hkq => ?_, hm1, hm2⟩, hbr, hr1⟩
  · rw [getT_set (by rw [hb1]; exact hhn) (by omega)]
    by_cases e : h = k
    · rw [if_pos e]
      subst e
      rw [hbr]
    · rw [if_neg e]
      exact hb2 k (by omega)
  · have := hc2 k q hkq
    exact ⟨by omega, this.2⟩

theorem stepB_found {O : WOrbit} (hO : Hyp O) {h n : Nat} {al bi : Table}
    {keys : Array (Array W)} {index : Std.HashMap (Array W) Nat} {alpha beta binv par lab : Table}
    (H : SInv O (h + 1) h n al bi keys index alpha beta binv par lab) (hhn : h < n)
    (hn : n ≤ O.keys.size) (hfb : ap O.beta h < n) :
    SInv O (h + 1) (h + 1) n al bi keys index alpha
      (beta.set! h (UInt32.ofNat (ap O.beta h))) (binv.set! (ap O.beta h) (UInt32.ofNat h))
      par lab := by
  obtain ⟨hK, hsa, ha3, ha4, hb1, hb2, hc1, hc2, hm1, hm2⟩ := H
  have hN := hO.hN
  refine ⟨hK, hsa, ha3, ha4, by rw [size_set', hb1], fun k hk => ?_, by rw [size_set', hc1],
    fun k q hkq => ?_, hm1, fun k q hkq => ?_⟩
  · rw [getT_set (by rw [hb1]; exact hhn) (by omega)]
    by_cases e : h = k
    · rw [if_pos e]
      subst e
      rfl
    · rw [if_neg e]
      exact hb2 k (by omega)
  · rw [getT_set (by rw [hc1]; exact hfb) (by omega)] at hkq
    by_cases e : ap O.beta h = k
    · rw [if_pos e] at hkq
      cases hkq
      exact ⟨by omega, e⟩
    · rw [if_neg e] at hkq
      have := hc2 k q hkq
      exact ⟨by omega, this.2⟩
  · have e1 := hm2 k q hkq
    rw [getT_set (by rw [hc1]; exact hfb) (by omega)]
    by_cases e : ap O.beta h = k
    · rw [if_pos e]
      obtain ⟨hq1, hq2⟩ := hc2 k q e1
      have := hO.binj (by omega) (by omega) (hq2.trans e.symm)
      rw [this]
    · rw [if_neg e]
      exact e1

theorem stepB_new {O : WOrbit} (hO : Hyp O) {h n : Nat} {al bi : Table}
    {keys : Array (Array W)} {index : Std.HashMap (Array W) Nat} {alpha beta binv par lab : Table}
    (H : SInv O (h + 1) h n al bi keys index alpha beta binv par lab) (hhn : h < n)
    (hnN : n < O.keys.size) (hfb : ap O.beta h = n) (hp : O.par[n]! = UInt32.ofNat h)
    (hl : O.lab[n]! = 2) :
    SInv O (h + 1) (h + 1) (n + 1) al bi (keys.push O.keys[n]!)
      (index.insert O.keys[n]! keys.size) (alpha.push none32)
      ((beta.push none32).set! h (UInt32.ofNat keys.size))
      ((binv.push none32).set! keys.size (UInt32.ofNat h)) (par.push (UInt32.ofNat h))
      (lab.push 2) := by
  obtain ⟨hK, hsa, ha3, ha4, hb1, hb2, hc1, hc2, hm1, hm2⟩ := H
  have hN := hO.hN
  have hks : keys.size = n := hK.1
  have hK1 := kw_new hK hO.inj hnN hp hl
  rw [hks] at hK1
  rw [hks]
  refine ⟨hK1, by rw [Array.size_push, hsa], fun k hk => ?_, fun k hk => ?_,
    by rw [size_set', Array.size_push, hb1], fun k hk => ?_,
    by rw [size_set', Array.size_push, hc1], fun k q hkq => ?_, fun k hk => ?_, fun k q hkq => ?_⟩
  · rw [getT_push_none, hsa]
    by_cases e : k < n
    · rw [if_pos e]
      rcases ha3 k e with e' | e'
      · exact Or.inl e'
      · exact Or.inr ⟨e'.1, by omega⟩
    · rw [if_neg e]
      exact Or.inl rfl
  · rw [getT_push_lt (by rw [hsa]; omega)]
    exact ha4 k hk
  · rw [getT_set (by rw [Array.size_push, hb1]; omega) (by omega)]
    by_cases e : h = k
    · rw [if_pos e]
      subst e
      rw [hfb]
    · rw [if_neg e, getT_push_lt (by rw [hb1]; omega)]
      exact hb2 k (by omega)
  · rw [getT_set (by rw [Array.size_push, hc1]; omega) (by omega), getT_push_none, hc1] at hkq
    by_cases e : n = k
    · rw [if_pos e] at hkq
      cases hkq
      exact ⟨by omega, by rw [hfb]; exact e⟩
    · rw [if_neg e] at hkq
      by_cases e2 : k < n
      · rw [if_pos e2] at hkq
        have := hc2 k q hkq
        exact ⟨by omega, this.2⟩
      · rw [if_neg e2] at hkq
        cases hkq
  · exact getT_push_some _ (hm1 k hk)
  · have e1 := hm2 k q hkq
    have hk := getT_lt e1
    rw [getT_set (by rw [Array.size_push, hc1]; omega) (by omega), if_neg (by omega),
      getT_push_lt hk]
    exact e1

theorem imgA_some {al alpha : Table} {h : Nat} {X : Array W}
    (hm1 : ∀ k, (getT al k).isSome → (getT alpha k).isSome) (hn : (getT alpha h).isNone) :
    (if (getT al h).isSome = true then none else some X) = some X := by
  have e : (getT al h).isSome = false := by
    cases e : (getT al h).isSome
    · rfl
    · have := hm1 h e
      rw [Option.isNone_iff_eq_none] at hn
      rw [hn] at this
      cases this
  rw [e]
  rfl

theorem imgB_some {bi binv : Table} {h : Nat} {X : Array W}
    (hm2 : ∀ k p, getT bi k = some p → getT binv k = some p)
    (hd : ∀ p, getT binv h = some p → getT binv p = none) :
    (match getT bi h with
      | some p => if (getT bi p).isSome = true then none else some X
      | none => some X) = some X := by
  rcases e : getT bi h with _ | p
  · rfl
  · have h1 := hd p (hm2 h p e)
    have h2 : (getT bi p).isSome = false := by
      rcases e2 : getT bi p with _ | r
      · rfl
      · rw [hm2 p r e2] at h1
        cases h1
    simp only [h2, Bool.false_eq_true, ↓reduceIte]

theorem getElem!_map_range {α : Type} [Inhabited α] {n i : Nat} (g : Nat → α) (h : i < n) :
    ((Array.range n).map g)[i]! = g i := by
  rw [getElem!_pos _ _ (by rw [Array.size_map, Array.size_range]; exact h), Array.getElem_map,
    Array.getElem_range]

theorem loop_bind {β γ : Type} {P : β → Prop} {R : γ → Prop} (x : Id β) (f : β → Id γ)
    (hx : P x) (hf : ∀ b, P b → R (f b)) : R (x >>= f) := hf x hx

theorem bfs_facts {fa fb fp fl : Nat → Nat} {N : Nat} (hbfs : bfsOrderOK fa fb fp fl N = true) :
    fp 0 = 0 ∧ fl 0 = 0 ∧ cnt fa fb fp fl N = N ∧ ∀ q < N, q < cnt fa fb fp fl q ∧
      ((fa q < cnt fa fb fp fl q ∧ bfsHit fp fl q 1 (fa q) (cnt fa fb fp fl q) =
          cnt fa fb fp fl q) ∨
        (fa q = cnt fa fb fp fl q ∧ fp (cnt fa fb fp fl q) = q ∧ fl (cnt fa fb fp fl q) = 1 ∧
          bfsHit fp fl q 1 (fa q) (cnt fa fb fp fl q) = cnt fa fb fp fl q + 1)) ∧
      ((fb q < bfsHit fp fl q 1 (fa q) (cnt fa fb fp fl q) ∧
          cnt fa fb fp fl (q + 1) = bfsHit fp fl q 1 (fa q) (cnt fa fb fp fl q)) ∨
        (fb q = bfsHit fp fl q 1 (fa q) (cnt fa fb fp fl q) ∧
          fp (bfsHit fp fl q 1 (fa q) (cnt fa fb fp fl q)) = q ∧
          fl (bfsHit fp fl q 1 (fa q) (cnt fa fb fp fl q)) = 2 ∧
          cnt fa fb fp fl (q + 1) = bfsHit fp fl q 1 (fa q) (cnt fa fb fp fl q) + 1)) := by
  simp only [bfsOrderOK, bAnd_eqP, Bool.and_eq_true, Nat.beq_eq] at hbfs
  obtain ⟨hp0, hl0, hfold⟩ := hbfs
  have hCN : cnt fa fb fp fl N = N := by
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
  have hCne : ∀ h ≤ N, cnt fa fb fp fl h ≠ 0 := by
    intro h hh e
    have := hCz (N - h) h e
    rw [Nat.add_sub_cancel' hh, hCN] at this
    have h0 : cnt fa fb fp fl 0 = 1 := rfl
    have hz : h = 0 := by omega
    rw [hz, h0] at e
    exact absurd e (by decide)
  refine ⟨hp0, hl0, hCN, fun q hq => ?_⟩
  have hn0 : cnt fa fb fp fl (q + 1) ≠ 0 := hCne (q + 1) (by omega)
  have hCs := cnt_succ fa fb fp fl q
  rw [bfsStep_eq] at hCs
  have hqn : q < cnt fa fb fp fl q := by
    by_cases hqn : q < cnt fa fb fp fl q
    · exact hqn
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
  rw [← hCs] at hB
  exact ⟨hqn, hA, hB⟩

theorem cnt_step {fa fb fp fl : Nat → Nat} {N : Nat} (hbfs : bfsOrderOK fa fb fp fl N = true)
    {q : Nat} (hq : q < N) : cnt fa fb fp fl q ≤ cnt fa fb fp fl (q + 1) ∧
      fa q < cnt fa fb fp fl (q + 1) ∧ fb q < cnt fa fb fp fl (q + 1) := by
  obtain ⟨-, -, -, h⟩ := bfs_facts hbfs
  obtain ⟨-, hA, hB⟩ := h q hq
  omega

theorem cnt_mono {fa fb fp fl : Nat → Nat} {N : Nat} (hbfs : bfsOrderOK fa fb fp fl N = true)
    {a : Nat} : ∀ t, a + t ≤ N → cnt fa fb fp fl a ≤ cnt fa fb fp fl (a + t)
  | 0, _ => Nat.le_refl _
  | t + 1, h => Nat.le_trans (cnt_mono hbfs t (by omega)) (cnt_step hbfs (by omega)).1

theorem cnt_le {fa fb fp fl : Nat → Nat} {N : Nat} (hbfs : bfsOrderOK fa fb fp fl N = true)
    {q : Nat} (hq : q ≤ N) : 1 ≤ cnt fa fb fp fl q ∧ cnt fa fb fp fl q ≤ N := by
  have h1 := cnt_mono hbfs (a := 0) q (by omega)
  have h2 := cnt_mono hbfs (a := q) (N - q) (by omega)
  rw [Nat.add_sub_cancel' hq, (bfs_facts hbfs).2.2.1] at h2
  have h0 : cnt fa fb fp fl 0 = 1 := rfl
  rw [Nat.zero_add, h0] at h1
  exact ⟨h1, h2⟩

theorem fp_reach {fa fb fp fl : Nat → Nat} {N : Nat} (hbfs : bfsOrderOK fa fb fp fl N = true) :
    ∀ h ≤ N, ∀ k, 0 < k → k < cnt fa fb fp fl h →
      fp k < h ∧ k < cnt fa fb fp fl (fp k + 1)
  | 0, _, k, hk, hk2 => by
    have h0 : cnt fa fb fp fl 0 = 1 := rfl
    omega
  | h + 1, hh, k, hk, hk2 => by
    rcases Nat.lt_or_ge k (cnt fa fb fp fl h) with e | e
    · have := fp_reach hbfs h (by omega) k hk e
      exact ⟨by omega, this.2⟩
    · obtain ⟨-, -, -, hF⟩ := bfs_facts hbfs
      obtain ⟨-, hA, hB⟩ := hF h (by omega)
      have hfk : fp k = h := by
        rcases hA with hA | hA <;> rcases hB with hB | hB
        · omega
        · have : k = bfsHit fp fl h 1 (fa h) (cnt fa fb fp fl h) := by omega
          rw [this]
          exact hB.2.1
        · have : k = cnt fa fb fp fl h := by omega
          rw [this]
          exact hA.2.1
        · rcases Nat.lt_or_ge k (bfsHit fp fl h 1 (fa h) (cnt fa fb fp fl h)) with e2 | e2
          · have : k = cnt fa fb fp fl h := by omega
            rw [this]
            exact hA.2.1
          · have : k = bfsHit fp fl h 1 (fa h) (cnt fa fb fp fl h) := by omega
            rw [this]
            exact hB.2.1
      rw [hfk]
      exact ⟨by omega, hk2⟩

theorem derived_none {t : Table} {h : Nat}
    (hr : (match getT t h with
      | some p => getT t p
      | none => none) = none) : ∀ p, getT t h = some p → getT t p = none := by
  intro p hp
  rw [hp] at hr
  exact hr

theorem fin_step {O : WOrbit} {q c n : Nat} {al bi : Table} {keys : Array (Array W)}
    {index : Std.HashMap (Array W) Nat} {alpha beta binv par lab : Table}
    (H : SInv O (q + 1) (q + 1) n al bi keys index alpha beta binv par lab) (e : c = n) :
    SInv O (q + 1) (q + 1) c al bi keys index alpha beta binv par lab := e ▸ H

set_option hygiene false in
local macro "phaseBsearch" : tactic => `(tactic| (
    split
    · rename_i k hk
      obtain ⟨rfl, hyn⟩ := kw_found H1.1 hinj hn1N (hO.blt _ hq) hk
      have e2 : cnt fa fb fp fl (lo + i + 1) = n1 := by
        rcases hFB with h | h <;> omega
      exact fin_step (stepB_found hO H1 hqn1 hn1N hyn) e2
    · rename_i hk
      have hfb : ap O.beta (lo + i) = n1 ∧ fp n1 = lo + i ∧ fl n1 = 2 ∧
          cnt fa fb fp fl (lo + i + 1) = n1 + 1 := by
        rcases hFB with h | h
        · exact absurd (kw_absent H1.1 h.1 hk) id
        · exact h
      obtain ⟨hfb1, hfp, hfl, e2⟩ := hfb
      have hn1N' : n1 < O.keys.size := by
        have := (cnt_le hbfs (q := lo + i + 1) (by omega)).2
        omega
      rw [hfb1]
      exact fin_step (stepB_new hO H1 hqn1 hn1N' hfb1 (hpar _ hn1N' _ hfp)
        ((hlab _ hn1N' _ hfl).trans rfl)) e2))

set_option hygiene false in
local macro "phaseB" : tactic => `(tactic| (
  have hn1N : n1 ≤ O.keys.size := by
    have := (cnt_le hbfs (q := lo + i + 1) (by omega)).2
    rcases hFB with h | h <;> omega
  have hqn1 : lo + i < n1 := by omega
  split
  · rename_i r hr
    split at hr
    · rename_i p hp
      obtain ⟨H2, hbr, hrq⟩ := stepB_derived hO H1 hqn1 hn1N hp hr
      have e2 : cnt fa fb fp fl (lo + i + 1) = n1 := by
        rcases hFB with h | h <;> omega
      exact fin_step H2 e2
    · cases hr
  · rename_i hr
    have hd := derived_none hr
    have hm2 := H1.2.2.2.2.2.2.2.2.2
    rcases hbs : getT binv (lo + i) with _ | p'
    · simp only [Option.getD_some]
      phaseBsearch
    · have h2 := hd p' (hm2 _ _ hbs)
      rcases hbs2 : getT binv p' with _ | r
      · simp only [hbs2, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, Option.getD_some]
        phaseBsearch
      · rw [hm2 _ _ hbs2] at h2
        cases h2))

theorem conjBFSW_eq_of {d cap chunks : Nat} {R A Ai B Bi : Array W} {O : WOrbit}
    {fa fb fp fl dep : Nat → Nat} (hN : O.keys.size < 4294967295) (hR : O.keys[0]! = R)
    (hsa : O.alpha.size = O.keys.size) (hsb : O.beta.size = O.keys.size)
    (hsp : O.par.size = O.keys.size) (hsl : O.lab.size = O.keys.size)
    (ha : ∀ i < O.keys.size, ap O.alpha i = fa i) (hb : ∀ i < O.keys.size, ap O.beta i = fb i)
    (hp : ∀ i < O.keys.size, ap O.par i = fp i) (hl : ∀ i < O.keys.size, ap O.lab i = fl i)
    (hbfs : bfsOrderOK fa fb fp fl O.keys.size = true)
    (hA : ∀ k < O.keys.size, conjW d A Ai O.keys[k]! = O.keys[ap O.alpha k]!)
    (hB : ∀ k < O.keys.size, conjW d B Bi O.keys[k]! = O.keys[ap O.beta k]!)
    (hinv : ∀ k < O.keys.size, ap O.alpha (ap O.alpha k) = k)
    (hord : ∀ k < O.keys.size, ap O.beta (ap O.beta (ap O.beta k)) = k)
    (hinj : ∀ i < O.keys.size, ∀ j < O.keys.size, O.keys[i]! = O.keys[j]! → i = j)
    (hdep : ∀ k < O.keys.size, dep k < cap)
    (hdp : ∀ k, 0 < k → k < O.keys.size → dep k = dep (fp k) + 1) :
    conjBFSW d R A Ai B Bi cap chunks = O := by
  obtain ⟨hp0, hl0, hCN, hF⟩ := bfs_facts hbfs
  have hO : Hyp O := ⟨hN, hinv, hord, hinj, fun k hk => by
      rw [ha k hk]
      exact Nat.lt_of_lt_of_le (cnt_step hbfs hk).2.1 (cnt_le hbfs hk).2,
    fun k hk => by
      rw [hb k hk]
      exact Nat.lt_of_lt_of_le (cnt_step hbfs hk).2.2 (cnt_le hbfs hk).2⟩
  have hpar : ∀ n < O.keys.size, ∀ q, fp n = q → O.par[n]! = UInt32.ofNat q := by
    intro n hn q e
    rw [← e, ← hp n hn, ofNat_ap]
  have hlab : ∀ n < O.keys.size, ∀ l, fl n = l → O.lab[n]! = UInt32.ofNat l := by
    intro n hn l e
    rw [← e, ← hl n hn, ofNat_ap]
  obtain ⟨s, hs, hQ⟩ : ∃ s : Array (Array W) × Std.HashMap (Array W) Nat × Table × Table ×
      Table × Table × Table × Nat, conjBFSW d R A Ai B Bi cap chunks =
        ⟨s.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2.2.1, s.2.2.2.2.2.2.1⟩ ∧
      SInv O O.keys.size O.keys.size O.keys.size s.2.2.1 s.2.2.2.2.1 s.1 s.2.1 s.2.2.1
        s.2.2.2.1 s.2.2.2.2.1 s.2.2.2.2.2.1 s.2.2.2.2.2.2.1 := by
    unfold conjBFSW
    refine ⟨_, rfl, ?_⟩
    refine forIn_range_loopW (fun t (s : Array (Array W) × Std.HashMap (Array W) Nat × Table ×
        Table × Table × Table × Table × Nat) => s.2.2.2.2.2.2.2 ≤ O.keys.size ∧
        SInv O s.2.2.2.2.2.2.2 s.2.2.2.2.2.2.2 (cnt fa fb fp fl s.2.2.2.2.2.2.2) s.2.2.1
          s.2.2.2.2.1 s.1 s.2.1 s.2.2.1 s.2.2.2.1 s.2.2.2.2.1 s.2.2.2.2.2.1 s.2.2.2.2.2.2.1 ∧
        ∀ k < O.keys.size, dep k < t → k < s.2.2.2.2.2.2.2)
      (fun (s : Array (Array W) × Std.HashMap (Array W) Nat × Table × Table × Table × Table ×
        Table × Nat) => SInv O O.keys.size O.keys.size O.keys.size s.2.2.1 s.2.2.2.2.1 s.1 s.2.1
          s.2.2.1 s.2.2.2.1 s.2.2.2.2.1 s.2.2.2.2.2.1 s.2.2.2.2.2.2.1) _ cap _ ?_ ?_ ?_
    ·
      intro t s ht hI
      obtain ⟨keys, index, alpha, beta, binv, par, lab, lo⟩ := s
      dsimp only at hI ⊢
      obtain ⟨hlo, hS, hD⟩ := hI
      have hks : keys.size = cnt fa fb fp fl lo := hS.1.1
      by_cases hlt : lo < keys.size
      · rw [if_pos hlt]
        have hloN : lo < O.keys.size := by
          rcases Nat.lt_or_ge lo O.keys.size with h | h
          · exact h
          · have e : lo = O.keys.size := by omega
            rw [e, hCN] at hks
            omega
        have hhi : keys.size ≤ O.keys.size := by
          rw [hks]
          exact (cnt_le hbfs hlo).2
        have hkeys0 : ∀ h < keys.size, keys[h]! = O.keys[h]! :=
          fun h hh => hS.1.2.1 h (by rw [← hks]; exact hh)
        rw [parMapRange_eq]
        refine loop_bind (P := fun (s : Array (Array W) × Std.HashMap (Array W) Nat × Table ×
            Table × Table × Table × Table) => SInv O keys.size keys.size
              (cnt fa fb fp fl keys.size) alpha binv s.1 s.2.1 s.2.2.1 s.2.2.2.1 s.2.2.2.2.1
              s.2.2.2.2.2.1 s.2.2.2.2.2.2) _ _ ?_ ?_
        · refine forIn_range_loopW (fun i (s : Array (Array W) × Std.HashMap (Array W) Nat ×
              Table × Table × Table × Table × Table) => SInv O (lo + i) (lo + i)
                (cnt fa fb fp fl (lo + i)) alpha binv s.1 s.2.1 s.2.2.1 s.2.2.2.1 s.2.2.2.2.1
                s.2.2.2.2.2.1 s.2.2.2.2.2.2)
            (fun (s : Array (Array W) × Std.HashMap (Array W) Nat × Table × Table × Table ×
              Table × Table) => SInv O keys.size keys.size (cnt fa fb fp fl keys.size) alpha binv
                s.1 s.2.1 s.2.2.1 s.2.2.2.1 s.2.2.2.2.1 s.2.2.2.2.2.1 s.2.2.2.2.2.2) _ _ _ ?_ ?_ ?_
          ·
            intro i s hi hI
            obtain ⟨keys', index', alpha', beta', binv', par', lab'⟩ := s
            dsimp only at hI ⊢
            rw [getElem!_map_range _ hi]
            dsimp only
            have hq : lo + i < O.keys.size := by omega
            obtain ⟨hqc, hFA, hFB⟩ := hF (lo + i) hq
            rw [← ha _ hq] at hFA hFB
            rw [← hb _ hq] at hFB
            obtain ⟨n1, hn1⟩ : ∃ n1, bfsHit fp fl (lo + i) 1 (ap O.alpha (lo + i))
                (cnt fa fb fp fl (lo + i)) = n1 := ⟨_, rfl⟩
            rw [hn1] at hFA hFB
            have hnN : cnt fa fb fp fl (lo + i) ≤ O.keys.size := (cnt_le hbfs (by omega)).2
            rw [hkeys0 _ (by omega), hA _ hq, hB _ hq]
            by_cases hc : (getT alpha' (lo + i)).isNone = true
            · rw [if_pos hc, imgA_some hI.2.2.2.2.2.2.2.2.1 hc]
              simp only [Option.getD_some]
              split
              · rename_i k hk
                obtain ⟨rfl, hxn⟩ := kw_found hI.1 hinj hnN (hO.alt _ hq) hk
                have e1 : n1 = cnt fa fb fp fl (lo + i) := by
                  rcases hFA with h | h <;> omega
                have H1 := stepA_found hO hI hqc hnN hxn
                rw [← e1] at H1
                phaseB
              · rename_i hk
                have hfa : ap O.alpha (lo + i) = cnt fa fb fp fl (lo + i) ∧
                    fp (cnt fa fb fp fl (lo + i)) = lo + i ∧ fl (cnt fa fb fp fl (lo + i)) = 1 ∧
                    n1 = cnt fa fb fp fl (lo + i) + 1 := by
                  rcases hFA with h | h
                  · exact absurd (kw_absent hI.1 h.1 hk) id
                  · exact h
                obtain ⟨hfa1, hfp, hfl, e1⟩ := hfa
                have hcN : cnt fa fb fp fl (lo + i) < O.keys.size := by
                  have := (cnt_le hbfs (q := lo + i + 1) (by omega)).2
                  rcases hFB with h | h <;> omega
                rw [hfa1]
                have H1 := stepA_new hO hI hqc hcN hfa1 (hpar _ hcN _ hfp)
                  ((hlab _ hcN _ hfl).trans rfl)
                rw [← e1] at H1
                phaseB
            · rw [if_neg hc]
              have hs : (getT alpha' (lo + i)).isSome := by
                cases e : getT alpha' (lo + i)
                · rw [e] at hc
                  exact absurd rfl hc
                · rfl
              obtain ⟨H1, hxn⟩ := stepA_skip hI hqc hs
              have e1 : n1 = cnt fa fb fp fl (lo + i) := by
                rcases hFA with h | h <;> omega
              rw [← e1] at H1
              phaseB
          · intro s hs
            have e : lo + (keys.size - lo) = keys.size := by omega
            rw [e] at hs
            exact hs
          · rw [Nat.add_zero]
            exact hS
        · intro s hs
          refine ⟨hhi, sinv_reset hs, fun k hk hdk => ?_⟩
          dsimp only
          rcases Nat.lt_or_ge (dep k) t with h1 | h1
          · have := hD k hk h1
            omega
          · rcases Nat.eq_zero_or_pos k with h0 | h0
            · omega
            · have hdk' := hdp k h0 hk
              have hr := fp_reach hbfs O.keys.size (Nat.le_refl _) k h0 (by rw [hCN]; exact hk)
              have hfp := hD (fp k) (by omega) (by omega)
              have hm := cnt_mono hbfs (a := fp k + 1) (lo - (fp k + 1)) (by omega)
              rw [Nat.add_sub_cancel' (by omega)] at hm
              omega
      · rw [if_neg hlt]
        have e : lo = O.keys.size := by
          rcases Nat.lt_or_ge lo O.keys.size with h | h
          · have := (hF lo h).1
            omega
          · omega
        rw [e, hCN] at hS
        exact sinv_reset hS
    ·
      intro s hs
      obtain ⟨hlo, hS, hD⟩ := hs
      have e : s.2.2.2.2.2.2.2 = O.keys.size := by
        rcases Nat.lt_or_ge s.2.2.2.2.2.2.2 O.keys.size with h | h
        · have := hD (O.keys.size - 1) (by omega) (hdep _ (by omega))
          omega
        · omega
      rw [e, hCN] at hS
      exact sinv_reset hS
    ·
      have hc0 : cnt fa fb fp fl 0 = 1 := rfl
      have hpos : 0 < O.keys.size := by
        have := (cnt_le hbfs (q := 0) (Nat.zero_le _)).2
        omega
      have hn0 : getT #[none32] 0 = none := rfl
      refine ⟨Nat.zero_le _, ?_, fun k _ h => absurd h (Nat.not_lt_zero _)⟩
      dsimp only
      rw [hc0]
      refine ⟨⟨rfl, fun i hi => ?_, fun i hi => ?_, fun Z i hZ => ?_, rfl, fun i hi => ?_, rfl,
        fun i hi => ?_⟩, rfl, fun k hk => Or.inl ?_, fun k hk => absurd hk (Nat.not_lt_zero _),
        rfl, fun k hk => absurd hk (Nat.not_lt_zero _), rfl, fun k p hkp => ?_, fun k h => h,
        fun k p h => h⟩
      · have hi0 : i = 0 := by omega
        subst hi0
        rw [hR]
        rfl
      · have hi0 : i = 0 := by omega
        subst hi0
        rw [hR, Std.HashMap.getElem?_insert, beq_self_eq_true, if_pos rfl]
      · rw [Std.HashMap.getElem?_insert, Std.HashMap.getElem?_empty] at hZ
        by_cases hz : (R == Z) = true
        · rw [if_pos hz] at hZ
          cases hZ
          exact ⟨by omega, by rw [hR]; exact beq_iff_eq.1 hz⟩
        · rw [if_neg hz] at hZ
          cases hZ
      · have hi0 : i = 0 := by omega
        subst hi0
        rw [hpar 0 hpos 0 hp0]
        rfl
      · have hi0 : i = 0 := by omega
        subst hi0
        rw [hlab 0 hpos 0 hl0]
        rfl
      · have hk0 : k = 0 := by omega
        rw [hk0]
        exact hn0
      · have hk := getT_lt hkp
        have hk0 : k = 0 := by
          have : (#[none32] : Table).size = 1 := rfl
          omega
        rw [hk0, hn0] at hkp
        cases hkp
  obtain ⟨hK, hsa', -, ha4, hsb', hb2, -⟩ := hQ
  have hkeys : s.1 = O.keys := by
    refine Array.ext hK.1 fun i h1 h2 => ?_
    have := hK.2.1 i (by rw [← hK.1]; exact h1)
    rwa [getElem!_pos _ i h1, getElem!_pos _ i h2] at this
  have htab : ∀ (T a : Table), T.size = O.keys.size → a.size = O.keys.size →
      (∀ i < O.keys.size, a[i]! = T[i]!) → a = T := by
    intro T a hT ha' H
    refine Array.ext (by rw [ha', hT]) fun i h1 h2 => ?_
    have := H i (by rw [← ha']; exact h1)
    rwa [getElem!_pos _ i h1, getElem!_pos _ i h2] at this
  rw [hs, hkeys, tab_eq (by rw [hsa', hsa]) (fun k hk => ha4 k (by rw [← hsa]; exact hk)),
    tab_eq (by rw [hsb', hsb]) (fun k hk => hb2 k (by rw [← hsb]; exact hk)),
    htab _ _ hsp hK.2.2.2.2.1 hK.2.2.2.2.2.1, htab _ _ hsl hK.2.2.2.2.2.2.1 hK.2.2.2.2.2.2.2]

end CFSG.Sporadic.Suz.Native.BfsSpec
