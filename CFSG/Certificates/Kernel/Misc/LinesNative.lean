module

public import Certificates.Data.CFSGNative.Fischer.Hyperoval
public import CFSG.Certificates.Kernel.Misc.LinesGeom
public import CFSG.Certificates.Kernel.Spor.TabWords
import Mathlib.Data.List.Sort

public section

namespace CFSG.KC.Misc.Lines

open CFSG.F4.Native CFSG.Sporadic.Th.Native CFSG.Fischer.Native CFSG.KS.TW

structure Tabs (P : Array Flags) (pl : Array (Array Nat)) (LT : Array (Array Nat))
    (rb : Nat → Nat → Bool) (PL : Nat → List Nat) (lf : Nat → Nat → List Nat) : Prop where
  P_get : ∀ x < 693, ∀ y < 693, (P[x]!)[y]! = rb x y
  pl_get : ∀ x < 693, pl[x]! = (PL x).toArray
  LT_get : ∀ x < 693, ∀ y < 693,
    LT[x * 693 + y]! = if rb x y = true then (lf x y).toArray else #[]

structure Geom (rb : Nat → Nat → Bool) (PL : Nat → List Nat) (lf : Nat → Nat → List Nat) :
    Prop where
  rel : PolarRel rb
  plmem : ∀ x < 693, ∀ y, y ∈ PL x ↔ y < 693 ∧ rb x y = true
  plsorted : ∀ x < 693, (PL x).Pairwise (· < ·)
  pllen : ∀ x < 693, (PL x).length = 181
  lmem : ∀ x < 693, ∀ y < 693, x ≠ y → rb x y = true → ∀ z, z ∈ lf x y ↔ z ∈ Ln rb x y
  lnodup : ∀ x < 693, ∀ y < 693, x < y → rb x y = true → (lf x y).Nodup
  llen : ∀ x y, (lf x y).length = 5

theorem toArray_get_ne {l : List Nat} (hnd : l.Nodup) {a b : Nat} (ha : a < l.length)
    (hb : b < l.length) (hab : a ≠ b) : l.toArray[a]! ≠ l.toArray[b]! := by
  have e1 : l.toArray[a]! = l[a] := by simp [ha]
  have e2 : l.toArray[b]! = l[b] := by simp [hb]
  rw [e1, e2]
  intro h
  exact hab ((List.Nodup.getElem_inj_iff hnd).1 h)

theorem filterRange_eq (p : Nat → Bool) : ∀ (n : Nat) (acc : List Nat),
    filterRange p n acc = (List.range n).filter p ++ acc := by
  intro n
  induction n with
  | zero => intro acc; simp [filterRange]
  | succ n ih =>
    intro acc
    rw [filterRange, ih, List.range_succ, List.filter_append]
    by_cases h : p n = true
    · simp [h]
    · simp [h]

theorem perpLists_get (P : Array Flags) (rb : Nat → Nat → Bool) (PL : Nat → List Nat)
    (hP : ∀ x < 693, ∀ y < 693, (P[x]!)[y]! = rb x y)
    (hmem : ∀ x < 693, ∀ y, y ∈ PL x ↔ y < 693 ∧ rb x y = true)
    (hsorted : ∀ x < 693, (PL x).Pairwise (· < ·)) :
    ∀ x < 693, (perpLists P)[x]! = (PL x).toArray := by
  intro x hx
  unfold perpLists
  rw [getElem!_pos _ x (by simpa using hx), Array.getElem_ofFn]
  unfold perpList
  dsimp only
  rw [filterRange_eq, List.append_nil]
  have e : (List.range 693).filter (fun y => (P[x]!)[y]!) = PL x := by
    refine List.Pairwise.eq_of_mem_iff (r := (· < ·)) (List.pairwise_lt_range.filter _)
      (hsorted x hx) ?_
    intro y
    rw [List.mem_filter, List.mem_range, hmem x hx y]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by rw [← hP x hx y h1]; exact h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by rw [hP x hx y h1]; exact h2⟩
  rw [e]

variable {P : Array Flags} {pl : Array (Array Nat)} {LT : Array (Array Nat)}
  {rb : Nat → Nat → Bool} {PL : Nat → List Nat} {lf : Nat → Nat → List Nat}

theorem plSizes_of (T : Tabs P pl LT rb PL lf) (G : Geom rb PL lf) :
    allIn 0 693 (fun p => pl[p]!.size == 181) = true := by
  rw [allIn_iff]
  intro p hp
  rw [T.pl_get p hp]
  simp [G.pllen p hp]

theorem linesOK_of (T : Tabs P pl LT rb PL lf) (G : Geom rb PL lf) : linesOK P pl LT = true := by
  unfold linesOK
  rw [allIn_iff]
  intro x hx
  rw [allIn_iff]
  intro y hy
  dsimp only
  by_cases h : x < y ∧ rb x y = true
  · obtain ⟨hxy, hr⟩ := h
    have hL := T.LT_get x hx y hy
    rw [if_pos hr] at hL
    rw [T.P_get x hx y hy, T.pl_get x hx, hL]
    have hne : x ≠ y := Nat.ne_of_lt hxy
    have hmem := G.lmem x hx y hy hne hr
    rw [Bool.or_eq_true]
    right
    rw [Bool.and_eq_true, Bool.and_eq_true]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simp only [List.all_toArray, List.all_eq_true, decide_eq_true_eq]
      intro z hz
      exact lt_of_mem_Ln ((hmem z).1 hz)
    · unfold distinct5
      rw [Bool.and_eq_true, allIn_iff]
      refine ⟨by simp [G.llen x y], fun a ha => ?_⟩
      rw [allIn_iff]
      intro b hb
      have hnd := G.lnodup x hx y hy hxy hr
      have hl5 := G.llen x y
      by_cases hab : a = b
      · simp [hab]
      · have := toArray_get_ne hnd (a := a) (b := b) (by omega) (by omega) hab
        rw [Bool.or_eq_true]
        exact Or.inr (bne_iff_ne.2 this)
    · rw [allIn_iff]
      intro z hz
      rw [beq_iff_eq, Bool.eq_iff_iff]
      have hsymm : ∀ a b, a < 693 → b < 693 → rb a b = rb b a := fun a b ha hb =>
        G.rel.rb_symm ha hb
      have hRHS : ((Array.filter (fun w => P[w]![y]!) (PL x).toArray).all fun w => P[z]![w]!) = true
          ↔ ∀ w ∈ PL x, rb w y = true → rb z w = true := by
        simp only [Array.all_eq_true', Array.mem_filter, List.mem_toArray]
        constructor
        · intro h w hw hwy
          have hw693 := ((G.plmem x hx w).1 hw).1
          have := h w ⟨hw, by rw [T.P_get w hw693 y hy]; exact hwy⟩
          rwa [T.P_get z hz w hw693] at this
        · rintro h w ⟨hw, hwy⟩
          have hw693 := ((G.plmem x hx w).1 hw).1
          rw [T.P_get w hw693 y hy] at hwy
          rw [T.P_get z hz w hw693]
          exact h w hw hwy
      rw [hRHS]
      simp only [List.contains_toArray, List.elem_eq_mem, decide_eq_true_eq, hmem z, mem_Ln]
      constructor
      · rintro ⟨-, h1⟩ w hw hwy
        obtain ⟨hw693, hxw⟩ := (G.plmem x hx w).1 hw
        have hyw : rb y w = true := by rw [hsymm y w hy hw693]; exact hwy
        have := h1 w hw693 hxw hyw
        rw [hsymm z w hz hw693]
        exact this
      · intro h
        refine ⟨hz, fun w hw hxw hyw => ?_⟩
        have hwPL : w ∈ PL x := (G.plmem x hx w).2 ⟨hw, hxw⟩
        have hwy : rb w y = true := by rw [hsymm w y hw hy]; exact hyw
        have := h w hwPL hwy
        rw [hsymm w z hw hz]
        exact this
  · rw [Bool.or_eq_true]
    left
    rw [T.P_get x hx y hy]
    by_cases hxy : x < y
    · have hr : rb x y = false := by
        by_contra hne
        exact h ⟨hxy, by simpa using hne⟩
      simp [hr]
    · simp [hxy]

theorem twinsOK_of (T : Tabs P pl LT rb PL lf) (G : Geom rb PL lf)
    (twins : ∀ x ∈ PL 0, x ≠ 0 → ∀ y ∈ PL 0, y ≠ 0 → y ≠ x →
      ((∀ w ∈ PL 0, w ≠ 0 → rb x w = rb y w) ↔ y ∈ lf 0 x)) : twinsOK P pl LT = true := by
  unfold twinsOK
  dsimp only
  rw [T.pl_get 0 (by omega)]
  simp only [Array.all_eq_true', List.mem_toArray]
  intro x hx
  by_cases hx0 : x = 0
  · simp [hx0]
  rw [Bool.or_eq_true]
  right
  simp only [Array.all_eq_true', List.mem_toArray]
  intro y hy
  by_cases hy0 : y = 0
  · simp [hy0]
  by_cases hyx : y = x
  · simp [hyx]
  obtain ⟨hx693, hr0x⟩ := (G.plmem 0 (by omega) x).1 hx
  have hLT : LT[x]! = (lf 0 x).toArray := by
    have := T.LT_get 0 (by omega) x hx693
    rw [if_pos hr0x] at this
    simpa using this
  rw [hLT]
  have hy0' : (y == 0) = false := by simpa using hy0
  have hyx' : (y == x) = false := by simpa using hyx
  rw [hy0', hyx', Bool.false_or, Bool.false_or, beq_iff_eq, Bool.eq_iff_iff]
  have hLHS : ((PL 0).toArray.all fun w => w == 0 || P[x]![w]! == P[y]![w]!) = true ↔
      ∀ w ∈ PL 0, w ≠ 0 → rb x w = rb y w := by
    simp only [Array.all_eq_true', List.mem_toArray, Bool.or_eq_true, beq_iff_eq]
    constructor
    · intro h w hw hw0
      have hw693 := ((G.plmem 0 (by omega) w).1 hw).1
      rcases h w hw with h1 | h1
      · exact absurd h1 hw0
      · rwa [T.P_get x hx693 w hw693, T.P_get y ((G.plmem 0 (by omega) y).1 hy).1 w hw693] at h1
    · intro h w hw
      by_cases hw0 : w = 0
      · exact Or.inl hw0
      · right
        have hw693 := ((G.plmem 0 (by omega) w).1 hw).1
        rw [T.P_get x hx693 w hw693, T.P_get y ((G.plmem 0 (by omega) y).1 hy).1 w hw693]
        exact h w hw hw0
  rw [hLHS]
  simp only [List.contains_toArray, List.elem_eq_mem, decide_eq_true_eq]
  exact twins x hx hx0 y hy hy0 hyx

@[expose] def NSet (rb : Nat → Nat → Bool) (q : Nat) : Finset Nat :=
  (Finset.range 693).filter fun w : Nat => rb 0 w = true ∧ rb q w = true

theorem mem_NSet {rb : Nat → Nat → Bool} {q w : Nat} :
    w ∈ NSet rb q ↔ w < 693 ∧ rb 0 w = true ∧ rb q w = true := by
  simp [NSet]

@[expose] def perpPerpOKT (T0 : Table) (P : Array Flags) (pl : Array (Array Nat))
    (LT : Array (Array Nat)) : Bool :=
  let D := pl[0]!
  allIn 0 693 fun q => (P[0]!)[q]! ||
    (let N := D.filter fun w => (P[w]!)[q]!
     N.size == 45 &&
       N.any (fun a => N.any fun b => a != b && (P[a]!)[b]! &&
         LT[a * 693 + b]!.any fun c => c != a && c != b && N.contains c) &&
       N.all (fun a => N.all fun b =>
         a == b || !(P[a]!)[b]! || N.any fun w => (P[w]!)[a]! != (P[w]!)[b]!) &&
       allIn 0 693 fun q' => (P[0]!)[q']! || !(D.all fun w => (P[w]!)[q]! == (P[w]!)[q']!) ||
         q' == q || q' == ap T0 q)

theorem perpPerpOKT_of (T : Tabs P pl LT rb PL lf) (G : Geom rb PL lf) (T0 : Table)
    (t0 : Nat → Nat) (hT0 : ∀ q < 693, ap T0 q = t0 q)
    (pp : ∀ q < 693, rb 0 q = false →
      (NSet rb q).card = 45 ∧
      (∃ a b, a ∈ NSet rb q ∧ b ∈ NSet rb q ∧ a ≠ b ∧ rb a b = true ∧
        ∃ c, c ∈ lf a b ∧ c ≠ a ∧ c ≠ b ∧ c ∈ NSet rb q) ∧
      (∀ a ∈ NSet rb q, ∀ b ∈ NSet rb q, a ≠ b → rb a b = true →
        ∃ w ∈ NSet rb q, rb a w ≠ rb b w) ∧
      (∀ q' < 693, rb 0 q' = false →
        (∀ w < 693, rb 0 w = true → rb q' w = rb q w) → q' = q ∨ q' = t0 q)) :
    perpPerpOKT T0 P pl LT = true := by
  unfold perpPerpOKT
  rw [allIn_iff]
  intro q hq
  dsimp only
  by_cases h0 : rb 0 q = true
  · rw [Bool.or_eq_true]
    left
    rw [T.P_get 0 (by omega) q hq]
    exact h0
  · have h0' : rb 0 q = false := by simpa using h0
    rw [T.pl_get 0 (by omega)]
    have hPL0 := G.plmem 0 (by omega)
    have hsymm : ∀ a b, a < 693 → b < 693 → rb a b = rb b a := fun a b ha hb =>
      G.rel.rb_symm ha hb
    have hN : Array.filter (fun w => P[w]![q]!) (PL 0).toArray =
        ((PL 0).filter fun w => rb w q).toArray := by
      rw [List.filter_toArray]
      congr 1
      apply List.filter_congr
      intro w hw
      exact T.P_get w ((hPL0 w).1 hw).1 q hq
    rw [hN]
    have hmemN : ∀ w, w ∈ (PL 0).filter (fun w => rb w q) ↔ w ∈ NSet rb q := by
      intro w
      rw [List.mem_filter, hPL0 w, mem_NSet]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨h1, h2, by rw [hsymm q w hq h1]; exact h3⟩
      · rintro ⟨h1, h2, h3⟩
        exact ⟨⟨h1, h2⟩, by rw [hsymm w q h1 hq]; exact h3⟩
    have hNnd : ((PL 0).filter fun w => rb w q).Nodup := (G.plsorted 0 (by omega)).nodup.filter _
    have hNlen : ((PL 0).filter fun w => rb w q).length = 45 := by
      have e : ((PL 0).filter fun w => rb w q).toFinset = NSet rb q := by
        ext w
        rw [List.mem_toFinset, hmemN]
      rw [← List.toFinset_card_of_nodup hNnd, e]
      exact (pp q hq h0').1
    obtain ⟨-, pp2, pp3, pp4⟩ := pp q hq h0'
    rw [Bool.or_eq_true]
    right
    rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · simp [hNlen]
    · simp only [List.any_toArray, List.any_eq_true]
      obtain ⟨a, b, ha, hb, hne, hab, c, hc, hca, hcb, hcN⟩ := pp2
      have ha693 := (mem_NSet.1 ha).1
      have hb693 := (mem_NSet.1 hb).1
      refine ⟨a, (hmemN a).2 ha, b, (hmemN b).2 hb, ?_⟩
      have hLT := T.LT_get a ha693 b hb693
      rw [if_pos hab] at hLT
      rw [hLT, T.P_get a ha693 b hb693]
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq]
      refine ⟨⟨hne, hab⟩, ?_⟩
      simp only [List.any_toArray, List.any_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq,
        List.contains_toArray, List.elem_eq_mem, decide_eq_true_eq]
      exact ⟨c, hc, ⟨hca, hcb⟩, (hmemN c).2 hcN⟩
    · simp only [List.all_toArray, List.all_eq_true, Bool.or_eq_true, beq_iff_eq,
        Bool.not_eq_true', List.any_toArray, List.any_eq_true, bne_iff_ne, ne_eq]
      intro a ha b hb
      by_cases hab : a = b
      · exact Or.inl (Or.inl hab)
      have ha' := (hmemN a).1 ha
      have hb' := (hmemN b).1 hb
      have ha693 := (mem_NSet.1 ha').1
      have hb693 := (mem_NSet.1 hb').1
      by_cases hr : rb a b = true
      · right
        obtain ⟨w, hw, hne⟩ := pp3 a ha' b hb' hab hr
        refine ⟨w, (hmemN w).2 hw, ?_⟩
        have hw693 := (mem_NSet.1 hw).1
        rw [T.P_get w hw693 a ha693, T.P_get w hw693 b hb693, hsymm w a hw693 ha693,
          hsymm w b hw693 hb693]
        exact hne
      · left
        right
        rw [T.P_get a ha693 b hb693]
        simpa using hr
    · rw [allIn_iff]
      intro q' hq'
      simp only [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true']
      by_cases hr0 : rb 0 q' = true
      · left
        left
        left
        rw [T.P_get 0 (by omega) q' hq']
        exact hr0
      have hr0' : rb 0 q' = false := by simpa using hr0
      by_cases hall : ((PL 0).toArray.all fun w => P[w]![q]! == P[w]![q']!) = true
      · have hw : ∀ w < 693, rb 0 w = true → rb q' w = rb q w := by
          intro w hw693 hw
          have hwPL : w ∈ PL 0 := (hPL0 w).2 ⟨hw693, hw⟩
          simp only [Array.all_eq_true', List.mem_toArray, beq_iff_eq] at hall
          have := hall w hwPL
          rw [T.P_get w hw693 q hq, T.P_get w hw693 q' hq', hsymm w q hw693 hq,
            hsymm w q' hw693 hq'] at this
          exact this.symm
        rcases pp4 q' hq' hr0' hw with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr (by rw [h, hT0 q hq])
      · left
        left
        right
        simpa using hall

end CFSG.KC.Misc.Lines

end
