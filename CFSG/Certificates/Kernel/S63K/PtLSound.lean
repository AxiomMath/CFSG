module

public import Certificates.Data.D4HexGeoCheck
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
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.KC.S63K

open CFSG.D4Hex

@[expose] def bkStep (pts : Array ℕ) (bk : Array (Array ℕ)) (v : ℕ) : Array (Array ℕ) :=
  (List.range' 0 3).foldl (fun bk k => bk.modify pts[3 * v + k]! fun l => l.push v) bk

@[expose] def outStep (bk : Array (Array ℕ)) (out : Array ℕ) (p : ℕ) : Array ℕ :=
  (List.range' 0 9).foldl (fun out k => out.push (bk[p]!)[k]!) out

theorem hexPtL_eq (pts : Array ℕ) :
    hexPtL pts = (List.range' 0 819).foldl
      (outStep ((List.range' 0 2457).foldl (bkStep pts) (Array.replicate 819 #[]))) #[] := by
  unfold hexPtL
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Id.run,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, List.forIn_pure_yield_eq_foldl, pure_bind]
  rfl

theorem push_fold (f : ℕ → ℕ) : ∀ (m s : ℕ) (out : Array ℕ),
    ((List.range' s m).foldl (fun out k => out.push (f k)) out).toList =
      out.toList ++ (List.range' s m).map f
  | 0, _, out => by simp
  | m + 1, s, out => by
    rw [List.range'_succ, List.foldl_cons, push_fold f m (s + 1), Array.toList_push,
      List.map_cons, List.append_assoc, List.singleton_append]

theorem out_toList (bk : Array (Array ℕ)) : ∀ n : ℕ,
    ((List.range' 0 n).foldl (outStep bk) #[]).toList =
      (List.range (9 * n)).map fun i => (bk[i / 9]!)[i % 9]!
  | 0 => by simp
  | n + 1 => by
    rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil, Nat.zero_add,
      Nat.one_mul]
    have e : ∀ out, outStep bk out n =
        (List.range' 0 9).foldl (fun out k => out.push (bk[n]!)[k]!) out := fun _ => rfl
    rw [e, push_fold, out_toList bk n, show 9 * (n + 1) = 9 * n + 9 by ring, List.range_add,
      List.map_append, List.map_map]
    congr 1
    rw [← List.range_eq_range']
    apply List.map_congr_left
    intro k hk
    have hk' := List.mem_range.1 hk
    simp only [Function.comp_apply]
    rw [show (9 * n + k) / 9 = n by omega, show (9 * n + k) % 9 = k by omega]

theorem get_of_toList {a : Array ℕ} {f : ℕ → ℕ} {n : ℕ}
    (h : a.toList = (List.range n).map f) {i : ℕ} (hi : i < n) : a[i]! = f i := by
  have hs : a.size = n := by rw [← Array.length_toList, h, List.length_map, List.length_range]
  rw [getElem!_pos a i (by omega), ← Array.getElem_toList]
  simp only [h, List.getElem_map, List.getElem_range]

@[expose] def incid (pts : Array ℕ) (p n : ℕ) : List ℕ :=
  (List.range n).flatMap fun v =>
    ((List.range 3).filter fun k => pts[3 * v + k]! == p).map fun _ => v

theorem modify_get (bk : Array (Array ℕ)) (i : ℕ) (f : Array ℕ → Array ℕ) {p : ℕ}
    (hp : p < bk.size) : (bk.modify i f)[p]! = if i = p then f bk[p]! else bk[p]! := by
  rw [getElem!_pos _ p (by simpa using hp), getElem!_pos bk p hp, Array.getElem_modify]

theorem bk_inner (pts : Array ℕ) (v : ℕ) : ∀ (m : ℕ) (bk : Array (Array ℕ)), bk.size = 819 →
    ((List.range' 0 m).foldl (fun bk k => bk.modify pts[3 * v + k]! fun l => l.push v) bk).size =
        819 ∧
      ∀ p < 819, ((List.range' 0 m).foldl
          (fun bk k => bk.modify pts[3 * v + k]! fun l => l.push v) bk)[p]!.toList =
        bk[p]!.toList ++ (((List.range m).filter fun k => pts[3 * v + k]! == p).map fun _ => v)
  | 0, bk, hs => ⟨hs, fun p _ => by simp⟩
  | m + 1, bk, hs => by
    obtain ⟨ih1, ih2⟩ := bk_inner pts v m bk hs
    rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil, Nat.zero_add,
      Nat.one_mul]
    refine ⟨by rw [Array.size_modify, ih1], fun p hp => ?_⟩
    rw [modify_get _ _ _ (by rw [ih1]; exact hp), List.range_succ, List.filter_append]
    by_cases e : pts[3 * v + m]! = p
    · rw [if_pos e, Array.toList_push, ih2 p hp]
      simp [e]
    · rw [if_neg e, ih2 p hp]
      simp [e]

theorem bk_toList (pts : Array ℕ) : ∀ n : ℕ,
    ((List.range' 0 n).foldl (bkStep pts) (Array.replicate 819 #[])).size = 819 ∧
      ∀ p < 819, ((List.range' 0 n).foldl (bkStep pts) (Array.replicate 819 #[]))[p]!.toList =
        incid pts p n
  | 0 => ⟨by simp, fun p hp => by
      rw [getElem!_pos _ p (by simpa using hp)]
      simp [incid]⟩
  | n + 1 => by
    obtain ⟨ih1, ih2⟩ := bk_toList pts n
    rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil, Nat.zero_add,
      Nat.one_mul]
    have e : ∀ bk, bkStep pts bk n =
        (List.range' 0 3).foldl (fun bk k => bk.modify pts[3 * n + k]! fun l => l.push n) bk :=
      fun _ => rfl
    rw [e]
    obtain ⟨h1, h2⟩ := bk_inner pts n 3 _ ih1
    refine ⟨h1, fun p hp => ?_⟩
    rw [h2 p hp, ih2 p hp]
    unfold incid
    rw [List.range_succ (n := n), List.flatMap_append, List.flatMap_singleton]

theorem flatMap_ite (c : ℕ → Bool) : ∀ l : List ℕ,
    (l.flatMap fun v => if c v then [v] else []) = l.filter c
  | [] => rfl
  | v :: l => by
    rw [List.flatMap_cons, flatMap_ite c l, List.filter_cons]
    cases c v <;> simp

theorem incid_eq (pts : Array ℕ) (p n : ℕ)
    (hinc : ∀ v < n, pts[3 * v]! < pts[3 * v + 1]! ∧ pts[3 * v + 1]! < pts[3 * v + 2]!) :
    incid pts p n = (List.range n).filter fun v =>
      (pts[3 * v]! == p || pts[3 * v + 1]! == p || pts[3 * v + 2]! == p) := by
  rw [← flatMap_ite]
  unfold incid
  apply List.flatMap_congr
  intro v hv
  have h := hinc v (List.mem_range.1 hv)
  have e3 : List.range 3 = [0, 1, 2] := rfl
  rw [e3]
  simp only [List.filter_cons, List.filter_nil, Nat.add_zero]
  by_cases a : pts[3 * v]! = p <;> by_cases b : pts[3 * v + 1]! = p <;>
    by_cases c : pts[3 * v + 2]! = p <;> simp [a, b, c] <;> omega

theorem eq_of_inc : ∀ {l₁ l₂ : List ℕ}, l₁.Pairwise (· < ·) → l₂.Pairwise (· < ·) →
    (∀ x, x ∈ l₁ ↔ x ∈ l₂) → l₁ = l₂
  | [], [], _, _, _ => rfl
  | [], b :: _, _, _, hm => absurd ((hm b).2 List.mem_cons_self) List.not_mem_nil
  | a :: _, [], _, _, hm => absurd ((hm a).1 List.mem_cons_self) List.not_mem_nil
  | a :: l₁, b :: l₂, h₁, h₂, hm => by
    have p₁ := List.pairwise_cons.1 h₁
    have p₂ := List.pairwise_cons.1 h₂
    have hab : a = b := by
      rcases List.mem_cons.1 ((hm a).1 List.mem_cons_self) with h | h
      · exact h
      · rcases List.mem_cons.1 ((hm b).2 List.mem_cons_self) with h' | h'
        · exact h'.symm
        · have := p₂.1 a h
          have := p₁.1 b h'
          omega
    subst hab
    congr 1
    refine eq_of_inc p₁.2 p₂.2 fun x => ⟨fun hx => ?_, fun hx => ?_⟩
    · rcases List.mem_cons.1 ((hm x).1 (List.mem_cons_of_mem _ hx)) with e | e
      · subst e
        exact absurd (p₁.1 x hx) (lt_irrefl x)
      · exact e
    · rcases List.mem_cons.1 ((hm x).2 (List.mem_cons_of_mem _ hx)) with e | e
      · subst e
        exact absurd (p₂.1 x hx) (lt_irrefl x)
      · exact e

theorem hexPtL_of {pts : Array ℕ} {PL : ℕ → ℕ}
    (hinc : ∀ v < 2457, pts[3 * v]! < pts[3 * v + 1]! ∧ pts[3 * v + 1]! < pts[3 * v + 2]!)
    (hrow : ∀ p < 819, ∀ j < 8, PL (9 * p + j) < PL (9 * p + (j + 1)))
    (hmem1 : ∀ p < 819, ∀ j < 9, PL (9 * p + j) < 2457 ∧
      (pts[3 * PL (9 * p + j)]! = p ∨ pts[3 * PL (9 * p + j) + 1]! = p ∨
        pts[3 * PL (9 * p + j) + 2]! = p))
    (hmem2 : ∀ v < 2457, ∀ k < 3, pts[3 * v + k]! < 819 →
      ∃ j < 9, PL (9 * pts[3 * v + k]! + j) = v) :
    (hexPtL pts).size = 7371 ∧ ∀ i < 7371, (hexPtL pts)[i]! = PL i := by
  obtain ⟨hb1, hb2⟩ := bk_toList pts 2457
  have hrowp : ∀ p < 819, incid pts p 2457 = (List.range 9).map fun j => PL (9 * p + j) := by
    intro p hp
    rw [incid_eq pts p 2457 hinc]
    apply eq_of_inc
    · exact (List.pairwise_lt_range).filter _
    · rw [List.pairwise_map]
      have hc : ∀ i j, i < j → j < 9 → PL (9 * p + i) < PL (9 * p + j) := by
        intro i j hij hj
        induction j with
        | zero => omega
        | succ j ih =>
          rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h | rfl
          · exact lt_trans (ih h (by omega)) (hrow p hp j (by omega))
          · exact hrow p hp i (by omega)
      exact List.pairwise_lt_range.imp_of_mem fun {a b} ha hb hab =>
        hc a b hab (List.mem_range.1 hb)
    · intro v
      simp only [List.mem_filter, List.mem_range, List.mem_map, Bool.or_eq_true, beq_iff_eq]
      constructor
      · rintro ⟨hv, h⟩
        have hk : ∃ k < 3, pts[3 * v + k]! = p := by
          rcases h with (h | h) | h
          · exact ⟨0, by omega, by simpa using h⟩
          · exact ⟨1, by omega, h⟩
          · exact ⟨2, by omega, h⟩
        obtain ⟨k, hk3, hkp⟩ := hk
        obtain ⟨j, hj, e⟩ := hmem2 v hv k hk3 (by omega)
        rw [hkp] at e
        exact ⟨j, hj, e⟩
      · rintro ⟨j, hj, rfl⟩
        obtain ⟨h1, h2⟩ := hmem1 p hp j hj
        refine ⟨h1, ?_⟩
        rcases h2 with h | h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr h)
        · exact Or.inr h
  have hF := out_toList ((List.range' 0 2457).foldl (bkStep pts) (Array.replicate 819 #[])) 819
  rw [hexPtL_eq]
  refine ⟨by rw [← Array.length_toList, hF, List.length_map, List.length_range], fun i hi => ?_⟩
  rw [get_of_toList hF (by omega)]
  have hp : i / 9 < 819 := by omega
  have hl := hb2 (i / 9) hp
  rw [hrowp (i / 9) hp] at hl
  have hk : i % 9 < 9 := Nat.mod_lt _ (by norm_num)
  rw [getElem!_pos _ (i % 9) (by
    rw [← Array.length_toList, hl, List.length_map, List.length_range]; exact hk),
    ← Array.getElem_toList]
  simp only [hl, List.getElem_map, List.getElem_range]
  rw [Nat.div_add_mod]

@[expose] def lineKey (pts : Array ℕ) (v : ℕ) : ℕ :=
  (pts[3 * v]! * 819 + pts[3 * v + 1]!) * 819 + pts[3 * v + 2]!

theorem hexLineKeyMap_eq (pts : Array ℕ) :
    hexLineKeyMap pts =
      (List.range' 0 2457).foldl (fun (m : Std.HashMap ℕ ℕ) v => m.insert (lineKey pts v) v) ∅ := by
  unfold hexLineKeyMap
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Id.run,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, List.forIn_pure_yield_eq_foldl, pure_bind]
  rfl

theorem keyMap_fold (pts : Array ℕ) (hinj : ∀ a < 2457, ∀ b < 2457, lineKey pts a = lineKey pts b →
    a = b) (d : ℕ) : ∀ n ≤ 2457, ∀ v < n,
    ((List.range' 0 n).foldl (fun (m : Std.HashMap ℕ ℕ) v => m.insert (lineKey pts v) v)
      ∅).getD (lineKey pts v) d =
      v := by
  intro n
  induction n with
  | zero => intro _ v hv; omega
  | succ n ih =>
    intro hn v hv
    rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil, Nat.zero_add,
      Nat.one_mul, Std.HashMap.getD_insert]
    by_cases e : v = n
    · subst e
      simp
    · have hne : (lineKey pts n == lineKey pts v) = false := by
        rw [beq_eq_false_iff_ne]
        exact fun h => e (hinj v (by omega) n (by omega) h.symm)
      rw [hne]
      exact ih (by omega) v (by omega)

theorem keyMap_getD {pts : Array ℕ}
    (hinj : ∀ a < 2457, ∀ b < 2457, lineKey pts a = lineKey pts b → a = b) (d : ℕ) {v : ℕ}
    (hv : v < 2457) : (hexLineKeyMap pts).getD (lineKey pts v) d = v := by
  rw [hexLineKeyMap_eq]
  exact keyMap_fold pts hinj d 2457 (le_refl _) v hv

end CFSG.KC.S63K

end
