module

public import Certificates.Data.Kernel.J4M4Sets
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.KC.J4M4

open scoped List

theorem splitA_cons (a : ℕ) (l : List ℕ) :
    splitA (a :: l) = (a :: (splitA l).2, (splitA l).1) := by
  rw [splitA]

theorem splitA_perm : ∀ l : List ℕ, (splitA l).1 ++ (splitA l).2 ~ l
  | [] => by
    rw [splitA]
    exact List.Perm.refl _
  | a :: l => by
    rw [splitA_cons, List.cons_append]
    exact List.Perm.cons a (List.perm_append_comm.trans (splitA_perm l))

theorem mergeF_perm : ∀ (n : ℕ) (l₁ l₂ : List ℕ), mergeF n l₁ l₂ ~ l₁ ++ l₂
  | 0, _, _ => by rw [mergeF]
  | _ + 1, [], l₂ => by rw [mergeF, List.nil_append]
  | _ + 1, a :: l₁, [] => by rw [mergeF, List.append_nil]
  | n + 1, a :: l₁, b :: l₂ => by
    rw [mergeF]
    cases Nat.ble a b
    · exact ((mergeF_perm n (a :: l₁) l₂).cons b).trans List.perm_middle.symm
    · exact (mergeF_perm n l₁ (b :: l₂)).cons a

theorem msortF_perm : ∀ (n : ℕ) (l : List ℕ), msortF n l ~ l
  | 0, _ => by rw [msortF]
  | _ + 1, [] => by rw [msortF]
  | _ + 1, [_] => by rw [msortF]
  | n + 1, a :: b :: l => by
    rw [msortF]
    have hs := splitA_perm (a :: b :: l)
    revert hs
    rcases splitA (a :: b :: l) with ⟨x, y⟩
    intro hs
    exact (mergeF_perm _ _ _).trans (((msortF_perm n x).append (msortF_perm n y)).trans hs)

theorem msort_perm (l : List ℕ) : msort l ~ l := msortF_perm 20 l

theorem subF_sound : ∀ (n : ℕ) (l₁ l₂ : List ℕ), subF n l₁ l₂ = true → ∀ a ∈ l₁, a ∈ l₂
  | _, [], _, _, a, ha => absurd ha List.not_mem_nil
  | 0, _ :: _, _, h, _, _ => by rw [subF] at h; exact absurd h Bool.false_ne_true
  | _ + 1, _ :: _, [], h, _, _ => by rw [subF] at h; exact absurd h Bool.false_ne_true
  | n + 1, c :: l₁, b :: l₂, h, a, ha => by
    rw [subF] at h
    cases h1 : Nat.beq c b
    · rw [h1, cond_false] at h
      cases h2 : Nat.blt b c
      · rw [h2, cond_false] at h
        exact absurd h Bool.false_ne_true
      · rw [h2, cond_true] at h
        exact List.mem_cons_of_mem _ (subF_sound n (c :: l₁) l₂ h a ha)
    · rw [h1, cond_true] at h
      have e : c = b := Nat.eq_of_beq_eq_true h1
      subst e
      rcases List.mem_cons.mp ha with rfl | ha
      · exact List.mem_cons_self
      · exact subF_sound n l₁ (c :: l₂) h a ha

theorem sortedB_lt : ∀ (a : ℕ) (l : List ℕ), sortedB (a :: l) = true → ∀ x ∈ l, a < x
  | _, [], _, _, hx => absurd hx List.not_mem_nil
  | a, b :: l, h, x, hx => by
    rw [sortedB, Bool.and_eq_true, Nat.blt_eq] at h
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h.1
    · exact lt_trans h.1 (sortedB_lt b l h.2 x hx)

theorem sortedB_tail {a : ℕ} {l : List ℕ} (h : sortedB (a :: l) = true) : sortedB l = true := by
  cases l with
  | nil => rfl
  | cons b l =>
    rw [sortedB, Bool.and_eq_true] at h
    exact h.2

theorem sortedB_nodup : ∀ l : List ℕ, sortedB l = true → l.Nodup
  | [], _ => List.nodup_nil
  | a :: l, h => List.nodup_cons.mpr ⟨fun ha => lt_irrefl a (sortedB_lt a l h a ha),
      sortedB_nodup l (sortedB_tail h)⟩

theorem eqL_iff : ∀ l₁ l₂ : List ℕ, eqL l₁ l₂ = true ↔ l₁ = l₂
  | [], [] => by simp [eqL]
  | [], _ :: _ => by simp [eqL]
  | _ :: _, [] => by simp [eqL]
  | a :: l₁, b :: l₂ => by
    rw [eqL, Bool.and_eq_true, Nat.beq_eq, eqL_iff l₁ l₂, List.cons.injEq]

variable (act : ℕ → ℕ → ℕ) (ng root : ℕ)

@[expose] def ReachN : ℕ → ℕ → Prop
  | 0, k => k = root
  | n + 1, k => ReachN n k ∨ ∃ s < ng, ∃ p, ReachN n p ∧ act s p = k

variable {act ng root}

theorem ReachN.le {n m k : ℕ} (h : ReachN act ng root n k) (hnm : n ≤ m) :
    ReachN act ng root m k := by
  induction m with
  | zero =>
    obtain rfl : n = 0 := by omega
    exact h
  | succ m ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hnm) with h' | h'
    · exact Or.inl (ih (by omega))
    · rw [h'] at h
      exact h

theorem layersOK_sound : ∀ (rest : List (List (ℕ × ℕ × ℕ))) (B : List ℕ) (m : ℕ),
    layersOK act ng B rest = true → (∀ k ∈ B, ReachN act ng root m k) →
      ∀ ly ∈ rest, ∀ r ∈ ly, ReachN act ng root (m + rest.length) r.1
  | [], _, _, _, _ => fun _ hly => absurd hly List.not_mem_nil
  | ly :: rest, B, m, h, hB => by
    rw [layersOK, Bool.and_eq_true, Bool.and_eq_true, List.all_eq_true] at h
    obtain ⟨⟨hrec, hsub⟩, hnext⟩ := h
    have hsub' := subF_sound _ _ _ hsub
    have hly : ∀ r ∈ ly, ReachN act ng root (m + 1) r.1 := by
      intro r hr
      have h1 := hrec r hr
      rw [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h1
      have hp : r.2.2 ∈ B :=
        hsub' _ ((msort_perm _).mem_iff.mpr (List.mem_map_of_mem hr))
      exact Or.inr ⟨r.2.1, h1.1, r.2.2, hB _ hp, h1.2⟩
    have hB' : ∀ k ∈ msort (B ++ ly.map fun r => r.1), ReachN act ng root (m + 1) k := by
      intro k hk
      rcases List.mem_append.mp ((msort_perm _).mem_iff.mp hk) with hk | hk
      · exact (hB k hk).le (by omega)
      · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hk
        exact hly r hr
    intro ly' hly' r hr
    rw [List.length_cons]
    rcases List.mem_cons.mp hly' with rfl | hly'
    · exact (hly r hr).le (by omega)
    · have := layersOK_sound rest _ (m + 1) hnext hB' ly' hly' r hr
      have e : m + 1 + rest.length = m + (rest.length + 1) := by omega
      rwa [e] at this

theorem certOK_sound {L : List ℕ} {Y : List (List (ℕ × ℕ × ℕ))}
    (h : certOK act ng root L Y = true) :
    root ∈ L ∧ (∀ k ∈ L, ReachN act ng root 64 k) ∧ L.Nodup := by
  unfold certOK at h
  simp only [Bool.and_eq_true, Nat.ble_eq, eqL_iff] at h
  obtain ⟨⟨⟨hlen, hsort⟩, hkeys⟩, hY⟩ := h
  have hperm : L ~ keysY Y := by
    rw [← hkeys]
    exact msort_perm _
  refine ⟨?_, fun k hk => ?_, sortedB_nodup L hsort⟩
  · cases Y with
    | nil => exact absurd hY Bool.false_ne_true
    | cons y₀ rest =>
      rw [Bool.and_eq_true, eqL_iff] at hY
      have : root ∈ y₀.map fun r => r.1 := by rw [hY.1]; exact List.mem_singleton_self _
      exact hperm.mem_iff.mpr (List.mem_flatMap.mpr ⟨y₀, List.mem_cons_self, this⟩)
  · cases Y with
    | nil => exact absurd hY Bool.false_ne_true
    | cons y₀ rest =>
      rw [Bool.and_eq_true, eqL_iff] at hY
      obtain ⟨ly, hly, hk'⟩ := List.mem_flatMap.mp (hperm.mem_iff.mp hk)
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hk'
      rcases List.mem_cons.mp hly with rfl | hly
      · have : r.1 ∈ [root] := hY.1 ▸ List.mem_map_of_mem hr
        rw [List.mem_singleton.mp this]
        have h0 : ReachN act ng root 0 root := rfl
        exact h0.le (by omega)
      · have := layersOK_sound rest [root] 0 hY.2 (fun k hk => by
          rw [List.mem_singleton.mp hk]; rfl) ly hly r hr
        rw [List.length_cons] at hlen
        exact this.le (by omega)

theorem keysY_take_succ (Y : List (List (ℕ × ℕ × ℕ))) (d : ℕ) :
    keysY (Y.take (d + 1)) = keysY (Y.take d) ++ (Y.getD d []).map fun r => r.1 := by
  by_cases hd : d < Y.length
  · rw [List.getD_eq_getElem _ _ hd, List.take_succ_eq_append_getElem hd]
    unfold keysY
    rw [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  · rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega),
      List.getD_eq_default _ _ (by omega)]
    simp

theorem layerOK_reach {B : List ℕ} {ly : List (ℕ × ℕ × ℕ)} {m : ℕ}
    (h : layerOK act ng B ly = true) (hB : ∀ k ∈ B, ReachN act ng root m k) :
    ∀ r ∈ ly, ReachN act ng root (m + 1) r.1 := by
  rw [layerOK, Bool.and_eq_true, List.all_eq_true] at h
  intro r hr
  have h1 := h.1 r hr
  rw [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h1
  have hp : r.2.2 ∈ B :=
    subF_sound _ _ _ h.2 _ ((msort_perm _).mem_iff.mpr (List.mem_map_of_mem hr))
  exact Or.inr ⟨r.2.1, h1.1, r.2.2, hB _ hp, h1.2⟩

theorem certHead_sound {L : List ℕ} {Y : List (List (ℕ × ℕ × ℕ))}
    (h : certHead root L Y = true)
    (hl : ∀ d, 1 ≤ d → d < Y.length → layerOK act ng (msort (keysY (Y.take d))) (Y.getD d []) = true) :
    root ∈ L ∧ (∀ k ∈ L, ReachN act ng root 64 k) ∧ L.Nodup := by
  unfold certHead at h
  simp only [Bool.and_eq_true, Nat.ble_eq, eqL_iff] at h
  obtain ⟨⟨⟨hlen, hsort⟩, hkeys⟩, h0⟩ := h
  have hperm : L ~ keysY Y := by
    rw [← hkeys]
    exact msort_perm _
  have key : ∀ d, ∀ k ∈ keysY (Y.take (d + 1)), ReachN act ng root d k := by
    intro d
    induction d with
    | zero =>
      intro k hk
      rw [keysY_take_succ, List.take_zero] at hk
      simp only [keysY, List.flatMap_nil, List.nil_append] at hk
      rw [h0] at hk
      exact List.mem_singleton.mp hk
    | succ d ih =>
      intro k hk
      rw [keysY_take_succ, List.mem_append] at hk
      rcases hk with hk | hk
      · exact Or.inl (ih k hk)
      · by_cases hd : d + 1 < Y.length
        · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hk
          exact layerOK_reach (hl (d + 1) (by omega) hd)
            (fun k hk => ih k ((msort_perm _).mem_iff.mp hk)) r hr
        · rw [List.getD_eq_default _ _ (by omega)] at hk
          exact absurd hk List.not_mem_nil
  have hY0 : Y ≠ [] := by
    rintro rfl
    simp at h0
  refine ⟨?_, fun k hk => ?_, sortedB_nodup L hsort⟩
  · have : root ∈ keysY (Y.take 1) := by
      rw [keysY_take_succ, List.take_zero, h0]
      simp [keysY]
    refine hperm.mem_iff.mpr ?_
    rw [← List.take_append_drop 1 Y]
    simp only [keysY, List.flatMap_append, List.mem_append] at this ⊢
    exact Or.inl this
  · have hk' : k ∈ keysY (Y.take (Y.length - 1 + 1)) := by
      rw [Nat.sub_add_cancel (List.length_pos_of_ne_nil hY0), List.take_length]
      exact hperm.mem_iff.mp hk
    exact (key _ k hk').le (by omega)

theorem closeOK_sound {L : List ℕ} (h : closeOK act ng L = true) :
    ∀ s < ng, ∀ k ∈ L, act s k ∈ L := by
  intro s hs k hk
  rw [closeOK, List.all_eq_true] at h
  have h1 := h s (List.mem_range.mpr hs)
  rw [eqL_iff] at h1
  have hperm : L ~ L.map (act s) := by
    have := msort_perm (L.map (act s))
    rwa [h1] at this
  exact hperm.mem_iff.mpr (List.mem_map_of_mem hk)

end CFSG.KC.J4M4
