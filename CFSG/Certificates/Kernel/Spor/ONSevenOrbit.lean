module

public import CFSG.RankThree.Native.ONSevenArrays
import CFSG.Certificates.Kernel.SporSch.KeyBfsSound

public section

namespace CFSG.KS.ONOrb

open CFSG.RankThree.Native CFSG.Sporadic.ON.Native
open CFSG.KS.KeyBfs (forIn_range'_done push_lt push_eq)

structure ORec (gs : Array (Array Nat)) (cnt : Nat) (T D : Nat → Nat) : Prop where
  k_pos : 0 < gs.size
  three_le : 3 ≤ cnt
  le_n : cnt ≤ 245520
  t0 : T 0 = 0
  t1 : T 1 = 227759
  t2 : T 2 = 100817
  inj : ∀ a < cnt, ∀ b < cnt, T a = T b → a = b
  tree : ∀ i, 3 ≤ i → i < cnt → D i / gs.size < i ∧ (gs[D i % gs.size]!)[T (D i / gs.size)]! = T i
  order : ∀ i, 3 ≤ i → i + 1 < cnt → D i < D (i + 1)
  close : ∀ h < cnt, ∀ j < gs.size, ∃ q < cnt, (gs[j]!)[T h]! = T q ∧
    (q < 3 ∨ D q ≤ gs.size * h + j)

def Inv (cnt : Nat) (T D : Nat → Nat) (e : Nat) (s : Array Nat × Std.HashMap Nat Nat) : Prop :=
  s.1.size ≤ cnt ∧ (∀ i < s.1.size, s.1[i]! = T i) ∧
    (∀ x, s.2.contains x = true ↔ ∃ i < s.1.size, T i = x) ∧
    ∀ i < cnt, (i < s.1.size ↔ (i < 3 ∨ D i < e))

section

variable {gs : Array (Array Nat)} {cnt : Nat} {T D : Nat → Nat}

theorem order_lt (R : ORec gs cnt T D) {i i' : Nat} (h3 : 3 ≤ i) (hi : i < i') (hi' : i' < cnt) :
    D i < D i' := by
  induction i' with
  | zero => omega
  | succ i' ih =>
    rcases Nat.lt_or_ge i i' with a | a
    · exact Nat.lt_trans (ih a (by omega)) (R.order i' (by omega) hi')
    · have e : i = i' := by omega
      subst e
      exact R.order i h3 hi'

theorem D_inj (R : ORec gs cnt T D) {i i' : Nat} (h3 : 3 ≤ i) (h3' : 3 ≤ i') (hi : i < cnt)
    (hi' : i' < cnt) (e : D i = D i') : i = i' := by
  rcases Nat.lt_trichotomy i i' with a | a | a
  · have := order_lt R h3 a hi'
    omega
  · exact a
  · have := order_lt R h3' a hi
    omega

theorem three_le_size {e : Nat} {s : Array Nat × Std.HashMap Nat Nat} (R : ORec gs cnt T D)
    (hI : Inv cnt T D e s) : 3 ≤ s.1.size := by
  have := (hI.2.2.2 2 (by have := R.three_le; omega)).2 (Or.inl (by omega))
  omega

theorem inv_step (R : ORec gs cnt T D) {h j : Nat} (hj : j < gs.size)
    {s : Array Nat × Std.HashMap Nat Nat} (hh : h < s.1.size)
    (hI : Inv cnt T D (gs.size * h + j) s) :
    Inv cnt T D (gs.size * h + (j + 1))
      (if (!s.2.contains ((gs[j]!)[s.1[h]!]!)) = true then
        (s.1.push ((gs[j]!)[s.1[h]!]!), s.2.insert ((gs[j]!)[s.1[h]!]!) s.1.size) else s) ∧
      h < (if (!s.2.contains ((gs[j]!)[s.1[h]!]!)) = true then
        (s.1.push ((gs[j]!)[s.1[h]!]!), s.2.insert ((gs[j]!)[s.1[h]!]!) s.1.size) else s).1.size := by
  obtain ⟨hle, hget, hK, hch⟩ := hI
  have hhc : h < cnt := by omega
  rw [hget h hh]
  obtain ⟨q, hq, hy, hor⟩ := R.close h hhc j hj
  rw [hy]
  by_cases hnew : 3 ≤ q ∧ D q = gs.size * h + j
  · obtain ⟨hq3, hDq⟩ := hnew
    have hqn : ¬ q < s.1.size := fun a => by
      rcases (hch q hq).1 a with b | b <;> omega
    have hnc : s.2.contains (T q) = false := by
      rw [Bool.eq_false_iff]
      intro hc
      obtain ⟨i, hi, e⟩ := (hK _).1 hc
      have := R.inj i (by omega) q hq e
      omega
    have hqs : q = s.1.size := by
      refine Nat.le_antisymm (Nat.le_of_not_lt fun hlt => ?_) (Nat.le_of_not_lt hqn)
      have h1 := (hch s.1.size (by omega)).1
      have h2 : s.1.size < 3 ∨ D s.1.size < gs.size * h + j := by
        by_cases h3 : s.1.size < 3
        · exact Or.inl h3
        · exact Or.inr (by have := order_lt R (by omega) hlt hq; omega)
      have := (hch s.1.size (by omega)).2 h2
      omega
    have es : (if (!s.2.contains (T q)) = true then
        (s.1.push (T q), s.2.insert (T q) s.1.size) else s) =
        (s.1.push (T q), s.2.insert (T q) s.1.size) := by
      rw [hnc]
      rfl
    rw [es]
    refine ⟨⟨?_, fun i hi => ?_, fun x => ?_, fun i hi => ?_⟩, ?_⟩
    · change (s.1.push (T q)).size ≤ cnt
      rw [Array.size_push]
      omega
    · change i < (s.1.push (T q)).size at hi
      change (s.1.push (T q))[i]! = T i
      rw [Array.size_push] at hi
      rcases Nat.lt_or_ge i s.1.size with a | a
      · rw [push_lt a]
        exact hget i a
      · have e : i = s.1.size := by omega
        rw [e, push_eq, ← hqs]
    · change (s.2.insert (T q) s.1.size).contains x = true ↔ ∃ i < (s.1.push (T q)).size, T i = x
      rw [Array.size_push, Std.HashMap.contains_insert, Bool.or_eq_true, beq_iff_eq, hK]
      constructor
      · rintro (e | ⟨i, hi, e⟩)
        · exact ⟨q, by omega, e⟩
        · exact ⟨i, by omega, e⟩
      · rintro ⟨i, hi, e⟩
        rcases Nat.lt_or_ge i s.1.size with a | a
        · exact Or.inr ⟨i, a, e⟩
        · have e' : i = q := by omega
          rw [e'] at e
          exact Or.inl e
    · change i < (s.1.push (T q)).size ↔ _
      rw [Array.size_push]
      constructor
      · intro a
        rcases Nat.lt_or_ge i s.1.size with b | b
        · rcases (hch i hi).1 b with c | c
          · exact Or.inl c
          · exact Or.inr (by omega)
        · have e : i = q := by omega
          rw [e]
          exact Or.inr (by omega)
      · rintro (a | a)
        · have := (hch i hi).2 (Or.inl a)
          omega
        · by_cases hlt : D i < gs.size * h + j
          · have := (hch i hi).2 (Or.inr hlt)
            omega
          · by_cases h3 : i < 3
            · have := (hch i hi).2 (Or.inl h3)
              omega
            · have := D_inj R (by omega) hq3 hi hq (by omega)
              omega
    · change h < (s.1.push (T q)).size
      rw [Array.size_push]
      omega
  · have hqs : q < s.1.size := (hch q hq).2 (by
      rcases hor with a | a
      · exact Or.inl a
      · by_cases h3 : q < 3
        · exact Or.inl h3
        · exact Or.inr (by
            have : ¬ D q = gs.size * h + j := fun e => hnew ⟨by omega, e⟩
            omega))
    have hc : s.2.contains (T q) = true := (hK _).2 ⟨q, hqs, rfl⟩
    have es : (if (!s.2.contains (T q)) = true then
        (s.1.push (T q), s.2.insert (T q) s.1.size) else s) = s := by
      rw [hc]
      rfl
    rw [es]
    refine ⟨⟨hle, hget, hK, fun i hi => ?_⟩, hh⟩
    rw [hch i hi]
    constructor
    · rintro (a | a)
      · exact Or.inl a
      · exact Or.inr (by omega)
    · rintro (a | a)
      · exact Or.inl a
      · by_cases hlt : D i < gs.size * h + j
        · exact Or.inr hlt
        · by_cases h3 : i < 3
          · exact Or.inl h3
          · exfalso
            have hDi : D i = gs.size * h + j := by omega
            obtain ⟨-, hTi⟩ := R.tree i (by omega) hi
            have em : D i % gs.size = j := by
              rw [hDi, Nat.mul_add_mod, Nat.mod_eq_of_lt hj]
            have ed : D i / gs.size = h := by
              rw [hDi, Nat.mul_add_div R.k_pos, Nat.div_eq_of_lt hj, Nat.add_zero]
            rw [em, ed, hy] at hTi
            have := R.inj q hq i hi hTi
            subst this
            exact hnew ⟨by omega, hDi⟩

theorem inv_inner (R : ORec gs cnt T D) {h : Nat} :
    ∀ (l : List (Array Nat)) (j : Nat), l = gs.toList.drop j → j ≤ gs.size →
      ∀ s : Array Nat × Std.HashMap Nat Nat, h < s.1.size → Inv cnt T D (gs.size * h + j) s →
      Inv cnt T D (gs.size * h + gs.size)
        (Id.run (forIn l s fun g (s : Array Nat × Std.HashMap Nat Nat) =>
          if (!s.2.contains (g[s.1[h]!]!)) = true then
            pure (ForInStep.yield (s.1.push (g[s.1[h]!]!), s.2.insert (g[s.1[h]!]!) s.1.size))
          else pure (ForInStep.yield (s.1, s.2))))
  | [], j, hl, hj, s, _, hI => by
    have : j = gs.size := by
      have := congrArg List.length hl
      simp at this
      omega
    subst this
    exact hI
  | g :: l, j, hl, hj, s, hh, hI => by
    have hjs : j < gs.size := by
      rcases Nat.lt_or_ge j gs.size with a | a
      · exact a
      · have : gs.toList.drop j = [] := List.drop_eq_nil_of_le (by simpa using a)
        rw [this] at hl
        exact absurd hl (List.cons_ne_nil g l)
    have hg : g = gs[j]! := by
      have h1 : gs.toList.drop j = gs[j] :: gs.toList.drop (j + 1) := by
        rw [List.drop_eq_getElem_cons (by simpa using hjs)]
        simp
      rw [h1] at hl
      rw [getElem!_pos gs j hjs]
      exact (List.cons.inj hl).1
    have hl' : l = gs.toList.drop (j + 1) := by
      have h1 : gs.toList.drop j = gs[j] :: gs.toList.drop (j + 1) := by
        rw [List.drop_eq_getElem_cons (by simpa using hjs)]
        simp
      rw [h1] at hl
      exact (List.cons.inj hl).2
    obtain ⟨hI', hh'⟩ := inv_step R hjs hh hI
    rw [List.forIn_cons]
    subst hg
    by_cases hc : (!s.2.contains ((gs[j]!)[s.1[h]!]!)) = true
    · simp only [hc, ↓reduceIte] at hI' hh' ⊢
      exact inv_inner R l (j + 1) hl' (by omega) _ hh' (by rw [← Nat.add_assoc]; exact hI')
    · simp only [hc, Bool.false_eq_true, ↓reduceIte] at hI' hh' ⊢
      exact inv_inner R l (j + 1) hl' (by omega) _ hh' (by rw [← Nat.add_assoc]; exact hI')

theorem full_of (R : ORec gs cnt T D) {h : Nat} {s : Array Nat × Std.HashMap Nat Nat}
    (hI : Inv cnt T D (gs.size * h) s) (hh : s.1.size ≤ h) : s.1.size = cnt := by
  have h3 := three_le_size R hI
  obtain ⟨hle, -, -, hch⟩ := hI
  refine Nat.le_antisymm hle (Nat.le_of_not_lt fun hlt => ?_)
  have hn : ¬ (s.1.size < 3 ∨ D s.1.size < gs.size * h) := fun a =>
    Nat.lt_irrefl _ ((hch _ hlt).2 a)
  obtain ⟨hlt', -⟩ := R.tree s.1.size h3 hlt
  have e1 := Nat.div_add_mod (D s.1.size) gs.size
  have e2 := Nat.mod_lt (D s.1.size) R.k_pos
  have e3 := Nat.mul_le_mul_left gs.size (by omega : D s.1.size / gs.size + 1 ≤ h)
  rw [Nat.mul_succ] at e3
  omega

theorem ofFn_eq {a : Array Nat} (hs : a.size = cnt) (hget : ∀ i < a.size, a[i]! = T i) :
    a = Array.ofFn (n := cnt) fun i => T i.val := by
  apply Array.ext
  · simp [hs]
  · intro i h1 h2
    rw [Array.getElem_ofFn, ← hget i h1, getElem!_pos a i h1]

theorem onSevenOrbit_eq (R : ORec gs cnt T D) :
    onSevenOrbit gs = Array.ofFn (n := cnt) fun i => T i.val := by
  unfold onSevenOrbit
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Id.run, nPts,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, ← Array.forIn_toList]
  have hinit : Inv cnt T D 0 (onSevenBase,
      (((∅ : Std.HashMap Nat Nat).insert 0 0).insert 227759 1).insert 100817 2) := by
    have hb : ∀ i < 3, onSevenBase[i]! = T i := by
      intro i hi
      interval_cases i
      · rw [R.t0]
        decide
      · rw [R.t1]
        decide
      · rw [R.t2]
        decide
    have hsz : onSevenBase.size = 3 := rfl
    refine ⟨by rw [hsz]; exact R.three_le, by rw [hsz]; exact hb, fun x => ?_, fun i _ => ?_⟩
    · rw [hsz]
      simp only [Std.HashMap.contains_insert, Std.HashMap.contains_empty, Bool.or_false,
        Bool.or_eq_true, beq_iff_eq]
      constructor
      · rintro (e | e | e)
        · exact ⟨2, by omega, by rw [R.t2]; exact e⟩
        · exact ⟨1, by omega, by rw [R.t1]; exact e⟩
        · exact ⟨0, by omega, by rw [R.t0]; exact e⟩
      · rintro ⟨i, hi, e⟩
        interval_cases i
        · exact Or.inr (Or.inr (by rw [← e, R.t0]))
        · exact Or.inr (Or.inl (by rw [← e, R.t1]))
        · exact Or.inl (by rw [← e, R.t2])
    · rw [hsz]
      omega
  refine forIn_range'_done 245520 0 _ _ (fun h s => Inv cnt T D (gs.size * h) s)
    (fun s => s.1 = Array.ofFn (n := cnt) fun i => T i.val) (fun h hh s hI => ?_)
    (fun s hI => ?_) (by simpa using hinit)
  · rw [Nat.zero_add]
    by_cases hs : h < s.1.size
    · left
      refine ⟨_, by simp only [hs, ↓reduceIte]; rfl, ?_⟩
      have := inv_inner R gs.toList 0 (by simp) (Nat.zero_le _) (s.1, s.2) hs
        (by simpa using hI)
      rw [Nat.mul_succ]
      exact this
    · right
      refine ⟨s, by simp only [hs, ↓reduceIte], ?_⟩
      exact ofFn_eq (full_of R hI (by omega)) hI.2.1
  · have hsz := full_of R hI (by have := hI.1; have := R.le_n; omega)
    exact ofFn_eq hsz hI.2.1

end

end CFSG.KS.ONOrb

end
