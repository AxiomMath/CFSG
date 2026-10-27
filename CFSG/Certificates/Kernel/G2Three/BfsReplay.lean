module

public import CFSG.Quasithin.Background.G2UClosure
public import Batteries.Data.Array.Lemmas
public import Std.Data.HashMap.Lemmas

public section

namespace CFSG.KC.G2Three

open CFSG.Quasithin.G2U

def BInv (E : Array (List ℕ)) (P : Array (ℕ × ℕ)) (c : ℕ)
    (st : Array (List ℕ) × Array (ℕ × ℕ) × Std.HashMap (List ℕ) Unit) : Prop :=
  st.1 = E.extract 0 c ∧ st.2.1 = P.extract 0 (c - 1) ∧
    ∀ y, st.2.2.contains y = true ↔ ∃ t < c, E.getD t [] = y

theorem getD_extract {E : Array (List ℕ)} {c h : ℕ} (hh : h < c) (hc : c ≤ E.size) :
    (E.extract 0 c).getD h [] = E.getD h [] := by
  have h1 : h < (E.extract 0 c).size := by simp; omega
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h1,
    Array.getElem?_eq_getElem (by omega), Array.getElem_extract]
  simp

@[expose] def StepOK (mul : List ℕ → List ℕ → List ℕ) (gens : List (List ℕ)) (E : Array (List ℕ))
    (P : Array (ℕ × ℕ)) (C POS : ℕ → ℕ) (h s i : ℕ) : Prop :=
  (h < C i → POS i ≤ C i ∧ POS i < E.size ∧
      E.getD (POS i) [] = mul (E.getD h []) (gens.getD s []) ∧
      (POS i = C i → C (i + 1) = C i + 1 ∧ P.getD (C i - 1) (0, 0) = (h, s)) ∧
      (POS i < C i → C (i + 1) = C i)) ∧
    (¬ h < C i → C (i + 1) = C i)

theorem step_mono {mul : List ℕ → List ℕ → List ℕ} {gens : List (List ℕ)} {E : Array (List ℕ)}
    {P : Array (ℕ × ℕ)} {C POS : ℕ → ℕ} {h s i : ℕ} (hs : StepOK mul gens E P C POS h s i) :
    C i ≤ C (i + 1) := by
  by_cases hh : h < C i
  · obtain ⟨h1, -, -, h4, h5⟩ := hs.1 hh
    rcases Nat.lt_or_eq_of_le h1 with h1 | h1
    · rw [h5 h1]
    · rw [(h4 h1).1]
      omega
  · rw [hs.2 hh]

theorem inner_step {mul : List ℕ → List ℕ → List ℕ} {gens : List (List ℕ)} {E : Array (List ℕ)}
    {P : Array (ℕ × ℕ)} {C POS : ℕ → ℕ} {h s i : ℕ}
    (hd : ∀ t < E.size, ∀ t' < E.size, E.getD t [] = E.getD t' [] → t = t')
    (hPs : P.size + 1 = E.size) (hsl : s < gens.length)
    (hs : StepOK mul gens E P C POS h s i) (hh : h < C i) (hc : C i ≤ E.size)
    {st : Array (List ℕ) × Array (ℕ × ℕ) × Std.HashMap (List ℕ) Unit} (hst : BInv E P (C i) st) :
    BInv E P (C (i + 1))
      (let y := mul (st.1.getD h []) (gens.toArray.getD s [])
       if st.2.2.contains y then st else (st.1.push y, st.2.1.push (h, s), st.2.2.insert y ())) := by
  obtain ⟨hp1, hp2, hp3, hp4, hp5⟩ := hs.1 hh
  obtain ⟨e1, e2, e3⟩ := hst
  have hg : gens.toArray.getD s [] = gens.getD s [] := by
    rw [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, List.getElem?_toArray]
  have hy : mul (st.1.getD h []) (gens.toArray.getD s []) = E.getD (POS i) [] := by
    rw [e1, getD_extract hh hc, hg, hp3]
  simp only
  rw [hy]
  rcases Nat.lt_or_eq_of_le hp1 with hlt | heq
  · have hin : st.2.2.contains (E.getD (POS i) []) = true := (e3 _).2 ⟨POS i, hlt, rfl⟩
    rw [if_pos hin, hp5 hlt]
    exact ⟨e1, e2, e3⟩
  · have hout : st.2.2.contains (E.getD (POS i) []) = false := by
      cases hm : st.2.2.contains (E.getD (POS i) [])
      · rfl
      · obtain ⟨t, ht, he⟩ := (e3 _).1 hm
        have := hd t (by omega) (POS i) hp2 he
        omega
    obtain ⟨hc1, hc2⟩ := hp4 heq
    rw [if_neg (by rw [hout]; exact Bool.false_ne_true), hc1]
    refine ⟨?_, ?_, fun y => ?_⟩ <;> dsimp only
    · rw [e1, heq, Array.extract_succ_right (by omega) (by omega)]
      congr 1
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by omega)]
      rfl
    · have hc0 : 0 < C i := by omega
      have e : C i + 1 - 1 = (C i - 1) + 1 := by omega
      rw [e2, e, Array.extract_succ_right (by omega) (by omega)]
      congr 1
      rw [← hc2, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by omega)]
      rfl
    · simp only [Std.HashMap.contains_insert, Bool.or_eq_true, beq_iff_eq]
      rw [e3]
      constructor
      · rintro (h1 | ⟨t, ht, h2⟩)
        · exact ⟨C i, by omega, by rw [← heq, h1]⟩
        · exact ⟨t, by omega, h2⟩
      · rintro ⟨t, ht, h2⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | ht
        · exact Or.inr ⟨t, ht, h2⟩
        · subst ht
          exact Or.inl (by rw [heq, h2])

theorem head_step {mul : List ℕ → List ℕ → List ℕ} {gens : List (List ℕ)} {E : Array (List ℕ)}
    {P : Array (ℕ × ℕ)} {C POS : ℕ → ℕ} {h : ℕ}
    (hd : ∀ t < E.size, ∀ t' < E.size, E.getD t [] = E.getD t' [] → t = t')
    (hPs : P.size + 1 = E.size)
    (hs : ∀ s < gens.length, StepOK mul gens E P C POS h s (h * gens.length + s))
    (hc : C (h * gens.length + gens.length) ≤ E.size) :
    ∀ st, BInv E P (C (h * gens.length)) st →
      BInv E P (C (h * gens.length + gens.length)) (bfsStep mul gens.toArray st h) := by
  intro st hst
  have hmono : ∀ s ≤ gens.length, C (h * gens.length + s) ≤ C (h * gens.length + gens.length) ∧
      C (h * gens.length) ≤ C (h * gens.length + s) := by
    intro s hs'
    induction s with
    | zero => exact ⟨by
        have key : ∀ r ≤ gens.length, C (h * gens.length + (gens.length - r)) ≤
            C (h * gens.length + gens.length) := by
          intro r hr
          induction r with
          | zero => simp
          | succ r ihr =>
            have h1 := step_mono (hs (gens.length - (r + 1)) (by omega))
            have e : h * gens.length + (gens.length - (r + 1)) + 1 =
                h * gens.length + (gens.length - r) := by omega
            rw [e] at h1
            exact h1.trans (ihr (by omega))
        have := key gens.length le_rfl
        simpa using this, le_rfl⟩
    | succ s ih =>
      obtain ⟨_, i2⟩ := ih (by omega)
      have h1 := step_mono (hs s (by omega))
      rw [Nat.add_assoc] at h1
      refine ⟨?_, i2.trans h1⟩
      have key : ∀ r ≤ gens.length - (s + 1), C (h * gens.length + (gens.length - r)) ≤
          C (h * gens.length + gens.length) := by
        intro r hr
        induction r with
        | zero => simp
        | succ r ihr =>
          have h1 := step_mono (hs (gens.length - (r + 1)) (by omega))
          have e : h * gens.length + (gens.length - (r + 1)) + 1 =
              h * gens.length + (gens.length - r) := by omega
          rw [e] at h1
          exact h1.trans (ihr (by omega))
      have := key (gens.length - (s + 1)) le_rfl
      have e : gens.length - (gens.length - (s + 1)) = s + 1 := by omega
      rwa [e] at this
  unfold bfsStep
  have hc0 : C (h * gens.length) ≤ E.size := by
    have := (hmono 0 (Nat.zero_le _)).1
    rw [Nat.add_zero] at this
    omega
  have hsz : st.1.size = C (h * gens.length) := by
    rw [hst.1]
    simp
    omega
  by_cases hh : h < st.1.size
  · rw [if_pos hh]
    have hlen : gens.toArray.size = gens.length := List.size_toArray
    rw [hlen]
    have key : ∀ s ≤ gens.length, BInv E P (C (h * gens.length + s))
        ((List.range s).foldl (fun st s =>
          let y := mul (st.1.getD h []) (gens.toArray.getD s [])
          if st.2.2.contains y then st else (st.1.push y, st.2.1.push (h, s), st.2.2.insert y ()))
          st) := by
      intro s hs'
      induction s with
      | zero => simpa using hst
      | succ s ih =>
        rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
        have hlt : h < C (h * gens.length + s) := by
          have := (hmono s (by omega)).2
          omega
        exact inner_step hd hPs (by omega) (hs s (by omega)) hlt
          (((hmono s (by omega)).1).trans hc) (ih (by omega))
    exact key gens.length le_rfl
  · rw [if_neg hh]
    have key : ∀ s ≤ gens.length, C (h * gens.length + s) = C (h * gens.length) := by
      intro s hs'
      induction s with
      | zero => rfl
      | succ s ih =>
        rw [← Nat.add_assoc, (hs s (by omega)).2 (by rw [ih (by omega)]; omega), ih (by omega)]
    rw [key gens.length le_rfl]
    exact hst

theorem bfsParents_replay {one : List ℕ} {mul : List ℕ → List ℕ → List ℕ} {gens : List (List ℕ)}
    {fuel : ℕ} {E : Array (List ℕ)} {P : Array (ℕ × ℕ)} {C POS : ℕ → ℕ}
    (hE0 : E.getD 0 [] = one) (hpos : 0 < E.size)
    (hd : ∀ t < E.size, ∀ t' < E.size, E.getD t [] = E.getD t' [] → t = t')
    (hPs : P.size + 1 = E.size) (hC0 : C 0 = 1)
    (hs : ∀ h < fuel, ∀ s < gens.length,
      StepOK mul gens E P C POS h s (h * gens.length + s))
    (hfin : C (fuel * gens.length) = E.size) :
    bfsParents one mul gens fuel = P.toList := by
  have hmono : ∀ i, i < fuel * gens.length → C i ≤ C (i + 1) := by
    intro i hi
    have hk : 0 < gens.length := by
      rcases Nat.eq_zero_or_pos gens.length with h0 | h0
      · rw [h0, Nat.mul_zero] at hi
        omega
      · exact h0
    have hh : i / gens.length < fuel := by
      rw [Nat.div_lt_iff_lt_mul hk]
      exact hi
    have e : i / gens.length * gens.length + i % gens.length = i := by
      rw [Nat.mul_comm]
      exact Nat.div_add_mod i gens.length
    have := step_mono (hs (i / gens.length) hh (i % gens.length) (Nat.mod_lt _ hk))
    rwa [e] at this
  have hle : ∀ j, j ≤ fuel * gens.length → C (fuel * gens.length - j) ≤ E.size := by
    intro j hj
    induction j with
    | zero => simp [hfin]
    | succ j ih =>
      have e : fuel * gens.length - j = fuel * gens.length - (j + 1) + 1 := by omega
      have := hmono (fuel * gens.length - (j + 1)) (by omega)
      rw [← e] at this
      exact this.trans (ih (by omega))
  have hcle : ∀ i ≤ fuel * gens.length, C i ≤ E.size := by
    intro i hi
    have := hle (fuel * gens.length - i) (by omega)
    rwa [Nat.sub_sub_self hi] at this
  have init : BInv E P (C 0) (#[one], #[], ({} : Std.HashMap (List ℕ) Unit).insert one ()) := by
    rw [hC0]
    refine ⟨?_, ?_, fun y => ?_⟩
    · apply Array.ext (by simp; omega)
      intro j h1 h2
      have hj : j = 0 := by simp at h1; omega
      subst hj
      simp only [Array.getElem_extract, Nat.zero_add]
      rw [← hE0, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hpos]
      rfl
    · simp
    · simp only [Std.HashMap.contains_insert, Std.HashMap.contains_empty, Bool.or_false,
        beq_iff_eq]
      constructor
      · rintro rfl
        exact ⟨0, by omega, hE0⟩
      · rintro ⟨t, ht, h2⟩
        have : t = 0 := by omega
        subst this
        rw [← h2, hE0]
  have key : ∀ h ≤ fuel, BInv E P (C (h * gens.length))
      ((List.range h).foldl (bfsStep mul gens.toArray)
        (#[one], #[], ({} : Std.HashMap (List ℕ) Unit).insert one ())) := by
    intro h hh
    induction h with
    | zero => simpa using init
    | succ h ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, Nat.succ_mul]
      exact head_step hd hPs (hs h (by omega))
        (hcle _ (by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hh)) _ (ih (by omega))
  obtain ⟨-, e2, -⟩ := key fuel le_rfl
  unfold bfsParents
  rw [e2, hfin, ← hPs, Nat.add_sub_cancel, Array.extract_size]

end CFSG.KC.G2Three

end
