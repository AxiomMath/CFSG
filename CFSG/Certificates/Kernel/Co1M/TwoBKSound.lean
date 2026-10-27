module

public import Certificates.Data.Kernel.Co1M.TwoBK
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.KC.Co1M

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.M1F2 CFSG.KC.Co1F2

theorem getL_eq (x : Nat) : ∀ (L : List Nat) (i : Nat), getL x L i = L.getD i x
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: L, i + 1 => getL_eq x L i

theorem andB_true {a b : Bool} (h : andB a b = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all [andB]

theorem orB_true {a b : Bool} (h : orB a b = true) : a = true ∨ b = true := by
  cases a <;> cases b <;> simp_all [orB]

theorem strictB_of {y : Nat} {k : Nat → Bool} (h : strictB y k = true) : k y = true := by
  cases y <;> exact h

theorem brec_of_true {c t e : Bool} (h : Bool.rec (motive := fun _ => Bool) e t c = true)
    (hc : c = true) : t = true := by
  subst hc
  exact h

theorem brec_of_false {c t e : Bool} (h : Bool.rec (motive := fun _ => Bool) e t c = true)
    (hc : c = false) : e = true := by
  subst hc
  exact h

theorem blt_true {a b : Nat} (h : a < b) : Nat.blt a b = true := by
  rw [Nat.blt_eq]
  exact h

theorem lt_of_blt {a b : Nat} (h : Nat.blt a b = true) : a < b := by
  rwa [Nat.blt_eq] at h

theorem notB_beq {a b : Nat} (h : notB (Nat.beq a b) = true) : a ≠ b := by
  cases e : Nat.beq a b
  · exact Nat.ne_of_beq_eq_false e
  · rw [e] at h
    simp [notB] at h

theorem allN_true {n : Nat} {f : Nat → Bool} (h : allN n f = true) : ∀ i < n, f i = true := by
  induction n with
  | zero => intro i hi; exact absurd hi (Nat.not_lt_zero i)
  | succ n ih =>
    obtain ⟨h1, h2⟩ := andB_true h
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · exact ih h2 i hi
    · exact h1

theorem sym_spec {AP : Nat} (h : symK AP = true) : ∀ i < 24, ∀ j < 24, avK AP i j = avK AP j i :=
  fun i hi j hj => Nat.eq_of_beq_eq_true (allN_true (allN_true h i hi) j hj)

theorem dist_core {AP w : Nat} (h : distFK AP w = true) {i j k l : Nat} (hi : i < 24) (hj : j < 24)
    (hk : k < 24) (hl : l < 24) (hij : i < j) (hkl : k < l) (hne : ¬ (i = k ∧ j = l)) :
    avK AP i j ≠ avK AP k l ∧ avK AP i j ≠ avK AP k l ^^^ w := by
  have h2 := strictB_of (brec_of_true (allN_true (allN_true h i hi) j hj) (blt_true hij))
  have h4 := brec_of_true (allN_true (allN_true h2 k hk) l hl) (blt_true hkl)
  have hc : andB (Nat.beq i k) (Nat.beq j l) = false := by
    cases e1 : Nat.beq i k with
    | false => rfl
    | true =>
      cases e2 : Nat.beq j l with
      | false => rfl
      | true => exact absurd ⟨Nat.eq_of_beq_eq_true e1, Nat.eq_of_beq_eq_true e2⟩ hne
  obtain ⟨h6, h7⟩ := andB_true (strictB_of (brec_of_false h4 hc))
  exact ⟨notB_beq h6, notB_beq h7⟩

theorem dist_spec {AP w : Nat} (hd : distFK AP w = true) (hs : symK AP = true) :
    ∀ i j k l, i < 24 → j < 24 → k < 24 → l < 24 → i ≠ j → k ≠ l →
      (avK AP i j = avK AP k l ∨ avK AP i j = avK AP k l ^^^ w) →
        (i = k ∧ j = l) ∨ (i = l ∧ j = k) := by
  have sym := sym_spec hs
  have core : ∀ i j k l, i < 24 → j < 24 → k < 24 → l < 24 → i < j → k < l →
      (avK AP i j = avK AP k l ∨ avK AP i j = avK AP k l ^^^ w) → i = k ∧ j = l := by
    intro i j k l hi hj hk hl hij hkl he
    by_cases hne : i = k ∧ j = l
    · exact hne
    · obtain ⟨h1, h2⟩ := dist_core hd hi hj hk hl hij hkl hne
      rcases he with e | e
      · exact absurd e h1
      · exact absurd e h2
  intro i j k l hi hj hk hl hij hkl he
  rcases Nat.lt_or_gt_of_ne hij with hij' | hij' <;> rcases Nat.lt_or_gt_of_ne hkl with hkl' | hkl'
  · exact Or.inl (core i j k l hi hj hk hl hij' hkl' he)
  · rw [sym k hk l hl] at he
    obtain ⟨e1, e2⟩ := core i j l k hi hj hl hk hij' hkl' he
    exact Or.inr ⟨e1, e2⟩
  · rw [sym i hi j hj] at he
    obtain ⟨e1, e2⟩ := core j i k l hj hi hk hl hij' hkl' he
    exact Or.inr ⟨e2, e1⟩
  · rw [sym i hi j hj, sym k hk l hl] at he
    obtain ⟨e1, e2⟩ := core j i l k hj hi hl hk hij' hkl' he
    exact Or.inl ⟨e2, e1⟩

theorem ind_spec {AP w MT P : Nat} (h : indK AP w MT P = true) :
    vmF 24 MT w = w ∧ ∀ i < 24, ∀ j < 24, i < j →
      (vmF 24 MT (avK AP i j) = avK AP (ppg P i) (ppg P j) ∨
        vmF 24 MT (avK AP i j) = avK AP (ppg P i) (ppg P j) ^^^ w) := by
  obtain ⟨h1, h2⟩ := andB_true h
  refine ⟨Nat.eq_of_beq_eq_true h1, fun i hi j hj hij => ?_⟩
  have h3 := brec_of_true (allN_true (allN_true h2 i hi) j hj) (blt_true hij)
  have h3 := strictB_of h3
  have h3 := strictB_of h3
  rcases orB_true h3 with e | e
  · exact Or.inl (Nat.eq_of_beq_eq_true e)
  · exact Or.inr (Nat.eq_of_beq_eq_true e)

theorem ind_full {AP w MT P : Nat} (h : indK AP w MT P = true) (hs : symK AP = true)
    (hP : ∀ i < 24, ppg P i < 24) :
    vmF 24 MT w = w ∧ ∀ i < 24, ∀ j < 24, i ≠ j →
      (vmF 24 MT (avK AP i j) = avK AP (ppg P i) (ppg P j) ∨
        vmF 24 MT (avK AP i j) = avK AP (ppg P i) (ppg P j) ^^^ w) := by
  obtain ⟨h0, h1⟩ := ind_spec h
  have sym := sym_spec hs
  refine ⟨h0, fun i hi j hj hij => ?_⟩
  rcases Nat.lt_or_gt_of_ne hij with hlt | hlt
  · exact h1 i hi j hj hlt
  · rw [sym i hi j hj, sym (ppg P i) (hP i hi) (ppg P j) (hP j hj)]
    exact h1 j hj i hi hlt

theorem ind1_spec {AP w MT : Nat} (h : ind1K AP w MT = true) :
    vmF 24 MT w = w ∧ ∀ i < 24, ∀ j < 24, i < j →
      (vmF 24 MT (avK AP i j) = avK AP i j ∨ vmF 24 MT (avK AP i j) = avK AP i j ^^^ w) := by
  obtain ⟨h1, h2⟩ := andB_true h
  refine ⟨Nat.eq_of_beq_eq_true h1, fun i hi j hj hij => ?_⟩
  have h3 := brec_of_true (allN_true (allN_true h2 i hi) j hj) (blt_true hij)
  have h3 := strictB_of h3
  have h3 := strictB_of h3
  rcases orB_true h3 with e | e
  · exact Or.inl (Nat.eq_of_beq_eq_true e)
  · exact Or.inr (Nat.eq_of_beq_eq_true e)

theorem ind1_full {AP w MT : Nat} (h : ind1K AP w MT = true) (hs : symK AP = true) :
    vmF 24 MT w = w ∧ ∀ i < 24, ∀ j < 24, i ≠ j →
      (vmF 24 MT (avK AP i j) = avK AP i j ∨ vmF 24 MT (avK AP i j) = avK AP i j ^^^ w) := by
  obtain ⟨h0, h1⟩ := ind1_spec h
  have sym := sym_spec hs
  refine ⟨h0, fun i hi j hj hij => ?_⟩
  rcases Nat.lt_or_gt_of_ne hij with hlt | hlt
  · exact h1 i hi j hj hlt
  · rw [sym i hi j hj]
    exact h1 j hj i hi hlt

theorem perm_spec {P Pi : Nat} (h : permK P Pi = true) : ∀ i < 24,
    ppg P i < 24 ∧ ppg Pi i < 24 ∧ ppg P (ppg Pi i) = i ∧ ppg Pi (ppg P i) = i := by
  intro i hi
  obtain ⟨h1, h⟩ := andB_true (allN_true h i hi)
  obtain ⟨h2, h⟩ := andB_true h
  obtain ⟨h3, h4⟩ := andB_true h
  exact ⟨lt_of_blt h1, lt_of_blt h2, Nat.eq_of_beq_eq_true h3, Nat.eq_of_beq_eq_true h4⟩

theorem zip_spec {α : Type} {f : α → Nat → Bool} (d : α) : ∀ {xs : List α} {ys : List Nat},
    zipK f xs ys = true → ys.length = xs.length ∧ ∀ k < xs.length, f (xs.getD k d) (ys.getD k 0) = true
  | [], [], _ => ⟨rfl, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | x :: xs, y :: ys, h => by
    obtain ⟨h1, h2⟩ := andB_true h
    obtain ⟨e, h3⟩ := zip_spec d h2
    refine ⟨by simp [e], fun k hk => ?_⟩
    cases k with
    | zero => simpa using h1
    | succ k => simpa using h3 k (by simpa using hk)

theorem invs_spec {E : List Nat} (h : invsK E = true) : ∀ e ∈ prodsK E 5, mulF 24 e e = idF 24 := by
  have h' : List.rec (motive := fun _ => Bool) true
      (fun e _ ih => andB (Nat.beq (mulF 24 e e) (idF 24)) ih) (prodsK E 5) = true := h
  generalize prodsK E 5 = L at h'
  induction L with
  | nil => intro e he; cases he
  | cons a L ih =>
    obtain ⟨h1, h2⟩ := andB_true h'
    intro e he
    rcases List.mem_cons.1 he with rfl | he
    · exact Nat.eq_of_beq_eq_true h1
    · exact ih h2 e he

theorem bit_testBit (X i : Nat) : bit X i = X.testBit i := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  change Nat.beq ((X >>> i) &&& 1) 1 = _
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, Bool.eq_iff_iff, Nat.beq_eq,
    decide_eq_true_iff]

theorem uni_spec {U : Nat} (h : uniK U = true) : ∀ i < 24,
    (∀ j < i, (fget U i 24).testBit j = false) ∧ (fget U i 24).testBit i = true := by
  intro i hi
  obtain ⟨h1, h2⟩ := andB_true (strictB_of (allN_true h i hi))
  have e1 : fget U i 24 &&& (2 ^ i - 1) = 0 := by
    have := Nat.eq_of_beq_eq_true h1
    have hp : pw2 i = 2 ^ i := Nat.one_shiftLeft i
    rw [hp] at this
    exact this
  refine ⟨fun j hj => ?_, ?_⟩
  · have := congrArg (fun x => x.testBit j) e1
    simp only [Nat.testBit_and, Nat.testBit_two_pow_sub_one, Nat.zero_testBit] at this
    simpa [hj] using this
  · rw [← bit_testBit]
    exact h2

end CFSG.KC.Co1M

end
