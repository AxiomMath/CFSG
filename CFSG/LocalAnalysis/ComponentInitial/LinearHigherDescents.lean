module

public import Mathlib.Data.Fintype.Prod
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Algebra.Group.End

public section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace LinearFlag

variable {n : ℕ}

@[expose] def adjSwap (n i : ℕ) : Equiv.Perm (Fin n) :=
  if h : 1 ≤ i ∧ i < n then Equiv.swap ⟨i - 1, by omega⟩ ⟨i, h.2⟩ else 1

@[expose] def IsAdjWord (n : ℕ) (l : List ℕ) : Prop :=
  ∀ i ∈ l, 1 ≤ i ∧ i < n

@[expose] def adjWordProd (n : ℕ) (l : List ℕ) : Equiv.Perm (Fin n) :=
  (l.map (adjSwap n)).prod

@[expose] noncomputable def adjLength (w : Equiv.Perm (Fin n)) : ℕ :=
  sInf {k | ∃ l : List ℕ, IsAdjWord n l ∧ l.length = k ∧ adjWordProd n l = w}

@[expose] def inversionCount (w : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ w p.2 < w p.1).card

@[expose] def IsReducedWord (w : Equiv.Perm (Fin n)) (l : List ℕ) : Prop :=
  IsAdjWord n l ∧ adjWordProd n l = w ∧ l.length = adjLength w

theorem adjSwap_of_lt {i : ℕ} (hi : 1 ≤ i) (hin : i < n) :
    adjSwap n i = Equiv.swap ⟨i - 1, by omega⟩ ⟨i, hin⟩ :=
  dite_eq_left ⟨hi, hin⟩

theorem adjSwap_mul_self (i : ℕ) : adjSwap n i * adjSwap n i = 1 := by
  unfold adjSwap
  split_ifs
  · exact Equiv.swap_mul_self _ _
  · exact mul_one 1

theorem adjWordProd_cons (i : ℕ) (l : List ℕ) :
    adjWordProd n (i :: l) = adjSwap n i * adjWordProd n l := by
  simp [adjWordProd]

theorem swap_lt_swap_iff {x y u v : Fin n} (hxy : (y : ℕ) = x + 1)
    (h1 : ¬(u = x ∧ v = y)) (h2 : ¬(u = y ∧ v = x)) :
    Equiv.swap x y u < Equiv.swap x y v ↔ u < v := by
  rw [Equiv.swap_apply_def, Equiv.swap_apply_def]
  simp only [Fin.ext_iff, Fin.lt_def] at *
  split_ifs <;> omega

theorem perm_apply_inv (w : Equiv.Perm (Fin n)) (x : Fin n) : w (w⁻¹ x) = x := by simp

theorem perm_inv_apply (w : Equiv.Perm (Fin n)) (x : Fin n) : w⁻¹ (w x) = x := by simp

theorem inversion_swap_mul_iff {x y : Fin n} (hxy : (y : ℕ) = x + 1) (w : Equiv.Perm (Fin n))
    {p : Fin n × Fin n} (h1 : ¬(w p.2 = x ∧ w p.1 = y)) (h2 : ¬(w p.2 = y ∧ w p.1 = x)) :
    (p.1 < p.2 ∧ (Equiv.swap x y * w) p.2 < (Equiv.swap x y * w) p.1) ↔
      (p.1 < p.2 ∧ w p.2 < w p.1) := by
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, swap_lt_swap_iff hxy h1 h2]

theorem inversionCount_adjSwap_mul {i : ℕ} (hi : 1 ≤ i) (hin : i < n)
    (w : Equiv.Perm (Fin n)) :
    (w⁻¹ ⟨i, hin⟩ < w⁻¹ ⟨i - 1, by omega⟩ →
      inversionCount (adjSwap n i * w) + 1 = inversionCount w) ∧
    (w⁻¹ ⟨i - 1, by omega⟩ < w⁻¹ ⟨i, hin⟩ →
      inversionCount (adjSwap n i * w) = inversionCount w + 1) := by
  classical
  set x : Fin n := ⟨i - 1, by omega⟩ with hx
  set y : Fin n := ⟨i, hin⟩ with hy
  have hxy : (y : ℕ) = x + 1 := by simp [hx, hy]; omega
  rw [adjSwap_of_lt hi hin]
  set s := Equiv.swap x y
  have hpos : ∀ (p : Fin n × Fin n) (a b : Fin n), w p.1 = a → w p.2 = b → p = (w⁻¹ a, w⁻¹ b) :=
    fun p a b h1 h2 => by
      rw [← h1, ← h2, perm_inv_apply, perm_inv_apply]
  constructor
  · intro hlt
    set p₀ : Fin n × Fin n := (w⁻¹ y, w⁻¹ x) with hp₀
    have hp₀mem : p₀ ∈ Finset.univ.filter
        fun p : Fin n × Fin n => p.1 < p.2 ∧ w p.2 < w p.1 := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt, ?_⟩
      rw [hp₀, perm_apply_inv, perm_apply_inv, Fin.lt_def, hxy]
      omega
    have heq : (Finset.univ.filter fun p : Fin n × Fin n =>
        p.1 < p.2 ∧ (s * w) p.2 < (s * w) p.1) =
        (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ w p.2 < w p.1).erase p₀ := by
      ext p
      rw [Finset.mem_erase, Finset.mem_filter, Finset.mem_filter]
      by_cases hp : p = p₀
      · subst hp
        simp only [hp₀, Equiv.Perm.mul_apply, perm_apply_inv, s, Equiv.swap_apply_left,
          Equiv.swap_apply_right, ne_eq, not_true_eq_false, false_and, iff_false, not_and,
          Finset.mem_univ, true_and]
        intro _
        rw [Fin.lt_def, hxy]
        omega
      · have h1 : ¬(w p.2 = x ∧ w p.1 = y) := fun ⟨h2, h1⟩ => hp (hpos p y x h1 h2)
        have h2 : p.1 < p.2 → ¬(w p.2 = y ∧ w p.1 = x) := fun hpl ⟨h2, h1⟩ => by
          rw [hpos p x y h1 h2] at hpl
          exact absurd hlt (not_lt.mpr hpl.le)
        simp only [Finset.mem_univ, true_and, ne_eq, hp, not_false_eq_true]
        constructor
        · rintro ⟨hpl, hinv⟩
          exact (inversion_swap_mul_iff hxy w h1 (h2 hpl)).mp ⟨hpl, hinv⟩
        · rintro ⟨hpl, hinv⟩
          exact (inversion_swap_mul_iff hxy w h1 (h2 hpl)).mpr ⟨hpl, hinv⟩
    rw [inversionCount, inversionCount, heq, Finset.card_erase_of_mem hp₀mem,
      Nat.sub_add_cancel (Finset.card_pos.mpr ⟨_, hp₀mem⟩)]
  · intro hlt
    set p₀ : Fin n × Fin n := (w⁻¹ x, w⁻¹ y) with hp₀
    have hp₀not : p₀ ∉ Finset.univ.filter
        fun p : Fin n × Fin n => p.1 < p.2 ∧ w p.2 < w p.1 := by
      rw [Finset.mem_filter, hp₀, perm_apply_inv, perm_apply_inv, Fin.lt_def, Fin.lt_def, hxy]
      omega
    have heq : (Finset.univ.filter fun p : Fin n × Fin n =>
        p.1 < p.2 ∧ (s * w) p.2 < (s * w) p.1) =
        insert p₀ (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ w p.2 < w p.1) := by
      ext p
      rw [Finset.mem_insert, Finset.mem_filter, Finset.mem_filter]
      by_cases hp : p = p₀
      · subst hp
        simp only [hp₀, Equiv.Perm.mul_apply, perm_apply_inv, s, Equiv.swap_apply_left,
          Equiv.swap_apply_right, true_or, iff_true, Finset.mem_univ, true_and]
        refine ⟨hlt, ?_⟩
        rw [Fin.lt_def, hxy]
        omega
      · have h1 : ¬(w p.2 = y ∧ w p.1 = x) := fun ⟨h2, h1⟩ => hp (hpos p x y h1 h2)
        have h2 : p.1 < p.2 → ¬(w p.2 = x ∧ w p.1 = y) := fun hpl ⟨h2, h1⟩ => by
          rw [hpos p y x h1 h2] at hpl
          exact absurd hlt (not_lt.mpr hpl.le)
        simp only [Finset.mem_univ, true_and, hp, false_or]
        constructor
        · rintro ⟨hpl, hinv⟩
          exact (inversion_swap_mul_iff hxy w (h2 hpl) h1).mp ⟨hpl, hinv⟩
        · rintro ⟨hpl, hinv⟩
          exact (inversion_swap_mul_iff hxy w (h2 hpl) h1).mpr ⟨hpl, hinv⟩
    rw [inversionCount, inversionCount, heq, Finset.card_insert_of_notMem hp₀not]

theorem inversionCount_one : inversionCount (1 : Equiv.Perm (Fin n)) = 0 := by
  rw [inversionCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro ⟨a, b⟩ - ⟨hab, hba⟩
  exact absurd hab (not_lt.mpr hba.le)

theorem eq_one_of_inversionCount_eq_zero {w : Equiv.Perm (Fin n)} (h : inversionCount w = 0) :
    w = 1 := by
  rw [inversionCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h
  have hmono : StrictMono w := fun a b hab => by
    rcases lt_or_gt_of_ne (w.injective.ne hab.ne) with hlt | hgt
    · exact hlt
    · exact absurd ⟨hab, hgt⟩ (h (Finset.mem_univ (a, b)))
  ext a
  exact congrArg Fin.val (hmono.apply_eq (x := a))

theorem strictMono_of_lt_succ {f : Fin n → Fin n}
    (h : ∀ (k : ℕ) (hk : k + 1 < n), f ⟨k, by omega⟩ < f ⟨k + 1, hk⟩) : StrictMono f := by
  have key : ∀ d a (had : a + d + 1 < n), f ⟨a, by omega⟩ < f ⟨a + d + 1, had⟩ := by
    intro d
    induction d with
    | zero => exact fun a had => h a had
    | succ d ih => exact fun a had => (ih a (by omega)).trans (h _ had)
  intro a b hab
  have hab' : (a : ℕ) < b := hab
  have := key (b - a - 1) a (by omega)
  simpa [show (a : ℕ) + (b - a - 1) + 1 = b by omega] using this

theorem exists_descent {w : Equiv.Perm (Fin n)} (hw : w ≠ 1) :
    ∃ (i : ℕ) (hi : 1 ≤ i) (hin : i < n), w⁻¹ ⟨i, hin⟩ < w⁻¹ ⟨i - 1, by omega⟩ := by
  by_contra hcon
  push Not at hcon
  apply hw
  have hmono : StrictMono (w⁻¹ : Equiv.Perm (Fin n)) := by
    refine strictMono_of_lt_succ fun k hk => ?_
    have h1 := hcon (k + 1) (by omega) hk
    simp only [Nat.add_sub_cancel] at h1
    exact lt_of_le_of_ne h1 (w⁻¹.injective.ne (by simp [Fin.ext_iff]))
  have : (w⁻¹ : Equiv.Perm (Fin n)) = 1 := by
    ext a
    exact congrArg Fin.val (hmono.apply_eq (x := a))
  rw [← inv_inv w, this, inv_one]

theorem inversionCount_le_length {l : List ℕ} (hl : IsAdjWord n l) :
    inversionCount (adjWordProd n l) ≤ l.length := by
  induction l with
  | nil => simp [adjWordProd, inversionCount_one]
  | cons i l ih =>
    have hl' : IsAdjWord n l := fun j hj => hl j (List.mem_cons_of_mem _ hj)
    obtain ⟨hi, hin⟩ := hl i List.mem_cons_self
    rw [adjWordProd_cons, List.length_cons]
    have := ih hl'
    have h := inversionCount_adjSwap_mul hi hin (adjWordProd n l)
    rcases lt_or_gt_of_ne ((adjWordProd n l)⁻¹.injective.ne
      (show (⟨i, hin⟩ : Fin n) ≠ ⟨i - 1, by omega⟩ by simp [Fin.ext_iff]; omega)) with hlt | hgt
    · have := h.1 hlt
      omega
    · have := h.2 hgt
      omega

theorem exists_word_length_eq (w : Equiv.Perm (Fin n)) :
    ∃ l : List ℕ, IsAdjWord n l ∧ l.length = inversionCount w ∧ adjWordProd n l = w := by
  induction h : inversionCount w using Nat.strong_induction_on generalizing w with
  | _ m ih =>
    by_cases hw : w = 1
    · subst hw
      refine ⟨[], fun _ h => absurd h List.not_mem_nil, ?_, rfl⟩
      rw [← h, inversionCount_one]
      rfl
    obtain ⟨i, hi, hin, hdesc⟩ := exists_descent hw
    have hcount := (inversionCount_adjSwap_mul hi hin w).1 hdesc
    obtain ⟨l, hl, hlen, hprod⟩ := ih _ (by omega) (adjSwap n i * w) rfl
    refine ⟨i :: l, ?_, ?_, ?_⟩
    · intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · exact ⟨hi, hin⟩
      · exact hl j hj
    · rw [List.length_cons, hlen]
      omega
    · rw [adjWordProd_cons, hprod, ← mul_assoc, adjSwap_mul_self, one_mul]

theorem adjLength_eq_inversionCount (w : Equiv.Perm (Fin n)) :
    adjLength w = inversionCount w := by
  obtain ⟨l, hl, hlen, hprod⟩ := exists_word_length_eq w
  apply le_antisymm
  · exact Nat.sInf_le ⟨l, hl, hlen, hprod⟩
  · obtain ⟨l', hl', hlen', hprod'⟩ := Nat.sInf_mem (s := {k | ∃ l : List ℕ, IsAdjWord n l ∧
      l.length = k ∧ adjWordProd n l = w}) ⟨_, l, hl, rfl, hprod⟩
    rw [adjLength, ← hlen', ← hprod']
    exact inversionCount_le_length hl'

theorem symmetric_group_descents (w : Equiv.Perm (Fin n)) :
    adjLength w = inversionCount w ∧
    (∀ (i : ℕ) (hi : 1 ≤ i) (hin : i < n),
      (adjLength (adjSwap n i * w) = adjLength w - 1 ↔
        w⁻¹ ⟨i, hin⟩ < w⁻¹ ⟨i - 1, by omega⟩) ∧
      (¬ w⁻¹ ⟨i, hin⟩ < w⁻¹ ⟨i - 1, by omega⟩ →
        adjLength (adjSwap n i * w) = adjLength w + 1)) ∧
    (∀ (i : ℕ) (l : List ℕ), IsReducedWord w (i :: l) →
      ∃ (hi : 1 ≤ i) (hin : i < n), w⁻¹ ⟨i, hin⟩ < w⁻¹ ⟨i - 1, by omega⟩ ∧
        IsReducedWord (adjSwap n i * w) l) := by
  have hcrit : ∀ (v : Equiv.Perm (Fin n)) (i : ℕ) (hi : 1 ≤ i) (hin : i < n),
      (adjLength (adjSwap n i * v) = adjLength v - 1 ↔
        v⁻¹ ⟨i, hin⟩ < v⁻¹ ⟨i - 1, by omega⟩) ∧
      (¬ v⁻¹ ⟨i, hin⟩ < v⁻¹ ⟨i - 1, by omega⟩ →
        adjLength (adjSwap n i * v) = adjLength v + 1) := by
    intro v i hi hin
    rw [adjLength_eq_inversionCount, adjLength_eq_inversionCount]
    have h := inversionCount_adjSwap_mul hi hin v
    have hne : v⁻¹ ⟨i - 1, by omega⟩ ≠ v⁻¹ ⟨i, hin⟩ :=
      v⁻¹.injective.ne (by simp [Fin.ext_iff]; omega)
    refine ⟨⟨fun heq => ?_, fun hlt => ?_⟩, fun hnot => h.2 ?_⟩
    · by_contra hnot
      have := h.2 (lt_of_le_of_ne (not_lt.mp hnot) hne)
      omega
    · have := h.1 hlt
      omega
    · exact lt_of_le_of_ne (not_lt.mp hnot) hne
  refine ⟨adjLength_eq_inversionCount w, hcrit w, fun i l ⟨hl, hprod, hlen⟩ => ?_⟩
  obtain ⟨hi, hin⟩ := hl i List.mem_cons_self
  have hl' : IsAdjWord n l := fun j hj => hl j (List.mem_cons_of_mem _ hj)
  have hsw : adjWordProd n l = adjSwap n i * w := by
    rw [← hprod, adjWordProd_cons, ← mul_assoc, adjSwap_mul_self, one_mul]
  have hle : adjLength (adjSwap n i * w) ≤ l.length := Nat.sInf_le ⟨l, hl', rfl, hsw⟩
  rw [List.length_cons] at hlen
  have hdesc : w⁻¹ ⟨i, hin⟩ < w⁻¹ ⟨i - 1, by omega⟩ := by
    by_contra hnot
    have := (hcrit w i hi hin).2 hnot
    omega
  refine ⟨hi, hin, hdesc, hl', hsw, ?_⟩
  have := (hcrit w i hi hin).1.mpr hdesc
  omega

end LinearFlag

end CFSG.LocalAnalysis.ComponentInitial
