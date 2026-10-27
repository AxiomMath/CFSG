module

public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Simple

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.YS08

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.UniquenessMaximal CFSG.HardMathSupport.Solomon.Coordinator

@[expose] def L3Ord (r : ℕ) (ε : Bool) : ℕ :=
  r ^ 3 * (r ^ 2 - 1) * (if ε then r ^ 3 - 1 else r ^ 3 + 1)

@[expose] def L3Cond (r : ℕ) (ε : Bool) : Prop :=
  (ε = true → 4 ≤ r ∧ r % 3 = 1) ∧ (ε = false → 5 ≤ r ∧ r % 3 = 2)

theorem sl3Eps_card_forms {p : ℕ} {X : Type} [Group X] [Finite X] (h : SL3EpsOfChar p X) :
    ∃ (r : ℕ) (ε : Bool), L3Cond r ε ∧ Nat.card X = L3Ord r ε := by
  rcases h with ⟨F, hF, hfin, -, hmod, ⟨e⟩⟩ | ⟨F, hF, hfin, q, -, hcard, hq3, hq2, ⟨e⟩⟩
  · have hnt : Nontrivial F := inferInstance
    have hq1 : 1 < Nat.card F := Finite.one_lt_card_iff_nontrivial.2 hnt
    refine ⟨Nat.card F, true, ⟨fun _ => ⟨by omega, hmod⟩, fun h => by simp at h⟩, ?_⟩
    rw [Nat.card_congr e.toEquiv, CFSG.SectionRank.OddCover.card_statedSL_three]
    simp [L3Ord]
  · refine ⟨q, false, ⟨fun h => by simp at h, fun _ => ⟨by omega, hq3⟩⟩, ?_⟩
    rw [Nat.card_congr e.toEquiv, CFSG.SectionRank.OddCover.card_statedSU_three_of_card_eq_sq hcard]
    simp [L3Ord]

theorem isL3Kind_card_forms {p : ℕ} {X : Type} [Group X] [Finite X] (h : IsL3Kind p X) :
    ∃ (r : ℕ) (ε : Bool) (e : ℕ), (e = 1 ∨ e = 3) ∧ L3Cond r ε ∧ Nat.card X * e = L3Ord r ε := by
  rcases h with hSL | ⟨W, hW, hWSL, ⟨f⟩⟩
  · obtain ⟨r, ε, hc, hcard⟩ := sl3Eps_card_forms hSL
    exact ⟨r, ε, 1, Or.inl rfl, hc, by rw [mul_one, hcard]⟩
  · haveI : Finite W := by
      rcases hWSL with ⟨F, hF, hfin, -, -, ⟨e⟩⟩ | ⟨F, hF, hfin, q, -, -, -, -, ⟨e⟩⟩
      · exact Finite.of_equiv _ e.symm.toEquiv
      · exact Finite.of_equiv _ e.symm.toEquiv
    obtain ⟨r, ε, hc, hcard⟩ := sl3Eps_card_forms hWSL
    obtain ⟨hZ3, -⟩ := sl3Eps_facts hWSL
    refine ⟨r, ε, 3, Or.inr rfl, hc, ?_⟩
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center W)
    rw [hZ3, ← Nat.card_congr f.toEquiv] at h1
    rw [← hcard, h1]

theorem L3Ord_ge {r : ℕ} {ε : Bool} (h : L3Cond r ε) : 60480 ≤ L3Ord r ε := by
  cases ε
  · obtain ⟨h5, -⟩ := h.2 rfl
    unfold L3Ord
    simp only [Bool.false_eq_true, ↓reduceIte]
    have h125 : 125 ≤ r ^ 3 := by
      calc 125 = 5 ^ 3 := by norm_num
        _ ≤ r ^ 3 := Nat.pow_le_pow_left h5 3
    have h25 : 25 ≤ r ^ 2 := by
      calc 25 = 5 ^ 2 := by norm_num
        _ ≤ r ^ 2 := Nat.pow_le_pow_left h5 2
    calc 60480 ≤ 125 * 24 * 126 := by norm_num
      _ ≤ r ^ 3 * (r ^ 2 - 1) * (r ^ 3 + 1) :=
        Nat.mul_le_mul (Nat.mul_le_mul h125 (by omega)) (by omega)
  · obtain ⟨h4, -⟩ := h.1 rfl
    unfold L3Ord
    simp only [↓reduceIte]
    have h64 : 64 ≤ r ^ 3 := by
      calc 64 = 4 ^ 3 := by norm_num
        _ ≤ r ^ 3 := Nat.pow_le_pow_left h4 3
    have h16 : 16 ≤ r ^ 2 := by
      calc 16 = 4 ^ 2 := by norm_num
        _ ≤ r ^ 2 := Nat.pow_le_pow_left h4 2
    calc 60480 = 64 * 15 * 63 := by norm_num
      _ ≤ r ^ 3 * (r ^ 2 - 1) * (r ^ 3 - 1) :=
        Nat.mul_le_mul (Nat.mul_le_mul h64 (by omega)) (by omega)

theorem isL3Kind_ge {p : ℕ} {X : Type} [Group X] [Finite X] (h : IsL3Kind p X) :
    20160 ≤ Nat.card X := by
  obtain ⟨r, ε, e, he, hc, hcard⟩ := isL3Kind_card_forms h
  have := L3Ord_ge hc
  rcases he with rfl | rfl <;> omega

theorem L3Ord_pow_le {r : ℕ} {ε : Bool} (h : L3Cond r ε) : r ^ 8 ≤ 4 * L3Ord r ε := by
  have h4 : 4 ≤ r := by
    cases ε
    · exact le_trans (by norm_num) (h.2 rfl).1
    · exact (h.1 rfl).1
  have h2 : 2 ≤ r ^ 2 := by nlinarith
  have h3 : 2 ≤ r ^ 3 := by nlinarith [Nat.pow_le_pow_left h4 3]
  have h1 : r ^ 2 ≤ 2 * (r ^ 2 - 1) := by omega
  cases ε
  · unfold L3Ord
    simp only [Bool.false_eq_true, ↓reduceIte]
    have h1' : r ^ 3 ≤ 2 * (r ^ 3 + 1) := by omega
    calc r ^ 8 = r ^ 3 * r ^ 2 * r ^ 3 := by ring
      _ ≤ r ^ 3 * (2 * (r ^ 2 - 1)) * (2 * (r ^ 3 + 1)) :=
        Nat.mul_le_mul (Nat.mul_le_mul le_rfl h1) h1'
      _ = 4 * (r ^ 3 * (r ^ 2 - 1) * (r ^ 3 + 1)) := by ring
  · unfold L3Ord
    simp only [↓reduceIte]
    have h1' : r ^ 3 ≤ 2 * (r ^ 3 - 1) := by omega
    calc r ^ 8 = r ^ 3 * r ^ 2 * r ^ 3 := by ring
      _ ≤ r ^ 3 * (2 * (r ^ 2 - 1)) * (2 * (r ^ 3 - 1)) :=
        Nat.mul_le_mul (Nat.mul_le_mul le_rfl h1) h1'
      _ = 4 * (r ^ 3 * (r ^ 2 - 1) * (r ^ 3 - 1)) := by ring

theorem L3Ord_dvd {r : ℕ} {ε : Bool} (h : L3Cond r ε) : 27 ∣ L3Ord r ε := by
  cases ε
  · obtain ⟨h5, hmod⟩ := h.2 rfl
    obtain ⟨t, rfl⟩ : ∃ t, r = 3 * t + 2 := ⟨r / 3, by omega⟩
    have e2 : (3 * t + 2) ^ 2 - 1 = 3 * ((3 * t + 1) * (t + 1)) :=
      Nat.sub_eq_of_eq_add (by ring)
    have e3 : (3 * t + 2) ^ 3 + 1 = 9 * ((t + 1) * (3 * t ^ 2 + 3 * t + 1)) := by ring
    unfold L3Ord
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [e2, e3]
    exact ⟨(3 * t + 2) ^ 3 * ((3 * t + 1) * (t + 1)) * ((t + 1) * (3 * t ^ 2 + 3 * t + 1)),
      by ring⟩
  · obtain ⟨h4, hmod⟩ := h.1 rfl
    obtain ⟨t, rfl⟩ : ∃ t, r = 3 * t + 1 := ⟨r / 3, by omega⟩
    have e2 : (3 * t + 1) ^ 2 - 1 = 3 * (t * (3 * t + 2)) :=
      Nat.sub_eq_of_eq_add (by ring)
    have e3 : (3 * t + 1) ^ 3 - 1 = 9 * (t * (3 * t ^ 2 + 3 * t + 1)) :=
      Nat.sub_eq_of_eq_add (by ring)
    unfold L3Ord
    simp only [↓reduceIte]
    rw [e2, e3]
    exact ⟨(3 * t + 1) ^ 3 * (t * (3 * t + 2)) * (t * (3 * t ^ 2 + 3 * t + 1)), by ring⟩

theorem isL3Kind_ninth {p : ℕ} {X : Type} [Group X] [Finite X] (h : IsL3Kind p X) :
    9 ∣ Nat.card X := by
  obtain ⟨r, ε, e, he, hc, hcard⟩ := isL3Kind_card_forms h
  obtain ⟨m, hm⟩ := L3Ord_dvd hc
  rcases he with rfl | rfl
  · exact ⟨3 * m, by omega⟩
  · exact ⟨m, by omega⟩

@[expose] def NoL3Eq (N : ℕ) : Prop :=
  ∀ (r : ℕ) (ε : Bool) (e : ℕ), (e = 1 ∨ e = 3) → L3Cond r ε → N * e ≠ L3Ord r ε

@[expose] def L3Check (N B : ℕ) : Bool :=
  (List.range B).all fun i => [true, false].all fun ε => [1, 3].all fun e =>
    decide (N * e ≠ L3Ord (i + 4) ε)

theorem noL3Eq_of_check {N B : ℕ} (hB : 12 * N < (B + 4) ^ 8) (h : L3Check N B = true) :
    NoL3Eq N := by
  intro r ε e he hc heq
  have hr4 : 4 ≤ r := by
    cases ε
    · exact le_trans (by norm_num) (hc.2 rfl).1
    · exact (hc.1 rfl).1
  have hrB : r < B + 4 := by
    by_contra hge
    push Not at hge
    have h1 : (B + 4) ^ 8 ≤ r ^ 8 := Nat.pow_le_pow_left hge 8
    have h2 := L3Ord_pow_le hc
    rw [← heq] at h2
    have h3 : 4 * (N * e) ≤ 12 * N := by rcases he with rfl | rfl <;> omega
    omega
  have hall := List.all_eq_true.1 h (r - 4) (List.mem_range.2 (by omega))
  have h2 := List.all_eq_true.1 hall ε (by cases ε <;> simp)
  have h3 := List.all_eq_true.1 h2 e (by rcases he with rfl | rfl <;> simp)
  have hr : r - 4 + 4 = r := by omega
  rw [hr] at h3
  exact of_decide_eq_true h3 heq

theorem noL3Eq_175560 : NoL3Eq 175560 := noL3Eq_of_check (B := 40) (by norm_num) (by decide +kernel)
theorem noL3Eq_7920 : NoL3Eq 7920 := noL3Eq_of_check (B := 40) (by norm_num) (by decide +kernel)

end CFSG.HardMathSupport.Solomon.Coordinator.YS08
