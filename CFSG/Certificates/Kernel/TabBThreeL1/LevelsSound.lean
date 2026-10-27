module

public import Certificates.Data.Kernel.TabBThreeL1Checks
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabBThreeL1Vec

public section

namespace CFSG.HardMathSupport.Dickson.I271.TabBThreeL1

open CFSG.Monster.B.Classical.E6Adjoint CFSG.Blueprint.Chevalley

theorem ch17575_levMask_ge {j : ℕ} (hj : 5 ≤ j) : levMask j = 0 := by
  rw [levMask, List.getD_eq_default _ _ (by simp only [List.length_cons, List.length_nil]; omega)]

theorem ch17575_lev_lt (hM : levMaskOK levMask = true) {k : ℕ} (hk : k < 78) : lev k < 5 := by
  simp only [levMaskOK, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at hM
  exact (hM.2 k hk).1

theorem ch17575_levMask_testBit (hM : levMaskOK levMask = true) {k : ℕ} (hk : k < 78) (j : ℕ) :
    (levMask j).testBit k = true ↔ lev k = j := by
  have hlt := ch17575_lev_lt hM hk
  simp only [levMaskOK, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq,
    beq_iff_eq] at hM
  by_cases hj : j < 5
  · rw [(hM.2 k hk).2 j hj]
    simp
  · rw [ch17575_levMask_ge (by omega), Nat.zero_testBit]
    simp only [Bool.false_eq_true, false_iff]
    omega

theorem ch17575_gradedOK (h0 : gradedRows brMask fbit 0 26 = true)
    (h1 : gradedRows brMask fbit 26 26 = true) (h2 : gradedRows brMask fbit 52 26 = true)
    {a b : ℕ} (ha : a < 78) (hb : b < 78) : gradedOK brMask fbit a b = true := by
  simp only [gradedRows, List.all_eq_true, List.mem_range] at h0 h1 h2
  by_cases ha1 : a < 26
  · have h := h0 a ha1 b hb
    rwa [Nat.zero_add] at h
  · by_cases ha2 : a < 52
    · have h := h1 (a - 26) (by omega) b hb
      rwa [show 26 + (a - 26) = a by omega] at h
    · have h := h2 (a - 52) (by omega) b hb
      rwa [show 52 + (a - 52) = a by omega] at h

abbrev Ch17575Graded : Prop := ∀ {a b : ℕ}, a < 78 → b < 78 → gradedOK brMask fbit a b = true

theorem ch17575_brMask_lev (hM : levMaskOK levMask = true) (hG : Ch17575Graded) {a b c : ℕ}
    (ha : a < 78) (hb : b < 78) (hc : c < 78) (hbit : (brMask a b).testBit c = true) :
    lev a + lev b = lev c + 2 := by
  have g := hG ha hb
  simp only [gradedOK, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at g
  rcases g.1 with h0 | ⟨h2, hand⟩
  · rw [h0, Nat.zero_testBit] at hbit
    exact absurd hbit Bool.false_ne_true
  · rw [← hand, Nat.testBit_and, Bool.and_eq_true] at hbit
    have := (ch17575_levMask_testBit hM hc _).1 hbit.2
    omega

theorem ch17575_fbit_lev (hG : Ch17575Graded) {a b : ℕ} (ha : a < 78) (hb : b < 78)
    (h : fbit a b = true) : lev a + lev b = 4 := by
  have g := hG ha hb
  simp only [gradedOK, Bool.and_eq_true, h, Bool.not_true, Bool.false_or, beq_iff_eq] at g
  exact g.2

variable {R : Type*} [CommRing R]

theorem ch17575_toVec_apply (m : ℕ) (k : Fin 78) :
    toVec R m (lab k) = if m.testBit k then 1 else 0 := by
  rw [toVec, Finsupp.finset_sum_apply, Finset.sum_eq_single k]
  · split_ifs <;> simp
  · intro j _ hj
    split_ifs
    · rw [Finsupp.single_apply, if_neg fun h => hj (lab_injective h)]
    · rfl
  · simp

theorem ch17575_eLab_apply (j k : Fin 78) : eLab R j (lab k) = if j = k then 1 else 0 := by
  rw [eLab, Finsupp.single_apply]
  by_cases h : j = k
  · rw [if_pos (congrArg lab h), if_pos h]
  · rw [if_neg fun h' => h (lab_injective h'), if_neg h]

theorem ch17575_eq_sum (y : RootModule Tag.E6 R) : y = ∑ k : Fin 78, y (lab k) • eLab R k := by
  ext l
  obtain ⟨k₀, rfl⟩ := lab_surjective l
  rw [Finsupp.finset_sum_apply, Finset.sum_eq_single k₀]
  · rw [Finsupp.smul_apply, ch17575_eLab_apply, if_pos rfl, smul_eq_mul, mul_one]
  · intro j _ hj
    rw [Finsupp.smul_apply, ch17575_eLab_apply, if_neg hj, smul_zero]
  · simp

theorem ch17575_ext {y w : RootModule Tag.E6 R} (h : ∀ k : Fin 78, y (lab k) = w (lab k)) :
    y = w := by
  ext l
  obtain ⟨k, rfl⟩ := lab_surjective l
  exact h k

variable [CharP R 2]

theorem ch17575_bracket_apply (a : Fin 78) (y : RootModule Tag.E6 R) (c : Fin 78) :
    bracket R (eLab R a) y (lab c) =
      ∑ k : Fin 78, if (brMask a k).testBit c then y (lab k) else 0 := by
  conv_lhs => rw [ch17575_eq_sum y]
  rw [map_sum, Finsupp.finset_sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, eLab, eLab, bracket_lab, Finsupp.smul_apply, ch17575_toVec_apply, smul_eq_mul]
  split_ifs <;> simp

theorem ch17575_bracket_lev (hM : levMaskOK levMask = true) (hG : Ch17575Graded) (a b c : Fin 78)
    (h : bracket R (eLab R a) (eLab R b) (lab c) ≠ 0) : lev a + lev b = lev c + 2 := by
  rw [eLab, eLab, bracket_lab, ch17575_toVec_apply] at h
  by_cases hb : (brMask a b).testBit c = true
  · exact ch17575_brMask_lev hM hG a.2 b.2 c.2 hb
  · simp [hb] at h

theorem ch17575_form_lev (hG : Ch17575Graded) (a b : Fin 78)
    (h : form R (eLab R a) (eLab R b) ≠ 0) : lev a + lev b = 4 := by
  rw [eLab, eLab, form_lab] at h
  by_cases hb : fbit a b = true
  · exact ch17575_fbit_lev hG a.2 b.2 hb
  · simp [hb] at h

theorem ch17575_piv_zero (f : ℕ → ℕ → ℕ) (g : ℕ → R) :
    ∀ P : List (ℕ × ℕ × ℕ), pivOK f P = true → (∀ p ∈ P, p.1 < 78) →
      (∀ k : Fin 78, (k : ℕ) ∉ P.map (·.1) → g k = 0) →
      (∀ p ∈ P, ∑ k : Fin 78, (if (f p.2.1 k).testBit p.2.2 then g k else 0) = 0) →
      ∀ p ∈ P, g p.1 = 0
  | [], _, _, _, _, p, hp => absurd hp List.not_mem_nil
  | (k, β, c) :: P, h, hlt, hsupp, hE, p, hp => by
    simp only [pivOK, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at h
    obtain ⟨⟨hkc, hclean⟩, hP⟩ := h
    have hk78 : k < 78 := hlt _ List.mem_cons_self
    have hk : g k = 0 := by
      have e := hE (k, β, c) List.mem_cons_self
      rw [Finset.sum_eq_single (⟨k, hk78⟩ : Fin 78)] at e
      · simpa only [hkc, if_true] using e
      · intro j _ hj
        by_cases hjP : (j : ℕ) ∈ P.map (·.1)
        · obtain ⟨q, hq, hqj⟩ := List.mem_map.1 hjP
          have := hclean q hq
          rw [hqj] at this
          simp [this]
        · have hj' : (j : ℕ) ∉ ((k, β, c) :: P).map (·.1) := by
            simp only [List.map_cons, List.mem_cons, not_or]
            exact ⟨fun h => hj (Fin.ext h), hjP⟩
          simp [hsupp j hj']
      · simp
    rcases List.mem_cons.1 hp with rfl | hp
    · exact hk
    · refine ch17575_piv_zero f g P hP (fun q hq => hlt q (List.mem_cons_of_mem _ hq)) ?_
        (fun q hq => hE q (List.mem_cons_of_mem _ hq)) p hp
      intro j hj
      by_cases hjk : (j : ℕ) = k
      · rw [hjk]
        exact hk
      · refine hsupp j ?_
        simp only [List.map_cons, List.mem_cons, not_or]
        exact ⟨hjk, hj⟩

theorem ch17575_testBit_certMask (P : List (ℕ × ℕ × ℕ)) (k : ℕ) :
    (certMask P).testBit k = true ↔ k ∈ P.map (·.1) := by
  induction P with
  | nil => simp [certMask]
  | cons p P ih =>
    rw [certMask, List.foldr_cons, ← certMask, Nat.testBit_or, Bool.or_eq_true, ih,
      Nat.one_shiftLeft, Nat.testBit_two_pow, decide_eq_true_eq, List.map_cons, List.mem_cons]
    exact or_congr ⟨fun h => h.symm, fun h => h.symm⟩ Iff.rfl

theorem ch17575_piv_lev (hM : levMaskOK levMask = true) (f : ℕ → ℕ → ℕ) (P : List (ℕ × ℕ × ℕ))
    (hP : pivOK f P = true) (hlt : ∀ p ∈ P, p.1 < 78) {j : ℕ} (hcert : certMask P = levMask j)
    (y : RootModule Tag.E6 R) (hy : ∀ k : Fin 78, lev k ≠ j → y (lab k) = 0)
    (hE : ∀ p ∈ P, ∑ k : Fin 78, (if (f p.2.1 k).testBit p.2.2 then y (lab k) else 0) = 0) :
    y = 0 := by
  set g : ℕ → R := fun k => if h : k < 78 then y (lab ⟨k, h⟩) else 0 with hg
  have hgk : ∀ k : Fin 78, g k = y (lab k) := fun k => by rw [hg]; simp
  have hmem : ∀ k : Fin 78, (k : ℕ) ∈ P.map (·.1) ↔ lev k = j := fun k => by
    rw [← ch17575_testBit_certMask, hcert, ch17575_levMask_testBit hM k.2]
  have h0 := ch17575_piv_zero f g P hP hlt
    (fun k hk => by rw [hgk]; exact hy k fun h => hk ((hmem k).2 h))
    (fun p hp => by simpa only [hgk] using hE p hp)
  refine ch17575_ext fun k => ?_
  rw [Finsupp.zero_apply]
  by_cases hk : lev k = j
  · obtain ⟨p, hp, hpk⟩ := List.mem_map.1 ((hmem k).2 hk)
    have := h0 p hp
    rw [hpk, hgk] at this
    exact this
  · exact hy k hk

theorem ch17575_adSq_test (hA : adSqTestOK testB = true) (β k : Fin 78) (hβ : (β : ℕ) ∈ testB)
    (hk : lev k = 1) : bracket R (eLab R β) (bracket R (eLab R β) (eLab R k)) = 0 := by
  simp only [adSqTestOK, List.all_eq_true, List.mem_range, Bool.or_eq_true, bne_iff_ne,
    ne_eq] at hA
  rcases hA β hβ k k.2 with h | h
  · exact absurd hk h
  · exact adSq_lab h

theorem ch17575_testB_lt : ∀ β ∈ testB, β < 78 := by decide

theorem ch17575_test_kernel (hM : levMaskOK levMask = true)
    (hP : pivOK brMask ch17575PivTest = true ∧ certMask ch17575PivTest = levMask 1 ∧
      ch17575PivTest.all (fun p => decide (p.1 < 78) && testB.contains p.2.1 &&
        decide (p.2.2 < 78)) = true)
    (y : RootModule Tag.E6 R) (hy : ∀ k : Fin 78, lev k ≠ 1 → y (lab k) = 0)
    (hβ : ∀ β : Fin 78, (β : ℕ) ∈ testB → bracket R (eLab R β) y = 0) : y = 0 := by
  obtain ⟨hpiv, hcert, hall⟩ := hP
  simp only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] at hall
  refine ch17575_piv_lev hM brMask _ hpiv (fun p hp => (hall p hp).1.1) hcert y hy ?_
  intro p hp
  obtain ⟨⟨-, hb⟩, hc⟩ := hall p hp
  have := congrArg (fun v => v (lab ⟨p.2.2, hc⟩)) (hβ ⟨p.2.1, ch17575_testB_lt _ hb⟩ hb)
  simp only [Finsupp.zero_apply] at this
  rw [ch17575_bracket_apply] at this
  exact this

theorem ch17575_xOne_apply (a : Fin 78) (y : RootModule Tag.E6 R) (c : Fin 78) :
    xOne R (eLab R a) y (lab c) = y (lab c) +
      (∑ k : Fin 78, if (brMask a k).testBit c then y (lab k) else 0) +
        if a = c then form R (eLab R a) y else 0 := by
  rw [xOne, Finsupp.add_apply, Finsupp.add_apply, Finsupp.smul_apply, ch17575_bracket_apply,
    ch17575_eLab_apply, smul_eq_mul]
  split_ifs <;> simp

theorem ch17575_sum_eq_zero (a c : Fin 78) (y : RootModule Tag.E6 R)
    (h : ∀ k : Fin 78, (brMask a k).testBit c = true → False) :
    (∑ k : Fin 78, if (brMask a k).testBit c then y (lab k) else 0) = 0 :=
  Finset.sum_eq_zero fun k _ => if_neg fun hb => h k hb

theorem ch17575_fixed_lev_of (hM : levMaskOK levMask = true) (hG : Ch17575Graded)
    (θp θm : Fin 78) (hθp : lev θp = 4) (hθm : lev θm = 0) (P : List (ℕ × ℕ × ℕ))
    (hpiv : pivOK brMask P = true) (hcert : certMask P = levMask 1)
    (hall : ∀ p ∈ P, ((p.1 < 78 ∧ p.2.1 = θp) ∧ p.2.2 < 78) ∧ lev p.2.2 = 3)
    (y : RootModule Tag.E6 R) (hz : xOne R (eLab R θp) (xOne R (eLab R θm) y) = y) :
    ∀ k : Fin 78, lev k = 1 → y (lab k) = 0 := by
  set w := xOne R (eLab R θm) y with hw
  have hlev : ∀ {a b c : Fin 78}, (brMask a b).testBit c = true → lev a + lev b = lev c + 2 :=
    fun h => ch17575_brMask_lev hM hG (Fin.isLt _) (Fin.isLt _) (Fin.isLt _) h
  have hne : ∀ {a c : Fin 78}, lev a ≠ lev c → a ≠ c := fun h e =>
    h (congrArg (fun x : Fin 78 => lev x) e)
  have hw3 : ∀ c : Fin 78, lev c = 3 → w (lab c) = y (lab c) := by
    intro c hc
    rw [hw, ch17575_xOne_apply, ch17575_sum_eq_zero, if_neg (hne (by omega)), add_zero,
      add_zero]
    intro k hk
    have h1 := hlev hk
    have h2 := ch17575_lev_lt hM k.2
    omega
  have hz1 : ∀ c : Fin 78, lev c = 1 → y (lab c) = w (lab c) := by
    intro c hc
    rw [← congrArg (fun v => v (lab c)) hz, ch17575_xOne_apply, ch17575_sum_eq_zero,
      if_neg (hne (by omega)), add_zero, add_zero]
    intro k hk
    have := hlev hk
    omega
  have hz3 : ∀ c : Fin 78, lev c = 3 →
      (∑ k : Fin 78, if (brMask θp k).testBit c then y (lab k) else 0) = 0 := by
    intro c hc
    have e : xOne R (eLab R θp) w (lab c) = y (lab c) := by rw [hz]
    rw [ch17575_xOne_apply, if_neg (hne (by omega)), add_zero, hw3 c hc] at e
    have hs : (∑ k : Fin 78, if (brMask θp k).testBit c then w (lab k) else 0) =
        ∑ k : Fin 78, if (brMask θp k).testBit c then y (lab k) else 0 := by
      refine Finset.sum_congr rfl fun k _ => ?_
      split_ifs with hk
      · have := hlev hk
        exact (hz1 k (by omega)).symm
      · rfl
    rw [hs] at e
    exact add_eq_left.1 e
  set g : ℕ → R := fun k => if h : k < 78 then (if lev k = 1 then y (lab ⟨k, h⟩) else 0) else 0
    with hg
  have hgk : ∀ k : Fin 78, g k = if lev k = 1 then y (lab k) else 0 := fun k => by
    rw [hg]
    simp
  have hmem : ∀ k : Fin 78, (k : ℕ) ∈ P.map (·.1) ↔ lev k = 1 := fun k => by
    rw [← ch17575_testBit_certMask, hcert, ch17575_levMask_testBit hM k.2]
  have h0 := ch17575_piv_zero brMask g P hpiv (fun p hp => (hall p hp).1.1.1)
    (fun k hk => by rw [hgk, if_neg fun h => hk ((hmem k).2 h)])
    (fun p hp => by
      obtain ⟨⟨⟨-, hθ⟩, hc⟩, hc3⟩ := hall p hp
      have e := hz3 ⟨p.2.2, hc⟩ hc3
      rw [hθ]
      refine Eq.trans (Finset.sum_congr rfl fun k _ => ?_) e
      split_ifs with hk
      · rw [hgk, if_pos]
        have := hlev (c := ⟨p.2.2, hc⟩) hk
        change lev θp + lev k = lev p.2.2 + 2 at this
        omega
      · rfl)
  intro k hk
  obtain ⟨p, hp, hpk⟩ := List.mem_map.1 ((hmem k).2 hk)
  have := h0 p hp
  rw [hpk, hgk, if_pos hk] at this
  exact this

theorem ch17575_fixed_lev (hM : levMaskOK levMask = true) (hG : Ch17575Graded)
    (hθ : lev 76 = 4 ∧ lev 77 = 0)
    (hP : pivOK brMask ch17575PivTheta = true ∧ certMask ch17575PivTheta = levMask 1 ∧
      ch17575PivTheta.all (fun p => decide (p.1 < 78) && p.2.1 == 76 && decide (p.2.2 < 78) &&
        lev p.2.2 == 3) = true)
    (y : RootModule Tag.E6 R) (hz : xOne R (eLab R 76) (xOne R (eLab R 77) y) = y) :
    ∀ k : Fin 78, lev k = 1 → y (lab k) = 0 := by
  obtain ⟨hpiv, hcert, hall⟩ := hP
  simp only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hall
  exact ch17575_fixed_lev_of hM hG 76 77 hθ.1 hθ.2 ch17575PivTheta hpiv hcert hall y hz

end CFSG.HardMathSupport.Dickson.I271.TabBThreeL1
