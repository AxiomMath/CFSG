module

public import CFSG.Timmesfeld.Orders.Distinct
public import CFSG.HardMathSupport.Solomon.Coordinator.I14_20LieEnd
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInputs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open CFSG.Open CFSG.Timmesfeld CFSG.Timmesfeld.Orders
open CFSG.HardMathSupport.Solomon.Coordinator (LieOrderBridge)
open CFSG.HardMathSupport.Solomon.Coordinator.I1420 (lieOrderFormula)

private theorem exp_cases {m N : ℕ} {Z : ℕ → Prop} (hP : Profile m N Z)
    (hm : m = 13685760 ∨ m = 9196830720) :
    (m = 13685760 ∧ N = 10) ∨ (m = 9196830720 ∧ N = 15) := by
  obtain ⟨r, hr, hmr⟩ := hP.two
  rcases hm with hm | hm
  · exact Or.inl ⟨hm, eq_of_two_pow_mul_odd hr (by decide : Odd 13365)
      ((hmr.symm.trans hm).trans (by norm_num : (13685760 : ℕ) = 2 ^ 10 * 13365))⟩
  · exact Or.inr ⟨hm, eq_of_two_pow_mul_odd hr (by decide : Odd 280665)
      ((hmr.symm.trans hm).trans (by norm_num : (9196830720 : ℕ) = 2 ^ 15 * 280665))⟩

private theorem two_pow_card {q : TauCeti.PrimePower} (hp : q.p = 2) :
    ∃ f, 1 ≤ f ∧ q.card = 2 ^ f :=
  ⟨q.exponent, q.exponent_pos, by rw [TauCeti.PrimePower.card_def, hp]⟩

private theorem ordTwistedA_eq (n Q : ℕ) (hQ : 1 ≤ Q) : ordTwistedA n Q = orderTwistedA n Q := by
  unfold ordTwistedA orderTwistedA
  congr 2
  refine Finset.prod_congr rfl fun i _ => ?_
  have h1 : 1 ≤ Q ^ i := Nat.one_le_pow _ _ hQ
  have hc : ((Q ^ i : ℕ) : ℤ) = (Q : ℤ) ^ i := Nat.cast_pow Q i
  rcases Nat.even_or_odd i with hi | hi
  · rw [if_pos hi, hi.neg_one_pow]
    omega
  · rw [if_neg (Nat.not_even_iff_odd.2 hi), hi.neg_one_pow]
    omega

private theorem le_five {n f N : ℕ} (hf : 1 ≤ f) (hN : f * (n * (n + 1) / 2) = N)
    (h15 : N ≤ 15) : n ≤ 5 := by
  by_contra hlt
  push Not at hlt
  have h21 : 21 ≤ n * (n + 1) / 2 := (Nat.le_div_iff_mul_le (by norm_num)).2 (by nlinarith)
  have := Nat.le_mul_of_pos_left (n * (n + 1) / 2) hf
  omega

private theorem no_A {n : ℕ} {q : TauCeti.PrimePower} (hn : 1 ≤ n) (hp : q.p = 2)
    (h : orderA n q.card = 13685760 ∨ orderA n q.card = 9196830720) : False := by
  obtain ⟨f, hf, hq⟩ := two_pow_card hp
  rw [hq] at h
  rcases exp_cases (profile_ordA hn hf) h with ⟨h, hN⟩ | ⟨h, hN⟩
  · have := le_five hf hN (by norm_num)
    interval_cases n
    · obtain rfl : f = 10 := by omega
      exact absurd h (by decide +kernel)
    · omega
    · omega
    · obtain rfl : f = 1 := by omega
      exact absurd h (by decide +kernel)
    · omega
  · have := le_five hf hN (by norm_num)
    interval_cases n
    · obtain rfl : f = 15 := by omega
      exact absurd h (by decide +kernel)
    · obtain rfl : f = 5 := by omega
      exact absurd h (by decide +kernel)
    · omega
    · omega
    · obtain rfl : f = 1 := by omega
      exact absurd h (by decide +kernel)

private theorem twistedA_card {n : ℕ} {q : TauCeti.PrimePower} (hn : 2 ≤ n) (hp : q.p = 2)
    (h : orderTwistedA n q.card = 13685760 ∨ orderTwistedA n q.card = 9196830720) :
    q.card = 2 := by
  obtain ⟨f, hf, hq⟩ := two_pow_card hp
  suffices hf1 : f = 1 by rw [hq, hf1, pow_one]
  rw [hq, ← ordTwistedA_eq n (2 ^ f) Nat.one_le_two_pow] at h
  rcases exp_cases (profile_ordTwistedA hn hf) h with ⟨-, hN⟩ | ⟨h, hN⟩
  · have := le_five hf hN (by norm_num)
    interval_cases n <;> omega
  · have := le_five hf hN (by norm_num)
    interval_cases n
    · obtain rfl : f = 5 := by omega
      exact absurd h (by decide +kernel)
    all_goals omega

private theorem no_B {n : ℕ} {q : TauCeti.PrimePower} (hn : 2 ≤ n) (hp : q.p = 2)
    (h : orderBC n q.card = 13685760 ∨ orderBC n q.card = 9196830720) : False := by
  obtain ⟨f, hf, hq⟩ := two_pow_card hp
  rw [hq] at h
  have hN : f * (n * n) = 10 ∨ f * (n * n) = 15 := by
    rcases exp_cases (profile_ordBC hf) h with ⟨-, hN⟩ | ⟨-, hN⟩ <;> omega
  have hn3 : n ≤ 3 := by
    by_contra hlt
    have h16 : 4 * 4 ≤ n * n := Nat.mul_le_mul (by omega) (by omega)
    have := Nat.le_mul_of_pos_left (n * n) hf
    omega
  interval_cases n <;> omega

private theorem no_D_exp {n f : ℕ} (hn : 4 ≤ n) (hf : 1 ≤ f)
    (hN : f * (n * (n - 1)) = 10 ∨ f * (n * (n - 1)) = 15) : False := by
  have := Nat.le_mul_of_pos_left (n * (n - 1)) hf
  rcases (show n = 4 ∨ 5 ≤ n by omega) with rfl | h5
  · omega
  · have h20 : 5 * 4 ≤ n * (n - 1) := Nat.mul_le_mul h5 (by omega)
    omega

private theorem no_const {q : TauCeti.PrimePower} (hp : q.p = 2) {F : ℕ → ℕ} {c : ℕ}
    {Z : ℕ → ℕ → Prop} (hP : ∀ {f : ℕ}, 1 ≤ f → Profile (F (2 ^ f)) (f * c) (Z f))
    (h : F q.card = 13685760 ∨ F q.card = 9196830720) (h10 : ¬ c ∣ 10) (h15 : ¬ c ∣ 15) :
    False := by
  obtain ⟨f, hf, hq⟩ := two_pow_card hp
  rw [hq] at h
  rcases exp_cases (hP hf) h with ⟨-, hN⟩ | ⟨-, hN⟩
  · exact h10 (Dvd.intro_left _ hN)
  · exact h15 (Dvd.intro_left _ hN)

theorem fieldSize_two_of_order_unTwo {e : TauCeti.LieTypeIndex} (he : e.Valid)
    (hc : e.characteristic = 2)
    (h : lieOrderFormula e = 13685760 ∨ lieOrderFormula e = 9196830720) :
    KD264Lie.fieldSize e = 2 := by
  have hs := ((TauCeti.LieTypeIndex.valid_iff e).1 he).1
  rw [TauCeti.LieTypeIndex.inStandardRange_iff] at hs
  cases e with
  | A _ _ => exact (no_A hs.1 (by simpa using hc) h).elim
  | twistedA _ _ => exact twistedA_card hs.1 (by simpa using hc) h
  | B _ _ => exact (no_B hs.1 (by simpa using hc) h).elim
  | C _ _ => exact absurd (by simpa using hc) hs.2
  | D n q =>
    obtain ⟨f, hf, hq⟩ := two_pow_card (q := q) (by simpa using hc)
    rw [show lieOrderFormula (.D n q) = orderD n q.card from rfl, hq] at h
    exact (no_D_exp hs hf (by
      rcases exp_cases (profile_ordD (by omega) hf) h with ⟨-, hN⟩ | ⟨-, hN⟩ <;> omega)).elim
  | twistedD n q =>
    obtain ⟨f, hf, hq⟩ := two_pow_card (q := q) (by simpa using hc)
    rw [show lieOrderFormula (.twistedD n q) = orderTwistedD n q.card from rfl, hq] at h
    exact (no_D_exp hs hf (by
      rcases exp_cases (profile_ordTwistedD (by omega) hf) h with ⟨-, hN⟩ | ⟨-, hN⟩ <;>
        omega)).elim
  | E6 _ => exact (no_const (by simpa using hc) profile_ordE6 h (by decide) (by decide)).elim
  | E7 _ => exact (no_const (by simpa using hc) profile_ordE7 h (by decide) (by decide)).elim
  | E8 _ => exact (no_const (by simpa using hc) profile_ordE8 h (by decide) (by decide)).elim
  | F4 _ => exact (no_const (by simpa using hc) profile_ordF4 h (by decide) (by decide)).elim
  | twistedE6 _ =>
    exact (no_const (by simpa using hc) profile_ordTwistedE6 h (by decide) (by decide)).elim
  | G2 _ => exact (no_const (by simpa using hc) profile_ordG2 h (by decide) (by decide)).elim
  | trialityD4 _ =>
    exact (no_const (by simpa using hc) profile_ordTrialityD4 h (by decide) (by decide)).elim
  | suzuki k =>
    rcases exp_cases (profile_ordSuzuki (by omega : 1 ≤ 2 * k + 1)) h with ⟨h, hN⟩ | ⟨-, hN⟩
    · obtain rfl : k = 2 := by omega
      exact absurd h (by decide +kernel)
    · omega
  | reeG2 _ => simp at hc
  | reeF4 k =>
    rcases exp_cases (profile_ordTwistedF4 (by omega : 1 ≤ 2 * k + 1)) h with
      ⟨-, hN⟩ | ⟨-, hN⟩ <;> omega
  | tits => exact absurd h (by decide +kernel)

private theorem eq_two_of_pow {a j : ℕ} (hj : 1 ≤ j) (h : a ^ j = 2) : a = 2 := by
  have hd : a ∣ 2 := by rw [← h]; exact dvd_pow_self a (by omega)
  rcases Nat.prime_two.eq_one_or_self_of_dvd a hd with rfl | rfl
  · simp at h
  · rfl

private theorem card_alt_ne {T : Type} {n : ℕ} (ψ : T ≃ alternatingGroup (Fin n))
    (hT : Nat.card T = 13685760 ∨ Nat.card T = 9196830720) (h : n = 5 ∨ n = 6 ∨ n = 8) :
    False := by
  have hc := Nat.card_congr ψ
  rcases hT with hT | hT <;> rw [hT] at hc <;> revert hc <;> rcases h with rfl | rfl | rfl <;>
  · intro hc
    rw [nat_card_alternatingGroup, Nat.card_fin] at hc
    revert hc
    decide +kernel

theorem fieldSize_two_of_compRelC_unTwo (hB : LieOrderBridge) {T : Type} [Group T] [Finite T]
    (d : TauCeti.ValidLieTypeIndex) (hd : d.1.characteristic = 2) (i : TauCeti.CFSGIndex)
    (hrel : KD264Lie.compRelC d.1 i) (φ : T ≃* i.Group)
    (hT : Nat.card T = 13685760 ∨ Nat.card T = 9196830720) : KD264Lie.fieldSize d.1 = 2 := by
  cases i with
  | cyclic _ _ => exact hrel.elim
  | sporadic _ => exact hrel.elim
  | alternating n _ =>
    exfalso
    rcases hrel with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> exact card_alt_ne φ.toEquiv hT (by omega)
  | lie e =>
    obtain ⟨e, he⟩ := e
    have hcard : lieOrderFormula e = 13685760 ∨ lieOrderFormula e = 9196830720 := by
      have h := hB ⟨e, he⟩ T ⟨φ⟩
      rcases hT with hT | hT
      · exact Or.inl (h.symm.trans hT)
      · exact Or.inr (h.symm.trans hT)
    have hrel' : KD264Lie.compRel d.1 e := hrel
    rcases hrel' with ⟨hc, ⟨j, hj, hf⟩, -⟩ | ⟨hf2, -⟩ | ⟨-, q, rfl, hq2⟩
    · exact eq_two_of_pow hj (hf.symm.trans
        (fieldSize_two_of_order_unTwo he (hc.trans hd) hcard))
    · exact hf2
    · rw [show lieOrderFormula (.twistedA 3 q) = orderTwistedA 3 q.card from rfl, hq2] at hcard
      exact absurd hcard (by decide +kernel)

end CFSG.LocalAnalysis.GLTheoremA.S265

end
