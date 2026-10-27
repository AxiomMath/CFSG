module

public import CFSG.Timmesfeld.Orders.Distinct
public import CFSG.HardMathSupport.Solomon.Coordinator.I14_20LieEnd
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInputs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.TriD4

open CFSG.Open CFSG.Timmesfeld CFSG.Timmesfeld.Orders
open CFSG.HardMathSupport.Solomon.Coordinator (LieOrderBridge)
open CFSG.HardMathSupport.Solomon.Coordinator.I1420 (lieOrderFormula)

private theorem exp_twelve {m N : ℕ} {Z : ℕ → Prop} (hP : Profile m N Z)
    (hm : m = 174182400) : N = 12 := by
  obtain ⟨r, hr, hmr⟩ := hP.two
  exact eq_of_two_pow_mul_odd hr (by decide : Odd 42525)
    ((hmr.symm.trans hm).trans (by norm_num : (174182400 : ℕ) = 2 ^ 12 * 42525))

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

private theorem le_four {n f : ℕ} (hf : 1 ≤ f) (hN : f * (n * (n + 1) / 2) = 12) : n ≤ 4 := by
  by_contra hlt
  push Not at hlt
  have h15 : 15 ≤ n * (n + 1) / 2 := (Nat.le_div_iff_mul_le (by norm_num)).2 (by nlinarith)
  have := Nat.le_mul_of_pos_left (n * (n + 1) / 2) hf
  omega

private theorem no_A {n : ℕ} {q : TauCeti.PrimePower} (hn : 1 ≤ n) (hp : q.p = 2)
    (h : orderA n q.card = 174182400) : False := by
  obtain ⟨f, hf, hq⟩ := two_pow_card hp
  rw [hq] at h
  have hN := exp_twelve (profile_ordA hn hf) h
  have hn4 := le_four hf hN
  interval_cases n
  · obtain rfl : f = 12 := by omega
    revert h
    decide +kernel
  · obtain rfl : f = 4 := by omega
    revert h
    decide +kernel
  · obtain rfl : f = 2 := by omega
    revert h
    decide +kernel
  · omega

private theorem no_twistedA {n : ℕ} {q : TauCeti.PrimePower} (hn : 2 ≤ n) (hp : q.p = 2)
    (h : orderTwistedA n q.card = 174182400) : False := by
  obtain ⟨f, hf, hq⟩ := two_pow_card hp
  rw [hq, ← ordTwistedA_eq n (2 ^ f) Nat.one_le_two_pow] at h
  have hN := exp_twelve (profile_ordTwistedA hn hf) h
  have hn4 := le_four hf hN
  interval_cases n
  · obtain rfl : f = 4 := by omega
    revert h
    decide +kernel
  · obtain rfl : f = 2 := by omega
    revert h
    decide +kernel
  · omega

private theorem no_B {n : ℕ} {q : TauCeti.PrimePower} (hn : 2 ≤ n) (hp : q.p = 2)
    (h : orderBC n q.card = 174182400) : False := by
  obtain ⟨f, hf, hq⟩ := two_pow_card hp
  rw [hq] at h
  have hN := exp_twelve (profile_ordBC hf) h
  have hn3 : n ≤ 3 := by
    by_contra hlt
    have h16 : 4 * 4 ≤ n * n := Nat.mul_le_mul (by omega) (by omega)
    have := Nat.le_mul_of_pos_left (n * n) hf
    omega
  interval_cases n
  · obtain rfl : f = 3 := by omega
    revert h
    decide +kernel
  · omega

private theorem d_params {n f : ℕ} (hn : 4 ≤ n) (hf : 1 ≤ f) (hN : f * (n * (n - 1)) = 12) :
    n = 4 ∧ f = 1 := by
  have := Nat.le_mul_of_pos_left (n * (n - 1)) hf
  have hn4 : n = 4 := by
    by_contra hne
    have h20 : 5 * 4 ≤ n * (n - 1) := Nat.mul_le_mul (by omega) (by omega)
    omega
  subst hn4
  exact ⟨rfl, by omega⟩

private theorem no_const {q : TauCeti.PrimePower} (hp : q.p = 2) {F : ℕ → ℕ} {c : ℕ}
    {Z : ℕ → ℕ → Prop} (hP : ∀ {f : ℕ}, 1 ≤ f → Profile (F (2 ^ f)) (f * c) (Z f))
    (h : F q.card = 174182400) (hc : ¬c ∣ 12) : False := by
  obtain ⟨f, hf, hq⟩ := two_pow_card hp
  rw [hq] at h
  exact hc (Dvd.intro_left _ (exp_twelve (hP hf) h))

theorem eq_d4two_of_lieOrderFormula {e : TauCeti.LieTypeIndex} (he : e.Valid)
    (hc : e.characteristic = 2) (h : lieOrderFormula e = 174182400) :
    ∃ q : TauCeti.PrimePower, e = .D 4 q ∧ q.card = 2 := by
  have hs := ((TauCeti.LieTypeIndex.valid_iff e).1 he).1
  rw [TauCeti.LieTypeIndex.inStandardRange_iff] at hs
  cases e with
  | A n q => exact (no_A hs.1 (by simpa using hc) h).elim
  | twistedA n q => exact (no_twistedA hs.1 (by simpa using hc) h).elim
  | B n q => exact (no_B hs.1 (by simpa using hc) h).elim
  | C n q => exact absurd (by simpa using hc) hs.2
  | D n q =>
    have hn4 : 4 ≤ n := hs
    obtain ⟨f, hf, hq⟩ := two_pow_card (q := q) (by simpa using hc)
    rw [show lieOrderFormula (.D n q) = orderD n q.card from rfl, hq] at h
    obtain ⟨rfl, rfl⟩ := d_params hn4 hf (exp_twelve (profile_ordD (by omega) hf) h)
    exact ⟨q, rfl, hq⟩
  | twistedD n q =>
    have hn4 : 4 ≤ n := hs
    obtain ⟨f, hf, hq⟩ := two_pow_card (q := q) (by simpa using hc)
    rw [show lieOrderFormula (.twistedD n q) = orderTwistedD n q.card from rfl, hq] at h
    obtain ⟨rfl, rfl⟩ := d_params hn4 hf (exp_twelve (profile_ordTwistedD (by omega) hf) h)
    exact absurd h (by decide +kernel)
  | E6 q => exact (no_const (by simpa using hc) profile_ordE6 h (by decide)).elim
  | E7 q => exact (no_const (by simpa using hc) profile_ordE7 h (by decide)).elim
  | E8 q => exact (no_const (by simpa using hc) profile_ordE8 h (by decide)).elim
  | F4 q => exact (no_const (by simpa using hc) profile_ordF4 h (by decide)).elim
  | twistedE6 q => exact (no_const (by simpa using hc) profile_ordTwistedE6 h (by decide)).elim
  | G2 q =>
    obtain ⟨f, hf, hq⟩ := two_pow_card (q := q) (by simpa using hc)
    rw [show lieOrderFormula (.G2 q) = orderG2 q.card from rfl, hq] at h
    obtain rfl : f = 2 := by have := exp_twelve (profile_ordG2 hf) h; omega
    exact absurd h (by decide +kernel)
  | trialityD4 q =>
    obtain ⟨f, hf, hq⟩ := two_pow_card (q := q) (by simpa using hc)
    rw [show lieOrderFormula (.trialityD4 q) = orderTrialityD4 q.card from rfl, hq] at h
    obtain rfl : f = 1 := by have := exp_twelve (profile_ordTrialityD4 hf) h; omega
    exact absurd h (by decide +kernel)
  | suzuki k => have := exp_twelve (profile_ordSuzuki (by omega : 1 ≤ 2 * k + 1)) h; omega
  | reeG2 k => simp at hc
  | reeF4 k =>
    have := exp_twelve (profile_ordTwistedF4 (by omega : 1 ≤ 2 * k + 1)) h
    omega
  | tits => exact absurd h (by decide +kernel)

private theorem eq_two_of_pow {a j : ℕ} (hj : 1 ≤ j) (h : a ^ j = 2) : a = 2 := by
  have hd : a ∣ 2 := by rw [← h]; exact dvd_pow_self a (by omega)
  rcases Nat.prime_two.eq_one_or_self_of_dvd a hd with rfl | rfl
  · simp at h
  · rfl

private theorem card_alt_ne {T : Type} {n : ℕ} (ψ : T ≃ alternatingGroup (Fin n))
    (hT : Nat.card T = 174182400) (h : n = 5 ∨ n = 6 ∨ n = 8) : False := by
  have hc := Nat.card_congr ψ
  rw [hT] at hc
  revert hc
  rcases h with rfl | rfl | rfl <;>
  · intro hc
    rw [nat_card_alternatingGroup, Nat.card_fin] at hc
    revert hc
    decide +kernel

private theorem exc_ne {e : TauCeti.LieTypeIndex} (h : lieOrderFormula e = 174182400)
    (he : (∃ q : TauCeti.PrimePower, e = .A 1 q ∧ q.card = 7) ∨
      (∃ q : TauCeti.PrimePower, e = .twistedA 2 q ∧ q.card = 3) ∨
      (∃ q : TauCeti.PrimePower, e = .twistedA 3 q ∧ q.card = 2)) : False := by
  rcases he with ⟨q, rfl, hq⟩ | ⟨q, rfl, hq⟩ | ⟨q, rfl, hq⟩
  · rw [show lieOrderFormula (.A 1 q) = orderA 1 q.card from rfl, hq] at h
    exact absurd h (by decide +kernel)
  · rw [show lieOrderFormula (.twistedA 2 q) = orderTwistedA 2 q.card from rfl, hq] at h
    exact absurd h (by decide +kernel)
  · rw [show lieOrderFormula (.twistedA 3 q) = orderTwistedA 3 q.card from rfl, hq] at h
    exact absurd h (by decide +kernel)

theorem fieldSize_eq_two_of_d4two (hB : LieOrderBridge) {T : Type} [Group T] [Finite T]
    (d : TauCeti.ValidLieTypeIndex) (hd : d.1.characteristic = 2) (i : TauCeti.CFSGIndex)
    (hrel : KD264Lie.compRelC d.1 i) (φ : T ≃* i.Group) (hT : Nat.card T = 174182400) :
    KD264Lie.fieldSize d.1 = 2 ∧ ∃ (q : TauCeti.PrimePower)
      (hv : (TauCeti.LieTypeIndex.D 4 q).Valid), q.card = 2 ∧ i = .lie ⟨.D 4 q, hv⟩ := by
  cases i with
  | cyclic _ _ => exact hrel.elim
  | sporadic _ => exact hrel.elim
  | alternating n hn =>
    exfalso
    rcases hrel with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> exact card_alt_ne φ.toEquiv hT (by omega)
  | lie e =>
    obtain ⟨e, he⟩ := e
    have hcard : lieOrderFormula e = 174182400 := (hB ⟨e, he⟩ T ⟨φ⟩).symm.trans hT
    have hrel' : KD264Lie.compRel d.1 e := hrel
    rcases hrel' with ⟨hc, ⟨j, hj, hf⟩, -⟩ | ⟨-, hex⟩ | ⟨-, q, hq, hq2⟩
    · obtain ⟨q, rfl, hq2⟩ := eq_d4two_of_lieOrderFormula he (hc.trans hd) hcard
      exact ⟨eq_two_of_pow hj (hf.symm.trans hq2), q, he, hq2, rfl⟩
    · exact (exc_ne hcard (hex.imp id Or.inl)).elim
    · exact (exc_ne hcard (Or.inr (Or.inr ⟨q, hq, hq2⟩))).elim

end CFSG.LocalAnalysis.GLTheoremA.TriD4

end
