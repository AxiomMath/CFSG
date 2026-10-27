module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ChevTwoInn
public import CFSG.LocalAnalysis.GLTheoremA.CatB.HStdExclDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.FStdDiag

open CFSG.Open CFSG.Timmesfeld CFSG.Timmesfeld.Orders
open CFSG.HardMathSupport.Solomon.Coordinator (LieOrderBridge)
open CFSG.HardMathSupport.Solomon.Coordinator renaming fixSubgroup → coordFix
open CFSG.HardMathSupport.Solomon.Coordinator.I1420 (lieOrderFormula)
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie (fieldSize compRelC CompIdxAt)
open CFSG.LocalAnalysis.GLTheoremA.HStdExcl (SmallOrd)
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived)
open CFSG.LocalAnalysis.GLTheoremA.I1431C2 (card_eq_two_pow exists_fieldSize_two_pow
  fieldSize_eq_two_of_lieOrderFormula ordTwistedA_eq_orderTwistedA_of_pos)

theorem fstd_two_pow_eq_three {N r : ℕ} (hr : Odd r) (h : 2 ^ N * r = 360) : N = 3 :=
  eq_of_two_pow_mul_odd hr (by decide : Odd 45) (h.trans (by norm_num : (360 : ℕ) = 2 ^ 3 * 45))

theorem fstd_lieOrderFormula_ne_360 {e : TauCeti.LieTypeIndex} (he : e.Valid)
    (hc : e.characteristic = 2) : lieOrderFormula e ≠ 360 := by
  intro h
  have hs := ((TauCeti.LieTypeIndex.valid_iff e).1 he).1
  rw [TauCeti.LieTypeIndex.inStandardRange_iff] at hs
  cases e with
  | A n q =>
    have hp : q.p = 2 := by simpa using hc
    have h2 : ordA n (2 ^ q.exponent) = 360 := by rw [← card_eq_two_pow hp]; exact h
    obtain ⟨r, hr, hm⟩ := (profile_ordA hs.1 q.exponent_pos).two
    have hN := fstd_two_pow_eq_three hr (hm.symm.trans h2)
    have hf := q.exponent_pos
    have hn2 : n ≤ 2 := by
      by_contra hn3
      have h12 : 12 ≤ n * (n + 1) := by nlinarith
      have h6 : 6 ≤ n * (n + 1) / 2 := by omega
      nlinarith
    have hn1 := hs.1
    interval_cases n
    · have h3 : q.exponent = 3 := by omega
      rw [h3] at h2
      revert h2
      decide +kernel
    · have h3 : q.exponent = 1 := by omega
      rw [h3] at h2
      revert h2
      decide +kernel
  | twistedA n q =>
    have hp : q.p = 2 := by simpa using hc
    have hq : q.card = 2 ^ q.exponent := card_eq_two_pow hp
    have h2 : ordTwistedA n (2 ^ q.exponent) = 360 := by
      rw [← hq, ordTwistedA_eq_orderTwistedA_of_pos n _ (by rw [hq]; exact Nat.one_le_two_pow)]
      exact h
    obtain ⟨r, hr, hm⟩ := (profile_ordTwistedA hs.1 q.exponent_pos).two
    have hN := fstd_two_pow_eq_three hr (hm.symm.trans h2)
    have hf := q.exponent_pos
    have hn2 : n ≤ 2 := by
      by_contra hn3
      have h12 : 12 ≤ n * (n + 1) := by nlinarith
      have h6 : 6 ≤ n * (n + 1) / 2 := by omega
      nlinarith
    have hn1 := hs.1
    interval_cases n
    have h3 : q.exponent = 1 := by omega
    rw [h3] at h2
    revert h2
    decide +kernel
  | B n q =>
    have hp : q.p = 2 := by simpa using hc
    have h2 : ordBC n (2 ^ q.exponent) = 360 := by rw [← card_eq_two_pow hp]; exact h
    obtain ⟨r, hr, hm⟩ := (profile_ordBC (n := n) q.exponent_pos).two
    have hN := fstd_two_pow_eq_three hr (hm.symm.trans h2)
    have hf := q.exponent_pos
    have hn := hs.1
    nlinarith
  | C n q =>
    have hp : q.p = 2 := by simpa using hc
    exact absurd hp hs.2
  | D n q =>
    have hp : q.p = 2 := by simpa using hc
    have hs4 : 4 ≤ n := hs
    have h2 : ordD n (2 ^ q.exponent) = 360 := by rw [← card_eq_two_pow hp]; exact h
    obtain ⟨r, hr, hm⟩ := (profile_ordD (by omega : 1 ≤ n) q.exponent_pos).two
    have hN := fstd_two_pow_eq_three hr (hm.symm.trans h2)
    have hf := q.exponent_pos
    have h12 : 4 * 3 ≤ n * (n - 1) := Nat.mul_le_mul hs4 (by omega)
    nlinarith
  | twistedD n q =>
    have hp : q.p = 2 := by simpa using hc
    have hs4 : 4 ≤ n := hs
    have h2 : ordTwistedD n (2 ^ q.exponent) = 360 := by rw [← card_eq_two_pow hp]; exact h
    obtain ⟨r, hr, hm⟩ := (profile_ordTwistedD (by omega : 1 ≤ n) q.exponent_pos).two
    have hN := fstd_two_pow_eq_three hr (hm.symm.trans h2)
    have hf := q.exponent_pos
    have h12 : 4 * 3 ≤ n * (n - 1) := Nat.mul_le_mul hs4 (by omega)
    nlinarith
  | E6 q =>
    have hp : q.p = 2 := by simpa using hc
    have h2 : ordE6 (2 ^ q.exponent) = 360 := by rw [← card_eq_two_pow hp]; exact h
    obtain ⟨r, hr, hm⟩ := (profile_ordE6 q.exponent_pos).two
    have hN := fstd_two_pow_eq_three hr (hm.symm.trans h2)
    have hf := q.exponent_pos
    omega
  | E7 q =>
    have hp : q.p = 2 := by simpa using hc
    have h2 : ordE7 (2 ^ q.exponent) = 360 := by rw [← card_eq_two_pow hp]; exact h
    obtain ⟨r, hr, hm⟩ := (profile_ordE7 q.exponent_pos).two
    have hN := fstd_two_pow_eq_three hr (hm.symm.trans h2)
    have hf := q.exponent_pos
    omega
  | E8 q =>
    have hp : q.p = 2 := by simpa using hc
    have h2 : ordE8 (2 ^ q.exponent) = 360 := by rw [← card_eq_two_pow hp]; exact h
    obtain ⟨r, hr, hm⟩ := (profile_ordE8 q.exponent_pos).two
    have hN := fstd_two_pow_eq_three hr (hm.symm.trans h2)
    have hf := q.exponent_pos
    omega
  | F4 q =>
    have hp : q.p = 2 := by simpa using hc
    have h2 : ordF4 (2 ^ q.exponent) = 360 := by rw [← card_eq_two_pow hp]; exact h
    obtain ⟨r, hr, hm⟩ := (profile_ordF4 q.exponent_pos).two
    have hN := fstd_two_pow_eq_three hr (hm.symm.trans h2)
    have hf := q.exponent_pos
    omega
  | G2 q =>
    have hp : q.p = 2 := by simpa using hc
    have h2 : ordG2 (2 ^ q.exponent) = 360 := by rw [← card_eq_two_pow hp]; exact h
    obtain ⟨r, hr, hm⟩ := (profile_ordG2 q.exponent_pos).two
    have hN := fstd_two_pow_eq_three hr (hm.symm.trans h2)
    have hf := q.exponent_pos
    omega
  | twistedE6 q =>
    have hp : q.p = 2 := by simpa using hc
    have h2 : ordTwistedE6 (2 ^ q.exponent) = 360 := by rw [← card_eq_two_pow hp]; exact h
    obtain ⟨r, hr, hm⟩ := (profile_ordTwistedE6 q.exponent_pos).two
    have hN := fstd_two_pow_eq_three hr (hm.symm.trans h2)
    have hf := q.exponent_pos
    omega
  | trialityD4 q =>
    have hp : q.p = 2 := by simpa using hc
    have h2 : ordTrialityD4 (2 ^ q.exponent) = 360 := by rw [← card_eq_two_pow hp]; exact h
    obtain ⟨r, hr, hm⟩ := (profile_ordTrialityD4 q.exponent_pos).two
    have hN := fstd_two_pow_eq_three hr (hm.symm.trans h2)
    have hf := q.exponent_pos
    omega
  | suzuki k =>
    have h2 : ordSuzuki (2 ^ (2 * k + 1)) = 360 := h
    obtain ⟨r, hr, hm⟩ := (profile_ordSuzuki (f := 2 * k + 1) (by omega)).two
    have hN := fstd_two_pow_eq_three hr (hm.symm.trans h2)
    omega
  | reeG2 k => simp at hc
  | reeF4 k =>
    have h2 : ordTwistedF4 (2 ^ (2 * k + 1)) = 360 := h
    obtain ⟨r, hr, hm⟩ := (profile_ordTwistedF4 (f := 2 * k + 1) (by omega)).two
    have hN := fstd_two_pow_eq_three hr (hm.symm.trans h2)
    omega
  | tits =>
    have h2 : ordTits = 360 := h
    rw [ordTits_eq] at h2
    norm_num at h2

theorem fstd_fieldSize_two_of_small (hB : LieOrderBridge) {T : Type} [Group T] [Finite T]
    (d : TauCeti.ValidLieTypeIndex) (hd : d.1.characteristic = 2) (i : TauCeti.CFSGIndex)
    (hrel : compRelC d.1 i) (φ : T ≃* i.Group)
    (hT : Nat.card T = 25920 ∨ Nat.card T = 360) : fieldSize d.1 = 2 := by
  obtain ⟨k, hk, hkd⟩ := exists_fieldSize_two_pow hd
  cases i with
  | cyclic _ _ => exact hrel.elim
  | sporadic _ => exact hrel.elim
  | alternating n hn =>
    haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 (by omega)
    simp only [compRelC] at hrel
    have hcard : Nat.card T = n.factorial / 2 := by
      rw [Nat.card_congr φ.toEquiv, nat_card_alternatingGroup]
      simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
    have h2 : ∀ m : ℕ, 2 ^ k = m → m ≠ 3 ∧ m ≠ 9 := by
      intro m hm
      have h2d : 2 ∣ 2 ^ k := dvd_pow_self 2 (by omega)
      rw [hm] at h2d
      omega
    rcases hrel with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩
    · exfalso
      rw [show Nat.factorial 5 / 2 = 60 by decide] at hcard
      omega
    · rcases h with h | h | h
      · exact h
      · exact absurd h (h2 _ (hkd.symm)).1
      · exact absurd h (h2 _ (hkd.symm)).2
    · exact h
  | lie e =>
    have hord : lieOrderFormula e.1 = Nat.card T := (hB e T ⟨φ⟩).symm
    rcases hrel with ⟨hc, ⟨j, hj, hf⟩, -⟩ | ⟨hf2, -⟩ | ⟨hf3, -⟩
    · have he2 : fieldSize e.1 = 2 := by
        rcases hT with h25 | h360
        · exact fieldSize_eq_two_of_lieOrderFormula e.2 (hc.trans hd) (hord.trans h25)
        · exact absurd (hord.trans h360) (fstd_lieOrderFormula_ne_360 e.2 (hc.trans hd))
      rw [he2, hkd, ← pow_mul] at hf
      have hkj : k * j = 1 := by
        have : 2 ^ 1 = 2 ^ (k * j) := by simpa using hf
        exact (Nat.pow_right_injective le_rfl this).symm
      rw [hkd, Nat.eq_one_of_mul_eq_one_right hkj]
      rfl
    · exact hf2
    · exfalso
      have h2 : 2 ∣ 2 ^ k := dvd_pow_self 2 (by omega)
      rw [← hkd, hf3] at h2
      omega

theorem fstd_fieldSize_two_of_compIdx (hB : LieOrderBridge) {S : Type} [Group S] [Finite S]
    (d : TauCeti.ValidLieTypeIndex) (hd : d.1.characteristic = 2) (hcomp : CompIdxAt 3 d.1 S)
    {α : MulAut S} (hα : α ∈ innAutDerived S) (hα3 : α ^ 3 = 1) (hα1 : α ≠ 1)
    {I : Subgroup S} (hI : IsComponentOf I (coordFix α)) (hsmall : SmallOrd I) :
    fieldSize d.1 = 2 := by
  obtain ⟨i, ⟨φ⟩, hrel⟩ := hcomp α hα hα3 hα1 I hI
  exact fstd_fieldSize_two_of_small hB d hd i hrel φ hsmall

end CFSG.LocalAnalysis.GLTheoremA.FStdDiag

end
