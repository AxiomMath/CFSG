module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCoreS
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Yardstones.Md0ec50421ce4

private theorem exists_fieldSize_eq_characteristic_pow (e : TauCeti.LieTypeIndex) :
    ∃ k : ℕ, 1 ≤ k ∧ fieldSize e = e.characteristic ^ k := by
  rcases e with ⟨n, q⟩ | ⟨n, q⟩ | ⟨n, q⟩ | ⟨n, q⟩ | ⟨n, q⟩ | ⟨n, q⟩ | q | q | q | q | q | q | q | m | m | m | _ <;>
    simp only [fieldSize]
  · exact ⟨q.exponent, q.exponent_pos, by simp [TauCeti.LieTypeIndex.characteristic_A,
      TauCeti.PrimePower.card_def]⟩
  · exact ⟨q.exponent, q.exponent_pos, by simp [TauCeti.LieTypeIndex.characteristic_twistedA,
      TauCeti.PrimePower.card_def]⟩
  · exact ⟨q.exponent, q.exponent_pos, by simp [TauCeti.LieTypeIndex.characteristic_B,
      TauCeti.PrimePower.card_def]⟩
  · exact ⟨q.exponent, q.exponent_pos, by simp [TauCeti.LieTypeIndex.characteristic_C,
      TauCeti.PrimePower.card_def]⟩
  · exact ⟨q.exponent, q.exponent_pos, by simp [TauCeti.LieTypeIndex.characteristic_D,
      TauCeti.PrimePower.card_def]⟩
  · exact ⟨q.exponent, q.exponent_pos, by simp [TauCeti.LieTypeIndex.characteristic_twistedD,
      TauCeti.PrimePower.card_def]⟩
  · exact ⟨q.exponent, q.exponent_pos, by simp [TauCeti.LieTypeIndex.characteristic_E6,
      TauCeti.PrimePower.card_def]⟩
  · exact ⟨q.exponent, q.exponent_pos, by simp [TauCeti.LieTypeIndex.characteristic_E7,
      TauCeti.PrimePower.card_def]⟩
  · exact ⟨q.exponent, q.exponent_pos, by simp [TauCeti.LieTypeIndex.characteristic_E8,
      TauCeti.PrimePower.card_def]⟩
  · exact ⟨q.exponent, q.exponent_pos, by simp [TauCeti.LieTypeIndex.characteristic_F4,
      TauCeti.PrimePower.card_def]⟩
  · exact ⟨q.exponent, q.exponent_pos, by simp [TauCeti.LieTypeIndex.characteristic_G2,
      TauCeti.PrimePower.card_def]⟩
  · exact ⟨q.exponent, q.exponent_pos, by simp [TauCeti.LieTypeIndex.characteristic_twistedE6,
      TauCeti.PrimePower.card_def]⟩
  · exact ⟨q.exponent, q.exponent_pos, by simp [TauCeti.LieTypeIndex.characteristic_trialityD4,
      TauCeti.PrimePower.card_def]⟩
  · exact ⟨2 * m + 1, by omega, by simp [TauCeti.LieTypeIndex.characteristic_suzuki]⟩
  · exact ⟨2 * m + 1, by omega, by simp [TauCeti.LieTypeIndex.characteristic_reeG2]⟩
  · exact ⟨2 * m + 1, by omega, by simp [TauCeti.LieTypeIndex.characteristic_reeF4]⟩
  · exact ⟨1, by norm_num, by simp [TauCeti.LieTypeIndex.characteristic_tits]⟩

private theorem k3Lie_or_k2Lie_three_of_A_two {q : TauCeti.PrimePower}
    (h3 : 3 ∣ q.card - 1) :
    k3Lie (TauCeti.LieTypeIndex.A 2 q) ∨ k2Lie 3 (TauCeti.LieTypeIndex.A 2 q) := by
  by_cases hp2 : q.p = 2
  · have hcard : q.card = 2 ^ q.exponent := by
      rw [TauCeti.PrimePower.card_def, hp2]
    have hdvd : 3 ∣ 2 ^ q.exponent - 1 := by rwa [hcard] at h3
    have hmod : ((2 ^ q.exponent : ℕ) : ZMod 3) = 1 := by
      change ((2 ^ q.exponent : ℕ) : ZMod 3) = ((1 : ℕ) : ZMod 3)
      rw [ZMod.natCast_eq_natCast_iff]
      have hle : 1 ≤ 2 ^ q.exponent := by
        have : 0 < 2 ^ q.exponent := pow_pos (by norm_num) _
        omega
      exact ((Nat.modEq_iff_dvd' hle).mpr hdvd).symm
    have heven : Even q.exponent := by
      have hneg : (-1 : ZMod 3) ^ q.exponent = 1 := by
        have h2 : (2 : ZMod 3) ^ q.exponent = 1 := by simpa using hmod
        rwa [show (2 : ZMod 3) = -1 by decide] at h2
      exact (neg_one_pow_eq_one_iff_even (show (-1 : ZMod 3) ≠ 1 by decide)).mp hneg
    right
    simp only [k2Lie]
    norm_num
    exact ⟨hp2, heven⟩
  · have hodd : Odd q.card := by
      rw [TauCeti.PrimePower.card_def]
      exact (q.prime_p.odd_of_ne_two hp2).pow
    have hcard1 : 1 ≤ q.card := by
      have h2 : 2 ≤ q.card := by
        rw [TauCeti.PrimePower.card_def]
        exact q.prime_p.two_le.trans (Nat.le_self_pow q.exponent_pos.ne' q.p)
      omega
    have h3mod : q.card ≡ 1 [MOD 3] := ((Nat.modEq_iff_dvd' hcard1).mpr h3).symm
    have h2mod : q.card ≡ 1 [MOD 2] := by
      simpa [Nat.ModEq] using Nat.odd_iff.mp hodd
    have h6 : q.card ≡ 1 [MOD 6] :=
      (Nat.modEq_and_modEq_iff_modEq_mul (by norm_num : Nat.Coprime 2 3)).mp
        ⟨h2mod, h3mod⟩
    left
    simp only [k3Lie]
    simpa [Nat.ModEq] using h6

private theorem k3Lie_or_k2Lie_three_of_twistedA_two {q : TauCeti.PrimePower}
    (h3 : 3 ∣ q.card + 1) (hvalid : (TauCeti.LieTypeIndex.twistedA 2 q).Valid) :
    k3Lie (TauCeti.LieTypeIndex.twistedA 2 q) ∨
      k2Lie 3 (TauCeti.LieTypeIndex.twistedA 2 q) := by
  by_cases hp2 : q.p = 2
  · have hcard : q.card = 2 ^ q.exponent := by
      rw [TauCeti.PrimePower.card_def, hp2]
    have hmod : ((2 ^ q.exponent : ℕ) : ZMod 3) = -1 := by
      have hzero : ((2 ^ q.exponent + 1 : ℕ) : ZMod 3) = 0 :=
        (ZMod.natCast_eq_zero_iff (2 ^ q.exponent + 1) 3).2 (by rwa [hcard] at h3)
      rw [Nat.cast_add, Nat.cast_one] at hzero
      exact eq_neg_of_add_eq_zero_left hzero
    have hodd : Odd q.exponent := by
      have hneg : (-1 : ZMod 3) ^ q.exponent = -1 := by
        have h2 : (2 : ZMod 3) ^ q.exponent = -1 := by simpa using hmod
        rwa [show (2 : ZMod 3) = -1 by decide] at h2
      exact (neg_one_pow_eq_neg_one_iff_odd (show (-1 : ZMod 3) ≠ 1 by decide)).mp hneg
    have hq3 : 3 ≤ q.card := by
      have hrange := ((TauCeti.LieTypeIndex.valid_iff
        (TauCeti.LieTypeIndex.twistedA 2 q)).1 hvalid).1
      have hstd := (TauCeti.LieTypeIndex.inStandardRange_iff
        (TauCeti.LieTypeIndex.twistedA 2 q)).1 hrange
      exact hstd.2 rfl
    clear h3
    have hexp2 : 1 < q.exponent := by
      by_contra hcon
      have hexp1 : q.exponent = 1 :=
        Nat.le_antisymm (Nat.le_of_not_lt hcon) q.exponent_pos
      rw [hcard, hexp1] at hq3
      norm_num at hq3
    right
    simp only [k2Lie]
    exact ⟨by norm_num, hp2, hodd, hexp2⟩
  · have hodd : Odd q.card := by
      rw [TauCeti.PrimePower.card_def]
      exact (q.prime_p.odd_of_ne_two hp2).pow
    have h4 : q.card + 1 ≡ 0 [MOD 3] := h3.modEq_zero_nat
    have h5 : q.card + 1 ≡ 2 + 1 [MOD 3] := by
      have h0 : (0 : ℕ) ≡ 3 [MOD 3] := by norm_num
      have h5' : q.card + 1 ≡ 3 [MOD 3] := h4.trans h0
      simpa using h5'
    have h3mod : q.card ≡ 2 [MOD 3] :=
      Nat.ModEq.add_right_cancel (Nat.ModEq.refl 1) h5
    have h2mod : q.card ≡ 1 [MOD 2] := by
      simpa [Nat.ModEq] using Nat.odd_iff.mp hodd
    have h6 : q.card ≡ 5 [MOD 6] := by
      have h2' : q.card ≡ 5 [MOD 2] := by simpa [Nat.ModEq] using h2mod
      have h3' : q.card ≡ 5 [MOD 3] := by simpa [Nat.ModEq] using h3mod
      exact (Nat.modEq_and_modEq_iff_modEq_mul (by norm_num : Nat.Coprime 2 3)).mp
        ⟨h2', h3'⟩
    left
    simp only [k3Lie]
    simpa [Nat.ModEq] using h6

theorem characteristic_eq_of_fieldSize_eq_pow {d : TauCeti.LieTypeIndex} {r k : ℕ}
    (hr : r.Prime) (hk : 1 ≤ k) (h : fieldSize d = r ^ k) : d.characteristic = r := by
  rcases d with ⟨n, q⟩ | ⟨n, q⟩ | ⟨n, q⟩ | ⟨n, q⟩ | ⟨n, q⟩ | ⟨n, q⟩ | q | q | q | q | q | q | q | m | m | m | _ <;>
    simp only [fieldSize] at h
  · have hq : q.p = r := by
      rw [TauCeti.PrimePower.card_def] at h
      exact (Nat.Prime.pow_inj' q.prime_p hr (ne_of_gt q.exponent_pos) (by omega) h).1
    simpa only [hq] using (TauCeti.LieTypeIndex.characteristic_A n q)
  · have hq : q.p = r := by
      rw [TauCeti.PrimePower.card_def] at h
      exact (Nat.Prime.pow_inj' q.prime_p hr (ne_of_gt q.exponent_pos) (by omega) h).1
    simpa only [hq] using (TauCeti.LieTypeIndex.characteristic_twistedA n q)
  · have hq : q.p = r := by
      rw [TauCeti.PrimePower.card_def] at h
      exact (Nat.Prime.pow_inj' q.prime_p hr (ne_of_gt q.exponent_pos) (by omega) h).1
    simpa only [hq] using (TauCeti.LieTypeIndex.characteristic_B n q)
  · have hq : q.p = r := by
      rw [TauCeti.PrimePower.card_def] at h
      exact (Nat.Prime.pow_inj' q.prime_p hr (ne_of_gt q.exponent_pos) (by omega) h).1
    simpa only [hq] using (TauCeti.LieTypeIndex.characteristic_C n q)
  · have hq : q.p = r := by
      rw [TauCeti.PrimePower.card_def] at h
      exact (Nat.Prime.pow_inj' q.prime_p hr (ne_of_gt q.exponent_pos) (by omega) h).1
    simpa only [hq] using (TauCeti.LieTypeIndex.characteristic_D n q)
  · have hq : q.p = r := by
      rw [TauCeti.PrimePower.card_def] at h
      exact (Nat.Prime.pow_inj' q.prime_p hr (ne_of_gt q.exponent_pos) (by omega) h).1
    simpa only [hq] using (TauCeti.LieTypeIndex.characteristic_twistedD n q)
  · have hq : q.p = r := by
      rw [TauCeti.PrimePower.card_def] at h
      exact (Nat.Prime.pow_inj' q.prime_p hr (ne_of_gt q.exponent_pos) (by omega) h).1
    simpa only [hq] using (TauCeti.LieTypeIndex.characteristic_E6 q)
  · have hq : q.p = r := by
      rw [TauCeti.PrimePower.card_def] at h
      exact (Nat.Prime.pow_inj' q.prime_p hr (ne_of_gt q.exponent_pos) (by omega) h).1
    simpa only [hq] using (TauCeti.LieTypeIndex.characteristic_E7 q)
  · have hq : q.p = r := by
      rw [TauCeti.PrimePower.card_def] at h
      exact (Nat.Prime.pow_inj' q.prime_p hr (ne_of_gt q.exponent_pos) (by omega) h).1
    simpa only [hq] using (TauCeti.LieTypeIndex.characteristic_E8 q)
  · have hq : q.p = r := by
      rw [TauCeti.PrimePower.card_def] at h
      exact (Nat.Prime.pow_inj' q.prime_p hr (ne_of_gt q.exponent_pos) (by omega) h).1
    simpa only [hq] using (TauCeti.LieTypeIndex.characteristic_F4 q)
  · have hq : q.p = r := by
      rw [TauCeti.PrimePower.card_def] at h
      exact (Nat.Prime.pow_inj' q.prime_p hr (ne_of_gt q.exponent_pos) (by omega) h).1
    simpa only [hq] using (TauCeti.LieTypeIndex.characteristic_G2 q)
  · have hq : q.p = r := by
      rw [TauCeti.PrimePower.card_def] at h
      exact (Nat.Prime.pow_inj' q.prime_p hr (ne_of_gt q.exponent_pos) (by omega) h).1
    simpa only [hq] using (TauCeti.LieTypeIndex.characteristic_twistedE6 q)
  · have hq : q.p = r := by
      rw [TauCeti.PrimePower.card_def] at h
      exact (Nat.Prime.pow_inj' q.prime_p hr (ne_of_gt q.exponent_pos) (by omega) h).1
    simpa only [hq] using (TauCeti.LieTypeIndex.characteristic_trialityD4 q)
  · have : 2 = r := (Nat.Prime.pow_inj' Nat.prime_two hr (by omega) (by omega) h).1
    simpa only [this.symm] using (TauCeti.LieTypeIndex.characteristic_suzuki m)
  · have : 3 = r := (Nat.Prime.pow_inj' Nat.prime_three hr (by omega) (by omega) h).1
    simpa only [this.symm] using (TauCeti.LieTypeIndex.characteristic_reeG2 m)
  · have : 2 = r := (Nat.Prime.pow_inj' Nat.prime_two hr (by omega) (by omega) h).1
    simpa only [this.symm] using (TauCeti.LieTypeIndex.characteristic_reeF4 m)
  · have : 2 = r := by
      have h' : 2 ^ 1 = r ^ k := by simpa using h
      exact (Nat.Prime.pow_inj' Nat.prime_two hr (by norm_num) (by omega) h').1
    simpa only [this.symm] using (TauCeti.LieTypeIndex.characteristic_tits)

theorem two_le_fieldSize (d : TauCeti.LieTypeIndex) : 2 ≤ fieldSize d := by
  rcases d with ⟨n, q⟩ | ⟨n, q⟩ | ⟨n, q⟩ | ⟨n, q⟩ | ⟨n, q⟩ | ⟨n, q⟩ | q | q | q | q | q | q | q | m | m | m | _ <;>
    simp only [fieldSize]
  · rw [TauCeti.PrimePower.card_def]
    exact q.prime_p.two_le.trans (Nat.le_self_pow q.exponent_pos.ne' q.p)
  · rw [TauCeti.PrimePower.card_def]
    exact q.prime_p.two_le.trans (Nat.le_self_pow q.exponent_pos.ne' q.p)
  · rw [TauCeti.PrimePower.card_def]
    exact q.prime_p.two_le.trans (Nat.le_self_pow q.exponent_pos.ne' q.p)
  · rw [TauCeti.PrimePower.card_def]
    exact q.prime_p.two_le.trans (Nat.le_self_pow q.exponent_pos.ne' q.p)
  · rw [TauCeti.PrimePower.card_def]
    exact q.prime_p.two_le.trans (Nat.le_self_pow q.exponent_pos.ne' q.p)
  · rw [TauCeti.PrimePower.card_def]
    exact q.prime_p.two_le.trans (Nat.le_self_pow q.exponent_pos.ne' q.p)
  · rw [TauCeti.PrimePower.card_def]
    exact q.prime_p.two_le.trans (Nat.le_self_pow q.exponent_pos.ne' q.p)
  · rw [TauCeti.PrimePower.card_def]
    exact q.prime_p.two_le.trans (Nat.le_self_pow q.exponent_pos.ne' q.p)
  · rw [TauCeti.PrimePower.card_def]
    exact q.prime_p.two_le.trans (Nat.le_self_pow q.exponent_pos.ne' q.p)
  · rw [TauCeti.PrimePower.card_def]
    exact q.prime_p.two_le.trans (Nat.le_self_pow q.exponent_pos.ne' q.p)
  · rw [TauCeti.PrimePower.card_def]
    exact q.prime_p.two_le.trans (Nat.le_self_pow q.exponent_pos.ne' q.p)
  · rw [TauCeti.PrimePower.card_def]
    exact q.prime_p.two_le.trans (Nat.le_self_pow q.exponent_pos.ne' q.p)
  · rw [TauCeti.PrimePower.card_def]
    exact q.prime_p.two_le.trans (Nat.le_self_pow q.exponent_pos.ne' q.p)
  · simpa using Nat.le_self_pow (show 2 * m + 1 ≠ 0 by omega) 2
  · exact le_trans (by norm_num : 2 ≤ 3) (Nat.le_self_pow (show 2 * m + 1 ≠ 0 by omega) 3)
  · simpa using Nat.le_self_pow (show 2 * m + 1 ≠ 0 by omega) 2
  · norm_num

theorem overEight_of_fieldSize_eq_eight {d : TauCeti.LieTypeIndex} (h : fieldSize d = 8)
    (hS : ¬ ∃ k : ℕ, d = .suzuki k) : overEight d := by
  rcases d with ⟨n, q⟩ | ⟨n, q⟩ | ⟨n, q⟩ | ⟨n, q⟩ | ⟨n, q⟩ | ⟨n, q⟩ | q | q | q | q | q | q | q | m | m | m | _ <;>
    simp only [fieldSize] at h
  all_goals first
    | simpa [overEight] using h
    | exact absurd ⟨m, rfl⟩ hS
    | (exfalso
       have h' : 3 ^ (2 * m + 1) = 2 ^ 3 := by norm_num at h ⊢; exact h
       exact absurd (Nat.Prime.pow_inj' Nat.prime_three Nat.prime_two (by omega) (by norm_num) h').1
         (by norm_num))
    | (have hm : m = 1 := by
         have h' : 2 ^ (2 * m + 1) = 2 ^ 3 := by norm_num at h ⊢; exact h
         have := (Nat.Prime.pow_inj' Nat.prime_two Nat.prime_two (by omega) (by norm_num) h').2
         omega
       subst hm
       simp [overEight])
    | omega

theorem k2Lie_three_of_card_eight {d : TauCeti.LieTypeIndex} {q : TauCeti.PrimePower}
    (hd : d = .A 1 q ∨ d = .twistedA 2 q) (hq : q.card = 8) : k2Lie 3 d := by
  rcases hd with rfl | rfl
  · simp only [k2Lie]
    rw [hq]
    norm_num
  · have hq' : q.p = 2 ∧ q.exponent = 3 := by
      have h8 : q.card = 2 ^ 3 := by rw [hq]; norm_num
      rw [TauCeti.PrimePower.card_def] at h8
      exact Nat.Prime.pow_inj' q.prime_p Nat.prime_two (ne_of_gt q.exponent_pos) (by norm_num) h8
    simp only [k2Lie, hq'.1, hq'.2]
    norm_num

theorem k3Lie_or_k2Lie_three_of_lpEpsIdx (d : TauCeti.ValidLieTypeIndex)
    (h : lpEpsIdx 3 d.1) : k3Lie d.1 ∨ k2Lie 3 d.1 := by
  rcases d with ⟨d, hdvalid⟩
  change k3Lie d ∨ k2Lie 3 d
  simp only [lpEpsIdx] at h
  have h3sub : (3 - 1 : ℕ) = 2 := by norm_num
  rw [h3sub] at h
  rcases h with ⟨q, hA | hA⟩
  · rcases hA with ⟨rfl, h3⟩
    exact k3Lie_or_k2Lie_three_of_A_two h3
  · rcases hA with ⟨rfl, h3⟩
    exact k3Lie_or_k2Lie_three_of_twistedA_two h3 hdvalid

theorem eight_le_of_twistedA_two (d : TauCeti.ValidLieTypeIndex) {n : ℕ}
    {q : TauCeti.PrimePower} (hd : d.1 = .twistedA n q) (hq : q.card = 2) (h3 : 3 ∣ n + 1)
    (hk : ¬ k2Lie 3 d.1) : 8 ≤ n := by
  rcases d with ⟨d, hdvalid⟩
  change ¬ k2Lie 3 d at hk
  subst hd
  have hq2 : q.p = 2 ∧ q.exponent = 1 := by
    rw [TauCeti.PrimePower.card_def] at hq
    exact (Nat.prime_two.pow_eq_iff).1 hq
  have hn2 : 3 ≤ n := by
    have hrange := ((TauCeti.LieTypeIndex.valid_iff
      (TauCeti.LieTypeIndex.twistedA n q)).1 hdvalid).1
    have hstd := (TauCeti.LieTypeIndex.inStandardRange_iff
      (TauCeti.LieTypeIndex.twistedA n q)).1 hrange
    have hn2' : 2 ≤ n := hstd.1
    by_contra hcon
    have hn : n = 2 := by omega
    subst hn
    exact absurd (hstd.2 rfl) (by rw [hq]; norm_num)
  by_contra hlt
  have hn8 : n < 8 := by omega
  interval_cases n <;> simp_all [k2Lie, hq2]

theorem isTrialityD4Big_of_trialityD4 {d : TauCeti.LieTypeIndex} {q : TauCeti.PrimePower}
    (hd : d = .trialityD4 q) (h2 : ¬ ov2Idx d) (h3 : d.characteristic ≠ 3) :
    isTrialityD4Big d := by
  subst hd
  refine ⟨?_, ?_⟩
  · have hne : q.card ≠ 2 := h2
    have h2le : 2 ≤ q.card := two_le_fieldSize (TauCeti.LieTypeIndex.trialityD4 q)
    omega
  · intro h3dvd
    rw [TauCeti.PrimePower.card_def] at h3dvd
    have h3p : 3 ∣ q.p := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3dvd
    have hqp : q.p = 3 := (q.prime_p.dvd_iff_eq (by norm_num : 3 ≠ 1)).1 h3p
    exact h3 (by rw [TauCeti.LieTypeIndex.characteristic_trialityD4, hqp])

theorem i5LowBound_of_lpEpsIdx {p : ℕ} {d : TauCeti.LieTypeIndex} (h : lpEpsIdx p d) :
    i5LowBound p d (p - 2) := by
  rcases h with ⟨q, h | h⟩
  · rcases h with ⟨rfl, hdvd⟩
    exact ⟨hdvd, by omega⟩
  · rcases h with ⟨rfl, hdvd⟩
    exact ⟨hdvd, by omega⟩

theorem not_multIdx_three_of_ov2Idx {d : TauCeti.LieTypeIndex} (h : ov2Idx d)
    (hU : ¬ ∃ (n : ℕ) (q : TauCeti.PrimePower), d = .twistedA n q ∧ 3 ∣ n + 1)
    (hE : ¬ ∃ q : TauCeti.PrimePower, d = .twistedE6 q) : ¬ multIdx 3 d := by
  intro hm
  rcases d with ⟨n, q⟩ | ⟨n, q⟩ | ⟨n, q⟩ | ⟨n, q⟩ | ⟨n, q⟩ | ⟨n, q⟩ | q | q | q | q | q | q | q | m | m | m | _ <;>
    simp only [ov2Idx, fieldSize, multIdx] at h hm
  all_goals first
    | exact hm
    | exact hU ⟨_, _, rfl, hm.1⟩
    | exact hE ⟨_, rfl⟩
    | (rw [h] at hm; norm_num at hm)

theorem not_multIdx_three_of_overEight {d : TauCeti.LieTypeIndex} (h : overEight d)
    (hU : ¬ ∃ (n : ℕ) (q : TauCeti.PrimePower), d = .twistedA n q ∧ 3 ∣ n + 1)
    (hE : ¬ ∃ q : TauCeti.PrimePower, d = .twistedE6 q) : ¬ multIdx 3 d := by
  intro hm
  rcases d with ⟨n, q⟩ | ⟨n, q⟩ | ⟨n, q⟩ | ⟨n, q⟩ | ⟨n, q⟩ | ⟨n, q⟩ | q | q | q | q | q | q | q | m | m | m | _ <;>
    simp only [overEight, fieldSize, multIdx] at h hm
  all_goals first
    | exact hm
    | exact h
    | exact hU ⟨_, _, rfl, hm.1⟩
    | exact hE ⟨_, rfl⟩
    | (rw [h] at hm; norm_num at hm)

theorem lpEpsIdx_of_multIdx_three {d : TauCeti.LieTypeIndex} (h : multIdx 3 d)
    (hlow : ∀ k, i5LowBound 3 d k → k ≤ 3) : lpEpsIdx 3 d := by
  rcases d with ⟨n, q⟩ | ⟨n, q⟩ | ⟨n, q⟩ | ⟨n, q⟩ | ⟨n, q⟩ | ⟨n, q⟩ | q | q | q | q | q | q | q | m | m | m | _ <;>
    simp only [multIdx] at h
  · have hle : n - 1 ≤ 3 := hlow (n - 1) ⟨h.2, rfl⟩
    have hn : n = 2 := by
      have hn4 : n ≤ 4 := by omega
      obtain ⟨k, hk⟩ := h.1
      omega
    subst hn
    exact ⟨q, Or.inl ⟨by norm_num, h.2⟩⟩
  · have hle : n - 1 ≤ 3 := hlow (n - 1) ⟨h.2, rfl⟩
    have hn : n = 2 := by
      have hn4 : n ≤ 4 := by omega
      obtain ⟨k, hk⟩ := h.1
      omega
    subst hn
    exact ⟨q, Or.inr ⟨by norm_num, h.2⟩⟩
  · have h5 : 5 ≤ 3 := hlow 5 ⟨rfl, h.2, rfl⟩
    omega
  · have h5 : 5 ≤ 3 := hlow 5 ⟨rfl, h.2, rfl⟩
    omega
  all_goals exact h

theorem not_multIdx_field_of_overEight (d : TauCeti.ValidLieTypeIndex) (h : overEight d.1)
    (hk : ¬ k2Lie 3 d.1) (hf : ∀ k, i5FieldBound d.1 k → k + 1 ≤ 4) :
    (¬ ∃ (n : ℕ) (q : TauCeti.PrimePower), d.1 = .twistedA n q ∧ 3 ∣ n + 1) ∧
      ¬ ∃ q : TauCeti.PrimePower, d.1 = .twistedE6 q := by
  rcases d with ⟨e, he⟩
  constructor
  · rintro ⟨n, q, rfl, h3n⟩
    have hq8 : q.card = 8 := by simpa [overEight] using h
    have hn2 : 2 ≤ n := by
      have hrange := ((TauCeti.LieTypeIndex.valid_iff
        (TauCeti.LieTypeIndex.twistedA n q)).1 he).1
      have hstd := (TauCeti.LieTypeIndex.inStandardRange_iff
        (TauCeti.LieTypeIndex.twistedA n q)).1 hrange
      simpa using hstd.1
    have hn4 : n ≤ 4 := by
      have hle := hf (n - 1) (by
        simp only [i5FieldBound]
        exact ⟨h3n, by rw [hq8]; norm_num, trivial⟩)
      omega
    have hn : n = 2 := by
      obtain ⟨k, hk⟩ := h3n
      omega
    subst hn
    have hq' : q.p = 2 ∧ q.exponent = 3 := by
      have h8 : q.card = 2 ^ 3 := by rw [hq8]; norm_num
      rw [TauCeti.PrimePower.card_def] at h8
      exact Nat.Prime.pow_inj' q.prime_p Nat.prime_two (ne_of_gt q.exponent_pos) (by norm_num) h8
    exact hk (by
      simp only [k2Lie, hq'.1, hq'.2]
      norm_num)
  · rintro ⟨q, rfl⟩
    have hq8 : q.card = 8 := by simpa [overEight] using h
    have hle := hf 5 (by
      simp only [i5FieldBound]
      exact ⟨by rw [hq8]; norm_num, trivial⟩)
    omega

theorem compRelC_alternating {d : TauCeti.LieTypeIndex} {n : ℕ} {hn : 5 ≤ n}
    (h : compRelC d (.alternating n hn)) :
    (n = 5 ∨ n = 6 ∨ n = 8) ∧ (n = 6 ∨ n = 8 → fieldSize d = 2 ∨ d.characteristic = 3) := by
  rcases h with ⟨rfl, hfs⟩ | ⟨rfl, hfs⟩ | ⟨rfl, hfs⟩
  · exact ⟨Or.inl rfl, by rintro (h | h) <;> omega⟩
  · refine ⟨Or.inr (Or.inl rfl), ?_⟩
    rintro (_ | h)
    · rcases hfs with h | h | h
      · exact Or.inl h
      · exact Or.inr (characteristic_eq_of_fieldSize_eq_pow (k := 1) Nat.prime_three
          (by norm_num) (by simpa using h))
      · exact Or.inr (characteristic_eq_of_fieldSize_eq_pow (k := 2) Nat.prime_three
          (by norm_num) (by simpa using h))
    · omega
  · refine ⟨Or.inr (Or.inr rfl), ?_⟩
    rintro (h | _)
    · omega
    · exact Or.inl hfs

theorem characteristic_ne_of_compRelC {p : ℕ} (hp2 : p ≠ 2) {d : TauCeti.LieTypeIndex}
    {e : TauCeti.ValidLieTypeIndex} (h : compRelC d (.lie e)) (hpd : p ≠ d.characteristic)
    (hX : ¬ (p = 3 ∧ ov2Idx d)) :
    p ≠ e.1.characteristic ∨ (p = 7 ∧ ∃ q : TauCeti.PrimePower, e.1 = .A 1 q ∧ q.card = 7) := by
  rcases e with ⟨e, he⟩
  simp only [compRelC, compRel] at h
  rcases h with ⟨hchar, hfield, hsuz⟩ | ⟨hd2, hA | hU⟩ | ⟨hd3, hq⟩
  · left
    intro hp
    exact hpd (hp.trans hchar)
  · rcases hA with ⟨q, rfl, hq7⟩
    by_cases hp7 : p = 7
    · exact Or.inr ⟨hp7, q, rfl, hq7⟩
    · left
      intro hp
      have hq : q.p = 7 := by
        rw [TauCeti.PrimePower.card_def] at hq7
        exact ((Nat.prime_seven.pow_eq_iff).1 hq7).1
      have hchar : (TauCeti.LieTypeIndex.A 1 q).characteristic = 7 := by
        simp [TauCeti.LieTypeIndex.characteristic_A, hq]
      exact hp7 (hp.trans hchar)
  · rcases hU with ⟨q, rfl, hq3⟩
    left
    intro hp
    have hq : q.p = 3 := by
      rw [TauCeti.PrimePower.card_def] at hq3
      exact ((Nat.prime_three.pow_eq_iff).1 hq3).1
    have hchar : (TauCeti.LieTypeIndex.twistedA 2 q).characteristic = 3 := by
      simp [TauCeti.LieTypeIndex.characteristic_twistedA, hq]
    exact hX ⟨hp.trans hchar, hd2⟩
  · rcases hq with ⟨q, rfl, hq2⟩
    left
    intro hp
    have hq : q.p = 2 := by
      rw [TauCeti.PrimePower.card_def] at hq2
      exact ((Nat.prime_two.pow_eq_iff).1 hq2).1
    have hchar : (TauCeti.LieTypeIndex.twistedA 3 q).characteristic = 2 := by
      simp [TauCeti.LieTypeIndex.characteristic_twistedA, hq]
    exact hp2 (hp.trans hchar)

theorem ov2Idx_of_compRel {d e : TauCeti.LieTypeIndex} (h : compRel d e) (he : ov2Idx e)
    (hd3 : d.characteristic ≠ 3) : ov2Idx d := by
  simp only [ov2Idx] at he ⊢
  rcases h with ⟨-, ⟨j, hj, hfield⟩, -⟩ | ⟨hd2, -⟩ | ⟨hfs3, -⟩
  · have hpow : fieldSize d ^ j = 2 := by rw [← hfield, he]
    have h2 : 2 ≤ fieldSize d := two_le_fieldSize d
    have hle : fieldSize d ≤ 2 := by
      have h1 : fieldSize d ^ 1 ≤ fieldSize d ^ j := Nat.pow_le_pow_right (by omega) hj
      simpa using h1.trans_eq hpow
    omega
  · exact hd2
  · exact absurd (characteristic_eq_of_fieldSize_eq_pow (k := 1) Nat.prime_three
      (by norm_num) (by simpa using hfs3)) hd3

theorem fieldSize_of_compRel_of_eight {d e : TauCeti.LieTypeIndex} (h : compRel d e)
    (he : fieldSize e = 8) : fieldSize d = 2 ∨ fieldSize d = 8 := by
  rcases h with ⟨-, ⟨j, hj, hfield⟩, -⟩ | ⟨hd2, -⟩ | ⟨hfs3, hq⟩
  · have hpow : fieldSize d ^ j = 8 := by rw [← hfield, he]
    have h2 : 2 ≤ fieldSize d := two_le_fieldSize d
    have hle : fieldSize d ≤ 8 := by
      have h1 : fieldSize d ^ 1 ≤ fieldSize d ^ j := Nat.pow_le_pow_right (by omega) hj
      simpa using h1.trans_eq hpow
    have hj3 : j ≤ 3 := by
      have h2j : 2 ^ j ≤ 2 ^ 3 := by
        calc 2 ^ j ≤ fieldSize d ^ j := Nat.pow_le_pow_left h2 j
          _ = 8 := hpow
          _ = 2 ^ 3 := by norm_num
      exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h2j
    set s := fieldSize d
    interval_cases j <;> interval_cases s <;> simp_all
  · exact Or.inl hd2
  · rcases hq with ⟨q, rfl, hq2⟩
    simp only [fieldSize] at he
    omega

theorem k2Lie_five_of_compRel (d : TauCeti.ValidLieTypeIndex) {e : TauCeti.LieTypeIndex}
    (h : compRel d.1 e) (he : e = .suzuki 2 ∨ e = .tits) : k2Lie 5 d.1 := by
  rcases d with ⟨d, hdvalid⟩
  change k2Lie 5 d
  rcases h with ⟨hchar, ⟨j, hj, hfield⟩, hsuz⟩ | ⟨hd2, hcase⟩ | ⟨hd3, hcase⟩
  · rcases he with rfl | rfl
    · rcases d with ⟨n, q⟩ | ⟨n, q⟩ | ⟨n, q⟩ | ⟨n, q⟩ | ⟨n, q⟩ | ⟨n, q⟩ | q | q | q | q | q | q | q | m | m | m | _ <;>
        simp only [suzRee, fieldSize] at hsuz hfield <;>
        simp at hsuz
      all_goals try exact hsuz
      · simp [k2Lie]
        norm_num at hfield
        have hm1 : 1 ≤ m := by
          have hrange := ((TauCeti.LieTypeIndex.valid_iff
            (TauCeti.LieTypeIndex.suzuki m)).1 hdvalid).1
          simpa [TauCeti.LieTypeIndex.inStandardRange_iff] using hrange
        have h5 : 5 = (2 * m + 1) * j := by
          rw [← pow_mul] at hfield
          exact Nat.pow_right_injective (by norm_num : 2 ≤ 2) hfield
        have hdvd : (2 * m + 1) ∣ 5 := ⟨j, h5⟩
        rcases (Nat.dvd_prime Nat.prime_five).1 hdvd with h1 | h1
        · omega
        · omega
      · simp only [TauCeti.LieTypeIndex.characteristic_suzuki,
          TauCeti.LieTypeIndex.characteristic_reeG2] at hchar
        omega
      · simp [k2Lie]
        norm_num at hfield
        have hm1 : 1 ≤ m := by
          have hrange := ((TauCeti.LieTypeIndex.valid_iff
            (TauCeti.LieTypeIndex.reeF4 m)).1 hdvalid).1
          simpa [TauCeti.LieTypeIndex.inStandardRange_iff] using hrange
        have h5 : 5 = (2 * m + 1) * j := by
          rw [← pow_mul] at hfield
          exact Nat.pow_right_injective (by norm_num : 2 ≤ 2) hfield
        have hdvd : (2 * m + 1) ∣ 5 := ⟨j, h5⟩
        rcases (Nat.dvd_prime Nat.prime_five).1 hdvd with h1 | h1
        · omega
        · omega
      · simp [k2Lie]
    · rcases d with ⟨n, q⟩ | ⟨n, q⟩ | ⟨n, q⟩ | ⟨n, q⟩ | ⟨n, q⟩ | ⟨n, q⟩ | q | q | q | q | q | q | q | m | m | m | _ <;>
        simp only [suzRee, fieldSize] at hsuz hfield <;>
        simp at hsuz
      all_goals try exact hsuz
      · simp [k2Lie]
        have hm1 : 1 ≤ m := by
          have hrange := ((TauCeti.LieTypeIndex.valid_iff
            (TauCeti.LieTypeIndex.suzuki m)).1 hdvalid).1
          simpa [TauCeti.LieTypeIndex.inStandardRange_iff] using hrange
        have h1 : 1 = (2 * m + 1) * j := by
          rw [← pow_mul] at hfield
          exact Nat.pow_right_injective (by norm_num : 2 ≤ 2) hfield
        have hdvd : (2 * m + 1) ∣ 1 := ⟨j, h1⟩
        have := Nat.le_of_dvd (by norm_num) hdvd
        omega
      · simp only [TauCeti.LieTypeIndex.characteristic_tits,
          TauCeti.LieTypeIndex.characteristic_reeG2] at hchar
        omega
      · simp [k2Lie]
        have hm1 : 1 ≤ m := by
          have hrange := ((TauCeti.LieTypeIndex.valid_iff
            (TauCeti.LieTypeIndex.reeF4 m)).1 hdvalid).1
          simpa [TauCeti.LieTypeIndex.inStandardRange_iff] using hrange
        have h1 : 1 = (2 * m + 1) * j := by
          rw [← pow_mul] at hfield
          exact Nat.pow_right_injective (by norm_num : 2 ≤ 2) hfield
        have hdvd : (2 * m + 1) ∣ 1 := ⟨j, h1⟩
        have := Nat.le_of_dvd (by norm_num) hdvd
        omega
      · simp [k2Lie]
  · rcases hcase with ⟨q, rfl, hq⟩ | ⟨q, rfl, hq⟩
    · rcases he with h | h <;> cases h
    · rcases he with h | h <;> cases h
  · rcases hcase with ⟨q, rfl, hq⟩
    rcases he with h | h <;> cases h

theorem subRelC_alternating_three {d : TauCeti.LieTypeIndex} {n : ℕ} {hn : 5 ≤ n}
    (h : subRelC 3 d (.alternating n hn)) (hd3 : d.characteristic ≠ 3) :
    n = 5 ∨ overEight d := by
  rcases h with ⟨h5, ⟨q, hd⟩, hfs⟩ | ⟨h6, h6'⟩ | ⟨h8, ⟨q, hd⟩, hfs⟩
  · exact Or.inl h5
  · rcases h6' with ⟨⟨q, hd⟩, hfs⟩ | ⟨⟨q, hd⟩, hfs⟩
    · subst hd
      have hq3 : q.p = 3 := by
        have h : q.card = 3 ^ 6 := by
          simp only [fieldSize] at hfs
          rw [hfs]; norm_num
        rw [TauCeti.PrimePower.card_def] at h
        exact (Nat.Prime.pow_inj' q.prime_p Nat.prime_three (ne_of_gt q.exponent_pos)
          (by norm_num) h).1
      exfalso
      exact hd3 (by simp [TauCeti.LieTypeIndex.characteristic_A, hq3])
    · subst hd
      right
      simp only [fieldSize] at hfs
      norm_num at hfs
      simpa [overEight] using hfs
  · subst hd
    right
    simp only [fieldSize] at hfs
    norm_num at hfs
    simpa [overEight] using hfs

theorem not_subRelC_alternating_of_lpEpsIdx {p : ℕ} (hp5 : 5 ≤ p) {d : TauCeti.LieTypeIndex}
    (hd : lpEpsIdx p d) {n : ℕ} {hn : 5 ≤ n} : ¬ subRelC p d (.alternating n hn) := by
  intro h
  rcases hd with ⟨Q, hQ | hQ⟩
  · rcases hQ with ⟨hA, -⟩
    rw [hA] at h
    simp only [subRelC, fieldSize] at h
    rcases h with ⟨-, ⟨q, hq⟩, -⟩ | ⟨-, h2⟩ | ⟨-, ⟨q, hq⟩, -⟩
    · injection hq with hp1 _
      omega
    · rcases h2 with ⟨⟨q, hq⟩, -⟩ | ⟨⟨q, hq⟩, -⟩
      · injection hq with hp1 _
        omega
      · cases hq
    · injection hq with hp1 _
      omega
  · rcases hQ with ⟨hA, -⟩
    rw [hA] at h
    simp only [subRelC, fieldSize] at h
    rcases h with ⟨-, ⟨q, hq⟩, -⟩ | ⟨-, h2⟩ | ⟨-, ⟨q, hq⟩, -⟩
    · cases hq
    · rcases h2 with ⟨⟨q, hq⟩, -⟩ | ⟨⟨q, hq⟩, -⟩ <;> cases hq
    · cases hq

private theorem ne_characteristic_of_field_descent {p : ℕ} (hp : p.Prime)
    {d e : TauCeti.LieTypeIndex} (hf : fieldSize e ^ p = fieldSize d)
    (hpd : p ≠ d.characteristic) : p ≠ e.characteristic := by
  intro hpe
  obtain ⟨k, hk1, hk⟩ := exists_fieldSize_eq_characteristic_pow e
  have hfsp : fieldSize d = p ^ (k * p) := by
    rw [← hf, hk, ← hpe]
    rw [pow_mul]
  have hkpos : 1 ≤ k * p := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) hp.ne_zero)
  exact hpd (characteristic_eq_of_fieldSize_eq_pow hp hkpos hfsp).symm

theorem characteristic_ne_of_subRel {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {d e : TauCeti.LieTypeIndex} (h : subRel p d e) (hpd : p ≠ d.characteristic) :
    p ≠ e.characteristic ∨
      (p = 7 ∧ (∃ q : TauCeti.PrimePower, e = .A 1 q ∧ q.card = 7) ∧
        ∃ q : TauCeti.PrimePower, d = .A 2 q) ∨
      (p = 3 ∧ (∃ q : TauCeti.PrimePower, e = .twistedA 2 q ∧ q.card = 3) ∧ overEight d) := by
  simp only [subRel] at h
  rcases h with ⟨hs, hf⟩ | h2 | h3 | h4 | h5 | h6 | h7
  · exact Or.inl (ne_characteristic_of_field_descent hp hf hpd)
  · obtain ⟨-, -, hf⟩ := h2
    exact Or.inl (ne_characteristic_of_field_descent hp hf hpd)
  · obtain ⟨⟨q, he, hq7⟩, ⟨q', hd⟩, hf⟩ := h3
    have he7 : e.characteristic = 7 := by
      rw [he]
      have hq : q.p = 7 := by
        rw [TauCeti.PrimePower.card_def] at hq7
        exact ((Nat.prime_seven.pow_eq_iff).1 hq7).1
      simp [TauCeti.LieTypeIndex.characteristic_A, hq]
    by_cases hp7 : p = 7
    · exact Or.inr (Or.inl ⟨hp7, ⟨q, he, hq7⟩, q', hd⟩)
    · left
      intro hpe
      exact hp7 (hpe.trans he7)
  · obtain ⟨⟨q, he, hq3⟩, ⟨q', hd⟩, hf⟩ := h4
    have he3 : e.characteristic = 3 := by
      rw [he]
      have hq : q.p = 3 := by
        rw [TauCeti.PrimePower.card_def] at hq3
        exact ((Nat.prime_three.pow_eq_iff).1 hq3).1
      simp [TauCeti.LieTypeIndex.characteristic_twistedA, hq]
    by_cases hp3 : p = 3
    · refine Or.inr (Or.inr ⟨hp3, ⟨q, he, hq3⟩, ?_⟩)
      rw [hd] at hf ⊢
      simp only [fieldSize, overEight] at hf ⊢
      rw [hf, hp3]
      norm_num
    · left
      intro hpe
      exact hp3 (hpe.trans he3)
  · obtain ⟨⟨q, he, hq2⟩, ⟨q', hd⟩, hf⟩ := h5
    left
    intro hpe
    have he2 : e.characteristic = 2 := by
      rw [he]
      have hq : q.p = 2 := by
        rw [TauCeti.PrimePower.card_def] at hq2
        exact ((Nat.prime_two.pow_eq_iff).1 hq2).1
      simp [TauCeti.LieTypeIndex.characteristic_twistedA, hq]
    exact hp2 (hpe.trans he2)
  · obtain ⟨he, ⟨k, hd⟩, hf⟩ := h6
    left
    intro hpe
    have he2 : e.characteristic = 2 := by
      rw [he]; simp [TauCeti.LieTypeIndex.characteristic_tits]
    exact hp2 (hpe.trans he2)
  · obtain ⟨⟨q, he, hq8⟩, ⟨k, hd⟩, hf⟩ := h7
    left
    intro hpe
    have he2 : e.characteristic = 2 := by
      rw [he]
      have hq : q.p = 2 := by
        have h8 : q.card = 2 ^ 3 := by rw [hq8]; norm_num
        rw [TauCeti.PrimePower.card_def] at h8
        exact (Nat.Prime.pow_inj' q.prime_p Nat.prime_two (ne_of_gt q.exponent_pos)
          (by norm_num) h8).1
      simp [TauCeti.LieTypeIndex.characteristic_A, hq]
    exact hp2 (hpe.trans he2)

theorem overEight_of_subRel {d : TauCeti.LieTypeIndex} (e : TauCeti.ValidLieTypeIndex)
    (h : subRel 3 d e.1) (he : ov2Idx e.1) (hd3 : d.characteristic ≠ 3) : overEight d := by
  rcases e with ⟨e, hev⟩
  simp only [ov2Idx] at he
  simp only [subRel] at h
  rcases h with ⟨hs, hf⟩ | h2 | h3 | h4 | h5 | h6 | h7
  · have hfs8 : fieldSize d = 8 := by
      rw [← hf, he]
      norm_num
    refine overEight_of_fieldSize_eq_eight hfs8 ?_
    rintro ⟨k, hk⟩
    subst hk
    rcases e with ⟨n, q⟩ | ⟨n, q⟩ | ⟨n, q⟩ | ⟨n, q⟩ | ⟨n, q⟩ | ⟨n, q⟩ | q | q | q | q | q | q | q | m | m | m | _ <;>
      simp only [sameShape] at hs
    all_goals try exact hs
    simp only [fieldSize] at he
    have hm1 : 1 ≤ m := by
      have hrange := ((TauCeti.LieTypeIndex.valid_iff
        (TauCeti.LieTypeIndex.suzuki m)).1 hev).1
      simpa [TauCeti.LieTypeIndex.inStandardRange_iff] using hrange
    have h' : 2 ^ (2 * m + 1) = 2 ^ 1 := by simpa using he
    have := Nat.pow_right_injective (by norm_num : 2 ≤ 2) h'
    omega
  · obtain ⟨⟨q, hd⟩, ⟨q', he'⟩, hf⟩ := h2
    rw [hd] at hf ⊢
    rw [he'] at hf he
    simp only [fieldSize, overEight] at hf he ⊢
    rw [← hf, he]
    norm_num
  · obtain ⟨⟨q, he', hq7⟩, ⟨q', hd⟩, hf⟩ := h3
    rw [he'] at he
    simp only [fieldSize] at he
    omega
  · obtain ⟨⟨q, he', hq3⟩, ⟨q', hd⟩, hf⟩ := h4
    rw [he'] at he
    simp only [fieldSize] at he
    omega
  · obtain ⟨⟨q, he', hq2⟩, ⟨q', hd⟩, hf⟩ := h5
    exfalso
    rw [hd] at hf
    simp only [fieldSize] at hf
    have hchar : (TauCeti.LieTypeIndex.B 2 q').characteristic = 3 :=
      characteristic_eq_of_fieldSize_eq_pow
        (k := 3) Nat.prime_three (by norm_num)
        (by simpa [fieldSize] using hf)
    exact hd3 (by rw [hd]; exact hchar)
  · obtain ⟨he', ⟨k, hd⟩, hf⟩ := h6
    rw [hd] at hf ⊢
    simp only [fieldSize] at hf
    have hk1 : k = 1 := by
      have h' : 2 ^ (2 * k + 1) = 2 ^ 3 := by rw [hf]
      have := Nat.pow_right_injective (by norm_num : 2 ≤ 2) h'
      omega
    subst hk1
    simp [overEight]
  · obtain ⟨⟨q, he', hq8⟩, ⟨k, hd⟩, hf⟩ := h7
    rw [he'] at he
    simp only [fieldSize] at he
    omega

theorem k2Lie_three_of_subRel_of_eight (d : TauCeti.ValidLieTypeIndex) {e : TauCeti.LieTypeIndex}
    (h : subRel 3 d.1 e) (hd3 : d.1.characteristic ≠ 3)
    (he : ∃ q : TauCeti.PrimePower, (e = .A 1 q ∨ e = .twistedA 2 q) ∧ q.card = 8) :
    k2Lie 3 d.1 := by
  rcases d with ⟨d, hdvalid⟩
  change k2Lie 3 d
  change d.characteristic ≠ 3 at hd3
  rcases he with ⟨Q, hQ, hQ8⟩
  simp only [subRel] at h
  rcases h with h1 | h2 | h3 | h4 | h5 | h6 | h7
  · obtain ⟨hs, hf⟩ := h1
    rcases hQ with rfl | rfl
    · rcases d with ⟨r, q⟩ | ⟨r, q⟩ | ⟨r, q⟩ | ⟨r, q⟩ | ⟨r, q⟩ | ⟨r, q⟩ | q | q | q | q | q | q | q | m | m | m | _ <;>
        simp only [sameShape, fieldSize] at hs hf ⊢
      subst hs
      rw [hQ8] at hf
      norm_num at hf
      have hcard : q.card = 512 := by
        rw [TauCeti.PrimePower.card_def, ← hf]
      simp only [k2Lie]
      rw [hcard]
      norm_num
    · rcases d with ⟨r, q⟩ | ⟨r, q⟩ | ⟨r, q⟩ | ⟨r, q⟩ | ⟨r, q⟩ | ⟨r, q⟩ | q | q | q | q | q | q | q | m | m | m | _ <;>
        simp only [sameShape, fieldSize] at hs hf ⊢
      subst hs
      rw [hQ8] at hf
      norm_num at hf
      have hcard : q.card = 2 ^ 9 := by
        rw [TauCeti.PrimePower.card_def, ← hf]
        norm_num
      have hq : q.p = 2 ∧ q.exponent = 9 := by
        rw [TauCeti.PrimePower.card_def] at hcard
        exact Nat.Prime.pow_inj' q.prime_p Nat.prime_two (ne_of_gt q.exponent_pos)
          (by norm_num) hcard
      simp [k2Lie, hq.1, hq.2]
      norm_num
  · obtain ⟨⟨q, hd⟩, ⟨q', he'⟩, hf⟩ := h2
    rcases hQ with rfl | rfl <;> cases he'
  · obtain ⟨⟨q, he', hq7⟩, ⟨q', hd⟩, hf⟩ := h3
    exfalso
    rcases hQ with rfl | rfl
    · cases he'
      omega
    · cases he'
  · obtain ⟨⟨q, he', hq3⟩, ⟨q', hd⟩, hf⟩ := h4
    exfalso
    rcases hQ with rfl | rfl
    · cases he'
    · cases he'
      omega
  · obtain ⟨⟨q, he', hq2⟩, ⟨q', hd⟩, hf⟩ := h5
    rcases hQ with rfl | rfl <;> cases he'
  · obtain ⟨he', ⟨k, hd⟩, hf⟩ := h6
    rcases hQ with rfl | rfl <;> cases he'
  · obtain ⟨⟨q, he', hq8⟩, ⟨k, hd⟩, hf⟩ := h7
    rcases hQ with rfl | rfl
    · cases he'
      exfalso
      exact hd3 (by rw [hd]; simp [TauCeti.LieTypeIndex.characteristic_reeG2])
    · cases he'

theorem not_suzuki_tits_of_subRel {p : ℕ} {d e : TauCeti.LieTypeIndex} (h : subRel p d e)
    (hd : lpEpsIdx p d) : ¬ (e = .suzuki 2 ∨ e = .tits) := by
  intro he
  rcases hd with ⟨Q, hQ | hQ⟩
  · rcases hQ with ⟨hA, -⟩
    rw [hA] at h
    simp only [subRel] at h
    rcases he with rfl | rfl <;>
      rcases h with h1 | h2 | h3 | h4 | h5 | h6 | h7 <;>
      simp_all [sameShape]
  · rcases hQ with ⟨hA, -⟩
    rw [hA] at h
    simp only [subRel] at h
    rcases he with rfl | rfl <;>
      rcases h with h1 | h2 | h3 | h4 | h5 | h6 | h7 <;>
      simp_all [sameShape]

theorem lpEpsIdx_of_subRel {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {d e : TauCeti.LieTypeIndex}
    (h : subRel p d e) (he : lpEpsIdx p e) : lpEpsIdx p d := by
  rcases he with ⟨Q, hQ | hQ⟩
  · rcases hQ with ⟨hA, hdiv⟩
    subst hA
    simp only [subRel] at h
    rcases h with h1 | h2 | h3 | h4 | h5 | h6 | h7
    · obtain ⟨hs, hf⟩ := h1
      rcases d with ⟨r, q⟩ | ⟨r, q⟩ | ⟨r, q⟩ | ⟨r, q⟩ | ⟨r, q⟩ | ⟨r, q⟩ | q | q | q | q | q | q | q | m | m | m | _ <;>
        simp only [sameShape, fieldSize] at hs hf ⊢
      subst hs
      refine ⟨q, Or.inl ⟨rfl, ?_⟩⟩
      rw [← hf]
      exact hdiv.trans (Nat.sub_one_dvd_pow_sub_one _ _)
    · obtain ⟨⟨q, hd⟩, ⟨q', he'⟩, hf⟩ := h2
      cases he'
    · obtain ⟨⟨q, he', hq7⟩, ⟨q', hd⟩, hf⟩ := h3
      injection he' with hp1 hq
      exfalso
      omega
    · obtain ⟨⟨q, he', hq3⟩, ⟨q', hd⟩, hf⟩ := h4
      cases he'
    · obtain ⟨⟨q, he', hq2⟩, ⟨q', hd⟩, hf⟩ := h5
      cases he'
    · obtain ⟨he', ⟨k, hd⟩, hf⟩ := h6
      cases he'
    · obtain ⟨⟨q, he', hq8⟩, ⟨k, hd⟩, hf⟩ := h7
      injection he' with hp1 hq
      exfalso
      omega
  · rcases hQ with ⟨hA, hdiv⟩
    subst hA
    simp only [subRel] at h
    rcases h with h1 | h2 | h3 | h4 | h5 | h6 | h7
    · obtain ⟨hs, hf⟩ := h1
      rcases d with ⟨r, q⟩ | ⟨r, q⟩ | ⟨r, q⟩ | ⟨r, q⟩ | ⟨r, q⟩ | ⟨r, q⟩ | q | q | q | q | q | q | q | m | m | m | _ <;>
        simp only [sameShape, fieldSize] at hs hf ⊢
      subst hs
      refine ⟨q, Or.inr ⟨rfl, ?_⟩⟩
      rw [← hf]
      simpa only [one_pow] using
        hdiv.trans ((hp.odd_of_ne_two hp2).nat_add_dvd_pow_add_pow _ 1)
    · obtain ⟨⟨q, hd⟩, ⟨q', he'⟩, hf⟩ := h2
      cases he'
    · obtain ⟨⟨q, he', hq7⟩, ⟨q', hd⟩, hf⟩ := h3
      cases he'
    · obtain ⟨⟨q, he', hq3⟩, ⟨q', hd⟩, hf⟩ := h4
      injection he' with hp1 hq
      have hp3 : p = 3 := by omega
      subst hq
      rw [hp3, hq3] at hdiv
      norm_num at hdiv
    · obtain ⟨⟨q, he', hq2⟩, ⟨q', hd⟩, hf⟩ := h5
      injection he' with hp1 hq
      exfalso
      have hp4 : p ≠ 4 := by
        rintro rfl
        norm_num at hp
      omega
    · obtain ⟨he', ⟨k, hd⟩, hf⟩ := h6
      cases he'
    · obtain ⟨⟨q, he', hq8⟩, ⟨k, hd⟩, hf⟩ := h7
      cases he' 

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
