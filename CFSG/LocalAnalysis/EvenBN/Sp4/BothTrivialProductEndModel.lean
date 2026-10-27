module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bCent

public section

namespace CFSG.LocalAnalysis.EvenBN.Sp4

namespace BothTrivialProductEnd

open Subgroup
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)

@[expose] def outerResidualOrder (n : ℕ) : ℕ :=
  if n = 2 then 360
  else if Even n then (2 ^ (n / 2)) ^ 4 * ((2 ^ (n / 2)) ^ 2 - 1) * ((2 ^ (n / 2)) ^ 4 - 1)
  else (2 ^ n) ^ 2 * (2 ^ n - 1) * ((2 ^ n) ^ 2 + 1)

section Arithmetic

theorem outerResidual_sq_sub_one {q : ℕ} (hq : 1 ≤ q) : q ^ 2 - 1 = (q - 1) * (q + 1) := by
  obtain ⟨p, rfl⟩ := Nat.exists_eq_add_of_le' hq
  rw [Nat.add_sub_cancel, show (p + 1) ^ 2 = p * (p + 1 + 1) + 1 by ring, Nat.add_sub_cancel]

theorem outerResidual_sq_add_one {q : ℕ} (hq : 1 ≤ q) : q ^ 2 + 1 = 2 + (q - 1) * (q + 1) := by
  obtain ⟨p, rfl⟩ := Nat.exists_eq_add_of_le' hq
  rw [Nat.add_sub_cancel]
  ring

theorem card_antiSp_factored {q : ℕ} (hq : 1 ≤ q) :
    q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1)) = q ^ 4 * (q - 1) ^ 2 * ((q + 1) ^ 2 * (q ^ 2 + 1)) := by
  have h4 : q ^ 4 - 1 = (q ^ 2 - 1) * (q ^ 2 + 1) := by
    rw [show q ^ 4 = (q ^ 2) ^ 2 by ring, outerResidual_sq_sub_one (Nat.one_le_pow _ _ hq)]
  rw [h4, outerResidual_sq_sub_one hq]
  ring

theorem outerResidual_sq_not_dvd_odd {q : ℕ} (hq : Even q) (hq2 : 2 ≤ q) :
    ¬ (q ^ 2 * (q - 1) * (q ^ 2 + 1)) ^ 2 ∣ q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1)) := by
  intro h
  have hq1 : 1 ≤ q := by omega
  have ha : 0 < q ^ 4 * (q - 1) ^ 2 := Nat.mul_pos (pow_pos (by omega) 4) (pow_pos (by omega) 2)
  have hX : 0 < q ^ 2 + 1 := Nat.succ_pos _
  have hlhs : (q ^ 2 * (q - 1) * (q ^ 2 + 1)) ^ 2 =
      q ^ 4 * (q - 1) ^ 2 * ((q ^ 2 + 1) * (q ^ 2 + 1)) := by ring
  have hrhs : q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1)) =
      q ^ 4 * (q - 1) ^ 2 * ((q ^ 2 + 1) * (q + 1) ^ 2) := by
    rw [card_antiSp_factored hq1]
    ring
  rw [hlhs, hrhs] at h
  have h1 : (q ^ 2 + 1) * (q ^ 2 + 1) ∣ (q ^ 2 + 1) * (q + 1) ^ 2 :=
    (Nat.mul_dvd_mul_iff_left ha).1 h
  have h2 : q ^ 2 + 1 ∣ (q + 1) ^ 2 := (Nat.mul_dvd_mul_iff_left hX).1 h1
  have hcop : Nat.Coprime (q ^ 2 + 1) (q + 1) := by
    rw [outerResidual_sq_add_one hq1, Nat.coprime_add_mul_right_left, Nat.coprime_two_left]
    exact hq.add_one
  have h3 : q ^ 2 + 1 = 1 := (Nat.Coprime.pow_right 2 hcop).eq_one_of_dvd h2
  have h4 : 2 ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left hq2 2
  omega

theorem outerResidual_sq_not_dvd_even {q : ℕ} (hq : Even q) (hq4 : 4 ≤ q) :
    ¬ (q ^ 2 * (q - 1) * (q ^ 2 - 1)) ^ 2 ∣ q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1)) := by
  intro h
  have hq1 : 1 ≤ q := by omega
  have ha : 0 < q ^ 4 * (q + 1) ^ 2 * (q - 1) ^ 2 :=
    Nat.mul_pos (Nat.mul_pos (pow_pos (by omega) 4) (pow_pos (by omega) 2))
      (pow_pos (by omega) 2)
  have hlhs : (q ^ 2 * (q - 1) * (q ^ 2 - 1)) ^ 2 =
      q ^ 4 * (q + 1) ^ 2 * (q - 1) ^ 2 * (q - 1) ^ 2 := by
    rw [outerResidual_sq_sub_one hq1]
    ring
  have hrhs : q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1)) =
      q ^ 4 * (q + 1) ^ 2 * (q - 1) ^ 2 * (q ^ 2 + 1) := by
    rw [card_antiSp_factored hq1]
    ring
  rw [hlhs, hrhs] at h
  have h1 : (q - 1) ^ 2 ∣ q ^ 2 + 1 := (Nat.mul_dvd_mul_iff_left ha).1 h
  have hodd : Odd (q - 1) := by
    obtain ⟨r, hr⟩ := hq
    exact ⟨r - 1, by omega⟩
  have hcop : Nat.Coprime (q - 1) (q ^ 2 + 1) := by
    rw [outerResidual_sq_add_one hq1, Nat.coprime_comm, Nat.coprime_add_mul_left_left,
      Nat.coprime_two_left]
    exact hodd
  have h2 : (q - 1) ^ 2 = 1 := (Nat.Coprime.pow_left 2 hcop).eq_one_of_dvd h1
  have h3 : 3 ≤ q - 1 := by omega
  have h4 : 3 ^ 2 ≤ (q - 1) ^ 2 := Nat.pow_le_pow_left h3 2
  omega

end Arithmetic

section Model

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem card_residual_antiSp_two {k : Type} [Field k] [Finite k] (hk : Nat.card k = 2) :
    Nat.card (residual (antiSp k)) = 360 := by
  let _ : Fintype k := Fintype.ofFinite k
  have hk' : Fintype.card k = 2 := by rwa [← Nat.card_eq_fintype_card]
  let ε : ZMod 2 ≃+* k := ZMod.ringEquivOfPrime k Nat.prime_two hk'
  have hJ : antiSp (ZMod 2) = CFSG.ComponentClassification.PresentationLocal.sympFour := by
    ext g
    rfl
  let e : antiSp k ≃* CFSG.ComponentClassification.PresentationLocal.sympFour :=
    (antiSpCongr ε.symm).trans (MulEquiv.subgroupCongr hJ)
  rw [card_residual_congr e, card_residual_sympFour]

theorem card_residual_fixedSubgroup_minorAut_pow {n : ℕ}
    (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n) :
    Nat.card (residual (fixedSubgroup (minorAut K ^ n))) = outerResidualOrder n := by
  rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
  · obtain ⟨k, hcp, lift, hcard, hinj, hrange⟩ := exists_even_fixed (m := m) (by omega) hK
    have := hcp
    let _ : Fintype k := Fintype.ofFinite k
    let e : antiSp k ≃* fixedSubgroup (minorAut K ^ (2 * m)) :=
      (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
    rw [← card_residual_congr e]
    by_cases hm2 : 2 ≤ m
    · have hperf : Group.IsPerfect (antiSp k) :=
        antiSp_isPerfect (by rw [← Nat.card_eq_fintype_card]; exact hcard) hm2
      rw [residual_eq_top_of_perfect hperf, Subgroup.card_top, card_antiSp hcard,
        outerResidualOrder, if_neg (by omega), if_pos (even_two_mul m),
        show 2 * m / 2 = m by omega]
      exact (Nat.mul_assoc _ _ _).symm
    · have hm1 : m = 1 := by omega
      subst hm1
      rw [card_residual_antiSp_two (by simpa using hcard)]
      rfl
  · have hperf : Group.IsPerfect (fixedSubgroup (minorAut K ^ (2 * m + 1))) := by
      have : Group.IsPerfect (CFSG.Blueprint.suzukiGroup m K) :=
        (CFSG.LieType.Ree.suzuki_perfect (by omega) hK).2
      exact Group.IsPerfect.ofSurjective (f := (fixedSubgroupEtaEquiv hK).symm.toMonoidHom)
        (fixedSubgroupEtaEquiv hK).symm.surjective
    have hodd : ¬ Even (2 * m + 1) := Nat.not_even_iff_odd.mpr (odd_two_mul_add_one m)
    rw [residual_eq_top_of_perfect hperf, Subgroup.card_top, card_fixedSubgroup_eta hK,
      outerResidualOrder, if_neg (by omega), if_neg hodd]

theorem card_residual_fixedSubgroup {n : ℕ} (hn : 2 ≤ n)
    (hK : Nat.card K = 2 ^ n) (θ : MulAut (antiSp K)) (hθ : θ * θ = 1)
    (hθi : θ ∉ inner (antiSp K)) :
    Nat.card (residual (fixedSubgroup θ)) = outerResidualOrder n := by
  obtain ⟨c, hc⟩ := outer_involution_conj hn hK θ hθ hθi
  have h := card_residual_congr (fixedSubgroupConjEquiv (MulAut.conj c) (minorAut K ^ n))
  rw [← hc] at h
  rw [← h]
  exact card_residual_fixedSubgroup_minorAut_pow hn hK

theorem not_sq_dvd_card_antiSp {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n) :
    ¬ outerResidualOrder n ^ 2 ∣ Nat.card (antiSp K) := by
  rw [card_antiSp hK]
  have hqe : Even ((2 : ℕ) ^ n) := Nat.even_pow.2 ⟨even_two, by omega⟩
  by_cases h2 : n = 2
  · subst h2
    norm_num [outerResidualOrder]
  · by_cases hev : Even n
    · obtain ⟨m, hm⟩ := hev
      have hnm : n = 2 * m := by omega
      have hq4 : 4 ≤ (2 : ℕ) ^ n := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
      have h4 : ((2 : ℕ) ^ m) ^ 4 = (2 ^ n) ^ 2 := by
        rw [hnm, ← pow_mul, ← pow_mul]
        ring_nf
      have h5 : ((2 : ℕ) ^ m) ^ 2 = 2 ^ n := by
        rw [hnm, ← pow_mul]
        ring_nf
      rw [outerResidualOrder, if_neg h2, if_pos ⟨m, hm⟩, show n / 2 = m by omega, h4, h5]
      exact outerResidual_sq_not_dvd_even hqe hq4
    · rw [outerResidualOrder, if_neg h2, if_neg hev]
      exact outerResidual_sq_not_dvd_odd hqe (Nat.le_self_pow (by omega) 2)

end Model

end BothTrivialProductEnd

end CFSG.LocalAnalysis.EvenBN.Sp4
