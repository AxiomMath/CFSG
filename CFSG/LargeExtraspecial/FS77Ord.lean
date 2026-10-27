module

public import CFSG.LargeExtraspecial.S12DWSetting

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.FS77

open Subgroup Module QuadraticMap

variable {G : Type*} [Group G] [Finite G]

theorem two_pow_dvd_card_M (S : Setting G) (hn : 1 ≤ S.width)
    (hΩ : S.Mbar.map S.O.subtype = CFSG.Open.timmesfeldOmega S.q) :
    2 ^ (S.width ^ 2 + S.width + 1) ∣ Nat.card S.M := by
  set n := S.width with hn'
  have hfin : finrank (ZMod 2) S.Qt = 2 * n := S.finrank_Qt_eq_two_mul_width
  have : Nontrivial S.Qt := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
  have : Finite S.Qt := Module.finite_of_finite (ZMod 2)
  have hMb : Nat.card S.Mbar =
      Nat.card (CFSG.RankThree.OrthogonalInvolutions.omegaGroup S.q S.q_nondegenerate) := by
    rw [← s12_timmesfeldOmega_eq S.q S.q_nondegenerate, ← hΩ]
    exact Nat.card_congr (S.Mbar.equivMapOfInjective S.O.subtype S.O.subtype_injective).toEquiv
  have hM : Nat.card S.M = 2 ^ (1 + 2 * n) *
      Nat.card (CFSG.RankThree.OrthogonalInvolutions.omegaGroup S.q S.q_nondegenerate) := by
    rw [← hMb]
    have h1 := card_ker_mul_card_range S.ρ
    rw [S.ker_ρ, S.card_Q_eq] at h1
    exact h1.symm
  have hO := S12DW.card_orthogonalGroup_eq S.q_nondegenerate
  have hOz := S12DW.card_orthogonalGroup_mul_ncard_eq S.q_nondegenerate hfin
  have hc := CFSG.Fischer.Classification.LocalSymp.two_mul_ncard_quadratic S.q
    (S12DW.polar_eq_zero_imp S.q_nondegenerate) (S12DW.natCard_eq_four_pow hfin)
  have h0 := S12DW.ncard_eq_zero_eq S.q
  rw [S12DW.natCard_eq_four_pow hfin] at h0
  set N1 := {x | S.q x = 1}.ncard
  set N0 := {x | S.q x = 0}.ncard
  have h4 : 4 ^ n = 2 ^ n * 2 ^ n := by rw [← mul_pow]; norm_num
  have h2n : 2 ^ n = 2 * 2 ^ (n - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have ht1 : 1 ≤ 2 ^ (n - 1) := Nat.one_le_two_pow
  obtain ⟨u, hu, hN0⟩ : ∃ u, Odd u ∧ N0 = 2 ^ (n - 1) * u := by
    rw [h4, h2n] at hc h0
    have e1 : 2 * 2 ^ (n - 1) * (2 * 2 ^ (n - 1)) = 4 * (2 ^ (n - 1) * 2 ^ (n - 1)) := by ring
    rw [e1] at hc h0
    rcases hc with hc | hc
    · refine ⟨2 * 2 ^ (n - 1) + 1, odd_two_mul_add_one _, ?_⟩
      have e2 : 2 ^ (n - 1) * (2 * 2 ^ (n - 1) + 1) =
          2 * (2 ^ (n - 1) * 2 ^ (n - 1)) + 2 ^ (n - 1) := by ring
      rw [e2]
      generalize 2 ^ (n - 1) * 2 ^ (n - 1) = s at *
      omega
    · refine ⟨2 * 2 ^ (n - 1) - 1, ⟨2 ^ (n - 1) - 1, by omega⟩, ?_⟩
      have e2 : 2 ^ (n - 1) * (2 * 2 ^ (n - 1) - 1) =
          2 * (2 ^ (n - 1) * 2 ^ (n - 1)) - 2 ^ (n - 1) := by
        rw [Nat.mul_sub, mul_one]
        ring_nf
      rw [e2]
      have : 2 ^ (n - 1) ≤ 2 ^ (n - 1) * 2 ^ (n - 1) := Nat.le_mul_of_pos_right _ (by omega)
      generalize 2 ^ (n - 1) * 2 ^ (n - 1) = s at *
      omega
  set o := Nat.card (TauCeti.QuadraticMap.orthogonalGroup S.q)
  have hdvd1 : 2 ^ (n ^ 2) ∣ o * 2 ^ (n - 1) * u := by
    rw [mul_assoc, ← hN0, hOz]
    exact dvd_mul_right _ _
  have hcop : Nat.Coprime (2 ^ (n ^ 2)) u :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hu)
  have hdvd2 : 2 ^ (n ^ 2) ∣ o * 2 ^ (n - 1) := hcop.dvd_of_dvd_mul_right hdvd1
  have hexp : n ^ 2 = (n ^ 2 - n + 1) + (n - 1) := by
    have : n ≤ n ^ 2 := by nlinarith
    omega
  rw [hexp, pow_add] at hdvd2
  have hdvd3 : 2 ^ (n ^ 2 - n + 1) ∣ o := Nat.dvd_of_mul_dvd_mul_right (by positivity) hdvd2
  rw [hO, pow_succ, mul_comm (2 ^ (n ^ 2 - n)) 2] at hdvd3
  have hdvd4 := Nat.dvd_of_mul_dvd_mul_left (by norm_num) hdvd3
  rw [hM]
  have hexp2 : n ^ 2 + n + 1 = (1 + 2 * n) + (n ^ 2 - n) := by
    have : n ≤ n ^ 2 := by nlinarith
    omega
  rw [hexp2, pow_add]
  exact Nat.mul_dvd_mul_left _ hdvd4

end CFSG.LargeExtraspecial.FS77
