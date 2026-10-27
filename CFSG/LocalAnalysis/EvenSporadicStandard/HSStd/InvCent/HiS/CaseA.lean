module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.OddInner

public section

namespace CFSG.EvenSporadicStandard.HSStd.InvCent

open Subgroup

theorem false_of_order_fifteen_z2_mulAut {X : Type*} [Group X]
    (e : X ≃* Multiplicative (ZMod 2) × MulAut (alternatingGroup (Fin 6))) (x : X)
    (hx : orderOf x = 15) : False := by
  let y := e x
  have hy : orderOf y = 15 := by
    dsimp [y]
    rw [MulEquiv.orderOf_eq e x, hx]
  have hprod : orderOf y = Nat.lcm (orderOf y.1) (orderOf y.2) := Prod.orderOf y
  have hεdvd2 : orderOf y.1 ∣ 2 := by
    rw [orderOf_dvd_iff_pow_eq_one]
    apply Multiplicative.ext
    rw [toAdd_pow, toAdd_one, nsmul_eq_mul, CharP.cast_eq_zero (ZMod 2) 2, zero_mul]
  have hεdvd15 : orderOf y.1 ∣ 15 := by
    have h := orderOf_fst_dvd_orderOf (x := y)
    rwa [hy] at h
  have hε1 : orderOf y.1 = 1 := by
    have hg : orderOf y.1 ∣ Nat.gcd 2 15 := Nat.dvd_gcd hεdvd2 hεdvd15
    rw [show Nat.gcd 2 15 = 1 by decide] at hg
    exact Nat.dvd_one.mp hg
  have hσ15 : orderOf y.2 = 15 := by
    have h := hprod
    rw [hy, hε1, Nat.lcm_one_left] at h
    exact h.symm
  have hσodd : Odd (orderOf y.2) := by
    rw [hσ15]
    exact ⟨7, by norm_num⟩
  obtain ⟨a, ha⟩ := oddInner_alternatingGroup_six y.2 hσodd
  have hdiv : orderOf y.2 ∣ orderOf a := by
    rw [← ha]
    exact orderOf_map_dvd
      (MulAut.conj : alternatingGroup (Fin 6) →* MulAut (alternatingGroup (Fin 6))) a
  have h15a : 15 ∣ orderOf a := by
    rw [← hσ15]
    exact hdiv
  let m := orderOf a / 15
  have hmul : 15 * m = orderOf a := by
    dsimp [m]
    rw [Nat.mul_comm, Nat.div_mul_cancel h15a]
  have hm0 : m ≠ 0 := by
    have hle : 15 ≤ orderOf a := Nat.le_of_dvd (orderOf_pos a) h15a
    have hpos : 0 < m := by
      dsimp [m]
      exact Nat.div_pos hle (by norm_num)
    exact hpos.ne'
  have hmdvd : m ∣ orderOf a := ⟨15, by rw [hmul.symm, Nat.mul_comm]⟩
  have hdivm : orderOf a / m = 15 := by
    rw [← hmul]
    exact Nat.mul_div_cancel 15 (Nat.pos_of_ne_zero hm0)
  have hpow : orderOf (a ^ m) = 15 := by
    rw [orderOf_pow_of_dvd hm0 hmdvd, hdivm]
  exact (no_order_fifteen_alternatingGroup_six (a ^ m)) hpow

end CFSG.EvenSporadicStandard.HSStd.InvCent
