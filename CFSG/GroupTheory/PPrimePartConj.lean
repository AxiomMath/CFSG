module

public import Mathlib.GroupTheory.PGroup
public import TauCeti.GroupTheory.OrderOfElement.PPart

public section

namespace CFSG.GroupTheory

variable {H : Type*} [Group H] [Finite H]

theorem exists_isPGroup_zpowers_conj_eq {p : ℕ} (hp : p.Prime) {x : H}
    (hpow : ∃ k, orderOf (MulAut.conj x) = p ^ k) :
    ∃ y : H, IsPGroup p (Subgroup.zpowers y) ∧ MulAut.conj y = MulAut.conj x := by
  classical
  let y : H := TauCeti.pPart p x
  let z : H := TauCeti.pFreePart p x
  have hyz : y * z = x := TauCeti.pPart_mul_pFreePart p x
  have hypow : ∃ k, orderOf y = p ^ k :=
    ⟨(orderOf x).factorization p, TauCeti.orderOf_pPart hp (orderOf_pos x).ne'⟩
  have hznot : ¬ p ∣ orderOf z :=
    TauCeti.not_dvd_orderOf_pFreePart hp (orderOf_pos x).ne'
  have hzpow : z ∈ Subgroup.zpowers x := TauCeti.pFreePart_mem_zpowers p x
  have hzconj : MulAut.conj z = 1 := by
    have hdvdz : orderOf (MulAut.conj z) ∣ orderOf z :=
      orderOf_map_dvd (MulAut.conj : H →* MulAut H) z
    have hmem : MulAut.conj z ∈ Subgroup.zpowers (MulAut.conj x) := by
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hzpow
      rw [show z = x ^ n from hn.symm]
      exact Subgroup.mem_zpowers_iff.mpr ⟨n, by rw [map_zpow]⟩
    have hdvd2 : orderOf (MulAut.conj z) ∣ orderOf (MulAut.conj x) :=
      orderOf_dvd_of_mem_zpowers hmem
    obtain ⟨j, hj⟩ := hpow
    have hcop : Nat.Coprime (p ^ j) (orderOf z) :=
      Nat.Coprime.pow_left j ((Nat.Prime.coprime_iff_not_dvd hp).mpr hznot)
    have hgcd : orderOf (MulAut.conj z) ∣ Nat.gcd (p ^ j) (orderOf z) := by
      rw [← hj]
      exact Nat.dvd_gcd hdvd2 hdvdz
    have h1 : orderOf (MulAut.conj z) = 1 := by
      rw [hcop.gcd_eq_one] at hgcd
      exact Nat.dvd_one.mp hgcd
    exact orderOf_eq_one_iff.mp h1
  refine ⟨y, ?_, ?_⟩
  · obtain ⟨k, hk⟩ := hypow
    refine IsPGroup.of_card (n := k) ?_
    rw [Nat.card_zpowers, hk]
  · calc MulAut.conj y = MulAut.conj y * 1 := (mul_one _).symm
      _ = MulAut.conj y * MulAut.conj z := by rw [hzconj]
      _ = MulAut.conj (y * z) := (map_mul MulAut.conj y z).symm
      _ = MulAut.conj x := by rw [hyz]

end CFSG.GroupTheory
