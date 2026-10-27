module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralGenerators

public section

namespace CFSG.ProperTwoGeneratedCore

variable {Q : Type*} [Group Q] [Finite Q]

theorem two_involution_odd_product_card (z t : Q)
    (hz : orderOf z = 2) (ht : t ^ 2 = 1)
    (hgen : (⊤ : Subgroup Q) = Subgroup.zpowers z ⊔ Subgroup.zpowers t)
    (hodd : Odd (orderOf (z * t))) : Nat.card Q = 2 * orderOf (z * t) := by
  let r := z * t
  have hz2 : z ^ 2 = 1 := (orderOf_eq_prime_iff.mp hz).1
  have hzinv : z⁻¹ = z := inv_eq_self_of_orderOf_eq_two hz
  have htinv : t⁻¹ = t := by
    apply inv_eq_of_mul_eq_one_right
    simpa only [pow_two] using ht
  have hgenr : (⊤ : Subgroup Q) = Subgroup.zpowers r ⊔ Subgroup.zpowers z := by
    symm
    apply top_le_iff.mp
    rw [hgen]
    refine sup_le le_sup_right ((Subgroup.zpowers_le).mpr ?_)
    have hzR : z ∈ Subgroup.zpowers r ⊔ Subgroup.zpowers z :=
      Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
    have hrR : r ∈ Subgroup.zpowers r ⊔ Subgroup.zpowers z :=
      Subgroup.mem_sup_left (Subgroup.mem_zpowers r)
    have htR := (Subgroup.zpowers r ⊔ Subgroup.zpowers z).mul_mem
      ((Subgroup.zpowers r ⊔ Subgroup.zpowers z).inv_mem hzR) hrR
    simpa [r, mul_assoc] using htR
  have hrel : z * r * z⁻¹ = r⁻¹ := by
    dsimp only [r]
    rw [mul_inv_rev, hzinv, htinv, ← mul_assoc, ← pow_two, hz2, one_mul]
  have hznot : z ∉ Subgroup.zpowers r := by
    intro hzR
    let zR : Subgroup.zpowers r := ⟨z, hzR⟩
    have hdvd : 2 ∣ orderOf r := by
      rw [← Nat.card_zpowers r, ← hz]
      change orderOf (zR : Q) ∣ Nat.card (Subgroup.zpowers r)
      rw [Subgroup.orderOf_coe]
      exact orderOf_dvd_natCard zR
    exact hodd.not_two_dvd_nat hdvd
  obtain ⟨e⟩ := CFSG.GorensteinWalter.dihedral_of_generators_of_not_mem
    r z hgenr hz2 hrel hznot
  rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]

theorem two_involution_odd_product_reflection_index (z t : Q)
    (hz : orderOf z = 2) (ht : t ^ 2 = 1)
    (hgen : (⊤ : Subgroup Q) = Subgroup.zpowers z ⊔ Subgroup.zpowers t)
    (hodd : Odd (orderOf (z * t))) :
    (Subgroup.zpowers z).index = orderOf (z * t) := by
  have hcard : Nat.card (Subgroup.zpowers z) = 2 := (Nat.card_zpowers z).trans hz
  have hmul := (Subgroup.zpowers z).card_mul_index
  rw [hcard, two_involution_odd_product_card z t hz ht hgen hodd] at hmul
  exact Nat.mul_left_cancel (by decide) hmul

end CFSG.ProperTwoGeneratedCore
