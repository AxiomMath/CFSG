module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.QzConj
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion2.Cover
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion3.Conj

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

private theorem orderOf_eq_of_isConj_class {G : Type} [Group G] {a b : G} (h : IsConj a b) :
    orderOf a = orderOf b := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  rw [← hc]
  simpa [MulAut.conj_apply] using (MulEquiv.orderOf_eq (MulAut.conj c) a).symm

theorem fusion3_class (hI : TwoHSInterface) {G : Type} [Group G] {a z : G} (h : IsF5Type a z)
    (hF1 : Fusion1Facts a z) (hF2 : Fusion2Facts a z) {t : G}
    (ht : IsConj a t ∨ IsConj z t) (hat : IsConj a (a * t) ∨ IsConj z (a * t)) :
    (IsConj z t ∧ IsConj a (a * t) ∧ IsShapeTwoTwoSixS5 ↥(Gxy a t) ∧ a ∈ Qz t) ∨
    (IsConj a t ∧ IsConj z (a * t) ∧ IsShapeTwoTwoSixS5 ↥(Gxy a t)) ∨
    (IsConj a t ∧ IsConj a (a * t) ∧ IsShapeTwoTwoTimesA8 ↥(Gxy a t)) ∨
    (IsConj z t ∧ IsConj z (a * t) ∧ IsShapeTwoTwoTimesTwoFourA5 ↥(Gxy a t) ∧ a ∉ Qz t) := by
  obtain ⟨z₀, b, u, hF, hz₀, hz₀a, -, haQ, -, hsh⟩ := hF1.rep_z
  obtain ⟨⟨hbA, hbaA, -, hbsh⟩, ⟨huB, hauB, hauQ, -, -, -, hush⟩⟩ := hF2.reps_bu z₀ b u hF hz₀
  have ha_ord : orderOf a = 2 := h.orderOf_a
  have hot : orderOf t = 2 := by
    rcases ht with hta | htz
    · rw [← orderOf_eq_of_isConj_class hta, h.orderOf_a]
    · rw [← orderOf_eq_of_isConj_class htz, h.orderOf_z]
  have hota : orderOf (a * t) = 2 := by
    rcases hat with hata | hatz
    · rw [← orderOf_eq_of_isConj_class hata, h.orderOf_a]
    · rw [← orderOf_eq_of_isConj_class hatz, h.orderOf_z]
  have ha2 : a ^ 2 = 1 := by rw [← ha_ord]; exact pow_orderOf_eq_one a
  have ht2 : t ^ 2 = 1 := by rw [← hot]; exact pow_orderOf_eq_one t
  have hat2 : (a * t) ^ 2 = 1 := by rw [← hota]; exact pow_orderOf_eq_one (a * t)
  have ht1 : t ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hot
    omega
  have hta_ne : t ≠ a := by
    intro h1
    have h : a * t = 1 := by rw [h1]; simpa [pow_two] using ha2
    rw [h, orderOf_one] at hota
    omega
  have htG : t ∈ Gx a := mem_Gx.mpr (comm_of_sq_mul ha2 ht2 hat2)
  rcases exists_conj_rep hF htG ht2 ht1 with hta | ⟨k, hk, hkt⟩ | ⟨k, hk, hkt⟩ |
    ⟨k, hk, hkt⟩ | ⟨k, hk, hkt⟩
  · exact absurd hta hta_ne
  ·
    have hkfix : k * a * k⁻¹ = a := by
      rw [← mem_Gx.mp hk, mul_assoc, mul_inv_cancel, mul_one]
    have hmc : a * t = k * (a * (z₀ : G)) * k⁻¹ := by
      rw [← hkt]; exact mul_conj_of_fix hkfix
    left
    refine ⟨hz₀.trans (isConj_iff.mpr ⟨k, hkt⟩), hz₀a.trans (isConj_iff.mpr ⟨k, hmc.symm⟩), ?_, ?_⟩
    · obtain ⟨e⟩ := nonempty_mulEquiv_Gxy_conj (a := a) (b := (z₀ : G)) (k := k) hkfix
      rw [← hkt]
      exact IsShapeTwoTwoSixS5.of_mulEquiv e hsh
    · have hQ : k * a * k⁻¹ ∈ Qz (k * (z₀ : G) * k⁻¹) :=
        (Qz_conj_mem_iff (x := (z₀ : G)) (y := a) k).mpr haQ
      simpa [hkfix, hkt] using hQ
  ·
    have hkfix : k * a * k⁻¹ = a := by
      rw [← mem_Gx.mp hk, mul_assoc, mul_inv_cancel, mul_one]
    have hmc : a * t = k * (a * (a * (z₀ : G))) * k⁻¹ := by
      rw [← hkt]; exact mul_conj_of_fix hkfix
    have haa : a * a = 1 := by simpa [pow_two] using ha2
    have haz : a * (a * (z₀ : G)) = (z₀ : G) := by rw [← mul_assoc, haa, one_mul]
    have hat_eq : a * t = k * (z₀ : G) * k⁻¹ := by rw [hmc, haz]
    right; left
    refine ⟨hz₀a.trans (isConj_iff.mpr ⟨k, hkt⟩), hz₀.trans (isConj_iff.mpr ⟨k, hat_eq.symm⟩), ?_⟩
    · have heq : Gxy a (a * (z₀ : G)) = Gxy a (z₀ : G) := Gxy_mul_left a (z₀ : G)
      have hsh_az : IsShapeTwoTwoSixS5 ↥(Gxy a (a * (z₀ : G))) :=
        IsShapeTwoTwoSixS5.of_mulEquiv (MulEquiv.subgroupCongr heq).symm hsh
      obtain ⟨e⟩ := nonempty_mulEquiv_Gxy_conj (a := a) (b := a * (z₀ : G)) (k := k) hkfix
      rw [← hkt]
      exact IsShapeTwoTwoSixS5.of_mulEquiv e hsh_az
  ·
    have hkfix : k * a * k⁻¹ = a := by
      rw [← mem_Gx.mp hk, mul_assoc, mul_inv_cancel, mul_one]
    have hmc : a * t = k * (a * (b : G)) * k⁻¹ := by
      rw [← hkt]; exact mul_conj_of_fix hkfix
    right; right; left
    refine ⟨hbA.trans (isConj_iff.mpr ⟨k, hkt⟩), hbaA.trans (isConj_iff.mpr ⟨k, hmc.symm⟩), ?_⟩
    · obtain ⟨e⟩ := nonempty_mulEquiv_Gxy_conj (a := a) (b := (b : G)) (k := k) hkfix
      rw [← hkt]
      exact IsShapeTwoTwoTimesA8.of_mulEquiv e hbsh
  ·
    have hkfix : k * a * k⁻¹ = a := by
      rw [← mem_Gx.mp hk, mul_assoc, mul_inv_cancel, mul_one]
    have hmc : a * t = k * (a * (u : G)) * k⁻¹ := by
      rw [← hkt]; exact mul_conj_of_fix hkfix
    right; right; right
    refine ⟨huB.trans (isConj_iff.mpr ⟨k, hkt⟩), hauB.trans (isConj_iff.mpr ⟨k, hmc.symm⟩), ?_, ?_⟩
    · obtain ⟨e⟩ := nonempty_mulEquiv_Gxy_conj (a := a) (b := (u : G)) (k := k) hkfix
      rw [← hkt]
      exact IsShapeTwoTwoTimesTwoFourA5.of_mulEquiv e hush
    · intro hQ
      have hQ' : k * a * k⁻¹ ∈ Qz (k * (u : G) * k⁻¹) := by
        rw [hkfix, hkt]; exact hQ
      exact hauQ ((Qz_conj_mem_iff (x := (u : G)) (y := a) k).mp hQ')

end CFSG.EvenSporadicStandard.HNRecog.Section3
