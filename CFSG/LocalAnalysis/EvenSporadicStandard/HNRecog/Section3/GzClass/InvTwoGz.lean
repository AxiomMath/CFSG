module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzClass.OddConj
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzClass.StarGz

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog
open scoped commutatorElement

private theorem orderOf_eq_of_isConj' {G : Type*} [Group G] {x y : G} (h : IsConj x y) :
    orderOf y = orderOf x := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  rw [← hc]
  simpa [MulAut.conj_apply] using (MulEquiv.orderOf_eq (MulAut.conj c) x)

theorem gzClass_inv_two (hI : TwoHSInterface) (hC : CSideFacts) {G : Type} [Group G]
    [Finite G] {a z : G} (h : IsF5Type a z) (hF1 : Vert Fusion1Facts a z)
    (hF2 : Vert Fusion2Facts a z) (hF3 : Vert Fusion3Facts a z) (hOrb : Vert GzOrbitFacts a z)
    (t : G) (ht : orderOf t = 2) : IsConj a t ∨ IsConj z t := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨htA, htB⟩ := hcon
  have ht2 : t ^ 2 = 1 := by
    have h := pow_orderOf_eq_one t
    rwa [ht] at h
  have ht1 : t ≠ 1 := by
    intro h
    have : orderOf t = 1 := by rw [h, orderOf_one]
    omega
  have htmul : t * t = 1 := by rwa [pow_two] at ht2
  obtain ⟨z₁, hz₁, htz₁⟩ := exists_isConj_commute_of_orderOf_two h ht
  have h₁ : IsF5Type a z₁ := isF5Type_of_isConj h (IsConj.refl a) hz₁
  have hF1z₁ : Fusion1Facts a z₁ := hF1 a z₁ (IsConj.refl a) hz₁
  obtain ⟨a₀, ha₀Q, ha₀A⟩ := exists_mem_Qz_isConj hF1z₁
  have ha₀ord : orderOf a₀ = 2 := (orderOf_eq_of_isConj' ha₀A).trans h.orderOf_a
  have ha₀2 : a₀ ^ 2 = 1 := by
    have h := pow_orderOf_eq_one a₀
    rwa [ha₀ord] at h
  have ha₀mul : a₀ * a₀ = 1 := by rwa [pow_two] at ha₀2
  have ha₀inv : a₀⁻¹ = a₀ := inv_eq_of_mul_eq_one_right ha₀mul
  let a₁ : G := t * a₀ * t⁻¹
  have ha₀a₁ : IsConj a₀ a₁ := isConj_iff.mpr ⟨t, rfl⟩
  have ha₁A : IsConj a a₁ := ha₀A.trans ha₀a₁
  have ha₁ord : orderOf a₁ = 2 := (orderOf_eq_of_isConj' ha₁A).trans h.orderOf_a
  have ha₁2 : a₁ ^ 2 = 1 := by
    have h := pow_orderOf_eq_one a₁
    rwa [ha₁ord] at h
  have ha₁mul : a₁ * a₁ = 1 := by rwa [pow_two] at ha₁2
  have ha₁inv : a₁⁻¹ = a₁ := inv_eq_of_mul_eq_one_right ha₁mul
  have hAt : t * a₀ * t⁻¹ = a₁ := rfl
  have hBt : t * a₁ * t⁻¹ = a₀ := by
    dsimp [a₁]
    calc t * (t * a₀ * t⁻¹) * t⁻¹ = (t * t) * a₀ * (t⁻¹ * t⁻¹) := by group
      _ = a₀ := by rw [htmul, one_mul, ← mul_inv_rev, htmul, inv_one, mul_one]
  have hA' : t * a₀ = a₁ * t := by rw [← hAt]; group
  have hB' : t * a₁ = a₀ * t := by rw [← hBt]; group
  have ht_z₁ : t * z₁ * t⁻¹ = z₁ := by
    rw [htz₁, mul_assoc, mul_inv_cancel, mul_one]
  have ha₁Q : a₁ ∈ Qz z₁ := by
    have h := Qz_conj_mem (x := z₁) t ha₀Q
    rwa [ht_z₁] at h
  let q : G := a₀ * a₁
  have hqQ : q ∈ Qz z₁ := mul_mem ha₀Q ha₁Q
  have hq : ⁅q, t⁆ = ⁅a₀, a₁⁆ := by
    rw [commutatorElement_def, commutatorElement_def]
    change a₀ * a₁ * t * (a₀ * a₁)⁻¹ * t⁻¹ = a₀ * a₁ * a₀⁻¹ * a₁⁻¹
    rw [mul_inv_rev, ha₀inv, ha₁inv]
    calc a₀ * a₁ * t * (a₁ * a₀) * t⁻¹
        = a₀ * a₁ * (t * a₁) * a₀ * t⁻¹ := by group
      _ = a₀ * a₁ * (a₀ * t) * a₀ * t⁻¹ := by rw [hB']
      _ = a₀ * a₁ * a₀ * (t * a₀) * t⁻¹ := by group
      _ = a₀ * a₁ * a₀ * (a₁ * t) * t⁻¹ := by rw [hA']
      _ = a₀ * a₁ * a₀ * a₁ := by group
  have hmem : ⁅q, t⁆ ∈ Subgroup.zpowers z₁ := by
    rw [hq]
    exact commutatorElement_mem_zpowers_of_mem_Qz h₁ ha₀Q ha₁Q
  have hstar := gzClass_star hI hC h hF1 hF2 hF3 hOrb ht2 ht1 htA htB hz₁ htz₁ q hqQ hmem
  have hcomm_el : ⁅a₀, a₁⁆ = 1 := hq ▸ hstar
  have hcomm_mul : a₀ * a₁ = a₁ * a₀ := commutatorElement_eq_one_iff_mul_comm.mp hcomm_el
  let z₀ : G := a₀ * a₁
  have hz₀2 : z₀ ^ 2 = 1 := by
    rw [pow_two]
    change (a₀ * a₁) * (a₀ * a₁) = 1
    calc (a₀ * a₁) * (a₀ * a₁) = a₀ * (a₁ * a₀) * a₁ := by group
      _ = a₀ * (a₀ * a₁) * a₁ := by rw [← hcomm_mul]
      _ = (a₀ * a₀) * (a₁ * a₁) := by group
      _ = 1 := by rw [ha₀mul, ha₁mul, mul_one]
  have hz₀1 : z₀ ≠ 1 := by
    intro hz
    change a₀ * a₁ = 1 at hz
    have h1 : a₁ = a₀ := by rw [eq_inv_of_mul_eq_one_right hz, ha₀inv]
    have hty : t * a₀ = a₀ * t := by
      have hconj : t * a₀ * t⁻¹ = a₀ := by rw [hAt, h1]
      calc t * a₀ = (t * a₀ * t⁻¹) * t := by group
        _ = a₀ * t := by rw [hconj]
    rcases isConj_of_commute hF1 hF2 ha₀A hty ht2 ht1 with hc | hc
    · exact htA hc
    · exact htB hc
  have hz₀a₀ : z₀ * a₀ = a₀ * z₀ := by
    change a₀ * a₁ * a₀ = a₀ * (a₀ * a₁)
    calc a₀ * a₁ * a₀ = a₀ * (a₁ * a₀) := by group
      _ = a₀ * (a₀ * a₁) := by rw [← hcomm_mul]
  have hz₀t : t * z₀ = z₀ * t := by
    have hconj : t * z₀ * t⁻¹ = z₀ := by
      change t * (a₀ * a₁) * t⁻¹ = a₀ * a₁
      calc t * (a₀ * a₁) * t⁻¹ = (t * a₀ * t⁻¹) * (t * a₁ * t⁻¹) := by group
        _ = a₁ * a₀ := by rw [hAt, hBt]
        _ = a₀ * a₁ := hcomm_mul.symm
    calc t * z₀ = (t * z₀ * t⁻¹) * t := by group
      _ = z₀ * t := by rw [hconj]
  have hz₀B : IsConj z z₀ := by
    rcases isConj_of_commute hF1 hF2 ha₀A hz₀a₀ hz₀2 hz₀1 with hz₀A | hz₀B
    · rcases isConj_of_commute hF1 hF2 hz₀A hz₀t ht2 ht1 with hc | hc
      · exact absurd hc htA
      · exact absurd hc htB
    · exact hz₀B
  have ha₀Qz₀ : a₀ ∈ Qz z₀ := by
    have hmem_orb : z₀ ∈ orb2AB a₀ z₀ a₀ := by
      refine ⟨IsConj.refl z₀, ?_⟩
      have h : a₀ * z₀ = a₁ := by
        change a₀ * (a₀ * a₁) = a₁
        rw [← mul_assoc, ha₀mul, one_mul]
      rw [h]
      exact ha₀a₁
    exact ((hF3 a₀ z₀ ha₀A hz₀B).shape_2AB z₀ hmem_orb).2
  have ha₀t : ⁅a₀, t⁆ = z₀ := by
    rw [commutatorElement_def, ha₀inv]
    change a₀ * t * a₀ * t⁻¹ = a₀ * a₁
    calc a₀ * t * a₀ * t⁻¹ = a₀ * (t * a₀) * t⁻¹ := by group
      _ = a₀ * (a₁ * t) * t⁻¹ := by rw [hA']
      _ = a₀ * a₁ := by group
  have hmem₂ : ⁅a₀, t⁆ ∈ Subgroup.zpowers z₀ := by
    rw [ha₀t]
    exact Subgroup.mem_zpowers z₀
  exact hz₀1 (ha₀t ▸ gzClass_star hI hC h hF1 hF2 hF3 hOrb ht2 ht1 htA htB hz₀B hz₀t
    a₀ ha₀Qz₀ hmem₂)

end CFSG.EvenSporadicStandard.HNRecog.Section3
