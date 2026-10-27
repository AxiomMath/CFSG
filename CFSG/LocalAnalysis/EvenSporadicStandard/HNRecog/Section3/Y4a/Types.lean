module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.LocalGz
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Vert
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion1.Qz
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion1.NotConj
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.DerivedOf
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.HSide.XFusion
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem y4a_not_mem_Qz (hI : TwoHSInterface) {G : Type} [Group G] {a z : G} (h : IsF5Type a z)
    {a₁ : G} (ha₁A : IsConj a a₁) (ha₁z : IsConj z (a₁ * z)) : a₁ ∉ Qz z := by
  intro hQ
  have hnot : ¬ IsConj a z := not_isConj_of_isF5Type hI h
  have hord : orderOf a₁ = 2 := by
    obtain ⟨d, hd⟩ := isConj_iff.mp ha₁A
    have h' := MulEquiv.orderOf_eq (MulAut.conj d) a
    rw [MulAut.conj_apply, hd] at h'
    rw [h', h.orderOf_a]
  have hne : a₁ ≠ z := by
    rintro rfl
    exact hnot ha₁A
  exact hnot (ha₁A.trans ((isConj_mul_of_mem_Qz h.cent_z h.orderOf_z hord hne hQ).trans
    ha₁z.symm))

private theorem y4aTypes_orderOf {G : Type} [Group G] {c x : G} (hc : orderOf c = 2)
    (hx : IsConj c x) : orderOf x = 2 := by
  obtain ⟨d, hd⟩ := isConj_iff.mp hx
  have h' := MulEquiv.orderOf_eq (MulAut.conj d) c
  rw [MulAut.conj_apply, hd] at h'
  rw [h', hc]

private theorem y4aTypes_orderOf_mul {G : Type} [Group G] {x y : G} (hx : x ^ 2 = 1)
    (hy : y ^ 2 = 1) (hxy : x * y = y * x) (hne : x ≠ y) : orderOf (x * y) = 2 := by
  apply orderOf_eq_prime
  · rw [((commute_iff_eq x y).mpr hxy).mul_pow, hx, hy, one_mul]
  · intro h1
    apply hne
    have hxx : x * x = 1 := by rw [← pow_two]; exact hx
    calc x = x * (x * y) := by rw [h1, mul_one]
      _ = y := by rw [← mul_assoc, hxx, one_mul]

theorem y4a_types (hI : TwoHSInterface) {G : Type} [Group G] {a z : G} (h : IsF5Type a z)
    (hF2 : Vert Fusion2Facts a z) (hCls : GzClassFacts a z) {a₁ t : G} (ha₁ : a₁ ∈ Gx z)
    (ha₁A : IsConj a a₁) (ha₁z : IsConj z (a₁ * z)) (htY : t ∈ derivedOf (Gxy a₁ z))
    (htQ : t ∈ Qz z) (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) :
    (IsConj a t ∧ IsConj z (a₁ * t) ∧ IsConj a (z * t) ∧ IsConj a (a₁ * z * t)) ∨
      (IsConj z t ∧ IsConj a (a₁ * t) ∧ IsConj z (z * t) ∧ IsConj z (a₁ * z * t)) := by
  have hnot : ¬ IsConj a z := not_isConj_of_isF5Type hI h
  have hF2' : Fusion2Facts a₁ z := hF2 a₁ z ha₁A (IsConj.refl z)
  have hcomm : a₁ * z = z * a₁ := (mem_Gx.mp ha₁).symm
  have htG : t ∈ Gxy a₁ z := derivedOf_le _ htY
  have hta₁ : a₁ * t = t * a₁ := mem_Gx.mp (mem_Gxy.mp htG).1
  have htz : z * t = t * z := mem_Gx.mp (mem_Gxy.mp htG).2
  have hz2 : z ^ 2 = 1 := by rw [← h.orderOf_z]; exact pow_orderOf_eq_one z
  have ha₁ord : orderOf a₁ = 2 := y4aTypes_orderOf h.orderOf_a ha₁A
  have ha₁2 : a₁ ^ 2 = 1 := by rw [← ha₁ord]; exact pow_orderOf_eq_one a₁
  have htord : orderOf t = 2 := orderOf_eq_prime ht2 ht1
  have htD : t ∈ derivedOf (Gx a₁) :=
    derivedOf_mono (by rw [Gxy_eq_inf]; exact inf_le_left) htY
  have hzD : z ∉ derivedOf (Gx a₁) := by
    intro hz
    have hiff := (hF2'.mem_derived_iff z (mem_Gx.mpr hcomm) hz2).mp hz
    have h1 : ¬ IsConj a₁ z := fun hc => hnot (ha₁A.trans hc)
    have h2 : ¬ IsConj a₁ (a₁ * z) := fun hc => hnot (ha₁A.trans (hc.trans ha₁z.symm))
    exact h1 (hiff.mpr h2)
  have htz1 : t ≠ z := fun he => hzD (he ▸ htD)
  have hzt : IsConj t (z * t) := by
    rw [htz]
    exact isConj_mul_of_mem_Qz h.cent_z h.orderOf_z htord htz1 htQ
  have hztD : z * t ∉ derivedOf (Gx a₁) := by
    intro hD
    apply hzD
    have hmem := (derivedOf (Gx a₁)).mul_mem hD ((derivedOf (Gx a₁)).inv_mem htD)
    rwa [mul_inv_cancel_right] at hmem
  have hztG : z * t ∈ Gx a₁ := mem_Gx.mpr (by rw [← mul_assoc, hcomm, mul_assoc, hta₁,
    ← mul_assoc])
  have hzt2 : (z * t) ^ 2 = 1 := by
    rw [((commute_iff_eq z t).mpr htz).mul_pow, hz2, ht2, one_mul]
  have ha₁Q : a₁ ∉ Qz z := y4a_not_mem_Qz hI h ha₁A ha₁z
  have hzQ : z ∈ Qz z := self_mem_Qz hz2
  have ha₁t : a₁ ≠ t := fun he => ha₁Q (he ▸ htQ)
  have ha₁zt : a₁ ≠ z * t := fun he => ha₁Q (he ▸ (Qz z).mul_mem hzQ htQ)
  have hord1 : orderOf (a₁ * t) = 2 := y4aTypes_orderOf_mul ha₁2 ht2 hta₁ ha₁t
  have hord2 : orderOf (a₁ * (z * t)) = 2 :=
    y4aTypes_orderOf_mul ha₁2 hzt2 (mem_Gx.mp hztG) ha₁zt
  have hassoc : a₁ * z * t = a₁ * (z * t) := mul_assoc a₁ z t
  rw [hassoc]
  have hiff1 := (hF2'.mem_derived_iff t (mem_Gxy.mp htG).1 ht2).mp htD
  have hiff2 : ¬ (IsConj a₁ (z * t) ↔ ¬ IsConj a₁ (a₁ * (z * t))) := fun hc =>
    hztD ((hF2'.mem_derived_iff (z * t) hztG hzt2).mpr hc)
  rcases hCls.inv_two t htord with htA | htB
  ·
    have h1 : IsConj a₁ t := ha₁A.symm.trans htA
    have h2 : ¬ IsConj a (a₁ * t) := fun hc => hiff1.mp h1 (ha₁A.symm.trans hc)
    have h3 : IsConj a₁ (z * t) := h1.trans hzt
    have h4 : IsConj a₁ (a₁ * (z * t)) := by
      by_contra hc
      exact hiff2 ⟨fun _ => hc, fun _ => h3⟩
    refine Or.inl ⟨htA, ?_, htA.trans hzt, ha₁A.trans h4⟩
    exact (hCls.inv_two _ hord1).resolve_left h2
  ·
    have h1 : ¬ IsConj a₁ t := fun hc => hnot ((ha₁A.trans hc).trans htB.symm)
    have h2 : IsConj a₁ (a₁ * t) := by
      by_contra hc
      exact h1 (hiff1.mpr hc)
    have h3 : ¬ IsConj a₁ (z * t) := fun hc => h1 (hc.trans hzt.symm)
    have h4 : ¬ IsConj a₁ (a₁ * (z * t)) := fun hc =>
      hiff2 ⟨fun h' => absurd h' h3, fun h' => absurd hc h'⟩
    refine Or.inr ⟨htB, ha₁A.trans h2, htB.trans hzt, ?_⟩
    exact (hCls.inv_two _ hord2).resolve_left fun hc => h4 (ha₁A.symm.trans hc)

end CFSG.EvenSporadicStandard.HNRecog.Section3
