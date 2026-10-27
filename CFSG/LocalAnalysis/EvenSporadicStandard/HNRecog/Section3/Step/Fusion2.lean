module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion1.Derived
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion2.Reps
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion2.TwoFourMap
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion2.QuFinal

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

private theorem orderOf_eq_of_isConj' {G : Type} [Group G] {x y : G} (h : IsConj x y) :
    orderOf x = orderOf y := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  rw [← hc]
  simpa [MulAut.conj_apply] using (MulEquiv.orderOf_eq (MulAut.conj c) x).symm

private theorem mem_derived_iff_of_fusion1 (hI : TwoHSInterface) {G : Type} [Group G] {a z : G}
    (h : IsF5Type a z) (hF1 : Fusion1Facts a z) (t : G) (htG : t ∈ Gx a) (ht2 : t ^ 2 = 1) :
    t ∈ derivedOf (Gx a) ↔ (IsConj a t ↔ ¬ IsConj a (a * t)) := by
  have ha2 : a ^ 2 = 1 := by rw [← h.orderOf_a]; exact pow_orderOf_eq_one a
  have haa : a * a = 1 := by simpa [pow_two] using ha2
  have ha1 : a ≠ 1 := by
    intro h1
    have ho := h.orderOf_a
    rw [h1, orderOf_one] at ho
    norm_num at ho
  have hnot1 : ¬ IsConj a (1 : G) := fun hc => ha1 (isConj_one_left.mp hc)
  by_cases ht1 : t = 1
  · rw [ht1, mul_one]
    exact ⟨fun _ => ⟨fun hc => absurd hc hnot1, fun hc => absurd (IsConj.refl a) hc⟩,
      fun _ => Subgroup.one_mem _⟩
  · have ho : orderOf t = 2 := orderOf_eq_prime ht2 ht1
    constructor
    · intro hmem
      rcases inv_mem_derivedOf_cases hI h hF1 hmem ho with hta | ⟨hzt, hat, -⟩ | ⟨hat, hzat⟩
      · rw [hta, haa]
        exact ⟨fun _ => hnot1, fun _ => IsConj.refl a⟩
      · exact ⟨fun hc => absurd (hc.trans hzt.symm) (not_isConj_of_isF5Type hI h),
          fun hn => absurd hat hn⟩
      · exact ⟨fun _ hc => not_isConj_of_isF5Type hI h (hc.trans hzat.symm), fun _ => hat⟩
    · intro hiff
      by_contra hnot
      obtain ⟨z', b', u', hF⟩ := exists_labelled_facts hI h
      let t' : ↥(Gx a) := ⟨t, htG⟩
      have ht'2 : t' ^ 2 = 1 := Subtype.ext (by simpa using ht2)
      have ht'D : t' ∉ commutator ↥(Gx a) := fun hc => hnot (mem_derivedOf_iff.mpr ⟨htG, hc⟩)
      have hconj : IsConj t' (GxSelf a * t') := TwoHSFacts.isConj_mul_of_not_mem_commutator hF ht'2 ht'D
      obtain ⟨k, hk⟩ := isConj_iff.mp hconj
      have hk' : (k : G) * t * (k : G)⁻¹ = a * t := congrArg Subtype.val hk
      have hconjG : IsConj t (a * t) := isConj_iff.mpr ⟨k, hk'⟩
      by_cases hc : IsConj a t
      · exact (hiff.mp hc) (hc.trans hconjG)
      · exact hc (hiff.mpr (fun h2 => hc (h2.trans hconjG.symm)))

theorem fusion2_of_a8Shapes (hI : TwoHSInterface) (hS : SuborbitFacts) {G : Type} [Group G]
    [Finite G] {a z : G} (h : IsF5Type a z) (hF1 : Vert Fusion1Facts a z)
    (hA8 : Vert A8Shapes a z) : Fusion2Facts a z := by
  have hF1a : Fusion1Facts a z := hF1.self
  have hA8a : A8Shapes a z := hA8.self
  have ha2 : a ^ 2 = 1 := by rw [← h.orderOf_a]; exact pow_orderOf_eq_one a
  have ha1 : a ≠ 1 := by
    intro h1
    have ho := h.orderOf_a
    rw [h1, orderOf_one] at ho
    norm_num at ho
  have hz2 : orderOf z = 2 := h.orderOf_z
  refine ⟨?_, fun t htG ht2 => mem_derived_iff_of_fusion1 hI h hF1a t htG ht2⟩
  intro z₀ b u hF _hz₀
  obtain ⟨hbcls, huB, hauB, hush⟩ := reps_bu_classes hI h hF1a hA8a hF
  refine ⟨hbcls, huB, hauB, ?_⟩
  obtain ⟨E, hE⟩ := h.cent_a
  have hT : TwoFourData (Gx u) := hS.two_four ↥(Gx a) E hE (GxSelf a) z₀ b u hF
  have hT' : TwoFourData (Gxy a (u : G)) := twoFourData_Gxy hT
  have hC : IsExtraspecialPlusByA5WrTwo ↥(Gx (u : G)) :=
    (isF5Type_of_isConj h (IsConj.refl a) huB).cent_z
  have hC' : IsExtraspecialPlusByA5WrTwo ↥(Gx (a * (u : G))) :=
    (isF5Type_of_isConj h (IsConj.refl a) hauB).cent_z
  have huord : orderOf (u : G) = 2 := by rw [← orderOf_eq_of_isConj' huB, hz2]
  have hu2 : (u : G) ^ 2 = 1 := by rw [← huord]; exact pow_orderOf_eq_one _
  have hu1 : (u : G) ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at huord
    norm_num at huord
  have hau : a ≠ (u : G) := by
    intro hau
    apply not_isConj_of_isF5Type hI h
    rw [hau]
    exact huB.symm
  have hcomm : a * (u : G) = (u : G) * a := mem_Gx.mp u.2
  obtain ⟨hnQ, hel5, hcore, hel4⟩ := qu_facts ha2 hu2 ha1 hu1 hau hcomm hC hC' hush hT'
  exact ⟨hnQ, hel5, hcore, hel4, hush⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
