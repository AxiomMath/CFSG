module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Vert
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.QzConj
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.A8.Decomp
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Y4a.Good

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem y4a_exists_mem_2A (hI : TwoHSInterface) {G : Type} [Group G] {a z : G}
    (h : IsF5Type a z) (hF1 : Vert Fusion1Facts a z) (hF2 : Vert Fusion2Facts a z)
    (hF3 : Vert Fusion3Facts a z) (hPic : Vert A8Pictures a z) {x w : G} (hx : IsConj a x)
    (hw : IsConj z w) (hxw : x * w = w * x) (hxwB : IsConj z (x * w)) :
    ∃ t : G, t ∈ Qz w ⊓ Qz (x * w) ∧ IsConj a t := by
  obtain ⟨z₀, b, u, hF, hz₀, -, -, -, -, -⟩ := hF1.self.rep_z
  obtain ⟨⟨hbA, habA, -, hshape⟩, -⟩ := hF2.self.reps_bu z₀ b u hF hz₀
  obtain ⟨φ⟩ := nonempty_mulEquiv_derivedOf_of_isShapeTwoTwoTimesA8 hshape
  obtain ⟨s₀, -, -, hs₀, -⟩ := exists_triple_cycleType_two_two
  obtain ⟨htA, -, hbtB, habtB⟩ := hPic.self.fig8a (b : G) ⟨hbA, habA⟩ φ s₀ hs₀
  have htG : ((φ s₀ : ↥(derivedOf (Gxy a b))) : G) ∈ Gxy a b := derivedOf_le _ (φ s₀).2
  generalize ((φ s₀ : ↥(derivedOf (Gxy a b))) : G) = t at htA hbtB habtB htG
  have hta : a * t = t * a := mem_Gx.mp (mem_Gxy.mp htG).1
  have htb : (b : G) * t = t * b := mem_Gx.mp (mem_Gxy.mp htG).2
  have hab : a * b = b * a := mem_Gx.mp b.2
  have ht2 : t * t = 1 := by
    obtain ⟨d, hd⟩ := isConj_iff.mp htA
    have hord := MulEquiv.orderOf_eq (MulAut.conj d) a
    rw [MulAut.conj_apply, hd, h.orderOf_a] at hord
    rw [← pow_two, ← hord, pow_orderOf_eq_one]
  have hgood : a * (b * t) = b * t * a := by
    rw [← mul_assoc, hab, mul_assoc, hta, ← mul_assoc]
  have hgoodB : IsConj z (a * (b * t)) := by
    rw [← mul_assoc]
    exact habtB
  have hF3t : Fusion3Facts t z := hF3 t z htA (IsConj.refl z)
  have h1 : t * (b * t) = b := by rw [← mul_assoc, ← htb, mul_assoc, ht2, mul_one]
  have htab : a * b * t = t * (a * b) := by
    rw [mul_assoc, htb, ← mul_assoc, hta, mul_assoc]
  have h2 : t * (a * b * t) = a * b := by rw [htab, ← mul_assoc, ht2, one_mul]
  have hQ1 : t ∈ Qz ((b : G) * t) :=
    (hF3t.shape_2AB ((b : G) * t) ⟨hbtB, by rw [h1]; exact htA.symm.trans hbA⟩).2
  have hQ2 : t ∈ Qz (a * b * t) :=
    (hF3t.shape_2AB (a * b * t) ⟨habtB, by rw [h2]; exact htA.symm.trans habA⟩).2
  obtain ⟨g, hga, hgw⟩ := y4a_conj_of_good hI h hF1.self hF2.self (IsConj.refl a) hbtB hgood
    hgoodB hx hw hxw hxwB
  refine ⟨g * t * g⁻¹, Subgroup.mem_inf.mpr ⟨?_, ?_⟩, htA.trans (isConj_iff.mpr ⟨g, rfl⟩)⟩
  · have hc := Qz_conj_mem g hQ1
    rwa [hgw] at hc
  · have hc := Qz_conj_mem g hQ2
    have hprod : g * (a * b * t) * g⁻¹ = x * w := by
      rw [← hga, ← hgw]
      group
    rwa [hprod] at hc

end CFSG.EvenSporadicStandard.HNRecog.Section3
