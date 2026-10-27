module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Y4a.Types
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Y4a.Cube
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Y4a.A8Split
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Y4a.A8Cent

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem y4a_card_cent (hI : TwoHSInterface) {G : Type} [Group G] {a z : G} (h : IsF5Type a z)
    (hF2 : Vert Fusion2Facts a z) (hF3 : Vert Fusion3Facts a z) (hPic : Vert A8Pictures a z)
    (hCls : GzClassFacts a z) {a₁ t : G} (ha₁ : a₁ ∈ Gx z) (ha₁A : IsConj a a₁)
    (ha₁z : IsConj z (a₁ * z)) (htY : t ∈ derivedOf (Gxy a₁ z)) (htQ : t ∈ Qz z)
    (ht2 : t ^ 2 = 1) (htA : IsConj a t) : Nat.card ↥(Gxy a₁ z ⊓ Gx t) = 384 := by
  have hnot : ¬ IsConj a z := not_isConj_of_isF5Type hI h
  have ht1 : t ≠ 1 := by
    rintro rfl
    have ha1 : a = 1 := isConj_one_left.mp htA
    have h2 := h.orderOf_a
    rw [ha1, orderOf_one] at h2
    exact absurd h2 (by decide)
  obtain ⟨-, hxt, hzt, hxzt⟩ :=
    (y4a_types hI h hF2 hCls ha₁ ha₁A ha₁z htY htQ ht2 ht1).resolve_right
      (fun h' => hnot (htA.trans h'.1.symm))
  have htG : t ∈ Gxy a₁ z := derivedOf_le _ htY
  have hta₁ : a₁ * t = t * a₁ := mem_Gx.mp (mem_Gxy.mp htG).1
  have htz : z * t = t * z := mem_Gx.mp (mem_Gxy.mp htG).2
  have hcomm : a₁ * z = z * a₁ := (mem_Gx.mp ha₁).symm
  have htt : t * t = 1 := by rw [← pow_two]; exact ht2
  have hxy : a₁ * (z * t) = z * t * a₁ := by
    rw [← mul_assoc, hcomm, mul_assoc, hta₁, ← mul_assoc]
  have hyt : z * t * t = t * (z * t) := by rw [← mul_assoc, ← htz]
  have hxyA : IsConj a (a₁ * (z * t)) := by rw [← mul_assoc]; exact hxzt
  have hytB : IsConj z (z * t * t) := by rw [mul_assoc, htt, mul_one]
  have hxytB : IsConj z (a₁ * (z * t) * t) := by
    rw [mul_assoc, mul_assoc, htt, mul_one]
    exact ha₁z
  obtain ⟨hshape, htD, hφ⟩ :=
    y4a_mem_derived_of_cube hI h hF3 hPic hxy hta₁ hyt ha₁A hzt hxyA htA hxt hytB hxytB
  have hEq : Gxy a₁ z ⊓ Gx t = Gxy a₁ (z * t) ⊓ Gx t := by
    ext g
    simp only [Subgroup.mem_inf, mem_Gxy, mem_Gx]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨⟨h1, ?_⟩, h3⟩
      rw [mul_assoc, h3, ← mul_assoc, h2, mul_assoc]
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨⟨h1, ?_⟩, h3⟩
      calc z * g = z * t * g * t := by
            rw [mul_assoc z t g, h3, ← mul_assoc, mul_assoc (z * g) t t, htt, mul_one]
        _ = g * (z * t) * t := by rw [h2]
        _ = g * z := by rw [mul_assoc, mul_assoc, htt, mul_one]
  obtain ⟨φ⟩ := nonempty_mulEquiv_derivedOf_of_isShapeTwoTwoTimesA8 hshape
  have h96 := y4a_card_Gx_two_two (hφ φ)
  have hφs : ((φ (φ.symm ⟨t, htD⟩) : ↥(derivedOf (Gxy a₁ (z * t)))) : G) = t := by
    rw [MulEquiv.apply_symm_apply]
  have hcard := y4a_card_inf_Gx_of_mulEquiv φ (φ.symm ⟨t, htD⟩)
  rw [hφs] at hcard
  rw [hEq, y4a_card_inf_Gx_eq hshape htD, hcard, h96]

end CFSG.EvenSporadicStandard.HNRecog.Section3
