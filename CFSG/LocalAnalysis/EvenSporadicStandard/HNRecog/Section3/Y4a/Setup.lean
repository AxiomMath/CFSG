module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Vert
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Y4a.Good
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Y4a.ShapeHom
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Y4a.Derived

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem y4a_setup (hI : TwoHSInterface) {G : Type} [Group G] [Finite G] {a z : G}
    (h : IsF5Type a z) (hF1 : Fusion1Facts a z) (hF2 : Fusion2Facts a z)
    (hF3 : Vert Fusion3Facts a z) {a₁ : G} (ha₁ : a₁ ∈ Gx z) (ha₁A : IsConj a a₁)
    (ha₁z : IsConj z (a₁ * z)) :
    IsShapeTwoTwoTimesTwoFourA5 ↥(Gxy a₁ z) ∧ IsElemTwo 5 (Qz z ⊓ Gx a₁) ∧
      CFSG.Open.pCoreOf 2 (derivedOf (Gxy a₁ z)) = Qz z ⊓ Qz (a₁ * z) ∧
      IsElemTwo 4 (CFSG.Open.pCoreOf 2 (derivedOf (Gxy a₁ z))) ∧
      Nat.card ↥(derivedOf (Gxy a₁ z)) = 960 ∧
      (∀ x ∈ Gxy a₁ z, ∃ l ∈ derivedOf (Gxy a₁ z),
        ∀ m ∈ CFSG.Open.pCoreOf 2 (derivedOf (Gxy a₁ z)), x * m * x⁻¹ = l * m * l⁻¹) ∧
      ∃ ψ : ↥(derivedOf (Gxy a₁ z)) →* alternatingGroup (Fin 5), Function.Surjective ψ ∧
        ∀ l : ↥(derivedOf (Gxy a₁ z)),
          ψ l = 1 ↔ (l : G) ∈ CFSG.Open.pCoreOf 2 (derivedOf (Gxy a₁ z)) := by
  have hcomm : a₁ * z = z * a₁ := (mem_Gx.mp ha₁).symm
  obtain ⟨h5, hMeq, h4⟩ := y4a_good_data hI h hF1 hF2 ha₁A (IsConj.refl z) hcomm ha₁z
  have hshape : IsShapeTwoTwoTimesTwoFourA5 ↥(Gxy a₁ z) :=
    ((hF3 a₁ z ha₁A (IsConj.refl z)).shape_2BB z ⟨IsConj.refl z, ha₁z⟩).1
  have hM4 : IsElemTwo 4 (CFSG.Open.pCoreOf 2 (derivedOf (Gxy a₁ z))) := hMeq ▸ h4
  have h16 : Nat.card ↥(CFSG.Open.pCoreOf 2 (derivedOf (Gxy a₁ z))) = 16 := by
    rw [hM4.2]
    norm_num
  obtain ⟨π, hπ, hK, hKab⟩ := y4a_exists_hom hshape
  obtain ⟨h960, hconj, ψ, hψ, hker⟩ := y4a_derived_of_hom π hπ hK hKab h16
  exact ⟨hshape, h5, hMeq, hM4, h960, hconj, ψ, hψ, hker⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
