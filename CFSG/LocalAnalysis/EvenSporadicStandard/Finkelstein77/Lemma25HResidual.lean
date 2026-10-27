module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Finkelstein77.Lemma25HMain
public import CFSG.LocalAnalysis.EvenSporadicStandard.Finkelstein77.Lemma25HWeak
public import CFSG.LocalAnalysis.ComponentClassification.Foote5HallInd

public section

namespace CFSG.EvenSporadicStandard.Finkelstein77.Lemma25HProof

open Subgroup CFSG CFSG.ABGLocalTools CFSG.ComponentClassification
  CFSG.ComponentClassification.FooteLit.F5 CFSG.EvenSporadicStandard.Finkelstein77.Lemma25Proof

theorem corB4Big_of_hallQ8Residual
    (hres : Foote5.HallGen.HallQ8Residual) : CorB4Big := by
  intro G _ _ D hD h8 hcl P hP
  obtain ⟨n, hn, ⟨e⟩⟩ := id hD
  have hcard : Nat.card D = 2 * 2 ^ (n - 1) := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  rcases (show n = 3 ∨ 4 ≤ n by
      have : 2 ^ (n - 1) ≥ 4 := by omega
      by_contra hcon
      have hn2 : n - 1 ≤ 1 := by omega
      have : 2 ^ (n - 1) ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hn2
      omega) with rfl | h4
  · exact isDihedral_or_isSemidihedral_of_strong hD h8
      (Foote5.HallD8.hall_d8 (e : D ≃* DihedralGroup 4) hcl) hP
  · have h16 : 16 ≤ Nat.card D := by
      rw [hcard]
      have : 2 ^ 3 ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    exact isDihedral_or_isSemidihedral_of_weak hD h16
      (Foote5.HallGen.hallWeak_of_residual hres G D hD h16 hcl) hP

theorem asc76Lemma25_of_hallQ8Residual
    (hres : Foote5.HallGen.HallQ8Residual) : Asc76Lemma25 :=
  asc76Lemma25_of_big (corB4Big_of_hallQ8Residual hres)

end CFSG.EvenSporadicStandard.Finkelstein77.Lemma25HProof
