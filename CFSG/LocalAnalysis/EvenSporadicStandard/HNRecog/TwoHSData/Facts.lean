module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Interface
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.F5Facts
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.InvClasses
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.TableIP
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.TableKP
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.SqClass
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ElevenP
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ShapeIITrue
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ShapeVTrue
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.M11P
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ShapeK
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.TableKSpec

public section

namespace CFSG.EvenSporadicStandard.HNRecog

open Subgroup

section Cert


theorem orderOf_pA : orderOf pA = 2 :=
  (Subgroup.orderOf_coe pA).symm.trans twoHSBasic_spec.1

theorem orderOf_pZ : orderOf pZ = 2 :=
  (Subgroup.orderOf_coe pZ).symm.trans twoHSBasic_spec.2.1

theorem orderOf_pB : orderOf pB = 2 :=
  (Subgroup.orderOf_coe pB).symm.trans twoHSBasic_spec.2.2.1

theorem orderOf_pZ₁ : orderOf pZ₁ = 2 :=
  (Subgroup.orderOf_coe pZ₁).symm.trans twoHSBasic_spec.2.2.2.1

theorem twoHSFacts_P1408 (hP : Nat.card ↥P1408 = 177408000) {E : Subgroup ↥P1408}
    (hF : TwoHS.IsF5Centralizer ↥P1408 E)
    (hE : ∀ x : ↥P1408, x ∈ E ↔ (x : Equiv.Perm (Fin 1408)) ∈ blocks1408) :
    TwoHSFacts ↥P1408 pA pZ pB pZ₁ := by
  have hcomm : commutator ↥P1408 = E := TwoHSData.commutator_eq_of_isF5Centralizer hF
  obtain ⟨-, -, -, -, -, hA, hZ, hAZ, hBn, hZ₁n⟩ := twoHSBasic_spec
  exact
    { center_eq := TwoHSData.center_eq_zpowers_of_isF5Centralizer hF pA_mem_center orderOf_pA
      orderOf_a := orderOf_pA
      orderOf_z := orderOf_pZ
      orderOf_b := orderOf_pB
      orderOf_z₁ := orderOf_pZ₁
      not_isConj := not_isConj_inv hP
      involution_cover := involution_cover_inv hP
      cent_z := cent_z_P hP
      cent_az := cent_az_P hP
      cent_b := cent_b_P hP
      cent_z₁ := cent_z₁_P hP
      mem_commutator := by
        rw [hcomm]
        exact ⟨(hE pA).2 hA, (hE pZ).2 hZ, (hE (pA * pZ)).2 hAZ⟩
      not_mem_commutator := by
        rw [hcomm]
        exact ⟨fun h => hBn ((hE pB).1 h), fun h => hZ₁n ((hE pZ₁).1 h)⟩
      K_shape := by
        rw [hcomm]
        exact K_shape_P hP hE
      center_K := by
        rw [hcomm]
        exact center_K_P hP hE
      exists_sq_eq := exists_sq_eq_P hP
      isConj_of_sq_eq := fun g g' hg hg' => isConj_of_sq_eq_P hP hg hg'
      not_isSectionOf_A8 := fun g hg => not_isSectionOf_A8_P hP hg
      card_eq := by rw [hP]; norm_num
      table_three := fun x hx => table_three_P hP x hx
      table_five := fun x hx => table_five_P hP x hx
      table_seven := fun x hx => table_seven_P hP x hx
      table_eleven := fun x hx => table_eleven_P hP x hx
      sl25_le_centralizer := fun ρ hρ hC => sl25_le_centralizer_P hP ρ hρ hC
      sylow_two_five := fun ρ hρ hB T => sylow_two_five_P hP ρ hρ hB T
      m11_unique_class := m11_unique_class_P hP hF.normal hF.index_eq_two hE
      m11_centralizer_five := fun M hM ρ hρM hρ =>
        m11_centralizer_five_P hP hF.normal hF.index_eq_two hE M hM ρ hρM hρ
      centralizer_five_of_A8 := fun c hc hA8 ρ hρ hρc =>
        centralizer_five_of_A8_P hP c hc hA8 ρ hρ hρc }

end Cert

end CFSG.EvenSporadicStandard.HNRecog
