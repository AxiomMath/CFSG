module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.TableIZ
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.TableIB
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.TableIZ1

public section

namespace CFSG.EvenSporadicStandard.HNRecog

open Subgroup

theorem centralizer_mul_of_mem_center {G : Type*} [Group G] {a : G} (ha : a ∈ center G) (z : G) :
    centralizer ({a * z} : Set G) = centralizer ({z} : Set G) := by
  ext x
  rw [mem_centralizer_iff, mem_centralizer_iff]
  have hax : a * x = x * a := (Subgroup.mem_center_iff.1 ha x).symm
  simp only [Set.mem_singleton_iff, forall_eq]
  constructor
  · intro h
    have h' : a * (z * x) = a * (x * z) := by
      calc a * (z * x) = a * z * x := by rw [mul_assoc]
        _ = x * (a * z) := h
        _ = x * a * z := by rw [mul_assoc]
        _ = a * x * z := by rw [hax]
        _ = a * (x * z) := by rw [mul_assoc]
    exact mul_left_cancel h'
  · intro h
    calc a * z * x = a * (z * x) := by rw [mul_assoc]
      _ = a * (x * z) := by rw [h]
      _ = a * x * z := by rw [mul_assoc]
      _ = x * a * z := by rw [hax]
      _ = x * (a * z) := by rw [mul_assoc]

section Cert


theorem pA_mem_center : pA ∈ center ↥P1408 := by
  rw [Subgroup.mem_center_iff]
  intro g
  exact Subtype.ext (elemA_comm g.2).symm

theorem cent_z_P (hP : Nat.card ↥P1408 = 177408000) :
    IsShapeTwoTwoSixS5 ↥(centralizer ({pZ} : Set ↥P1408)) :=
  IsShapeTwoTwoSixS5.of_mulEquiv (centralizerSubtypeEquiv P1408 pZ).symm
    (isShape_centralizer_z hP)

theorem cent_az_P (hP : Nat.card ↥P1408 = 177408000) :
    IsShapeTwoTwoSixS5 ↥(centralizer ({pA * pZ} : Set ↥P1408)) := by
  have e : centralizer ({pA * pZ} : Set ↥P1408) = centralizer ({pZ} : Set ↥P1408) :=
    centralizer_mul_of_mem_center pA_mem_center pZ
  exact IsShapeTwoTwoSixS5.of_mulEquiv (MulEquiv.subgroupCongr e).symm (cent_z_P hP)

theorem cent_b_P (hP : Nat.card ↥P1408 = 177408000) :
    IsShapeTwoTwoTimesA8 ↥(centralizer ({pB} : Set ↥P1408)) :=
  IsShapeTwoTwoTimesA8.of_mulEquiv (centralizerSubtypeEquiv P1408 pB).symm
    (isShape_centralizer_b hP)

theorem cent_z₁_P (hP : Nat.card ↥P1408 = 177408000) :
    IsShapeTwoTwoTimesTwoFourA5 ↥(centralizer ({pZ₁} : Set ↥P1408)) :=
  IsShapeTwoTwoTimesTwoFourA5.of_mulEquiv (centralizerSubtypeEquiv P1408 pZ₁).symm
    (isShape_centralizer_z₁ hP)

end Cert

end CFSG.EvenSporadicStandard.HNRecog
