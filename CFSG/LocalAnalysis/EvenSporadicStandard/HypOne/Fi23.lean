module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Fi23KSound
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Fi23Rows
public import CFSG.Sporadic.FischerOddCore.Fi23Aut
public import CFSG.Sporadic.FischerOddCore.Fi23Cent
public import Certificates.Certificate27301

public section

namespace CFSG.EvenSporadicStandard.HypOne.Fi23

open Subgroup CFSG.ComponentClassification.M12Cover CFSG.Sporadic.Fi23 CFSG.Sporadic.FischerOddCore
  CFSG.Blueprint.Fischer CFSG.Blueprint.NativeSporadic
  CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem fourClassesLarge_J
    (v : J) (hv : orderOf v = 2) :
    FourClassesLarge ↥(centralizer ({v} : Set J)) := by
  have hv2 : v ^ 2 = 1 := by rw [← hv]; exact pow_orderOf_eq_one v
  have hv1 : v ≠ 1 := fun h => by rw [h, orderOf_one] at hv; exact absurd hv (by norm_num)
  obtain ⟨e1, c, P, he1eq, he1, hc, hce1, hP, hdP, he1P, hcomm⟩ :=
    kCheckOf_sound Certificates.certificate27301
  rcases involution_cover v hv2 hv1 with h | h | h
  · exact fourClassesLarge_of_isConj h fourClassesLarge_d
  · exact fourClassesLarge_of_isConj
      ((isConj_d_mul_d1_of_mem (IsConj.refl d : d ∈ D23) he1).symm.trans h)
      (fourClassesLarge_pair he1eq he1 hP hdP he1P fun p hp => ⟨(hcomm p hp).1, (hcomm p hp).2.1⟩)
  · exact fourClassesLarge_of_isConj
      ((isConj_t2_of_mem (IsConj.refl d : d ∈ D23) he1 hc hce1).symm.trans h)
      (fourClassesLarge_triple he1eq he1 hc hce1 hP hdP he1P hcomm)

theorem conj_injective_of_center_bot {G : Type*} [Group G] (h : Subgroup.center G = ⊥) :
    Function.Injective (MulAut.conj : G →* MulAut G) := by
  intro g g' e
  have hc : g'⁻¹ * g ∈ Subgroup.center G := Subgroup.mem_center_iff.2 fun x => by
    have h1 := congrArg (fun α : MulAut G => α x) e
    simp only [MulAut.conj_apply] at h1
    calc x * (g'⁻¹ * g) = g'⁻¹ * (g' * x * g'⁻¹) * g := by group
      _ = g'⁻¹ * (g * x * g⁻¹) * g := by rw [h1]
      _ = g'⁻¹ * g * x := by group
  rw [h, Subgroup.mem_bot, inv_mul_eq_one] at hc
  exact hc.symm

theorem hypothesisOne_J :
    HypothesisOne J := by
  refine hypothesisOne_of_inner (conj_injective_of_center_bot center_J) (fun α => ?_)
    fun y hy => ?_
  · exact @forall_eq_conj_of_mulEquiv Blueprint.NativeSporadic.Fi23 J Units.instGroup J.toGroup
      fi23EquivJ fi23_mulAut_eq_conj α
  · exact SmallNormalFree.of_fourClassesLarge (oddCore_centralizer_J y hy) (fourClassesLarge_J y hy)

theorem hypothesisOne_fi23 :
    HypothesisOne (Carrier .Fi23) :=
  @CFSG.EvenSmallLie.hypothesisOne_of_mulEquiv J Blueprint.NativeSporadic.Fi23 J.toGroup
    Units.instGroup fi23EquivJ.symm hypothesisOne_J

end CFSG.EvenSporadicStandard.HypOne.Fi23
