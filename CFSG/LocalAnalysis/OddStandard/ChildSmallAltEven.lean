module

public import CFSG.LocalAnalysis.OddStandard.Children
public import CFSG.LocalAnalysis.ComponentClassification.GSLitInputs
import CFSG.LocalAnalysis.SteinbergCEAltEvenCenterQuaternionCover
import CFSG.LocalAnalysis.ComponentClassification.QuaternionComponentWitness
import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionQuaternion
import CFSG.CharacterTheory.Semidihedral.ProperSubgroupRegularity
import CFSG.ClassicalInvolution.OrderForm

public section

namespace CFSG.OddStandard

open Subgroup CFSG.Open CFSG.Blueprint

theorem childSmallAltEven_of_classicalInvolution
    (hCI : ComponentClassification.GSLit.ClassicalInvolutionInput) : ChildSmallAltEven := by
  intro G _ _ L hS hn hev
  obtain ⟨n, hn5, hn7, ⟨θ⟩⟩ := hn
  obtain ⟨hsimple, hnonab, -, hstd⟩ := hS
  have hq : CFSG.IsQuasisimple L :=
    (ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mp hstd.1
  obtain ⟨-, z, hz2, -, hzZ, -, -, -, -, -, -, -, hsyl⟩ :=
    LocalAnalysis.small_alternating_even_center_exact_quaternion_cover hn5 hn7 hq hev θ
  have hz : orderOf (z : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hz2
  have hzC : (z : G) ∈ centralizer (L : Set G) := by
    rw [mem_centralizer_iff]
    intro l hl
    exact congrArg Subtype.val (mem_center_iff.mp hzZ ⟨l, hl⟩)
  obtain ⟨-, hLT, -, hcomp, -⟩ :=
    LocalAnalysis.ComponentInitial.standard_involution_centralizer_normality hstd hzC hz
  obtain ⟨S⟩ : Nonempty (Sylow 2 L) := inferInstance
  have hSq : ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup L) ≃* QuaternionGroup (2 ^ (r - 2))) := by
    rcases eq_or_lt_of_le hn5 with h5 | h6
    · exact ⟨3, le_rfl, (hsyl S).1 h5.symm⟩
    · exact ⟨4, by norm_num, (hsyl S).2 h6⟩
  obtain ⟨hw, hsub⟩ :=
    ComponentClassification.QuaternionComponent.classicalInvolutionWitness_of_component hz hcomp
      z.2 S hSq
  let eF : genFittingFStar G ≃* G :=
    (MulEquiv.subgroupCongr
      (ComponentClassification.StandardRecognition.genFittingFStar_eq_top_of_isSimpleGroup
        hnonab)).trans Subgroup.topEquiv
  have : IsSimpleGroup (genFittingFStar G) := eF.isSimpleGroup
  have hFnonab : ∃ a b : genFittingFStar G, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnonab
    refine ⟨eF.symm a, eF.symm b, fun h => hab (eF.symm.injective ?_)⟩
    rw [map_mul, map_mul]
    exact h
  rcases (hCI G hFnonab (z : G) hz L z.2 hsub S hSq).1 hw with h | h
  · exact (ClassicalInvolution.oddLieType_congr eF).1 h
  ·
    exfalso
    obtain ⟨e⟩ := (ClassicalInvolution.isSporadic_congr eF).1 h
    let e' : G ≃* NativeSporadic.M11 := e
    have hez : orderOf (e' z) = 2 :=
      (orderOf_injective e'.toMonoidHom e'.injective (z : G)).trans hz
    obtain ⟨hc, hN⟩ :=
      Semidihedral.ProperSubgroupRegularity.m11_involution_centralizer_card_and_odd_core
        (e' z) hez
    obtain ⟨hc', -⟩ :=
      Semidihedral.ProperSubgroupRegularity.centralizer_card_and_core_of_equiv e' (z : G) hc hN
    have hLle : Nat.card L ≤ 48 := by
      rw [← hc']
      exact Subgroup.card_le_of_le hLT
    have hAn : 60 ≤ Nat.card (alternatingGroup (Fin n)) := by
      have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
      have h2 := two_mul_nat_card_alternatingGroup (α := Fin n)
      rw [Nat.card_perm, Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin] at h2
      have : Nat.factorial 5 ≤ Nat.factorial n := Nat.factorial_le hn5
      have h120 : Nat.factorial 5 = 120 := rfl
      omega
    have h1 : Nat.card (L ⧸ center L) ≤ Nat.card L :=
      Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)
    rw [Nat.card_congr θ.toEquiv] at h1
    omega

end CFSG.OddStandard
