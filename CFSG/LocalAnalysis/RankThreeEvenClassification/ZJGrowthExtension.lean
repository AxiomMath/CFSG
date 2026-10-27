module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.ZJFixedSubgroup
public import CFSG.LocalAnalysis.RankThreeEvenClassification.StableNormalActions
public import CFSG.LocalAnalysis.RankThreeEvenClassification.AmbientReplacement
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ActionCoreFrattini
public import CFSG.LocalAnalysis.RankThreeEvenClassification.AmbientThompsonComparison

public section

open CFSG.Open

namespace CFSG.RankThreeEvenClassification.Helpers

universe u

open scoped commutatorElement

theorem ambientMaximum_contains_thompsonCenter {G : Type u} [Group G] [Finite G]
    (abelian overgroup : Subgroup G) (hle : abelian ≤ overgroup)
    (hmaximum : MaximumOrderAbelian (abelian.subgroupOf overgroup)) :
    thompsonCenterOf overgroup ≤ abelian := by
  have hbound : thompsonOrderCenter overgroup ≤ abelian.subgroupOf overgroup := by
    rw [thompsonOrderCenter_eq_intersection]
    exact iInf_le _ (⟨abelian.subgroupOf overgroup, hmaximum⟩ :
      {candidate : Subgroup overgroup // MaximumOrderAbelian candidate})
  have hmapped := Subgroup.map_mono (f := overgroup.subtype) hbound
  rwa [Subgroup.map_subgroupOf_eq_of_le hle] at hmapped

theorem zj_growth_extension {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (hodd : Odd prime) (sylow : Sylow prime G)
    (kernel : Subgroup G) [kernel.Normal] (hproper : kernel < thompsonCenterOf (sylow : Subgroup G))
    (hcharacteristic : Subgroup.centralizer (pCore prime G : Set G) ≤ pCore prime G)
    (hstable : StableNormalPrimeActions prime G) :
    ∃ extension : Subgroup G, extension.Normal ∧ kernel < extension ∧
      extension ≤ thompsonCenterOf (sylow : Subgroup G) := by
  obtain ⟨fixed, hstrict, hfixedLe, hfixedNormalized, habelian, hcommutator⟩ :=
    zj_fixed_subgroup_exists prime hprime sylow kernel hproper
  let closure := conjugateJoin fixed
  have hclosureNormal : closure.Normal := conjugateJoin_normal fixed
  have : closure.Normal := hclosureNormal
  obtain ⟨hclosureCore, hderivedKernel, hkernelCentral⟩ := zj_fixed_normal_closure_core_and_classTwo
    prime sylow kernel fixed hcharacteristic hstable hstrict.le hfixedNormalized habelian hcommutator
  have hclosureSylow : closure ≤ (sylow : Subgroup G) := hclosureCore.trans (pCore_le_sylow prime sylow)
  have hclosureClass : ⁅closure, closure⁆ ≤ Subgroup.centralizer (closure : Set G) :=
    hderivedKernel.trans hkernelCentral
  have hderivedCenter : ⁅closure, closure⁆ ≤ thompsonCenterOf (sylow : Subgroup G) :=
    hderivedKernel.trans hproper.le
  have hclosureLe : closure ≤ thompsonCenterOf (sylow : Subgroup G) := by
    by_contra hnot
    obtain ⟨abelian, habSylow, hmaximum, hnotContains, hnormalized⟩ :=
      ambient_glauberman_replacement_witness prime hprime hodd (sylow : Subgroup G) closure sylow.isPGroup'
        hclosureSylow (hclosureNormal.subgroupOf _) hclosureClass hderivedCenter hnot
    let action : G →* MulAut closure := MulAut.conjNormal
    let actionCore := actionPrimeCore prime action
    let intersection := (sylow : Subgroup G) ⊓ actionCore
    have hclosurePGroup : IsPGroup prime closure := (pCore_isPGroup G prime).to_le hclosureCore
    have hstableClosure := hstable closure hclosureNormal hclosurePGroup
    have habCore : abelian ≤ actionCore := stable_normalized_abelian_le_actionCore prime closure abelian hstableClosure
      (ambientMaximum_commutative abelian (sylow : Subgroup G) habSylow hmaximum) hnormalized
    have habIntersection : abelian ≤ intersection := le_inf habSylow habCore
    have hcomparison : thompsonCenterOf (sylow : Subgroup G) ≤ thompsonCenterOf intersection :=
      thompsonCenterOf_le_of_common_maximum abelian intersection (sylow : Subgroup G) habIntersection inf_le_left hmaximum
    have hkernelFixed : action.ker ≤ Subgroup.centralizer (fixed : Set G) := by
      have heq : action.ker = Subgroup.centralizer (closure : Set G) := conjugation_kernel_eq_centralizer closure
      rw [heq]
      exact Subgroup.centralizer_le (le_conjugateJoin fixed)
    have hfactor : action.ker ⊔ Subgroup.normalizer (intersection : Set G) = ⊤ :=
      action_core_frattini_normalizer_eq_top prime hprime action sylow
    have htrapped : closure ≤ thompsonCenterOf intersection :=
      conjugateJoin_le_of_kernel_normalizer fixed (Subgroup.normalizer (intersection : Set G)) action.ker
        (thompsonCenterOf intersection) hfactor hkernelFixed (hfixedLe.trans hcomparison)
          (thompsonCenterOf_normalized intersection)
    have hmaximumIntersection := ambientMaximum_restrict abelian intersection (sylow : Subgroup G)
      habIntersection inf_le_left hmaximum
    exact hnotContains (htrapped.trans
      (ambientMaximum_contains_thompsonCenter abelian intersection habIntersection hmaximumIntersection))
  refine ⟨closure, hclosureNormal, ?_, hclosureLe⟩
  exact lt_of_lt_of_le hstrict (le_conjugateJoin fixed)

end CFSG.RankThreeEvenClassification.Helpers
