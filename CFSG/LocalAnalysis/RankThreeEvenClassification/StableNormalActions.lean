module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.ReplacementAbelian
public import CFSG.LocalAnalysis.RankThreeEvenClassification.StableActionCore
public import CFSG.LocalAnalysis.RankThreeEvenClassification.NormalClosureCommutator

public section

open CFSG.Open

namespace CFSG.RankThreeEvenClassification.Helpers

universe u

@[expose] def StableNormalPrimeActions (prime : ℕ) (G : Type u) [Group G] : Prop :=
  ∀ normal : Subgroup G, ∀ hnormal : normal.Normal, IsPGroup prime normal →
    letI := hnormal
    PrimeStableAction prime (MulAut.conjNormal : G →* MulAut normal)

theorem conjugation_quadratic_of_normalized_abelian {G : Type u} [Group G]
    (normal abelian : Subgroup G) [normal.Normal] (habelian : IsMulCommutative abelian)
    (hnormalizes : normal ≤ Subgroup.normalizer (abelian : Set G))
    (member : G) (hmember : member ∈ abelian) :
    QuadraticAutomorphism (MulAut.conjNormal member : MulAut normal) := by
  intro element
  have hconjugate : (element : G)⁻¹ * member * element ∈ abelian := by
    have hmem := Subgroup.le_normalizer_iff.mp hnormalizes (element : G)⁻¹
      (normal.inv_mem element.property) member hmember
    simpa only [inv_inv] using hmem
  have hdifference : (element : G)⁻¹ * member * element * member⁻¹ ∈ abelian :=
    abelian.mul_mem hconjugate (abelian.inv_mem hmember)
  have hcommute : member * ((element : G)⁻¹ * member * element * member⁻¹) =
      ((element : G)⁻¹ * member * element * member⁻¹) * member := by
    exact congrArg (fun value : abelian => (value : G))
      (isMulCommutative_iff.mp habelian ⟨member, hmember⟩ ⟨_, hdifference⟩)
  apply Subtype.ext
  have heq : normal.subtype (element⁻¹ * (MulAut.conjNormal member : MulAut normal) element) =
      (element : G)⁻¹ * member * element * member⁻¹ := normal_conjugation_difference_apply normal member element
  rw [MulAut.conjNormal_apply]
  change member * normal.subtype (element⁻¹ * (MulAut.conjNormal member : MulAut normal) element) * member⁻¹ =
    normal.subtype (element⁻¹ * (MulAut.conjNormal member : MulAut normal) element)
  rw [heq, hcommute]
  group

theorem stable_normalized_abelian_le_actionCore {G : Type u} [Group G]
    (prime : ℕ) (normal abelian : Subgroup G) [normal.Normal]
    (hstable : PrimeStableAction prime (MulAut.conjNormal : G →* MulAut normal))
    (habelian : IsMulCommutative abelian)
    (hnormalizes : normal ≤ Subgroup.normalizer (abelian : Set G)) :
    abelian ≤ actionPrimeCore prime (MulAut.conjNormal : G →* MulAut normal) := by
  intro member hmember
  exact hstable member (conjugation_quadratic_of_normalized_abelian normal abelian habelian hnormalizes member hmember)

theorem zj_fixed_normal_closure_core_and_classTwo {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (sylow : Sylow prime G) (kernel fixed : Subgroup G) [kernel.Normal]
    (hcharacteristic : Subgroup.centralizer (pCore prime G : Set G) ≤ pCore prime G)
    (hstable : StableNormalPrimeActions prime G)
    (hkernel : kernel ≤ fixed)
    (hfixedNormal : (sylow : Subgroup G) ≤ Subgroup.normalizer (fixed : Set G))
    (habelian : IsMulCommutative fixed) (hcommutator : ⁅fixed, (sylow : Subgroup G)⁆ ≤ kernel) :
    conjugateJoin fixed ≤ pCore prime G ∧ ⁅conjugateJoin fixed, conjugateJoin fixed⁆ ≤ kernel ∧
      kernel ≤ Subgroup.centralizer (conjugateJoin fixed : Set G) := by
  have : (pCore prime G).Normal := pCore_normal G prime
  have hfixedCore : fixed ≤ pCore prime G := by
    have hstableCore := hstable (pCore prime G) (pCore_normal G prime) (pCore_isPGroup G prime)
    have hle := stable_normalized_abelian_le_actionCore prime (pCore prime G) fixed hstableCore habelian
      ((pCore_le_sylow prime sylow).trans hfixedNormal)
    rwa [conjugation_actionPrimeCore_eq_primeCore prime hcharacteristic] at hle
  have hclosureCore := conjugateJoin_le_normal fixed (pCore prime G) hfixedCore
  refine ⟨hclosureCore, ?_, ?_⟩
  · have hcommCore : ⁅fixed, pCore prime G⁆ ≤ kernel :=
      (Subgroup.commutator_mono le_rfl (pCore_le_sylow prime sylow)).trans hcommutator
    exact (Subgroup.commutator_mono le_rfl hclosureCore).trans
      (conjugateJoin_commutator_le_normal fixed (pCore prime G) kernel hcommCore)
  · exact centralizer_symmetry_le (conjugateJoin fixed) kernel
      (conjugateJoin_centralizes_normal_of_abelian fixed kernel habelian hkernel)

end CFSG.RankThreeEvenClassification.Helpers
