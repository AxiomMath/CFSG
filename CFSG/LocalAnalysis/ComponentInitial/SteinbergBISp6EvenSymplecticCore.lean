module

public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTISpSocle
public import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixFusionOrbits
public import Certificates.Certificate113
import CFSG.LocalAnalysis.ComponentInitial.SteinbergCFOddLinearTwoSocleCore
public import CFSG.CharacterTheory.Semidihedral.OddFieldLift
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogRigidityLinear
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUFieldOddCore
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalSmallSourceLinear
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82

public section

namespace CFSG.LocalAnalysis.ComponentInitial.SteinbergBI

open Subgroup Matrix CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.FusionOrbits
  (isSimpleGroup_GL_three_two)
open CFSG.ComponentClassification.OutcomeLocal
  (faithful_even_symplectic_socle_small_source_involution_selector)
open scoped commutatorElement

theorem exists_mul_ne_mul_GL_three_two : ∃ a b : GL (Fin 3) (ZMod 2), a * b ≠ b * a :=
  CFSG.LocalAnalysis.ComponentInitial.SteinbergCF.exists_ne_GL_three_two

theorem isQuasisimple_and_center_eq_bot {S : Type*} [Group S] [IsSimpleGroup S]
    (hnab : ∃ a b : S, a * b ≠ b * a) :
    CFSG.Assembly.IsQuasisimple S ∧ center S = ⊥ := by
  obtain ⟨a, b, hab⟩ := hnab
  have hcen : center S = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center S) with h | h
    · exact h
    · exact absurd ((mem_center_iff.mp (by rw [h]; exact mem_top b)) a) hab
  refine ⟨⟨?_, ((QuotientGroup.quotientMulEquivOfEq hcen).trans
    QuotientGroup.quotientBot).isSimpleGroup⟩, hcen⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator S) with h | h
  · have hmem : ⁅a, b⁆ ∈ commutator S := by
      rw [_root_.commutator_def]
      exact Subgroup.commutator_mem_commutator (mem_top a) (mem_top b)
    rw [h, mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact absurd hmem hab
  · exact h

theorem lieModel_PSL_three_two_of_mulEquiv {X : Type} [Group X]
    (e : X ≃* GL (Fin 3) (ZMod 2)) : CFSG.Blueprint.LieModel X .PSL 3 2 1 := by
  let e₃ : SpecialLinearGroup (Fin 3) (ZMod 2) ≃* GL (Fin 3) (ZMod 2) :=
    MulEquiv.ofBijective _ bijective_toGL_three_zmod_two
  let e₂ : ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2) ≃*
      SpecialLinearGroup (Fin 3) (ZMod 2) :=
    (QuotientGroup.quotientMulEquivOfEq center_SL_three_zmod_two_eq_bot).trans
      QuotientGroup.quotientBot
  have hadm : StatedLieAdmissible .PSL 3 2 1 :=
    ⟨Nat.prime_two, le_rfl, by norm_num, by decide, by decide⟩
  have hmem : (StatedLieTag.PSL) ∈ CFSG.Blueprint.classicalTags := by decide
  exact Or.inl ⟨hmem, hadm, ZMod 2, inferInstance, inferInstance,
    by rw [Nat.card_zmod, pow_one],
    ⟨((e.trans e₃.symm).trans e₂.symm).trans (projectiveSpecialLinearGroupEquivStatedProj 3 _)⟩⟩

theorem classicalModel_PSL_two_seven_of_mulEquiv {X : Type} [Group X]
    (e : X ≃* GL (Fin 3) (ZMod 2)) : StatedClassicalModel X .PSL 2 7 1 := by
  rcases PSL3_two_PSL2_seven_paired_isomorphism X (lieModel_PSL_three_two_of_mulEquiv e) with
    ⟨-, h⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · exact h
  all_goals exact absurd ht (by decide)

theorem not_lieModel_PSp_of_GL_three_two_component {Y : Type} [Group Y] [Finite Y]
    {D : Subgroup Y} [D.Normal] (hDs : IsSimpleGroup D) (hDnab : ∃ x y : D, x * y ≠ y * x)
    (hCD : centralizer (D : Set Y) = ⊥) {a : Y} (ha : orderOf a = 2) {J : Subgroup Y}
    (hJD : J ≤ D) (hJa : J ≤ centralizer ({a} : Set Y))
    (hJn : (J.subgroupOf (centralizer ({a} : Set Y))).Normal)
    (hJ : Nonempty (J ≃* GL (Fin 3) (ZMod 2))) :
    ∀ r e : ℕ, 2 ≤ r → 1 ≤ e → ¬ CFSG.Blueprint.LieModel D .PSp r 2 e := by
  intro r e _ _ hD
  obtain ⟨eJ⟩ := hJ
  have := isSimpleGroup_GL_three_two
  have : IsSimpleGroup J := eJ.isSimpleGroup
  have hJnab : ∃ x y : J, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := exists_mul_ne_mul_GL_three_two
    exact ⟨eJ.symm x, eJ.symm y, fun h => hxy (by simpa using congrArg eJ h)⟩
  obtain ⟨hquasi, hcen⟩ := isQuasisimple_and_center_eq_bot hJnab
  have hcomp : CFSG.Assembly.IsComponentOf J (centralizer ({a} : Set Y)) :=
    ⟨hJa, CFSG.Assembly.IsSubnormal.step hJa hJn (CFSG.Assembly.IsSubnormal.refl _), hquasi⟩
  have hsrc : StatedClassicalModel (J ⧸ center J) .PSL 2 7 1 :=
    classicalModel_PSL_two_seven_of_mulEquiv
      (((QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot).trans eJ)
  rcases hD with ⟨-, hc⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · obtain ⟨⟨-, he, hr, hre⟩, K, _, _, hK, ⟨φ⟩⟩ := hc
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    let : Fintype K := Fintype.ofFinite K
    have : CharP K 2 := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
    have hre' : ¬ (r = 2 ∧ e = 1) := by
      rintro ⟨rfl, rfl⟩
      exact hre rfl
    obtain ⟨-, -, -, -, -, -, hp3, -⟩ :=
      faithful_even_symplectic_socle_small_source_involution_selector hDs hDnab hCD ha hJD hcomp
        Nat.prime_seven (by norm_num) le_rfl (Or.inl hsrc) hr he hre' hK φ
    omega
  all_goals exact absurd ht (by decide)

theorem normal_subgroupOf_centralizer_of_sup_eq {Y : Type*} [Group Y] {a : Y} {J : Subgroup Y}
    (hJa : J ≤ centralizer ({a} : Set Y)) (hC : zpowers a ⊔ J = centralizer ({a} : Set Y)) :
    (J.subgroupOf (centralizer ({a} : Set Y))).Normal := by
  rw [normal_subgroupOf_iff_le_normalizer hJa, ← hC]
  refine sup_le ?_ le_normalizer
  rw [zpowers_le, mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have hc : a * h = h * a := mem_centralizer_iff.1 (hJa hh) a rfl
    rwa [hc, mul_inv_cancel_right]
  · intro hh
    have hc : a * (a * h * a⁻¹) = a * h * a⁻¹ * a := mem_centralizer_iff.1 (hJa hh) a rfl
    have hha : h = a * h * a⁻¹ := by
      calc h = a⁻¹ * (a * h * a⁻¹ * a) := by group
        _ = a⁻¹ * (a * (a * h * a⁻¹)) := by rw [hc]
        _ = a * h * a⁻¹ := by rw [inv_mul_cancel_left]
    rw [hha]
    exact hh

theorem not_lieModel_PSp_of_GL_three_two_centralizer {Y : Type} [Group Y] [Finite Y]
    {D : Subgroup Y} [D.Normal] (hDs : IsSimpleGroup D) (hDnab : ∃ x y : D, x * y ≠ y * x)
    (hCD : centralizer (D : Set Y) = ⊥) {a : Y} (ha : orderOf a = 2) {J : Subgroup Y}
    (hJD : J ≤ D) (hJa : J ≤ centralizer ({a} : Set Y))
    (hC : zpowers a ⊔ J = centralizer ({a} : Set Y))
    (hJ : Nonempty (J ≃* GL (Fin 3) (ZMod 2))) :
    ∀ r e : ℕ, 2 ≤ r → 1 ≤ e → ¬ CFSG.Blueprint.LieModel D .PSp r 2 e :=
  not_lieModel_PSp_of_GL_three_two_component hDs hDnab hCD ha hJD hJa
    (normal_subgroupOf_centralizer_of_sup_eq hJa hC) hJ

end CFSG.LocalAnalysis.ComponentInitial.SteinbergBI
