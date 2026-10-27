module

public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTIReeSocle
public import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixFusionOrbits
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
import CFSG.Blueprint.LieModelAPI
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.CentralResidueMaps
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalizerClassLifting
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.PrincipalClassDefects
public import CFSG.CharacterTheory.Semidihedral.ElementStructure
public import CFSG.CharacterTheory.Semidihedral.Principal.DegreeZeroGram
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogRigidityLinear
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUFieldOddCore
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAntiunitaryDescent
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PSLRangeCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvolutionCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUDecomposition
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTen
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FieldProjectionArithmetic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction
public import Certificates.Certificate1
public import Certificates.Certificate10
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate42
public import Certificates.Certificate44
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate9

public section

namespace CFSG.LocalAnalysis.ComponentInitial.SteinbergCA

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Ree
  CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.OutcomeLocal
  (faithful_small_Ree_socle_small_source_involution_selector_explicit)
open scoped commutatorElement

theorem isSimpleGroup_nonabelian_center_of_equiv_GL_three_two {J : Type*} [Group J]
    (ι : J ≃* GL (Fin 3) (ZMod 2)) :
    IsSimpleGroup J ∧ (∃ x y : J, x * y ≠ y * x) ∧ center J = ⊥ := by
  have : IsSimpleGroup (GL (Fin 3) (ZMod 2)) :=
    BinarySymplecticSix.FusionOrbits.isSimpleGroup_GL_three_two
  have hs : IsSimpleGroup J := ι.isSimpleGroup
  have hZGL : center (GL (Fin 3) (ZMod 2)) = ⊥ := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar, eq_bot_iff]
    rintro _ ⟨c, rfl⟩
    rw [mem_bot, Subsingleton.elim c 1, map_one]
  have hZ : center J = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have h1 : ι x ∈ center (GL (Fin 3) (ZMod 2)) := by
      rw [mem_center_iff]
      intro y
      obtain ⟨y', rfl⟩ := ι.surjective y
      rw [← map_mul, ← map_mul, (mem_center_iff.mp hx) y']
    rw [hZGL, mem_bot] at h1
    rw [mem_bot, ← map_eq_one_iff ι ι.injective, h1]
  refine ⟨hs, ?_, hZ⟩
  by_contra hab
  simp only [not_exists, ne_eq, not_not] at hab
  have htop : center J = ⊤ := eq_top_iff.2 fun x _ => mem_center_iff.2 fun y => hab y x
  have h1 : Nat.card J = 1 := by
    rw [← card_top (G := J), ← htop, hZ, card_bot]
  rw [Nat.card_congr ι.toEquiv, card_GL_three_zmod_two] at h1
  exact absurd h1 (by norm_num)

theorem isQuasisimple_of_equiv_GL_three_two {J : Type*} [Group J]
    (ι : J ≃* GL (Fin 3) (ZMod 2)) : CFSG.Assembly.IsQuasisimple J := by
  obtain ⟨hs, ⟨x, y, hxy⟩, hZ⟩ := isSimpleGroup_nonabelian_center_of_equiv_GL_three_two ι
  refine ⟨?_,
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).isSimpleGroup⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator J) with h | h
  · have h1 : ⁅x, y⁆ ∈ commutator J := by
      rw [commutator_def]
      exact commutator_mem_commutator (mem_top x) (mem_top y)
    rw [h, mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact absurd h1 hxy
  · exact h

theorem isComponentOf_of_normal_of_equiv_GL_three_two {Y : Type*} [Group Y] {J C : Subgroup Y}
    (hJC : J ≤ C) (hJn : (J.subgroupOf C).Normal) (ι : J ≃* GL (Fin 3) (ZMod 2)) :
    CFSG.Assembly.IsComponentOf J C :=
  ⟨hJC, CFSG.Assembly.IsSubnormal.step hJC hJn (CFSG.Assembly.IsSubnormal.refl C),
    isQuasisimple_of_equiv_GL_three_two ι⟩

theorem lieModel_PSL_three_two_of_equiv {J : Type} [Group J] (ι : J ≃* GL (Fin 3) (ZMod 2)) :
    LieModel (J ⧸ center J) .PSL 3 2 1 := by
  obtain ⟨-, -, hZ⟩ := isSimpleGroup_nonabelian_center_of_equiv_GL_three_two ι
  let e₁ : J ⧸ center J ≃* J := (QuotientGroup.quotientMulEquivOfEq hZ).trans
    QuotientGroup.quotientBot
  let e₂ : GL (Fin 3) (ZMod 2) ≃* SpecialLinearGroup (Fin 3) (ZMod 2) :=
    (MulEquiv.ofBijective _ bijective_toGL_three_zmod_two).symm
  let e₃ : SpecialLinearGroup (Fin 3) (ZMod 2) ≃* ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2) :=
    ((QuotientGroup.quotientMulEquivOfEq center_SL_three_zmod_two_eq_bot).trans
      QuotientGroup.quotientBot).symm
  have hmem : (StatedLieTag.PSL) ∈ classicalTags := by decide
  exact Or.inl ⟨hmem, ⟨Nat.prime_two, le_rfl, by norm_num, by decide, by decide⟩, ZMod 2,
    inferInstance, inferInstance, by rw [Nat.card_zmod, pow_one],
    ⟨(((e₁.trans ι).trans e₂).trans e₃).trans (projectiveSpecialLinearGroupEquivStatedProj 3 _)⟩⟩

theorem statedClassicalModel_PSL_two_seven_of_equiv {J : Type} [Group J]
    (ι : J ≃* GL (Fin 3) (ZMod 2)) : StatedClassicalModel (J ⧸ center J) .PSL 2 7 1 := by
  rcases PSL3_two_PSL2_seven_paired_isomorphism _ (lieModel_PSL_three_two_of_equiv ι) with
    ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · exact h
  all_goals exact absurd h (by norm_num)

theorem lieModel_twistedG2_iff (X : Type) [Group X] (n ℓ e : ℕ) :
    LieModel X .twistedG2 n ℓ e ↔ n = 0 ∧ ReeTitsModel X .twistedG2 ℓ e :=
  CFSG.Blueprint.LieModel.reeTits_iff (by decide)

theorem not_reeTitsModel_twistedG2_of_GL_three_two_component
    {Y : Type} [Group Y] [Finite Y]
    {D : Subgroup Y} [D.Normal] (hDs : IsSimpleGroup D) (hDnab : ∃ x y : D, x * y ≠ y * x)
    (hCD : centralizer (D : Set Y) = ⊥) {a : Y} (ha : orderOf a = 2) {J : Subgroup Y}
    (hJD : J ≤ D) (hJ : CFSG.Assembly.IsComponentOf J (centralizer ({a} : Set Y)))
    (hJGL : Nonempty (J ≃* GL (Fin 3) (ZMod 2))) (ℓ e : ℕ) :
    ¬ ReeTitsModel D .twistedG2 ℓ e ∧ ¬ LieModel D .twistedG2 0 ℓ e := by
  obtain ⟨ι⟩ := hJGL
  have hsrc := statedClassicalModel_PSL_two_seven_of_equiv ι
  have hR : ∀ ℓ e : ℕ, ¬ ReeTitsModel D .twistedG2 ℓ e := by
    intro ℓ e h
    obtain ⟨-, -, hℓ, ⟨m', hm', hem'⟩, hiso⟩ := small_Ree_model_Schreier _ ℓ e h
    subst hℓ
    obtain ⟨-, m, hem, K, _, _, hK, ⟨η⟩⟩ := h
    have : CharP K ReeTag.G2.prime :=
      finite_field_prime_power_characteristic Nat.prime_three (by omega) hK
    obtain ⟨φ⟩ := hiso m K hem hK ⟨η⟩
    have hm : 1 ≤ m := by omega
    obtain ⟨-, -, -, -, hp3, -⟩ :=
      faithful_small_Ree_socle_small_source_involution_selector_explicit hDs hDnab hCD ha hJD hJ
        Nat.prime_seven (by norm_num) le_rfl (Or.inl hsrc) hm (by rw [hK, hem]) φ
    omega
  exact ⟨hR ℓ e, fun h => hR ℓ e ((lieModel_twistedG2_iff D 0 ℓ e).1 h).2⟩

end CFSG.LocalAnalysis.ComponentInitial.SteinbergCA
