module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherFactsSDCore
public import CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupOddHigherLinear
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAllInvolutionFourGroup
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_6Out
public import CFSG.CharacterTheory.Semidihedral.GL2Recognition.M11Order
public import Certificates.Certificate110
public import CFSG.CharacterTheory.Blocks.BrauerInduction
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5Semisimple
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearDescentFixedBasis
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherScalarSquareSplit
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
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
public import Certificates.Certificate43
public import Certificates.Certificate44
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate9

public section

namespace CFSG.ComponentClassification.AschbacherKnownGroup.FactsSD

open CFSG.Open

theorem exists_pair_of_fixed_four {X : Type} [Group X] {α : MulAut X} {V : Subgroup X}
    (hV : V ≤ FixedCommutingProduct.fixedSubgroup α) (hab : CFSG.IsElementaryAbelian 2 V)
    (hcard : Nat.card V = 4) :
    ∃ u w : X, u ^ 2 = 1 ∧ w ^ 2 = 1 ∧ u ≠ 1 ∧ w ≠ 1 ∧ u ≠ w ∧ u * w = w * u ∧
      α u = u ∧ α w = w := by
  have : CFSG.IsElementaryAbelian 2 V := hab
  have hsq : ∀ x ∈ V, x ^ 2 = 1 := fun x hx => elemPow_eq_one_of_isElementaryAbelian x hx
  have hfix : ∀ x ∈ V, α x = x := fun x hx => hV hx
  have hVbot : V ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hcard
    omega
  obtain ⟨⟨u, huV⟩, hu1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hVbot
  have hu1' : u ≠ 1 := fun h => hu1 (Subtype.ext h)
  have hle : Subgroup.zpowers u ≤ V := (Subgroup.zpowers_le).mpr huV
  have hlt : Subgroup.zpowers u < V := by
    refine lt_of_le_of_ne hle fun h => ?_
    have h1 : Nat.card (Subgroup.zpowers u) = orderOf u := Nat.card_zpowers u
    have h2 : orderOf u ∣ 2 := orderOf_dvd_of_pow_eq_one (hsq u huV)
    have h3 := Nat.le_of_dvd (by norm_num) h2
    rw [h, hcard] at h1
    omega
  obtain ⟨w, hwV, hwu⟩ := IsConcreteLE.exists_of_lt hlt
  have hw1 : w ≠ 1 := fun h => hwu (h ▸ Subgroup.one_mem _)
  have huw : u ≠ w := fun h => hwu (h ▸ Subgroup.mem_zpowers u)
  have hcomm : u * w = w * u := by
    have := (isMulCommutative_iff.mp hab.toIsMulCommutative) ⟨u, huV⟩ ⟨w, hwV⟩
    exact congrArg Subtype.val this
  exact ⟨u, w, hsq u huV, hsq w hwV, hu1', hw1, huw, hcomm, hfix u huV, hfix w hwV⟩

theorem psl_three_fixed_involution_pair {X : Type} [Group X] {p f : ℕ} (hp : p ≠ 2)
    (hX : StatedClassicalModel X .PSL 3 p f) (α : MulAut X) (hα : α ^ 2 = 1) :
    ∃ u w : X, u ^ 2 = 1 ∧ w ^ 2 = 1 ∧ u ≠ 1 ∧ w ≠ 1 ∧ u ≠ w ∧ u * w = w * u ∧
      α u = u ∧ α w = w := by
  obtain ⟨V, hV, hab, hcard⟩ :=
    LocalAnalysis.ComponentInitial.OddHigherLinear.odd_higher_linear_all_involution_fixed_four_group
      X hp le_rfl hX α hα
  exact exists_pair_of_fixed_four hV hab hcard

theorem psu_three_fixed_involution_pair {X : Type} [Group X] {p f : ℕ} (hp : p ≠ 2)
    (hX : StatedClassicalModel X .PSU 3 p f) (α : MulAut X) (hα : α ^ 2 = 1) :
    ∃ u w : X, u ^ 2 = 1 ∧ w ^ 2 = 1 ∧ u ≠ 1 ∧ w ≠ 1 ∧ u ≠ w ∧ u * w = w * u ∧
      α u = u ∧ α w = w := by
  obtain ⟨V, hV, hab, hcard⟩ :=
    LocalAnalysis.ComponentInitial.UnitaryHigher.odd_unitary_all_involution_fixed_four_group
      X hp hX α hα
  exact exists_pair_of_fixed_four hV hab hcard

theorem m11_fixed_involution_pair {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    (hnonab : ∃ a b : X, a * b ≠ b * a) (hsd : HasSemidihedralSylowTwo X)
    (hX : Nonempty (X ≃* StatedM11)) (α : MulAut X) (hα : α ^ 2 = 1) :
    ∃ u w : X, u ^ 2 = 1 ∧ w ^ 2 = 1 ∧ u ≠ 1 ∧ w ≠ 1 ∧ u ≠ w ∧ u * w = w * u ∧
      α u = u ∧ α w = w := by
  obtain ⟨e₀⟩ := hX
  let e : X ≃* CFSG.Blueprint.NativeSporadic.M11 :=
    e₀.trans (MulEquiv.subgroupCongr Semidihedral.GL2Recognition.statedM11_eq_nativeM11)
  obtain ⟨g, hg⟩ := QuasithinUnique.Unc25G2.aut_inner (MulAut.congr e α)
  set g' : X := e.symm g with hg'
  have hαg : ∀ y : X, α y = g' * y * g'⁻¹ := by
    intro y
    have h := hg (e y)
    have h' : (MulAut.congr e α) (e y) = e (α y) := by
      simp [MulAut.congr_apply]
    rw [h'] at h
    have h2 := congrArg e.symm h
    rw [MulEquiv.symm_apply_apply] at h2
    rw [h2, hg', map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply]
  have hZ : Subgroup.center X = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnonab
      apply hab
      have ha : a ∈ Subgroup.center X := h ▸ Subgroup.mem_top a
      exact (Subgroup.mem_center_iff.mp ha b).symm
  have hg2 : g' ^ 2 = 1 := by
    have hc : g' ^ 2 ∈ Subgroup.center X := by
      rw [Subgroup.mem_center_iff]
      intro y
      have h1 : (α ^ 2) y = y := by rw [hα, MulAut.one_apply]
      rw [pow_two, MulAut.mul_apply, hαg, hαg] at h1
      calc y * g' ^ 2 = g' * (g' * y * g'⁻¹) * g'⁻¹ * g' ^ 2 := by rw [h1]
        _ = g' ^ 2 * y := by rw [pow_two]; group
    rw [hZ, Subgroup.mem_bot] at hc
    exact hc
  obtain ⟨u, w, hu2, hw2, hu1, hw1, huw, hc, hug, hwg⟩ := exists_involution_pair_commuting hsd hg2
  refine ⟨u, w, hu2, hw2, hu1, hw1, huw, hc, ?_, ?_⟩
  · rw [hαg, ← hug]
    group
  · rw [hαg, ← hwg]
    group

end CFSG.ComponentClassification.AschbacherKnownGroup.FactsSD
