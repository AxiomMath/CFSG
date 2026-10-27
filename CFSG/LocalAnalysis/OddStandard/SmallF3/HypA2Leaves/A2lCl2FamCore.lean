module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddInnerComp
public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorOrthSplit
public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorSpCert
public import CFSG.LocalAnalysis.ComponentInitial.CentralQuotientComponentLift
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl2Defs
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.CentralResidueMaps
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalizerClassLifting
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.PrincipalClassDefects
public import CFSG.CharacterTheory.Semidihedral.Principal.DegreeZeroGram
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
public import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
public import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorOddE6
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
public import CFSG.LocalAnalysis.ComponentClassification.KProper
public import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorInner
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTILinearSocle
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSLAllInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUFieldOddCore
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCriticalStandard
public import CFSG.LocalAnalysis.ComponentInitial.ProjectiveEigenspaceComponent
public import CFSG.LocalAnalysis.ComponentInitial.ProjectiveOrthogonalLocalComponentSplit
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.SectionRank.BruhatLift
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SLTwo
public import CFSG.LocalAnalysis.SectionRank.LargeReeCover
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus
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
public import Certificates.Certificate10
public import Certificates.Certificate11
public import Certificates.Certificate12
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

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open CFSG Subgroup CFSG.Blueprint CFSG.Open CFSG.ComponentClassification
open CFSG.ComponentClassification.CatLeafProof CFSG.Assembly.LowTwoRank

@[expose] def Cl24Q (p : ℕ) (R : ℕ → Prop) (L : Type) [Group L] : Prop :=
  ∃ (τ' : StatedLieTag) (n' f' : ℕ), R f' ∧ StatedLieAdmissible τ' n' p f' ∧
    LieModel (L ⧸ center L) τ' n' p f'

macro "cl24_rel" : tactic =>
  `(tactic| (intro f' h; first | omega | (unfold Cl24FieldRel; omega) |
    (apply_assumption <;> first | omega | (unfold Cl24FieldRel; omega))))

macro "cl24_rel_at" : tactic =>
  `(tactic| first | omega | (unfold Cl24FieldRel; omega) |
    (apply_assumption <;> first | omega | (unfold Cl24FieldRel; omega)))

theorem Cl24Q.mono {p : ℕ} {R R' : ℕ → Prop} {L : Type} [Group L] (h : Cl24Q p R L)
    (hR : ∀ f, R f → R' f) : Cl24Q p R' L := by
  obtain ⟨τ', n', f', hf, hadm, hL⟩ := h
  exact ⟨τ', n', f', hR f' hf, hadm, hL⟩

theorem cl24_of_mulEquiv {p : ℕ} {R : ℕ → Prop} {L L' : Type} [Group L] [Group L']
    (e : L ≃* L') (h : Cl24Q p R L') : Cl24Q p R L := by
  obtain ⟨τ', n', f', hf, hadm, hL⟩ := h
  exact ⟨τ', n', f', hf, hadm, LieType.CurtisTits.lieModel_of_mulEquiv
    (QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)).symm hL⟩

theorem cl24_of_component_equiv {X Y : Type} [Group X] [Group Y] (Φ : X ≃* Y) {p : ℕ}
    {R : ℕ → Prop} (h : ∀ M : Subgroup Y, IsComponent M → Cl24Q p R M) {L : Subgroup X}
    (hL : IsComponent L) : Cl24Q p R L :=
  cl24_of_mulEquiv (L.equivMapOfInjective Φ.toMonoidHom Φ.injective)
    (h _ (LocalCores.isComponent_map_mulEquiv Φ hL))

theorem cl24_of_centerQuotient_equiv {p : ℕ} {R : ℕ → Prop} {L M : Type} [Group L] [Group M]
    (e : L ⧸ center L ≃* M ⧸ center M) (h : Cl24Q p R M) : Cl24Q p R L := by
  obtain ⟨τ', n', f', hf, hadm, hM⟩ := h
  exact ⟨τ', n', f', hf, hadm, LieType.CurtisTits.lieModel_of_mulEquiv e.symm hM⟩

theorem cl24_of_isQuasisimple {G : Type} [Group G] (hG : IsQuasisimple G) {p : ℕ}
    {R : ℕ → Prop} (h : Cl24Q p R G) {L : Subgroup G} (hL : IsComponent L) : Cl24Q p R L := by
  obtain rfl := OddClassSelector.eq_top_of_isComponent_of_quasisimple hG hL
  exact cl24_of_mulEquiv Subgroup.topEquiv h

theorem cl24_of_commutator_le {X : Type} [Group X] [Finite X] {S : Subgroup X}
    (hS : IsQuasisimple S) (hSX : _root_.commutator X ≤ S) {p : ℕ} {R : ℕ → Prop}
    (h : Cl24Q p R S) {L : Subgroup X} (hL : IsComponent L) : Cl24Q p R L := by
  obtain rfl := LocalAnalysis.ComponentInitial.CentralQuotientLift.eq_of_isComponent_of_quasisimple
    hS hSX hL
  exact h

theorem cl24_prod {G₁ G₂ : Type} [Group G₁] [Group G₂] [Finite G₁] [Finite G₂] {p : ℕ}
    {R : ℕ → Prop} (h₁ : ∀ M : Subgroup G₁, IsComponent M → Cl24Q p R M)
    (h₂ : ∀ M : Subgroup G₂, IsComponent M → Cl24Q p R M)
    {L : Subgroup (G₁ × G₂)} (hL : IsComponent L) : Cl24Q p R L := by
  rcases LocalAnalysis.ComponentInitial.CentralQuotientLift.fst_eq_or_snd_eq_of_isComponent_prod
      hL with h2 | h1
  · obtain ⟨ρ, hρi, hρc, -⟩ := OddClassSelector.restrict_component (MulEquiv.refl _) hL h2
    exact cl24_of_mulEquiv (MonoidHom.ofInjective hρi) (h₁ _ hρc)
  · obtain ⟨ρ, hρi, hρc, -⟩ := OddClassSelector.restrict_component MulEquiv.prodComm hL h1
    exact cl24_of_mulEquiv (MonoidHom.ofInjective hρi) (h₂ _ hρc)

theorem cl24_of_simple_model {L Y : Type} [Group L] [Group Y] [IsSimpleGroup Y]
    (hnab : ∃ a b : Y, a * b ≠ b * a) (E : L ≃* Y) {t : StatedLieTag} {n p e : ℕ}
    (hadm : StatedLieAdmissible t n p e) (hY : LieModel Y t n p e) {R : ℕ → Prop}
    (hR : R e := by cl24_rel_at) : Cl24Q p R L := by
  have hZ : center Y = ⊥ := ExcSelector.center_eq_bot_of_isSimpleGroup' hnab
  exact cl24_of_mulEquiv E ⟨t, n, e, hR, hadm, LieType.CurtisTits.lieModel_of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm hY⟩

theorem cl24_of_equiv_psl_two {M : Type} [Group M] {F : Type} [Field F] [Finite F] {p e : ℕ}
    (hp : p.Prime) (he : 1 ≤ e) (hF : Nat.card F = p ^ e) (hF2 : Nat.card F ≠ 2)
    (hF3 : Nat.card F ≠ 3) (E : M ⧸ center M ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
    {R : ℕ → Prop} (hR : R e := by cl24_rel_at) : Cl24Q p R M := by
  have hadm : StatedLieAdmissible .PSL 2 p e :=
    ⟨hp, he, le_rfl, fun h => hF2 (hF.trans (Prod.mk.inj h).2),
      fun h => hF3 (hF.trans (Prod.mk.inj h).2)⟩
  exact ⟨.PSL, 2, e, hR, hadm, LieType.CurtisTits.lieModel_of_mulEquiv E.symm
    (Or.inl ⟨by decide, ⟨hadm, F, inferInstance, inferInstance, hF,
      ⟨projectiveSpecialLinearGroupEquivStatedProj 2 F⟩⟩⟩)⟩

@[expose] def Cl24OddFamily (τ : StatedLieTag) : Prop :=
  ∀ (J : Type) [Group J] (n p f : ℕ), p.Prime → p ≠ 2 →
    StatedLieAdmissible τ n p f → LieModel J τ n p f →
    ∀ α : MulAut J, orderOf α = 2 → ∀ K : Subgroup (FixedCommutingProduct.fixedSubgroup α),
      IsComponent K →
      Cl24Q p (Cl24FieldRel f) K ∨
        (p = 3 ∧ LieModel J .G2 0 3 1 ∧ α ∉ (MulAut.conj : J →* MulAut J).range ∧
          LieModel K .PSL 2 2 3)

theorem Cl24OddFamily.tracked {τ : StatedLieTag} (h : Cl24OddFamily τ) : Cl24TrackedFamily τ := by
  intro J _ n f hadm hm α hα K hK
  rcases h J n 3 f Nat.prime_three (by decide) hadm hm α hα K hK with h | ⟨-, h1, h2, h3⟩
  · exact Or.inl h
  · exact Or.inr ⟨h1, h2, h3⟩

end CFSG.OddStandard.SmallF3.HypA2Leaves
