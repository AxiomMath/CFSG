module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog516Rows
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB516LeafRed
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB516LeafModel
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aOddQuotIso
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X10RecChar
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitN36OddChar
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX10SpCard
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.ClassicalGroups
public import CFSG.GH74.GLS.Classes
public import CFSG.GH74.Generic.Shapes
public import CFSG.GH74.Statements
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OrdU2
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog516Pump
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitKGFieldClass
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma36Inputs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitN36MType
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitStatement412
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCriticalStandard
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
public import CFSG.LocalAnalysis.SectionRank.BruhatLift
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
public import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearStep
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SLTwo
public import CFSG.LocalAnalysis.SectionRank.LargeReeCover
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.Open.GorensteinHaradaSectionalRankFourMilestoneDefs
public import CFSG.Open.QuasithinDefs
public import CFSG.Sporadic.Schreier.TitsOther
public import CFSG.Sporadic.SmallOddCore.HSAut
public import CFSG.Sporadic.SmallOddCore.J2
public import CFSG.Sporadic.SmallOddCore.J3Aut
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus

public section

namespace CFSG.ComponentClassification.GSThmB.Pump516

open CFSG Subgroup CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

variable {S : Type} [Group S] [Finite S]

omit [Finite S] in
theorem orderOf_conj_eq_two (hZ : center S = ⊥) {t : S} (ht : orderOf t = 2) :
    orderOf (MulAut.conj t) = 2 := by
  have htt : t ^ 2 = 1 := ht ▸ pow_orderOf_eq_one t
  refine orderOf_eq_prime (by rw [← map_pow, htt, map_one]) fun h1 => ?_
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ht
    omega
  refine ht1 (mem_bot.mp (hZ ▸ mem_center_iff.mpr fun g => ?_))
  have h2 := congrArg (fun φ : MulAut S => φ g) h1
  simp only [MulAut.conj_apply, MulAut.one_apply] at h2
  calc g * t = t * g * t⁻¹ * t := by rw [h2]
    _ = t * g := by group

theorem fixed_component_data (hQ : FixedTwoComponentsQuasisimple S) {α : MulAut S}
    (hα2 : α * α = 1) (hα1 : α ≠ 1) {M : Subgroup S} (hMα : M ≤ fixedSubgroup α)
    (hM : IsPComponent 2 (M.subgroupOf (fixedSubgroup α)))
    (hs : IsSimpleGroup (M ⧸ pPrimeCore 2 M)) :
    IsComponent (M.subgroupOf (fixedSubgroup α)) ∧
      (∀ z ∈ M.subgroupOf (fixedSubgroup α),
        (∀ y ∈ M.subgroupOf (fixedSubgroup α), z * y = y * z) → z * z = 1 → z = 1) ∧
      Nonempty (↥(M.subgroupOf (fixedSubgroup α)) ⧸ center ↥(M.subgroupOf (fixedSubgroup α)) ≃*
        M ⧸ pPrimeCore 2 M) := by
  set Mt := M.subgroupOf (fixedSubgroup α) with hMt
  have hq : IsQuasisimple Mt := hQ α hα2 hα1 Mt hM
  have hsub : Mt.IsSubnormal := by
    obtain ⟨-, -, h, -, -⟩ := hM
    exact h
  let e : Mt ≃* M := subgroupOfEquivOfLe hMα
  let eO : Mt ⧸ pPrimeCore 2 Mt ≃* M ⧸ pPrimeCore 2 M :=
    CatalogueBAlternating.primeCoreQuotientEquiv 2 e
  have hs' : IsSimpleGroup (Mt ⧸ pPrimeCore 2 Mt) := eO.isSimpleGroup
  have hZO := X10Rec.center_eq_pPrimeCore hq hs'
  refine ⟨⟨hq, hsub⟩, fun z hzL hzc hzz => ?_,
    ⟨(QuotientGroup.quotientMulEquivOfEq hZO).trans eO⟩⟩
  exact congrArg Subtype.val (CatLeafProof.X10Sp.eq_one_of_mem_center hZO (z := ⟨z, hzL⟩)
    (mem_center_iff.2 fun y => Subtype.ext (hzc y y.2).symm) (Subtype.ext hzz))

theorem lieModel_center_of_fixed {M : Type} [Group M] {Q : Type} [Group Q]
    (e : M ⧸ center M ≃* Q) {τ : StatedLieTag} {n p f : ℕ} (h : Blueprint.LieModel Q τ n p f) :
    Blueprint.LieModel (M ⧸ center M) τ n p f :=
  OddQuot.lieModel_of_equiv e.symm h

theorem char_eq_of_psl_two_sq
    {X : Type} [Group X] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    {τ : StatedLieTag} {n r e : ℕ} (hr2 : r ≠ 2) (hX : Blueprint.LieModel X .PSL 2 p (2 * f))
    (hX' : Blueprint.LieModel X τ n r e) : r = p := by
  have h9 : 9 ≤ p ^ (2 * f) :=
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ p ^ 2 := Nat.pow_le_pow_left (by have := hp.two_le; omega) 2
      _ ≤ p ^ (2 * f) := Nat.pow_le_pow_right hp.pos (by omega)
  exact HarrisLit.N36.OddChar.pslTwoOddCharacteristicFact_holds X p (2 * f) τ n r e hp hp2
    (by omega) hr2 hX hX'

end CFSG.ComponentClassification.GSThmB.Pump516
