module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LayerSimple
public import CFSG.Open.StatedDefs
import CFSG.RankThree.PartOne.KC.OrthogonalDerivedInLayer
import CFSG.LocalAnalysis.ComponentInitial.TwoPrimeSolvable
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Assembly.QuasithinDefs
public import CFSG.CharacterTheory.Wreathed.BrauerWongTypes
public import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
public import CFSG.ClassicalInvolution.Balance.LocalBalance.Faithful
public import CFSG.Dihedral.DihedralFusionPrefixes
public import CFSG.Foundations
public import CFSG.HardMathSupport.Solomon.Coordinator.B3FamPC
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma28
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
public import CFSG.HardMathSupport.Timmesfeld.Proving.ExistsOrderPCentralizer
public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPrimeCoreCentralizer
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
public import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
public import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.KProper
public import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.ComponentInitial.PerfectOuterInjection
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.LargeEvenClassification.TopScalarLiftSquare
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.IG1114
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremB
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremC
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.ZJTheorem
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GW1965RemarkDGroup
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29Helpers
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFourSplitQuotient
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsDomain
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
import CFSG.RankThree.PartOne.KC.OrthogonalEvenMinusExtraction
import CFSG.RankThree.PartOne.KC.OrthogonalInnerPlane
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Pointwise

section Abstract

variable {G : Type*} [Group G]

private theorem perfect_le_of_le_sup_solvable {C E S P : Subgroup G} (hEC : E ≤ C) (hSC : S ≤ C)
    (hEn : ∀ c ∈ C, ∀ e ∈ E, c * e * c⁻¹ ∈ E) [Group.IsSolvable S] (hcomm : ⁅C, C⁆ ≤ E ⊔ S)
    (hPC : P ≤ C) (hP : ⁅P, P⁆ = P) : P ≤ E := by
  have hPX : P ≤ E ⊔ S := by
    calc P = ⁅P, P⁆ := hP.symm
      _ ≤ ⁅C, C⁆ := Subgroup.commutator_mono hPC hPC
      _ ≤ E ⊔ S := hcomm
  have hXC : E ⊔ S ≤ C := sup_le hEC hSC
  haveI : (E.subgroupOf (E ⊔ S)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff le_sup_left]
    intro e k he hk
    exact hEn k (hXC hk) e he
  have hS : S ≤ Subgroup.normalizer E := by
    intro s hs
    rw [Subgroup.mem_normalizer_iff]
    intro e
    refine ⟨fun he => hEn s (hSC hs) e he, fun he' => ?_⟩
    have := hEn s⁻¹ (inv_mem (hSC hs)) _ he'
    simpa [mul_assoc] using this
  have hmul := Subgroup.coe_mul_of_right_le_normalizer_left E S hS
  have hsol : Group.IsSolvable (↥(E ⊔ S) ⧸ E.subgroupOf (E ⊔ S)) := by
    let φ : ↥S →* ↥(E ⊔ S) ⧸ E.subgroupOf (E ⊔ S) :=
      (QuotientGroup.mk' (E.subgroupOf (E ⊔ S))).comp (Subgroup.inclusion le_sup_right)
    refine Group.isSolvable_of_surjective (f := φ) ?_
    intro y
    induction y using QuotientGroup.induction_on with
    | H g =>
      have hg : (g : G) ∈ ((E : Set G) * (S : Set G)) := by
        rw [← hmul]
        exact g.2
      obtain ⟨e, he, s, hs, hes⟩ := hg
      refine ⟨⟨s, hs⟩, ?_⟩
      show QuotientGroup.mk (Subgroup.inclusion le_sup_right ⟨s, hs⟩) = QuotientGroup.mk g
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      have h1 := hEn s⁻¹ (inv_mem (hSC hs)) e he
      rw [inv_inv] at h1
      have h2 : (((Subgroup.inclusion le_sup_right ⟨s, hs⟩)⁻¹ * g : ↥(E ⊔ S)) : G) =
          s⁻¹ * e * s := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion]
        rw [← hes, mul_assoc]
      rw [h2]
      exact h1
  exact perfect_le_of_solvable_quotient (le_sup_left : E ≤ E ⊔ S) hsol hPX hP

end Abstract

section Commuting

variable {G : Type*} [Group G]

private theorem isSolvable_pi_of_finite_index {ι : Type*} [Finite ι] {H : ι → Type*}
    [∀ i, Group (H i)] [∀ i, Group.IsSolvable (H i)] : Group.IsSolvable (∀ i, H i) := by
  cases nonempty_fintype ι
  have hle : ∀ m : ℕ, derivedSeries (∀ i, H i) m ≤
      Subgroup.pi Set.univ (fun i => derivedSeries (H i) m) := by
    intro m
    induction m with
    | zero =>
      simp only [derivedSeries_zero]
      rw [Subgroup.pi_top]
    | succ m ih =>
      rw [derivedSeries_succ]
      calc ⁅derivedSeries (∀ i, H i) m, derivedSeries (∀ i, H i) m⁆
          ≤ ⁅Subgroup.pi Set.univ (fun i => derivedSeries (H i) m),
              Subgroup.pi Set.univ (fun i => derivedSeries (H i) m)⁆ :=
            Subgroup.commutator_mono ih ih
        _ ≤ Subgroup.pi Set.univ (fun i => ⁅derivedSeries (H i) m, derivedSeries (H i) m⁆) :=
            Subgroup.commutator_pi_pi_le _ _
        _ = Subgroup.pi Set.univ (fun i => derivedSeries (H i) (m + 1)) := by
            simp_rw [derivedSeries_succ]
  choose d hd using fun i => (inferInstance : Group.IsSolvable (H i)).solvable
  refine ⟨⟨Finset.univ.sup d, ?_⟩⟩
  rw [eq_bot_iff]
  refine (hle _).trans ?_
  rw [le_bot_iff, Subgroup.pi_eq_bot_iff]
  intro i
  rw [eq_bot_iff, ← hd i]
  exact derivedSeries_antitone (H i) (Finset.le_sup (f := d) (Finset.mem_univ i))

private theorem isSolvable_iSup_of_commute {ι : Type*} [Finite ι] (H : ι → Subgroup G)
    (hcomm : Pairwise fun i j : ι => ∀ x y : G, x ∈ H i → y ∈ H j → Commute x y)
    (hsol : ∀ i, Group.IsSolvable ↥(H i)) : Group.IsSolvable ↥(⨆ i, H i) := by
  classical
  cases nonempty_fintype ι
  haveI := hsol
  haveI : Group.IsSolvable (∀ i, ↥(H i)) := isSolvable_pi_of_finite_index
  have h1 : Group.IsSolvable ↥(Subgroup.noncommPiCoprod hcomm).range :=
    Group.isSolvable_of_surjective (Subgroup.noncommPiCoprod hcomm).rangeRestrict_surjective
  rwa [Subgroup.noncommPiCoprod_range] at h1

private theorem commute_of_mem_iSup {ι : Type*} (a b : ι → Subgroup G)
    (h : ∀ i j, ∀ x ∈ a i, ∀ y ∈ b j, Commute x y) :
    ∀ x ∈ ⨆ i, a i, ∀ y ∈ ⨆ j, b j, Commute x y := by
  intro x hx y hy
  refine Subgroup.iSup_induction a (C := fun x => Commute x y) hx
    (fun i x hxi => ?_) (Commute.one_left _) fun x₁ x₂ h₁ h₂ => h₁.mul_left h₂
  exact Subgroup.iSup_induction b (C := fun y => Commute x y) hy
    (fun j y hyj => h i j x hxi y hyj) (Commute.one_right _) fun y₁ y₂ h₁ h₂ => h₁.mul_right h₂

end Commuting

section Blocks

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.LocalAnalysis.ComponentInitial

variable {K : Type} [Field K] [Finite K] {V : Type*} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

private theorem isQuasisimple_specialBlock_of_paired (hx : OddOrderIsometry Q p x) (hp : p.Prime)
    (hp2 : p ≠ 2) {h : K[X]} [Fact (Irreducible h)] (hh : h ∈ primaryFactors x.toLinearMap)
    (hne1 : h ≠ X - 1) (hne : h ≠ reciprocalPolynomial h)
    (hm : 2 ≤ primaryMultiplicity x.toLinearMap h) : CFSG.IsQuasisimple ↥(specialBlock Q x h) := by
  have h4 : 4 ≤ Nat.card (AdjoinRoot h) := by
    have := hx.p_lt_card_adjoinRoot hp hh hne1
    have := hp.two_le
    omega
  let b : Module.Basis (Fin (primaryMultiplicity x.toLinearMap h)) (AdjoinRoot h)
      (primaryComponent x.toLinearMap h) := Module.finBasisOfFinrankEq _ _ rfl
  let e₁ : ↥(specialBlock Q x h) ≃*
      SpecialLinearGroup (AdjoinRoot h) (primaryComponent x.toLinearMap h) :=
    MulEquiv.ofBijective (specialToSL Q x h)
      ⟨hx.specialToSL_injective hh, hx.specialToSL_surjective_paired hh hne⟩
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
    ((Matrix.SpecialLinearGroup.toLin_equiv b).trans e₁.symm)
    (CFSG.RankThree.CALinearPlane.isQuasisimple_SL_of_two_le hm h4)

private theorem quasisimple_or_solvable_specialBlock_selfDual (hx : OddOrderIsometry Q p x)
    (hp : p.Prime) (hp2 : p ≠ 2) {h : K[X]} [Fact (Irreducible h)]
    (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1)
    (hself : h = reciprocalPolynomial h) (hm : 2 ≤ primaryMultiplicity x.toLinearMap h) :
    CFSG.IsQuasisimple ↥(specialBlock Q x h) ∨ Group.IsSolvable ↥(specialBlock Q x h) := by
  classical
  have hp2' : Odd p := hp.odd_of_ne_two hp2
  have hirr := irreducible_of_mem_primaryFactors hh
  obtain ⟨d, H, hdeg, hroot, hH, hadd1, hadd2, hleft, hright, hsymm⟩ :=
    hx.exists_selfDual_hermitian hp2' hh hne1 hself
  have hd : finrank K (AdjoinRoot h) = 2 * d := by
    rw [(AdjoinRoot.powerBasis hirr.ne_zero).finrank, AdjoinRoot.powerBasis_dim, hdeg]
  obtain ⟨ℓ, f, hU, hq, hbar⟩ := exists_unitaryFieldData K (AdjoinRoot h) hd
  have hbar' : ∀ z, frobPow K (AdjoinRoot h) d z = hU.bar z := fun z => by
    rw [hbar, frobPow_apply]
  let B : primaryComponent x.toLinearMap h →ₛₗ[hU.bar]
      primaryComponent x.toLinearMap h →ₗ[AdjoinRoot h] AdjoinRoot h :=
    LinearMap.mk₂'ₛₗ hU.bar (RingHom.id _) H hadd1
      (fun c u w => by rw [hleft, smul_eq_mul, hbar']) hadd2
      (fun c u w => by rw [hright, smul_eq_mul, RingHom.id_apply])
  have hBH : ∀ u w, B u w = H u w := fun u w => rfl
  have hBsymm : B.IsSymm := ⟨fun u w => by rw [hBH, hBH, hsymm u w, hbar']⟩
  have hBl : B.SeparatingLeft := by
    intro u hu
    refine Subtype.ext (hx.eq_zero_of_polar_selfdual hh hself u.2 fun w hw => ?_)
    have h1 := hH u ⟨w, hw⟩ 1
    rw [mul_one, one_smul] at h1
    have h2 : H u ⟨w, hw⟩ = 0 := by rw [← hBH]; exact hu _
    rw [h2, map_zero] at h1
    exact h1.symm
  have hrange : (specialBlockGL Q x h).range = sesqSpecialUnitaryGroup B := by
    rw [range_specialBlockGL, sesqSpecialUnitaryGroup]
    congr 1
    ext γ
    rw [hx.mem_range_blockGL_selfDual_iff hh hne1 hself H hH, mem_sesqUnitaryGroup]
    exact Iff.rfl
  have hd0 : d ≠ 0 := by
    rintro rfl
    have : 0 < finrank K (AdjoinRoot h) := Module.finrank_pos
    omega
  have hQ2 : 2 ≤ ℓ ^ (f * d) := by
    have h1 : Nat.card K ^ d = ℓ ^ (f * d) := by rw [hq, pow_mul]
    have h2 : Nat.card K ≤ Nat.card K ^ d := Nat.le_self_pow hd0 _
    have h3 : 1 < Nat.card K := Finite.one_lt_card
    omega
  let e₁ : ↥(specialBlock Q x h) ≃* ↥(sesqSpecialUnitaryGroup B) :=
    (MonoidHom.ofInjective (hx.specialBlockGL_injective hh)).trans
      (MulEquiv.subgroupCongr hrange)
  have hm' : finrank (AdjoinRoot h) (primaryComponent x.toLinearMap h) =
      primaryMultiplicity x.toLinearMap h := rfl
  by_cases hexc : (primaryMultiplicity x.toLinearMap h = 2 ∧ ℓ ^ (f * d) = 2) ∨
      (primaryMultiplicity x.toLinearMap h = 2 ∧ ℓ ^ (f * d) = 3) ∨
      (primaryMultiplicity x.toLinearMap h = 3 ∧ ℓ ^ (f * d) = 2)
  · right
    have hcard := (CFSG.LinearGroups.unitary_full_group_order hU hBsymm hBl hm' (by omega)).2.1
    have : Finite V := Module.finite_of_finite K
    have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
      fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
    have hsolv : Group.IsSolvable ↥(sesqSpecialUnitaryGroup B) := by
      have hfin : Finite ↥(sesqSpecialUnitaryGroup B) := Finite.of_equiv _ e₁.toEquiv
      refine isSolvable_of_card_primeFactors_le_two ?_
      rcases hexc with ⟨hm2, hQ⟩ | ⟨hm2, hQ⟩ | ⟨hm2, hQ⟩
      · rw [hm2, hQ] at hcard
        have e : ((2 : ℕ) : ℤ) ^ (2 * (2 - 1) / 2) *
            ∏ i ∈ Finset.Icc 2 2, (((2 : ℕ) : ℤ) ^ i - (-1) ^ i) = 6 := by decide +kernel
        have h6 : Nat.card ↥(sesqSpecialUnitaryGroup B) = 6 := by exact_mod_cast hcard.trans e
        rw [h6]
        decide +kernel
      · rw [hm2, hQ] at hcard
        have e : ((3 : ℕ) : ℤ) ^ (2 * (2 - 1) / 2) *
            ∏ i ∈ Finset.Icc 2 2, (((3 : ℕ) : ℤ) ^ i - (-1) ^ i) = 24 := by decide +kernel
        have h24 : Nat.card ↥(sesqSpecialUnitaryGroup B) = 24 := by exact_mod_cast hcard.trans e
        rw [h24]
        decide +kernel
      · rw [hm2, hQ] at hcard
        have e : ((2 : ℕ) : ℤ) ^ (3 * (3 - 1) / 2) *
            ∏ i ∈ Finset.Icc 2 3, (((2 : ℕ) : ℤ) ^ i - (-1) ^ i) = 216 := by decide +kernel
        have h216 : Nat.card ↥(sesqSpecialUnitaryGroup B) = 216 := by
          exact_mod_cast hcard.trans e
        rw [h216]
        decide +kernel
    haveI := hsolv
    exact Group.isSolvable_of_isSolvable_injective (f := e₁.toMonoidHom) e₁.injective
  · left
    refine CFSG.LocalCores.isQuasisimple_of_mulEquiv e₁.symm ?_
    rcases Nat.lt_or_ge (primaryMultiplicity x.toLinearMap h) 3 with h2 | h3
    · have hm2 : finrank (AdjoinRoot h) (primaryComponent x.toLinearMap h) = 2 := by
        have : primaryMultiplicity x.toLinearMap h = 2 := by omega
        exact this
      have hq4 : 4 ≤ ℓ ^ (f * d) := by
        by_contra hlt
        have h22 : primaryMultiplicity x.toLinearMap h = 2 := by omega
        have : ℓ ^ (f * d) = 2 ∨ ℓ ^ (f * d) = 3 := by omega
        rcases this with h' | h'
        · exact hexc (Or.inl ⟨h22, h'⟩)
        · exact hexc (Or.inr (Or.inl ⟨h22, h'⟩))
      exact CFSG.RankThree.Classical.isQuasisimple_sesqSpecialUnitaryGroup hU hBsymm hBl hm2 hq4
    · have hn3 : (finrank (AdjoinRoot h) (primaryComponent x.toLinearMap h),
          ℓ ^ (f * d)) ≠ (3, 2) := by
        intro e
        have h1 := congrArg Prod.fst e
        have h2 := congrArg Prod.snd e
        simp only at h1 h2
        exact hexc (Or.inr (Or.inr ⟨h1, h2⟩))
      exact isQuasisimple_sesqSpecialUnitaryGroup_of_three_le hU hBsymm hBl h3 hn3

private theorem quasisimple_or_solvable_specialBlock (hx : OddOrderIsometry Q p x)
    (hp : p.Prime) (hp2 : p ≠ 2) {h : K[X]} (hh : h ∈ primaryFactors x.toLinearMap)
    (hne1 : h ≠ X - 1) :
    CFSG.IsQuasisimple ↥(specialBlock Q x h) ∨ Group.IsSolvable ↥(specialBlock Q x h) := by
  have : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  by_cases hm : 2 ≤ primaryMultiplicity x.toLinearMap h
  · by_cases hself : h = reciprocalPolynomial h
    · exact quasisimple_or_solvable_specialBlock_selfDual hx hp hp2 hh hne1 hself hm
    · exact Or.inl (isQuasisimple_specialBlock_of_paired hx hp hp2 hh hne1 hself hm)
  · right
    have hpos := hx.primaryMultiplicity_pos hh
    have h1 : primaryMultiplicity x.toLinearMap h = 1 := by omega
    rw [hx.specialBlock_eq_bot_of_finrank_eq_one hh h1]
    infer_instance

end Blocks

section Fixed

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.Classical2 CFSG.LocalAnalysis.ComponentInitial

private theorem isSolvable_orthogonalGroup_of_smallFixedException {K : Type} [Field K] [Finite K]
    {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W] (R : QuadraticForm K W)
    (hR : (QuadraticMap.polarBilin R).Nondegenerate) (h3 : 3 ≤ finrank K W)
    (hS : SmallFixedException R) : Group.IsSolvable ↥(TauCeti.QuadraticMap.orthogonalGroup R) := by
  classical
  have : Finite W := Module.finite_of_finite K
  have : Finite (W ≃ₗ[K] W) := Finite.of_injective (fun e : W ≃ₗ[K] W => (e : W → W))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  have hno := (orthogonal_regular_space_coverage R hR h3).1 hS
  refine isSolvable_of_card_primeFactors_le_two ?_
  have hsub : (Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup R)).primeFactors ⊆ {2, 3} := by
    intro r hr
    have hrp : r.Prime := Nat.prime_of_mem_primeFactors hr
    have hdvd : r ∣ Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup R) :=
      Nat.dvd_of_mem_primeFactors hr
    haveI : Fact r.Prime := ⟨hrp⟩
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' r hdvd
    by_contra hne
    have h3r : 3 < r := by
      have h2 := hrp.two_le
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hne
      omega
    exact hno g r hrp h3r hg
  exact (Finset.card_le_card hsub).trans Finset.card_le_two

variable {K : Type} [Field K] [Finite K] {V : Type*} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

private theorem isSolvable_supportedFixedDerived_of_smallFixedException
    (hx : OddOrderIsometry Q p x) (h3 : 3 ≤ finrank K (fixedSpace x))
    (hS : SmallFixedException (Q.comp (fixedSpace x).subtype)) :
    Group.IsSolvable ↥(supportedFixedDerived Q x) := by
  haveI := isSolvable_orthogonalGroup_of_smallFixedException (Q.comp (fixedSpace x).subtype)
    hx.polarBilin_fixed_nondegenerate h3 hS
  have hle : orthDerived (Q.comp (fixedSpace x).subtype) ≤
      TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype) :=
    orthDerived_le_orthogonalGroup
  haveI : Group.IsSolvable ↥(orthDerived (Q.comp (fixedSpace x).subtype)) :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle)
  exact Group.isSolvable_of_isSolvable_injective (f := (supportedFixedDerivedEquiv hx).toMonoidHom)
    (supportedFixedDerivedEquiv hx).injective

private theorem X_sub_one_mem_rep (hx : OddOrderIsometry Q p x) {Rep : Finset K[X]}
    (hRep : IsOrbitRepresentatives x Rep) (h1 : 1 ≤ finrank K (fixedSpace x)) :
    (X - 1 : K[X]) ∈ Rep := by
  have hmem : (X - 1 : K[X]) ∈ primaryFactors x.toLinearMap := by
    by_contra hnot
    have := fixedSpace_eq_bot_of_not_mem hnot
    rw [this, finrank_bot] at h1
    omega
  obtain ⟨r, ⟨hr, hXr⟩, -⟩ := hRep.2 _ hmem
  rcases hXr with h | h
  · rw [h]
    exact hr
  · have h2 := hx.reciprocal_reciprocal_eq (hRep.1 hr)
    rw [← h, reciprocalPolynomial_X_sub_one] at h2
    rw [h2]
    exact hr

end Fixed

section Derived

open Polynomial Module CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal
  CFSG.LocalAnalysis.ComponentInitial

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

private theorem exists_solvable_comm_le
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (x : orthDerived Q)
    (hx : OddOrderIsometry Q p (x : V ≃ₗ[K] V))
    {Rep : Finset K[X]} (hRep : IsOrbitRepresentatives (x : V ≃ₗ[K] V) Rep)
    (EN : Subgroup (ProjOrthDerived Q))
    (hJ : ∀ h ∈ Rep, h ≠ X - 1 → CFSG.IsQuasisimple ↥(specialBlock Q (x : V ≃ₗ[K] V) h) →
      componentImage Q (x : V ≃ₗ[K] V) h ≤ EN)
    (hfix : FixedLayerListed Q (x : V ≃ₗ[K] V) → fixedComponentImage Q (x : V ≃ₗ[K] V) ≤ EN) :
    ∃ S₀ : Subgroup (ProjOrthDerived Q), S₀ ≤ centralizerImage Q (x : V ≃ₗ[K] V) ∧
      Group.IsSolvable ↥S₀ ∧
      ⁅centralizerImage Q (x : V ≃ₗ[K] V), centralizerImage Q (x : V ≃ₗ[K] V)⁆ ≤ EN ⊔ S₀ := by
  classical
  have hp2' : Odd p := hp.odd_of_ne_two hp2
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  set xe : V ≃ₗ[K] V := (x : V ≃ₗ[K] V) with hxe
  set ρ : ↥(orthDerived Q) →* ProjOrthDerived Q :=
    QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)) with hρ
  set Mo : Subgroup ↥(orthDerived Q) := (isometryCentralizer Q xe).subgroupOf (orthDerived Q)
    with hMo
  set Jf : Subgroup (V ≃ₗ[K] V) :=
    if 3 ≤ finrank K (fixedSpace xe) ∧ SmallFixedException (Q.comp (fixedSpace xe).subtype)
      then supportedFixedDerived Q xe else ⊥ with hJf
  have hJfB : Jf ≤ supportedBlock Q xe (X - 1) := by
    rw [hJf]
    split_ifs
    · exact supportedFixedDerived_le_supportedBlock
    · exact bot_le
  have hJfsol : Group.IsSolvable ↥Jf := by
    by_cases h : 3 ≤ finrank K (fixedSpace xe) ∧
        SmallFixedException (Q.comp (fixedSpace xe).subtype)
    · have e : Jf = supportedFixedDerived Q xe := by simp only [hJf, if_pos h]
      rw [e]
      exact isSolvable_supportedFixedDerived_of_smallFixedException hx h.1 h.2
    · have e : Jf = ⊥ := by simp only [hJf, if_neg h]
      rw [e]
      infer_instance
  set G : ↥Rep → Subgroup (V ≃ₗ[K] V) := fun r =>
    if r.1 = X - 1 then Jf
    else if CFSG.IsQuasisimple ↥(specialBlock Q xe r.1) then ⊥ else specialBlock Q xe r.1
    with hG
  have hGB : ∀ r : ↥Rep, G r ≤ supportedBlock Q xe r.1 := by
    intro r
    simp only [hG]
    split_ifs with h1 h2
    · rw [h1]
      exact hJfB
    · exact bot_le
    · exact specialBlock_le_supportedBlock r.1
  have hGsol : ∀ r : ↥Rep, Group.IsSolvable ↥(G r) := by
    intro r
    by_cases h1 : r.1 = X - 1
    · have e : G r = Jf := by simp only [hG, if_pos h1]
      rw [e]
      exact hJfsol
    · by_cases h2 : CFSG.IsQuasisimple ↥(specialBlock Q xe r.1)
      · have e : G r = ⊥ := by simp only [hG, if_neg h1, if_pos h2]
        rw [e]
        infer_instance
      · have e : G r = specialBlock Q xe r.1 := by simp only [hG, if_neg h1, if_neg h2]
        rw [e]
        exact (quasisimple_or_solvable_specialBlock hx hp hp2 (hRep.1 r.2) h1).resolve_left h2
  set Sg : Subgroup (V ≃ₗ[K] V) := ⨆ r, G r with hSg
  have hSgM : Sg ≤ isometryCentralizer Q xe :=
    iSup_le fun r => (hGB r).trans (supportedBlock_le_isometryCentralizer _)
  have hSgsol : Group.IsSolvable ↥Sg :=
    isSolvable_iSup_of_commute G (fun r s hrs g g' hg hg' =>
      hx.blocks_commute hRep hrs g g' (hGB r hg) (hGB s hg')) hGsol
  set S₀ : Subgroup (ProjOrthDerived Q) := (Sg.subgroupOf (orthDerived Q)).map ρ with hS₀
  have hS₀le : S₀ ≤ centralizerImage Q xe := by
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨u, Subgroup.mem_subgroupOf.mpr (hSgM (Subgroup.mem_subgroupOf.mp hu)), rfl⟩
  have hS₀sol : Group.IsSolvable ↥S₀ := by
    haveI : Group.IsSolvable ↥(Sg.subgroupOf (orthDerived Q)) :=
      Group.isSolvable_of_isSolvable_injective
        (f := ((orthDerived Q).subtype.comp (Sg.subgroupOf (orthDerived Q)).subtype).codRestrict Sg
          (fun u => u.2))
        (fun u v h => by
          have h' := congrArg Subtype.val h
          exact Subtype.ext (Subtype.ext h'))
    exact Group.isSolvable_of_surjective (ρ.subgroupMap_surjective (Sg.subgroupOf (orthDerived Q)))
  refine ⟨S₀, hS₀le, hS₀sol, ?_⟩
  set Aterm : ↥Rep → Subgroup (V ≃ₗ[K] V) := fun r =>
    if r.1 ≠ X - 1 ∧ CFSG.IsQuasisimple ↥(specialBlock Q xe r.1) then specialBlock Q xe r.1 else ⊥
    with hAterm
  set Bterm : ↥Rep → Subgroup (V ≃ₗ[K] V) := fun r =>
    if r.1 ≠ X - 1 ∧ ¬ CFSG.IsQuasisimple ↥(specialBlock Q xe r.1) then specialBlock Q xe r.1
      else ⊥ with hBterm
  have hAle : ∀ r : ↥Rep, Aterm r ≤ supportedBlock Q xe r.1 := by
    intro r
    simp only [hAterm]
    split_ifs
    · exact specialBlock_le_supportedBlock r.1
    · exact bot_le
  have hBle : ∀ r : ↥Rep, Bterm r ≤ supportedBlock Q xe r.1 := by
    intro r
    simp only [hBterm]
    split_ifs
    · exact specialBlock_le_supportedBlock r.1
    · exact bot_le
  have hBG : ∀ r : ↥Rep, Bterm r ≤ G r := by
    intro r
    simp only [hBterm]
    split_ifs with h1
    · have e : G r = specialBlock Q xe r.1 := by simp only [hG, if_neg h1.1, if_neg h1.2]
      rw [e]
    · exact bot_le
  have hAB : ∀ r s : ↥Rep, ∀ u ∈ Aterm r, ∀ v ∈ Bterm s, Commute u v := by
    intro r s u hu v hv
    by_cases hrs : r = s
    · subst hrs
      by_cases hq : CFSG.IsQuasisimple ↥(specialBlock Q xe r.1)
      · have e : Bterm r = ⊥ := by
          simp only [hBterm]
          rw [if_neg (fun h => h.2 hq)]
        rw [e, Subgroup.mem_bot] at hv
        rw [hv]
        exact Commute.one_right _
      · have e : Aterm r = ⊥ := by
          simp only [hAterm]
          rw [if_neg (fun h => hq h.2)]
        rw [e, Subgroup.mem_bot] at hu
        rw [hu]
        exact Commute.one_left _
    · exact hx.blocks_commute hRep hrs u v (hAle r hu) (hBle s hv)
  set A : Subgroup (V ≃ₗ[K] V) := ⨆ r, Aterm r with hA
  set B : Subgroup (V ≃ₗ[K] V) := ⨆ r, Bterm r with hB
  have hBSg : B ≤ Sg := iSup_le fun r => (hBG r).trans (le_iSup G r)
  have hspAB : specialProduct Q xe Rep ≤ A ⊔ B := by
    refine iSup₂_le fun h hh => iSup_le fun hne => ?_
    by_cases hq : CFSG.IsQuasisimple ↥(specialBlock Q xe h)
    · refine le_sup_of_le_left (le_iSup_of_le ⟨h, hh⟩ ?_)
      simp only [hAterm]
      rw [if_pos ⟨hne, hq⟩]
    · refine le_sup_of_le_right (le_iSup_of_le ⟨h, hh⟩ ?_)
      simp only [hBterm]
      rw [if_pos ⟨hne, hq⟩]
  set K₀ : Subgroup (V ≃ₗ[K] V) := (EN.comap ρ).map (orthDerived Q).subtype with hK₀
  have hAK : ∀ r : ↥Rep, Aterm r ≤ K₀ := by
    intro r
    simp only [hAterm]
    split_ifs with hc
    · intro u hu
      have hFΩ : specialBlock Q xe r.1 ≤ orthDerived Q :=
        specialBlock_le_orthDerived_of_perfect hc.2.1
          ((specialBlock_le_isometryCentralizer r.1).trans
            (fun _ hg => (Subgroup.mem_inf.mp hg).1))
      refine ⟨⟨u, hFΩ hu⟩, ?_, rfl⟩
      show ρ ⟨u, hFΩ hu⟩ ∈ EN
      exact hJ r.1 r.2 hc.1 hc.2 ⟨⟨u, hFΩ hu⟩, Subgroup.mem_subgroupOf.mpr hu, rfl⟩
    · exact bot_le
  have hAK' : A ≤ K₀ := iSup_le hAK
  have hspM : specialProduct Q xe Rep ≤ isometryCentralizer Q xe :=
    iSup₂_le fun h _ => iSup_le fun _ => specialBlock_le_isometryCentralizer h
  have hBcent : B ≤ Subgroup.centralizer (A : Set (V ≃ₗ[K] V)) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact (commute_of_mem_iSup Aterm Bterm hAB u hu y hy).eq
  have hmulAB : (↑(A ⊔ B) : Set (V ≃ₗ[K] V)) = (A : Set (V ≃ₗ[K] V)) * (B : Set (V ≃ₗ[K] V)) :=
    Subgroup.coe_mul_of_right_le_normalizer_left A B
      (hBcent.trans (Subgroup.centralizer_le_normalizer _))
  have hkey : ⁅Mo, Mo⁆ ≤ (EN ⊔ S₀).comap ρ := by
    rw [Subgroup.commutator_le]
    intro m hm m' hm'
    rw [Subgroup.mem_comap]
    have hmM : (m : V ≃ₗ[K] V) ∈ isometryCentralizer Q xe := Subgroup.mem_subgroupOf.mp hm
    have hm'M : (m' : V ≃ₗ[K] V) ∈ isometryCentralizer Q xe := Subgroup.mem_subgroupOf.mp hm'
    have hg : (((⁅m, m'⁆ : ↥(orthDerived Q))) : V ≃ₗ[K] V) ∈
        ⁅isometryCentralizer Q xe, isometryCentralizer Q xe⁆ :=
      Subgroup.commutator_mem_commutator hmM hm'M
    obtain ⟨f, hf, j, hj, hgjf⟩ := hx.exists_decomposition_of_mem_commutator hRep hg
    have hfΩ : f ∈ orthDerived Q := hx.supportedFixedDerived_le_orthDerived hf
    have hfpart : ρ ⟨f, hfΩ⟩ ∈ EN ⊔ S₀ := by
      by_cases hdim : 3 ≤ finrank K (fixedSpace xe)
      · by_cases hSE : SmallFixedException (Q.comp (fixedSpace xe).subtype)
        · have hXRep := X_sub_one_mem_rep hx hRep (by omega)
          have hfJf : f ∈ Jf := by
            have e : Jf = supportedFixedDerived Q xe := by
              simp only [hJf, if_pos (And.intro hdim hSE)]
            rw [e]
            exact hf
          have hfG : f ∈ G ⟨X - 1, hXRep⟩ := by
            have e : G ⟨X - 1, hXRep⟩ = Jf := by simp only [hG, if_pos rfl]
            rw [e]
            exact hfJf
          exact Subgroup.mem_sup_right ⟨⟨f, hfΩ⟩,
            Subgroup.mem_subgroupOf.mpr (Subgroup.mem_iSup_of_mem _ hfG), rfl⟩
        · exact Subgroup.mem_sup_left (hfix ⟨hdim, hSE⟩
            ⟨⟨f, hfΩ⟩, Subgroup.mem_subgroupOf.mpr hf, rfl⟩)
      · have hdim2 : finrank K (fixedSpace xe) ≤ 2 := by omega
        have hfM : f ∈ isometryCentralizer Q xe :=
          supportedFixedDerived_le_isometryCentralizer hf
        have hjM : j ∈ isometryCentralizer Q xe := hspM hj
        have hgM : (((⁅m, m'⁆ : ↥(orthDerived Q))) : V ≃ₗ[K] V) ∈ isometryCentralizer Q xe := by
          rw [hgjf]
          exact mul_mem hjM hfM
        have h1 : isometryRestrictFixed Q xe
            ⟨(((⁅m, m'⁆ : ↥(orthDerived Q))) : V ≃ₗ[K] V), hgM⟩ = 1 := by
          have h2 : (⟨(((⁅m, m'⁆ : ↥(orthDerived Q))) : V ≃ₗ[K] V), hgM⟩ :
              ↥(isometryCentralizer Q xe)) =
              ⁅(⟨(m : V ≃ₗ[K] V), hmM⟩ : ↥(isometryCentralizer Q xe)),
                (⟨(m' : V ≃ₗ[K] V), hm'M⟩ : ↥(isometryCentralizer Q xe))⁆ :=
            Subtype.ext rfl
          rw [h2, map_commutatorElement]
          exact commutatorElement_eq_one_iff_mul_comm.mpr
            (hx.restrict_commute_of_mem_orthDerived hp2' hQ hRep hdim2 hmM m.2 hm'M m'.2).eq
        have h3 : isometryRestrictFixed Q xe ⟨f, hfM⟩ = 1 := by
          have h4 : (⟨(((⁅m, m'⁆ : ↥(orthDerived Q))) : V ≃ₗ[K] V), hgM⟩ :
              ↥(isometryCentralizer Q xe)) = ⟨j, hjM⟩ * ⟨f, hfM⟩ := Subtype.ext hgjf
          rw [h4, map_mul, hx.restrictFixed_trivial_of_mem_specialProduct hRep hj hjM,
            one_mul] at h1
          exact h1
        have hfB := supportedFixedDerived_le_supportedBlock hf
        have h5 : restrictFixed Q xe ⟨f, hfB⟩ = 1 := by
          rw [← isometryRestrictFixed_restrictFixed]
          exact h3
        have hf1 : f = 1 := hx.eq_one_of_restrictFixed_eq_one hfB h5
        have : (⟨f, hfΩ⟩ : ↥(orthDerived Q)) = 1 := Subtype.ext hf1
        rw [this, map_one]
        exact one_mem _
    obtain ⟨a₀, ha₀, b₀, hb₀, hab⟩ : ∃ a ∈ A, ∃ b ∈ B, a * b = j := by
      have hjmem : j ∈ (↑(A ⊔ B) : Set (V ≃ₗ[K] V)) := hspAB hj
      rw [hmulAB] at hjmem
      exact hjmem
    obtain ⟨aΩ, haρ, haeq⟩ := hAK' ha₀
    have haρ' : ρ aΩ ∈ EN := haρ
    set bΩ : ↥(orthDerived Q) := aΩ⁻¹ * ⁅m, m'⁆ * (⟨f, hfΩ⟩ : ↥(orthDerived Q))⁻¹ with hbΩ
    have hbeq : (bΩ : V ≃ₗ[K] V) = b₀ := by
      have h1 : ((orthDerived Q).subtype aΩ : V ≃ₗ[K] V) = a₀ := haeq
      show ((aΩ : V ≃ₗ[K] V))⁻¹ * (((⁅m, m'⁆ : ↥(orthDerived Q))) : V ≃ₗ[K] V) * f⁻¹ = b₀
      have h2 : (aΩ : V ≃ₗ[K] V) = a₀ := h1
      rw [h2, hgjf, ← hab]
      group
    have hbS : ρ bΩ ∈ S₀ :=
      ⟨bΩ, Subgroup.mem_subgroupOf.mpr (by rw [hbeq]; exact hBSg hb₀), rfl⟩
    have hfac : (⁅m, m'⁆ : ↥(orthDerived Q)) = aΩ * bΩ * ⟨f, hfΩ⟩ := by
      rw [hbΩ]
      group
    rw [hfac, map_mul, map_mul]
    exact mul_mem (mul_mem (Subgroup.mem_sup_left haρ') (Subgroup.mem_sup_right hbS)) hfpart
  show ⁅Mo.map ρ, Mo.map ρ⁆ ≤ EN ⊔ S₀
  rw [← Subgroup.map_commutator]
  exact Subgroup.map_le_iff_le_comap.mpr hkey

end Derived

section Projective

open Polynomial Module CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal

attribute [local instance] CFSG.LocalCores.layer_characteristic

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

private theorem fixSubgroup_conj_eq_centralizer' {X : Type*} [Group X] (x : X) :
    fixSubgroup (MulAut.conj x) = Subgroup.centralizer ({x} : Set X) := by
  ext g
  rw [mem_fixSubgroup, MulAut.conj_apply, mul_inv_eq_iff_eq_mul,
    Subgroup.mem_centralizer_singleton_iff]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

private theorem perfectInLayer_conj_projOrth_of_orderOf
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpl : p ≠ ringChar K)
    (a : ProjOrthDerived Q) (ha : orderOf a = p) : PerfectInLayer (MulAut.conj a) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  obtain ⟨-, -, -, -, -, -, -, -, hlift⟩ :=
    CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hQ hT
  obtain ⟨x, ⟨hxa, hxp⟩, -, hcent⟩ := hlift p hp hp2 a ha
  subst hxa
  have hx := oddOrderIsometry_of_orthDerived hp hpl hQ x hxp
  obtain ⟨Rep, hRep⟩ := hx.exists_orbitRepresentatives
  set xe : V ≃ₗ[K] V := (x : V ≃ₗ[K] V) with hxe
  set N : Subgroup (ProjOrthDerived Q) :=
    fixSubgroup (MulAut.conj (QuotientGroup.mk x : ProjOrthDerived Q)) with hN
  have hNeq : N = centralizerImage Q xe := by
    rw [hN, fixSubgroup_conj_eq_centralizer', hcent]
    exact map_centralizer_eq_centralizerImage x
  set EN : Subgroup (ProjOrthDerived Q) := (CFSG.layer ↥N).map N.subtype with hEN
  have hENN : EN ≤ N := Subgroup.map_subtype_le _
  have hENn : ∀ c ∈ N, ∀ e ∈ EN, c * e * c⁻¹ ∈ EN := by
    have hEN' : EN.subgroupOf N = CFSG.layer ↥N :=
      Subgroup.comap_map_eq_self_of_injective N.subtype_injective _
    haveI : (EN.subgroupOf N).Normal := by
      rw [hEN']
      infer_instance
    exact fun c hc e he => (Subgroup.normal_subgroupOf_iff hENN).mp this e c he hc
  have hcomp : ∀ C : Subgroup (ProjOrthDerived Q), CFSG.IsQuasisimple ↥C → C ≤ N →
      (C.subgroupOf N).IsSubnormal → C ≤ EN := by
    intro C hq hCN hsub
    have hc : CFSG.IsComponent (C.subgroupOf N) :=
      ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hCN).symm hq, hsub⟩
    have h1 := CFSG.LocalCores.component_le_layer hc
    calc C = (C.subgroupOf N).map N.subtype := (Subgroup.map_subgroupOf_eq_of_le hCN).symm
      _ ≤ EN := Subgroup.map_mono h1
  have hJ : ∀ h ∈ Rep, h ≠ X - 1 → CFSG.IsQuasisimple ↥(specialBlock Q xe h) →
      componentImage Q xe h ≤ EN := by
    intro h hh hne hq
    have hFΩ : specialBlock Q xe h ≤ orthDerived Q :=
      specialBlock_le_orthDerived_of_perfect hq.1
        ((specialBlock_le_isometryCentralizer h).trans (fun _ hg => (Subgroup.mem_inf.mp hg).1))
    have hqJ : CFSG.IsQuasisimple ↥(componentImage Q xe h) := isQuasisimple_map_projective hFΩ hq
    refine hcomp _ hqJ ?_ ?_
    · rw [hNeq]
      exact componentImage_le_centralizerImage
    · rw [hNeq]
      exact normal_componentImage.isSubnormal
  have hfix : FixedLayerListed Q xe → fixedComponentImage Q xe ≤ EN := by
    intro hlist
    obtain ⟨n, C, -, -, hsup, hC, -, -⟩ := hx.fixedLayer_data hlist
    rw [← hsup]
    refine iSup_le fun i => hcomp (C i) (hC i).1 ?_ ?_
    · rw [hNeq]
      exact (hC i).2.1
    · rw [hNeq]
      exact (hC i).2.2
  obtain ⟨S₀, hS₀N, hS₀sol, hcomm⟩ := exists_solvable_comm_le hQ hp hp2 x hx hRep EN hJ hfix
  have hS₀N' : S₀ ≤ N := by
    rw [hNeq]
    exact hS₀N
  have hcomm' : ⁅N, N⁆ ≤ EN ⊔ S₀ := by
    rw [hNeq]
    exact hcomm
  intro P hPC hP
  haveI := hS₀sol
  exact (perfect_le_of_le_sup_solvable hENN hS₀N' hENn hcomm' hPC hP).trans
    (map_layer_le_glaLayer N)

private noncomputable def omegaOrthEquiv {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] {Q : QuadraticForm K (ι → K)} {Q₀ : (ι → K) → K} (hQ : ⇑Q = Q₀) :
    StatedOmega Q₀ ≃* orthDerived Q :=
  ((toLinEquiv ι K).subgroupMap (StatedOmega Q₀)).trans (MulEquiv.subgroupCongr (by
    rw [statedOmega_eq_comap hQ]
    exact Subgroup.map_comap_eq_self_of_surjective (toLinEquiv ι K).surjective _))

private theorem coe_omegaOrthEquiv {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] {Q : QuadraticForm K (ι → K)} {Q₀ : (ι → K) → K} (hQ : ⇑Q = Q₀)
    (A : StatedOmega Q₀) :
    (omegaOrthEquiv hQ A : (ι → K) ≃ₗ[K] (ι → K)) = toLinEquiv ι K A :=
  rfl

private noncomputable def projOrthEquiv {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] {Q : QuadraticForm K (ι → K)} {Q₀ : (ι → K) → K} (hQ : ⇑Q = Q₀) :
    StatedProj (StatedOmega Q₀) ≃* ProjOrthDerived Q :=
  QuotientGroup.congr _ _ (omegaOrthEquiv hQ) (by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, mem_statedScalars_iff] at hy
      rw [Subgroup.mem_subgroupOf]
      change ((omegaOrthEquiv hQ y : orthDerived Q) : (ι → K) ≃ₗ[K] (ι → K)) ∈
        scalars K (ι → K)
      rw [coe_omegaOrthEquiv]
      exact hy
    · intro hx
      refine ⟨(omegaOrthEquiv hQ).symm x, ?_, by simp⟩
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, mem_statedScalars_iff]
      rw [Subgroup.mem_subgroupOf] at hx
      have h1 : (omegaOrthEquiv hQ ((omegaOrthEquiv hQ).symm x) :
          (ι → K) ≃ₗ[K] (ι → K)) = x := by rw [MulEquiv.apply_symm_apply]
      rw [coe_omegaOrthEquiv] at h1
      rw [h1]
      exact hx)

end Projective

private theorem perfectInLayer_conj_of_equiv {G : Type} [Group G] {K : Type} [Field K] [Finite K]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, Module.finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpl : p ≠ ringChar K)
    (e : G ≃* CFSG.RankThree.Classical2.ProjOrthDerived Q) (a : G) (ha : a ^ p = 1) :
    PerfectInLayer (MulAut.conj a) := by
  haveI : Fact p.Prime := ⟨hp⟩
  refine perfectInLayer_of_congr e (MulAut.conj a) ?_
  have hc : MulAut.congr e (MulAut.conj a) = MulAut.conj (e a) := by
    ext y
    simp [MulAut.conj_apply]
  rw [hc]
  have hea : (e a) ^ p = 1 := by rw [← map_pow, ha, map_one]
  by_cases h1 : e a = 1
  · rw [h1]
    obtain ⟨-, -, -, hsimple, hnonab, -⟩ :=
      CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hQ hT
    have hfix : fixSubgroup
        (MulAut.conj (1 : CFSG.RankThree.Classical2.ProjOrthDerived Q)) = ⊤ := by
      ext g
      simp [mem_fixSubgroup, MulAut.conj_apply]
    have hs : IsSimpleGroup ↥(fixSubgroup
        (MulAut.conj (1 : CFSG.RankThree.Classical2.ProjOrthDerived Q))) := by
      rw [hfix]
      exact MulEquiv.isSimpleGroup (Subgroup.topEquiv)
    obtain ⟨u, v, huv⟩ := hnonab
    refine perfectInLayer_of_isSimpleGroup _ hs ⟨⟨u, ?_⟩, ⟨v, ?_⟩, fun h => huv ?_⟩
    · simp [mem_fixSubgroup, MulAut.conj_apply]
    · simp [mem_fixSubgroup, MulAut.conj_apply]
    · exact congrArg Subtype.val h
  · exact perfectInLayer_conj_projOrth_of_orderOf hQ hT hp hp2 hpl (e a) (orderOf_eq_prime hea h1)

theorem perfectInLayer_conj_omega {t : StatedLieTag}
    (ht : t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus) {G : Type} [Group G]
    {n ℓ f : ℕ} (hG : StatedClassicalModel G t n ℓ f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpℓ : p ≠ ℓ) (a : G) (ha : a ^ p = 1) : PerfectInLayer (MulAut.conj a) := by
  rcases ht with rfl | rfl | rfl
  · obtain ⟨hadm, K, hKf, hKfin, hcard, ⟨e⟩⟩ := hG
    have h3 : 3 ≤ n ∧ ℓ ≠ 2 := hadm.2.2
    have hring : ringChar K = ℓ :=
      CFSG.ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq hadm.1 hadm.2.1 hcard
    have h2 : (2 : K) ≠ 0 := by
      rw [Ne, CFSG.ClassicalGroups.Orthogonal.two_eq_zero_iff_ringChar_eq_two
        (by rw [hring]; exact hadm.1), hring]
      exact h3.2
    obtain ⟨hQ, hT⟩ := CFSG.ClassicalGroups.Orthogonal.regular_quadOdd (K := K) (n := n) h2 h3.1
    exact perfectInLayer_conj_of_equiv hQ hT hp hp2 (by rw [hring]; exact hpℓ)
      (e.trans (projOrthEquiv (CFSG.LieType.Universal.Spin.coe_quadOdd n K))) a ha
  · obtain ⟨hadm, K, hKf, hKfin, hcard, ⟨e⟩⟩ := hG
    have h4 : 4 ≤ n := hadm.2.2
    have hring : ringChar K = ℓ :=
      CFSG.ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq hadm.1 hadm.2.1 hcard
    obtain ⟨hQ, hT⟩ := CFSG.ClassicalGroups.Orthogonal.regular_quadPlus (K := K) (n := n)
      (by omega)
    exact perfectInLayer_conj_of_equiv hQ hT hp hp2 (by rw [hring]; exact hpℓ)
      (e.trans (projOrthEquiv (CFSG.LieType.Universal.Spin.coe_quadPlus (n := n) (K := K)))) a ha
  · obtain ⟨hadm, K, hKf, hKfin, hcard, b, c, hirr, ⟨e⟩⟩ := hG
    have h4 : 4 ≤ n := hadm.2.2
    have hring : ringChar K = ℓ :=
      CFSG.ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq hadm.1 hadm.2.1 hcard
    obtain ⟨hQ, hT⟩ := CFSG.ClassicalGroups.Orthogonal.regular_quadMinus (K := K) (n := n) h4 hirr
    exact perfectInLayer_conj_of_equiv hQ hT hp hp2 (by rw [hring]; exact hpℓ)
      (e.trans (projOrthEquiv (CFSG.LieType.Universal.Spin.coe_quadMinus n K b c))) a ha

end CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
