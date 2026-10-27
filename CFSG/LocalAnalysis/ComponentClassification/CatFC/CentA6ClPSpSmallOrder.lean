module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClPSpModels
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofA6PSpInner
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClPSpSmallBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddCentralFixed
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddInnerLift
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddInnerUGraph
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddOrthAll
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofSLForm
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofToralReps
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorOddE6
public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorInner
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTILinearSocle
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSLAllInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUFieldOddCore
public import CFSG.LocalAnalysis.ComponentInitial.ProjectiveEigenspaceComponent
public import CFSG.LocalAnalysis.ComponentInitial.ProjectiveOrthogonalLocalComponentSplit
public import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
public import CFSG.RankThree.PartOne.KC.OrthogonalFieldDescentCore
public import CFSG.RankThree.PartOne.KC.OrthogonalFieldDescentDisplayed
public import CFSG.RankThree.PartOne.KC.OrthogonalFieldDescentTags
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeOrbits
public import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus

public section

namespace CFSG.ComponentClassification.CatFC.PSpSmall

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank Module
open CFSG.ComponentClassification.CatLeaf CFSG.ComponentClassification.CatLeafProof
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open scoped MatrixGroups

@[expose] def InnerOut (f : ℕ) {K : Type} [Field K] (d μ : K) (G : Type) [Group G] : Prop :=
  ((∃ l : K, l ^ 2 = d) ∧ μ = d ∧ (f = 1 → Group.IsSolvable G) ∧ (f = 2 → 518400 ≤ Nat.card G)) ∨
  ((∃ l : K, l ^ 2 = d) ∧ μ = -d ∧ (f = 1 → Group.IsSolvable G) ∧ (f = 2 → 5760 ≤ Nat.card G)) ∨
  ((∀ l : K, l ^ 2 ≠ d) ∧ μ = d ∧ (f = 1 → Perfect360 G ∧ 720 ≤ Nat.card G) ∧
    (f = 2 → 531360 ≤ Nat.card G)) ∨
  ((∀ l : K, l ^ 2 ≠ d) ∧ μ = -d ∧ (f = 1 → Group.IsSolvable G) ∧ (f = 2 → 3600 ≤ Nat.card G))

theorem InnerOut.of_mulEquiv {f : ℕ} {K : Type} [Field K] {d μ : K} {G G' : Type} [Group G]
    [Group G'] (e : G ≃* G') (h : InnerOut f d μ G) : InnerOut f d μ G' := by
  have hs : ∀ (H : f = 1 → Group.IsSolvable G), f = 1 → Group.IsSolvable G' := fun H hf => by
    haveI := H hf
    exact solvable_of_solvable_injective (f := e.symm.toMonoidHom) e.symm.injective
  have hc : ∀ n : ℕ, n ≤ Nat.card G → n ≤ Nat.card G' := fun n hn => by
    rwa [← Nat.card_congr e.toEquiv]
  rcases h with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
  · exact Or.inl ⟨h1, h2, hs h3, fun hf => hc _ (h4 hf)⟩
  · exact Or.inr (Or.inl ⟨h1, h2, hs h3, fun hf => hc _ (h4 hf)⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨h1, h2, fun hf => ⟨(h3 hf).1.of_mulEquiv e,
      hc _ (h3 hf).2⟩, fun hf => hc _ (h4 hf)⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨h1, h2, hs h3, fun hf => hc _ (h4 hf)⟩))

section Orders

variable {k : Type} [Field k] [Finite k]

theorem card_statedSp_one (k : Type) [Field k] [Finite k] :
    Nat.card (StatedSp 1 k) = Nat.card k * (Nat.card k ^ 2 - 1) := by
  rw [card_statedSp 1]
  simp

theorem isSolvable_statedSp_one (hk : Nat.card k = 3) : Group.IsSolvable (StatedSp 1 k) :=
  LieType.HighestRoot.isSolvable_of_mulEquiv hk
    (ClassicalInvolution.Models.SymplecticPairs.longBlockEquivOne k).symm

theorem innerOut_one {f a b : ℕ} (hK : Nat.card k = 3 ^ f) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hab : a + b = 2) {G : Type} [Group G] (e : G ≃* StatedSp a k × StatedSp b k) :
    (f = 1 → Group.IsSolvable G) ∧ (f = 2 → 518400 ≤ Nat.card G) := by
  obtain rfl : a = 1 := by omega
  obtain rfl : b = 1 := by omega
  refine ⟨fun hf => ?_, fun hf => ?_⟩
  · subst hf
    haveI := isSolvable_statedSp_one (k := k) (by simpa using hK)
    haveI : Group.IsSolvable (StatedSp 1 k × StatedSp 1 k) := inferInstance
    exact solvable_of_solvable_injective (f := e.toMonoidHom) e.injective
  · subst hf
    rw [Nat.card_congr e.toEquiv, Nat.card_prod, card_statedSp_one, hK]
    norm_num

theorem innerOut_two {f : ℕ} (hK : Nat.card k = 3 ^ f) {G : Type} [Group G]
    (e : G ≃* GL (Fin 2) k) :
    (f = 1 → Group.IsSolvable G) ∧ (f = 2 → 5760 ≤ Nat.card G) := by
  refine ⟨fun hf => ?_, fun hf => ?_⟩
  · subst hf
    haveI := CatalogueBGeneralLinear.generalLinear_small_solvable 2 k
      (Or.inr ⟨rfl, Or.inr (by simpa using hK)⟩)
    exact solvable_of_solvable_injective (f := e.toMonoidHom) e.injective
  · subst hf
    haveI := Fintype.ofFinite k
    have h9 : Fintype.card k = 9 := by
      rw [← Nat.card_eq_fintype_card, hK]
      norm_num
    rw [Nat.card_congr e.toEquiv, Matrix.card_GL_field, h9]
    simp [Fin.prod_univ_two]

theorem innerOut_three {f : ℕ} {E : Type} [Field E] [Finite E] (hE : Nat.card E = 3 ^ (2 * f))
    {G : Type} [Group G] (e : G ≃* StatedSp 1 E) :
    (f = 1 → Perfect360 G ∧ 720 ≤ Nat.card G) ∧ (f = 2 → 531360 ≤ Nat.card G) := by
  refine ⟨fun hf => ?_, fun hf => ?_⟩
  · subst hf
    refine ⟨(perfect360_statedSp_one (k := E) (by rw [hE]; norm_num)).of_mulEquiv e.symm, ?_⟩
    rw [Nat.card_congr e.toEquiv, card_statedSp_one, hE]
    norm_num
  · subst hf
    rw [Nat.card_congr e.toEquiv, card_statedSp_one, hE]
    norm_num

end Orders

section Unitary

open CFSG.ComponentClassification.CatalogueBUnitaryIsometry

variable {E W : Type} [Field E] [Finite E] [AddCommGroup W] [Module E W] [FiniteDimensional E W]
  {sigma : E ≃+* E}

theorem card_isometryGroup_two_ge (hE : Nat.card E = (3 ^ 2) ^ 2) (hW : finrank E W = 2)
    (h : W →ₛₗ[sigma.toRingHom] W →ₗ[E] E) (hsym : h.IsSymm) (hnd : h.Nondegenerate)
    (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1) (hsig : ∀ z, sigma z = z ^ (3 ^ 2)) :
    3600 ≤ Nat.card (isometryGroup h) := by
  have hfix := OddInner.card_fixedSubfield hsigma hne hE
  obtain ⟨-, -, eSL, -⟩ := CatalogueBUnitaryTwo.exists_unitary_two_special_linear_isomorphism
    sigma h hsym hnd hsigma hne hW
  have hSU : Nat.card (specialIsometry h) = 720 := by
    rw [Nat.card_congr eSL.toEquiv, CatFactsSp4.card_SL2, hfix]
    norm_num
  haveI : Fintype E := Fintype.ofFinite E
  have hE81 : Fintype.card E = 81 := by
    rw [← Nat.card_eq_fintype_card, hE]
    norm_num
  have h80 : Nat.card Eˣ = 80 := by
    classical
    rw [Nat.card_eq_fintype_card, Fintype.card_units, hE81]
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Eˣ) 5 (by rw [h80]; norm_num)
  have hz5 : z ^ 5 = 1 := by
    rw [← hz]
    exact pow_orderOf_eq_one z
  have hz10 : (z : E) ^ (3 ^ 2) * (z : E) = 1 := by
    have h1 : (z : E) ^ 5 = 1 := by
      have := congrArg Units.val hz5
      simpa using this
    calc (z : E) ^ (3 ^ 2) * (z : E) = ((z : E) ^ 5) ^ 2 := by ring
      _ = 1 := by rw [h1]; norm_num
  let s : W ≃ₗ[E] W := LinearEquiv.smulOfUnit z
  have hs : s ∈ isometryGroup h := by
    intro x y
    change h ((z : E) • x) ((z : E) • y) = h x y
    rw [map_smulₛₗ h (z : E) x, LinearMap.smul_apply, map_smul, smul_eq_mul, smul_eq_mul]
    change sigma (z : E) * ((z : E) * h x y) = h x y
    rw [hsig, ← mul_assoc, hz10, one_mul]
  have hdet : isometryDeterminant h ⟨s, hs⟩ = z ^ 2 := by
    apply Units.ext
    change (LinearEquiv.det s : E) = ((z ^ 2 : Eˣ) : E)
    rw [LinearEquiv.coe_det]
    have : (s : W →ₗ[E] W) = (z : E) • LinearMap.id := by
      ext x
      rfl
    rw [this, LinearMap.det_smul, hW, LinearMap.det_id, mul_one, Units.val_pow_eq_pow_val]
  have hu : z ^ 2 ∈ (isometryDeterminant h).range := ⟨⟨s, hs⟩, hdet⟩
  have hu5 : orderOf (z ^ 2) = 5 := by
    refine orderOf_eq_prime (by rw [← pow_mul, show 2 * 5 = 5 * 2 from rfl, pow_mul, hz5, one_pow])
      fun h2 => ?_
    have := orderOf_dvd_of_pow_eq_one h2
    rw [hz] at this
    omega
  have h5 : 5 ∣ Nat.card (isometryDeterminant h).range := by
    have := Subgroup.orderOf_dvd_natCard _ hu
    rwa [hu5] at this
  have h5' : 5 ≤ Nat.card (isometryDeterminant h).range := Nat.le_of_dvd Nat.card_pos h5
  have hcard : Nat.card (isometryGroup h) = Nat.card (isometryDeterminant h).range *
      Nat.card (isometryDeterminant h).ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (isometryDeterminant h).ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange (isometryDeterminant h)).toEquiv]
  rw [hcard]
  have hker : Nat.card (isometryDeterminant h).ker = 720 := hSU
  rw [hker]
  omega

theorem innerOut_four {f : ℕ} (hE : Nat.card E = (3 ^ f) ^ 2) (hW : finrank E W = 2)
    (h : W →ₛₗ[sigma.toRingHom] W →ₗ[E] E) (hsym : h.IsSymm) (hnd : h.Nondegenerate)
    (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1) (hsig : ∀ z, sigma z = z ^ (3 ^ f)) {G : Type}
    [Group G] (e : G ≃* isometryGroup h) :
    (f = 1 → Group.IsSolvable G) ∧ (f = 2 → 3600 ≤ Nat.card G) := by
  refine ⟨fun hf => ?_, fun hf => ?_⟩
  · subst hf
    have hfix := OddInner.card_fixedSubfield hsigma hne hE
    haveI := isometry_two_three_solvable h hsym hnd hsigma hne hW (by rw [hfix]; norm_num)
    exact solvable_of_solvable_injective (f := e.toMonoidHom) e.injective
  · subst hf
    rw [Nat.card_congr e.toEquiv]
    exact card_isometryGroup_two_ge hE hW h hsym hnd hsigma hne hsig

end Unitary

end CFSG.ComponentClassification.CatFC.PSpSmall
