module

public import CFSG.ClassicalInvolution.RouteD.MultiStarModel
public import CFSG.ClassicalInvolution.ModelFacts.FundamentalSL2Main
public import CFSG.ClassicalInvolution.ModelFacts.FundNoncentralBridge
public import CFSG.ClassicalInvolution.ModelFacts.ClauseZero
public import CFSG.ClassicalInvolution.SL2Facts
import CFSG.ClassicalInvolution.ModelFacts.FundNoncentralMain
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.ClassicalInvolution.Generic.InductionMain
public import CFSG.ClassicalInvolution.ModelFacts.OddCover
public import CFSG.ClassicalInvolution.Models.LinearFrames
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Quadruple
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.TypeCLayer
public import CFSG.ClassicalInvolution.Models.Transfer
public import CFSG.ClassicalInvolution.Models.UnitaryFrames
public import CFSG.ClassicalInvolution.RouteD.MultiStarStd
public import CFSG.ClassicalInvolution.RouteD.TypeAChain
public import CFSG.ClassicalInvolution.RouteD.TypeEModel
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddLieClassical
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddLieE6E7Triality
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwo
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.ClassicalInvolution.Asc77.BSC

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
open scoped MatrixGroups

set_option linter.unusedSectionVars false

variable {p : ℕ} [Fact p.Prime]


abbrev ModelK (p : ℕ) [Fact p.Prime] (t : StatedLieTag) (n e : ℕ) : Type :=
  (modelUniv t n p e Fact.out).K

section Involution

variable {t : StatedLieTag} {n e : ℕ}

local notation "𝕂" => ModelK p t n e

@[expose] def IsInvIn {X : Type*} [Group X] (R : Subgroup X) (x : X) : Prop :=
  x ∈ R ∧ x * x = 1 ∧ x ≠ 1

theorem odd_card_gf (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e) : Odd (Nat.card (GaloisField p e)) := by
  have he : e ≠ 0 := by
    rintro rfl
    simp at hq
  rw [GaloisField.card p e he]
  exact (Nat.Prime.odd_of_ne_two Fact.out hp2).pow

theorem fund_equiv_sl2 (hp2 : p ≠ 2) (hfund : IsFundTag t) (hadm : StatedLieAdmissible t n p e)
    (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4) {R : Subgroup 𝕂}
    (hR : R ∈ ModelFund p t n e) : Nonempty (R ≃* SL(2, GaloisField p e)) := by
  obtain ⟨g, γ, hγ, rfl⟩ := hR
  rcases hγ with h | ⟨h, -⟩ | ⟨h, -⟩
  · exact ModelFacts.fundamentalSL2_of_isFundTag hp2 hfund hadm g γ h
  · exact absurd h hG2
  · exact absurd h hD4

theorem exists_inv (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e) (hfund : IsFundTag t)
    (hadm : StatedLieAdmissible t n p e) (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4)
    {R : Subgroup 𝕂} (hR : R ∈ ModelFund p t n e) : ∃ x : 𝕂, IsInvIn R x := by
  obtain ⟨φ⟩ := fund_equiv_sl2 hp2 hfund hadm hG2 hD4 hR
  have hodd : Odd (Nat.card (GaloisField p e)) := odd_card_gf hp2 hq
  refine ⟨((φ.symm (-1) : R) : 𝕂), (φ.symm (-1)).2, ?_, ?_⟩
  · have h : φ.symm (-1) * φ.symm (-1) = 1 := by
      rw [← map_mul]
      simp
    exact congrArg Subtype.val h
  · intro h1
    have h2 : φ.symm (-1) = 1 := Subtype.ext h1
    have h3 : (-1 : SL(2, GaloisField p e)) = 1 := by
      have := congrArg φ h2
      simpa using this
    exact sl2_neg_one_ne_one hodd h3

theorem inv_unique (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e) (hfund : IsFundTag t)
    (hadm : StatedLieAdmissible t n p e) (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4)
    {R : Subgroup 𝕂} (hR : R ∈ ModelFund p t n e) {x y : 𝕂} (hx : IsInvIn R x)
    (hy : IsInvIn R y) : x = y := by
  obtain ⟨φ⟩ := fund_equiv_sl2 hp2 hfund hadm hG2 hD4 hR
  have hodd : Odd (Nat.card (GaloisField p e)) := odd_card_gf hp2 hq
  have key : ∀ (w : 𝕂) (hw : IsInvIn R w), (⟨w, hw.1⟩ : R) = φ.symm (-1) := by
    intro w hw
    have hw2 : (⟨w, hw.1⟩ : R) ^ 2 = 1 := Subtype.ext (by simpa [pow_two] using hw.2.1)
    have hw1 : (⟨w, hw.1⟩ : R) ≠ 1 := fun h => hw.2.2 (congrArg Subtype.val h)
    have hord : orderOf (⟨w, hw.1⟩ : R) = 2 := orderOf_eq_prime hw2 hw1
    exact (orderOf_eq_two_iff_of_equiv_sl2 hodd φ _).mp hord
  have h := (key x hx).trans (key y hy).symm
  exact congrArg Subtype.val h

theorem eq_one_of_mem_center (hfund : IsFundTag t) (hadm : StatedLieAdmissible t n p e)
    (hnA1 : ¬ (t = .PSL ∧ n = 2)) {R : Subgroup 𝕂} (hR : R ∈ ModelFund p t n e) {x : 𝕂}
    (hxR : x ∈ R) (hxZ : x ∈ Subgroup.center 𝕂) : x = 1 := by
  refine RouteD.Gaps.fundNoncentral p t n e hfund hadm hnA1 R hR x hxR fun y => ?_
  have h := Subgroup.mem_center_iff.mp hxZ y
  have h1 : x * y * x⁻¹ * y⁻¹ = 1 := by
    rw [show x * y = y * x from h.symm]
    group
  rw [h1]
  exact Subgroup.one_mem _

theorem conjSub_mem_modelFund {R : Subgroup 𝕂} (hR : R ∈ ModelFund p t n e) (g : 𝕂) :
    conjSub g R ∈ ModelFund p t n e := by
  obtain ⟨g₀, γ, hγ, rfl⟩ := hR
  exact ⟨g * g₀, γ, hγ, by rw [conjSub_mul]⟩

theorem exists_commuting_pair_ne (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e) (hfund : IsFundTag t)
    (hadm : StatedLieAdmissible t n p e) (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4)
    (hnA1 : ¬ (t = .PSL ∧ n = 2)) (hconn : CommFamilyConnected (ModelFund p t n e))
    {R₀ : Subgroup 𝕂} (hR₀ : R₀ ∈ ModelFund p t n e) :
    ∃ R ∈ ModelFund p t n e, ∃ S ∈ ModelFund p t n e, Commutes R S ∧
      ∀ r ∈ R, ∀ s ∈ S, r * r ∈ Subgroup.center 𝕂 → s * s ∈ Subgroup.center 𝕂 →
        r ∉ Subgroup.center 𝕂 → s ∉ Subgroup.center 𝕂 → r * s⁻¹ ∉ Subgroup.center 𝕂 := by
  by_contra hcon
  push Not at hcon
  have hK : CFSG.Open.IsQuasisimple 𝕂 :=
    (ModelFacts.modelClauseZero t n p e Fact.out hfund hadm).1
  have hinv : ∀ {R : Subgroup 𝕂}, R ∈ ModelFund p t n e → ∀ {x : 𝕂}, x ∈ R →
      x * x ∈ Subgroup.center 𝕂 → x ∉ Subgroup.center 𝕂 → IsInvIn R x := by
    intro R hR x hxR hx2 hxZ
    refine ⟨hxR, eq_one_of_mem_center hfund hadm hnA1 hR (R.mul_mem hxR hxR) hx2, ?_⟩
    rintro rfl
    exact hxZ (Subgroup.one_mem _)
  have hall : ∀ S : Subgroup 𝕂, Relation.ReflTransGen
      (fun U V : Subgroup 𝕂 => U ∈ ModelFund p t n e ∧ V ∈ ModelFund p t n e ∧ Commutes U V)
      R₀ S → ∀ {r s : 𝕂}, IsInvIn R₀ r → IsInvIn S s → r * s⁻¹ ∈ Subgroup.center 𝕂 := by
    intro S hpath
    induction hpath with
    | refl =>
        intro r s hr hs
        have h := inv_unique hp2 hq hfund hadm hG2 hD4 hR₀ hr hs
        rw [h, mul_inv_cancel]
        exact Subgroup.one_mem _
    | @tail B C _ hbc ih =>
        intro r s hr hs
        obtain ⟨hB, hC, hBC⟩ := hbc
        obtain ⟨r', hr'B, s', hs'C, hr2, hs2, hrZ, hsZ, hrs⟩ := hcon B hB C hC hBC
        have hr'inv := hinv hB hr'B hr2 hrZ
        have hs'inv := hinv hC hs'C hs2 hsZ
        have e2 : s = s' := inv_unique hp2 hq hfund hadm hG2 hD4 hC hs hs'inv
        have h1 := ih hr hr'inv
        rw [e2]
        have e : r * s'⁻¹ = (r * r'⁻¹) * (r' * s'⁻¹) := by group
        rw [e]
        exact Subgroup.mul_mem _ h1 hrs
  obtain ⟨r₀, hr₀⟩ := exists_inv hp2 hq hfund hadm hG2 hD4 hR₀
  have hcent : ∀ y : 𝕂, r₀ * y * r₀⁻¹ * y⁻¹ ∈ Subgroup.center 𝕂 := by
    intro y
    have hgR : conjSub y R₀ ∈ ModelFund p t n e := conjSub_mem_modelFund hR₀ y
    have hinv' : IsInvIn (conjSub y R₀) (y * r₀ * y⁻¹) := by
      refine ⟨conj_mem_conjSub hr₀.1, ?_, ?_⟩
      · calc y * r₀ * y⁻¹ * (y * r₀ * y⁻¹) = y * (r₀ * r₀) * y⁻¹ := by group
          _ = 1 := by rw [hr₀.2.1]; group
      · intro h
        apply hr₀.2.2
        have e : r₀ = y⁻¹ * (y * r₀ * y⁻¹) * y := by group
        rw [e, h]
        group
    have h := hall (conjSub y R₀) (hconn R₀ hR₀ _ hgR) hr₀ hinv'
    have e : r₀ * (y * r₀ * y⁻¹)⁻¹ = r₀ * y * r₀⁻¹ * y⁻¹ := by group
    rwa [e] at h
  have hz : r₀ ∈ Subgroup.center 𝕂 := ModelFacts.mem_center_of_commutators_mem_center hK hcent
  exact hr₀.2.2 (eq_one_of_mem_center hfund hadm hnA1 hR₀ hr₀.1 hz)

end Involution

end CFSG.ClassicalInvolution.Asc77.BSC
