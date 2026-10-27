module

public import CFSG.ClassicalInvolution.RouteD.TWT8Class
public import CFSG.ClassicalInvolution.RouteD.GapsFrMinusOrth
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
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
public import CFSG.ClassicalInvolution.Asc77.Lemma310
public import CFSG.ClassicalInvolution.Asc77.ThmEStatement
public import CFSG.ClassicalInvolution.Asc77.WP1Section18
public import CFSG.ClassicalInvolution.Asc77.WP1Section6
public import CFSG.ClassicalInvolution.Balance.QNineFuzzyFree
public import CFSG.ClassicalInvolution.Balance.Theorem5Models
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalIsogeny
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Conj
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Roots
public import CFSG.ClassicalInvolution.ModelFacts.OrthAutMinusNormalized
public import CFSG.ClassicalInvolution.RouteD.GapsFrOdd
public import CFSG.ClassicalInvolution.RouteD.TWEB6Fixed
public import CFSG.ClassicalInvolution.RouteD.TWEB6YBridge
public import CFSG.LocalAnalysis.ComponentClassification.BadTwoComponentSubgroup
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
public import CFSG.LocalAnalysis.SignalizerFunctor
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

namespace CFSG.ClassicalInvolution.RouteD.TWT9

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.RouteD.TWE.B6
  CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
open CFSG.ClassicalInvolution.RouteD.TWE.B4 (normalized_span eigen_planes_of_inverted)
open CFSG.ClassicalInvolution.Generic (Commutes)
open scoped MatrixGroups

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

set_option linter.unusedSectionVars false

section Spin

open CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.ModelFacts.OrthAut
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT CFSG.LieType.Universal.Spin
open CFSG.LieType.Universal (minusCoeffs minusCoeffs_irr)

variable {p f : ℕ} [Fact p.Prime]

local notation "𝔔" => quadMinus 4 (GaloisField p f) (Prod.fst (minusCoeffs p f))
  (Prod.snd (minusCoeffs p f))

local notation "𝔽" => GaloisField p f

local notation "𝕍" => Vm 4 (GaloisField p f)



theorem leaf_planes_td4 (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    {𝓕 : Set (Subgroup (spinGroup 𝔔))}
    (cq : CentralQuot (spinAction 𝔔) 𝓕 (fundSet 𝔔) (scalars 𝔽 𝕍))
    {g₀ : 𝕍 ≃ₗ[𝔽] 𝕍} (hgO : g₀ ∈ TauCeti.QuadraticMap.orthogonalGroup 𝔔) (hg2 : g₀ * g₀ = 1)
    {RJ : Subgroup (spinGroup 𝔔)} (hRJ : RJ ∈ 𝓕)
    (hnormJ : ∀ l ∈ RJ.map (spinAction 𝔔), g₀ * l * g₀ ∈ RJ.map (spinAction 𝔔))
    {x₀ : spinGroup 𝔔} (hx₀J : x₀ ∈ RJ) (hx₀1 : x₀ ≠ 1) (hx₀p : x₀ ^ p = 1)
    (hx₀inv : ∀ v, g₀ (spinAction 𝔔 x₀ v) = (spinAction 𝔔 x₀).symm (g₀ v))
    {ε : 𝔽} (hε : ε = 1 ∨ ε = -1) :
    ∃ (FJ : OFrame 𝔔) (π' ρ' : HypPair 𝔔), RJ.map (spinAction 𝔔) = FJ.La.range ∧
      π'.Orth ρ' ∧ hypPlane π' ⊔ hypPlane ρ' = FJ.span ∧
      (∀ x ∈ hypPlane π', g₀ x = (-ε) • x) ∧ (∀ x ∈ hypPlane ρ', g₀ x = ε • x) := by
  classical
  obtain ⟨hf0, hK⟩ := RouteD.card_galoisField_of_four_le (p := p) (f := f) (by omega)
  have h2 : (2 : 𝔽) ≠ 0 := CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f hp2
  have hodd : Odd (Nat.card 𝔽) := by
    rw [hK]
    exact (Nat.Prime.odd_of_ne_two Fact.out hp2).pow
  have : Invertible (2 : 𝔽) := invertibleOfNonzero h2
  have hirr := minusCoeffs_irr p f
  have hQ' : (polarBilin 𝔔).Nondegenerate :=
    nondegenerate_polarBilin_quadMinus_of_finite 4 𝔽 hirr
  obtain ⟨iJ, hiJ⟩ := cq.map_mem _ hRJ
  obtain ⟨FJ, hFJ, hiJe⟩ := hiJ
  have hJspan : ∀ x ∈ FJ.span, g₀ x ∈ FJ.span :=
    normalized_span hodd hgO hg2 FJ (by rw [← hFJ]; exact hnormJ)
  have hx₀mem : spinAction 𝔔 x₀ ∈ FJ.La.range := by
    rw [← hFJ]
    exact ⟨x₀, hx₀J, rfl⟩
  obtain ⟨A, hA⟩ := hx₀mem
  have hAp : A ^ p = 1 := by
    apply FJ.La_injective
    rw [map_pow, hA, ← map_pow, hx₀p, map_one, map_one]
  have hA1 : A ≠ 1 := by
    rintro rfl
    rw [map_one] at hA
    exact hx₀1 (cq.inj RJ hRJ x₀ hx₀J hA.symm)
  have hinv : ∀ v, g₀ (FJ.La A v) = (FJ.La A).symm (g₀ v) := by
    intro v
    rw [hA]
    exact hx₀inv v
  obtain ⟨π, ρ, hπρ, hsup, hgπ, hgρ⟩ := eigen_planes_of_inverted hodd hQ' (p := p) hgO hg2 FJ
    hJspan hA1 hAp hinv
  rcases hε with rfl | rfl
  · exact ⟨FJ, π, ρ, hFJ, hπρ, hsup, fun x hx => by rw [hgπ x hx]; simp, fun x hx => by
      rw [hgρ x hx]; simp⟩
  · exact ⟨FJ, ρ, π, hFJ, hπρ.symm, by rw [sup_comm]; exact hsup, fun x hx => by
      rw [hgρ x hx]; simp, fun x hx => by rw [hgπ x hx]; simp⟩

theorem adapted_frame_td4 (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {𝓕 : Set (Subgroup (spinGroup 𝔔))}
    (cq : CentralQuot (spinAction 𝔔) 𝓕 (fundSet 𝔔) (scalars 𝔽 𝕍))
    {RJ : Subgroup (spinGroup 𝔔)} (hRJ : RJ ∈ 𝓕) {FJ : OFrame 𝔔}
    (hFJ : RJ.map (spinAction 𝔔) = FJ.La.range) {π' ρ' : HypPair 𝔔} (hπρ' : π'.Orth ρ')
    (hsup' : hypPlane π' ⊔ hypPlane ρ' = FJ.span) {g₀ : 𝕍 ≃ₗ[𝔽] 𝕍} {ε : 𝔽}
    (hperp : ∀ y, y ∈ π'.perp → g₀ y = ε • y) :
    ∃ x' : spinGroup 𝔔,
      RJ = ((rootSL2 (minusFrame 4 (minusCoeffs p f).1 (minusCoeffs p f).2).toHypFrame 0 1
        (by omega) (by omega) (by omega) true false).map (MulAut.conj x').toMonoidHom) ∧
      ∀ y, polar 𝔔 (spinAction 𝔔 x'
          ((minusFrame 4 (minusCoeffs p f).1 (minusCoeffs p f).2).toHypFrame.vec ⟨0, by omega⟩
            true)) y = 0 →
        polar 𝔔 (spinAction 𝔔 x'
          ((minusFrame 4 (minusCoeffs p f).1 (minusCoeffs p f).2).toHypFrame.vec ⟨0, by omega⟩
            false)) y = 0 →
        g₀ y = ε • y := by
  classical
  obtain ⟨hf0, hK⟩ := RouteD.card_galoisField_of_four_le (p := p) (f := f) (by omega)
  have h2 : (2 : 𝔽) ≠ 0 := CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f hp2
  have hodd : Odd (Nat.card 𝔽) := by
    rw [hK]
    exact (Nat.Prime.odd_of_ne_two Fact.out hp2).pow
  have : Invertible (2 : 𝔽) := invertibleOfNonzero h2
  have hirr := minusCoeffs_irr p f
  have hQ : (quadMinus 4 𝔽 (minusCoeffs p f).1 (minusCoeffs p f).2).Nondegenerate :=
    QuadraticMap.nondegenerate_polar_iff.mp
      (nondegenerate_polarBilin_quadMinus_of_finite 4 𝔽 hirr)
  have hQ' : (polarBilin 𝔔).Nondegenerate :=
    nondegenerate_polarBilin_quadMinus_of_finite 4 𝔽 hirr
  have hdimV : 2 * 2 + 3 ≤ Module.finrank 𝔽 (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → 𝔽) := by
    rw [finrank_minus p f 4 (by omega)]
    omega
  set F₀ : HypFrame 𝔔 (4 - 1) := (minusFrame 4 (minusCoeffs p f).1 (minusCoeffs p f).2).toHypFrame
    with hF₀
  have hspanG : FJ.span = (mkFrame π' ρ' hπρ').span := by
    rw [frame_span_eq (mkFrame π' ρ' hπρ')]
    exact hsup'.symm
  have hii : FJ.La (-1) = (mkFrame π' ρ' hπρ').La (-1) :=
    Frame.La_neg_one_eq_of_span_eq hspanG
  obtain ⟨P1, hP1o, hP1pl, hFJP1⟩ : ∃ (P1 : HypPair 𝔔) (h : π'.Orth (swapPair P1)),
      hypPlane P1 = hypPlane ρ' ∧ FJ.La.range = (mkFrame π' (swapPair P1) h).La.range := by
    rcases Frame.La_range_eq_or_eq_swap h2 hii with hA | hB
    · exact ⟨swapPair ρ', hπρ', by rw [hypPlane_swapPair], hA⟩
    · exact ⟨ρ', orth_swapPair hπρ', rfl, hB⟩
  have o01 : π'.Orth P1 := orth_swapPair hP1o
  let p₀ : ℕ → HypPair 𝔔 := fun k => if k = 0 then π' else P1
  have ho₀ : ∀ a b, a < 2 → b < 2 → a ≠ b → (p₀ a).Orth (p₀ b) := by
    intro a b ha hb hab
    interval_cases a <;> interval_cases b <;>
      first
      | exact absurd rfl hab
      | simp [p₀, o01, o01.symm]
  obtain ⟨Q3, hQ3⟩ := exists_pair_perp_fam hodd hQ' p₀ 2 ho₀ hdimV
  have o02 : π'.Orth Q3 := by simpa [p₀] using hQ3 0 (by omega)
  have o12 : P1.Orth Q3 := by simpa [p₀] using hQ3 1 (by omega)
  let Pn : ℕ → HypPair 𝔔 := fun k => if k = 0 then π' else if k = 1 then P1 else Q3
  have hPn : ∀ a b, a < 3 → b < 3 → a ≠ b → (Pn a).Orth (Pn b) := by
    intro a b ha hb hab
    interval_cases a <;> interval_cases b <;>
      first
      | exact absurd rfl hab
      | simp [Pn, o01, o01.symm, o02, o02.symm, o12, o12.symm]
  let P : Fin (4 - 1) → HypPair 𝔔 := fun i => Pn i.val
  have hPo : ∀ i j : Fin (4 - 1), i ≠ j → (P i).Orth (P j) := fun i j hij =>
    hPn i.val j.val i.isLt j.isLt (fun h => hij (Fin.ext h))
  obtain ⟨x', hx1, -⟩ := exists_spin_family hodd hQ F₀ hPo (⟨2, by omega⟩ : Fin (4 - 1))
  have hP0 : π'.e = spinAction 𝔔 x' (F₀.vec ⟨0, by omega⟩ true) ∧
      π'.f = spinAction 𝔔 x' (F₀.vec ⟨0, by omega⟩ false) := by
    have := hx1 ⟨0, by omega⟩ (fun h => by have := congrArg Fin.val h; simp at this)
    have e : P ⟨0, by omega⟩ = π' := by simp [P, Pn]
    rw [e] at this
    exact this
  have hP1 : P1.e = spinAction 𝔔 x' (F₀.vec ⟨1, by omega⟩ true) ∧
      P1.f = spinAction 𝔔 x' (F₀.vec ⟨1, by omega⟩ false) := by
    have := hx1 ⟨1, by omega⟩ (fun h => by have := congrArg Fin.val h; simp at this)
    have e : P ⟨1, by omega⟩ = P1 := by simp [P, Pn]
    rw [e] at this
    exact this
  have hrange := La_range_eq_of_pairs F₀ (a := 0) (b := 1) (by omega) (by omega) (by omega) true
    false x' hP1o hP0 ⟨hP1.2, hP1.1⟩
  have hq4 : 4 ≤ p ^ f := by omega
  refine ⟨x', cq.map_inj hRJ (rootSL2_conj_mem_gen hq4 cq F₀ _ _ _ true false x')
    (by rw [hFJ, hFJP1, hrange]), fun y h1 h2' => hperp y ?_⟩
  rw [← hP0.1] at h1
  rw [← hP0.2] at h2'
  exact HypPair.mem_perp.mpr ⟨h1, h2'⟩

end Spin

end CFSG.ClassicalInvolution.RouteD.TWT9
