module

public import CFSG.ClassicalInvolution.ModelFacts.L6CDefs
public import CFSG.ClassicalInvolution.ModelFacts.L6CLin
public import CFSG.ClassicalInvolution.ModelFacts.LinearAutLift
import CFSG.ClassicalInvolution.Asc77.AscT8S26UModL
import CFSG.ClassicalInvolution.RouteD.TypeABridge
import CFSG.ClassicalInvolution.Models.LinearFrames.Frame
import CFSG.ClassicalInvolution.Models.LinearPairs.RootSL2
public import CFSG.LieType.Steinberg.CentralExt.Families
public import CFSG.LieType.Steinberg.Classical.SpinFrame
public import CFSG.LieType.Steinberg.Families
public import CFSG.LieType.Steinberg.G2
public import CFSG.LieType.Universal.Spin.Generation
public import CFSG.LieType.Universal.Spin.OddCT
public import CFSG.LieType.Universal.Spin.PlusCT
public import CFSG.LieType.Universal.Spin.Structure
public import CFSG.LieType.Universal.SpinOmega
public import CFSG.LieType.Universal.Unitary
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearDescentFixedBasis
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials
import CFSG.ClassicalInvolution.Asc77.Lemma310
import CFSG.ClassicalInvolution.Asc77.ThmEStatement
import CFSG.ClassicalInvolution.Asc77.WP1Section18
import CFSG.ClassicalInvolution.Asc77.WP1Section6
import CFSG.ClassicalInvolution.Asc77.WP3L52Main
import CFSG.ClassicalInvolution.Balance.QNineFuzzyFree
import CFSG.ClassicalInvolution.Balance.StrongLocalBalanceGlue
import CFSG.ClassicalInvolution.Balance.Theorem5Models
import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalIsogeny
import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Conj
import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Roots
import CFSG.LocalAnalysis.ComponentClassification.BadTwoComponentSubgroup
import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages
import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
import CFSG.LocalAnalysis.SignalizerFunctor
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizer
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PSLRangeCentralizer
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvolutionCount
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixCount
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUDecomposition
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTen
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FieldProjectionArithmetic
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction
import Certificates.Certificate1
import Certificates.Certificate10
import Certificates.Certificate11
import Certificates.Certificate12
import Certificates.Certificate2
import Certificates.Certificate3
import Certificates.Certificate4
import Certificates.Certificate42
import Certificates.Certificate44
import Certificates.Certificate5
import Certificates.Certificate6
import Certificates.Certificate7
import Certificates.Certificate8
import Certificates.Certificate9

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.ModelFacts.L6C

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.Asc77
open scoped MatrixGroups

theorem gf_facts (p e : ℕ) [Fact p.Prime] (he : e ≠ 0) (h4 : p ^ e % 4 = 3) :
    (2 : GaloisField p e) ≠ 0 ∧ ¬ IsSquare (-1 : GaloisField p e) ∧
      ∀ σ : GaloisField p e ≃+* GaloisField p e, σ * σ = 1 → σ = 1 := by
  have hF : Nat.card (GaloisField p e) = p ^ e := GaloisField.card p e he
  have hq3 : Nat.card (GaloisField p e) % 4 = 3 := by rw [hF]; exact h4
  have hodd2 : Odd (Nat.card (GaloisField p e)) := Nat.odd_iff.mpr (by omega)
  refine ⟨two_ne_zero_of_odd_natCard hodd2, ?_, ?_⟩
  · intro hsq
    let _ := Fintype.ofFinite (GaloisField p e)
    have := FiniteField.isSquare_neg_one_iff.mp hsq
    rw [← Nat.card_eq_fintype_card] at this
    exact this hq3
  · intro σ hσσ
    by_contra hne
    have := (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.even_and_eq_pow_of_involution_prime
      (Fact.out : p.Prime) (Nat.one_le_iff_ne_zero.mpr he) hF hne hσσ).1
    exact (Nat.not_even_iff_odd.mpr (s26_odd_of_pow_mod_four h4)) this

theorem aut164L4 (p : ℕ) [Fact p.Prime] : Aut164L4 p := by
  intro e hadm h4 Y _ ψ hker hsurj β hβ
  obtain ⟨ψ, rfl⟩ : ∃ ψ₀ : SL(4, GaloisField p e) →* Y, ψ₀ = ψ := ⟨ψ, rfl⟩
  have he : e ≠ 0 := by
    have := hadm.2.1
    omega
  obtain ⟨h2, hn1, hσ⟩ := gf_facts p e he h4
  have hββ : ∀ y, β (β y) = y := fun y => by
    have := congrArg (fun f : MulAut Y => f y) hβ
    simpa [pow_two] using this
  obtain ⟨α, hα⟩ := LinearAut.exists_mulEquiv_lift (p := p) (by norm_num : 1 ≤ 4) ψ hsurj hker β
  have hαα : α * α = 1 := by
    have hperf : Group.IsPerfect SL(4, GaloisField p e) :=
      CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect (by norm_num)
    have := UnitaryAut.hom_eq_of_central_ker_perfect hker (α * α).toMonoidHom
      (1 : MulAut SL(4, GaloisField p e)).toMonoidHom (fun x => by
        show ψ (α (α x)) = ψ x
        rw [hα, hα, hββ])
    exact MulEquiv.ext fun x => DFunLike.congr_fun this x
  obtain ⟨k, hk⟩ := lin4_exists_fixed h2 hn1 hσ α hαα
  have hn : 2 ≤ 4 := by norm_num
  have hmem : k * rot4 (GaloisField p e) * k⁻¹ ∈
      (rootSL2 (GaloisField p e) hn).map (MulAut.conj k).toMonoidHom :=
    ⟨rot4 (GaloisField p e), ⟨MF15.rotJ, rfl⟩, rfl⟩
  refine ⟨(rootSL2 (GaloisField p e) hn).map (MulAut.conj k).toMonoidHom, ?_,
    k * rot4 (GaloisField p e) * k⁻¹, hmem, ?_, ?_⟩
  · exact CFSG.ClassicalInvolution.RouteD.longRootSet_subset_fundamentalSubgroups_psl (m := 3) hn
      ((mem_longRootSet_iff hn).mpr ⟨k, rfl⟩)
  · set s₀ : SL(4, GaloisField p e) := k * rot4 (GaloisField p e) * k⁻¹ with hs₀
    have hs₀4 : s₀ ^ 4 = 1 := by
      rw [hs₀, conj_pow, rot4_pow_four]
      group
    have hs₀2 : ψ (s₀ ^ 2) ≠ 1 := by
      intro h
      have hc : s₀ ^ 2 ∈ Subgroup.center SL(4, GaloisField p e) := hker h
      apply rot4_sq_not_central h2
      apply s26_center_of_conj k
      have : k * rot4 (GaloisField p e) ^ 2 * k⁻¹ = s₀ ^ 2 := by
        rw [hs₀, conj_pow]
      rw [this]
      exact hc
    have h4' : (ψ s₀) ^ 4 = 1 := by rw [← map_pow, hs₀4, map_one]
    have h2' : (ψ s₀) ^ 2 ≠ 1 := by rw [← map_pow]; exact hs₀2
    have := orderOf_eq_prime_pow (p := 2) (n := 1) (x := ψ s₀) (by simpa using h2')
      (by simpa using h4')
    exact this
  · exact (hα _).symm.trans (congrArg ψ hk)

end CFSG.ClassicalInvolution.ModelFacts.L6C
