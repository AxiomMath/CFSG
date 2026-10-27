module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5KeyNotSylow
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuCert
public import CFSG.Adapters.FrobeniusKernel
public import CFSG.Adapters.GeneralizedFitting
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.CentralResidueMaps
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalizerClassLifting
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.PrincipalClassDefects
public import CFSG.Foundations
public import CFSG.Goldschmidt.StatementsG4
public import CFSG.Goldschmidt.Steps.G37Transport
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherGoldschmidtFour
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3SixCaseOne
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3SixProper
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitGlaubermanCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwo
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Lemma314Perm
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Lemma39
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5SzComm
public import CFSG.Sporadic.Bridge.M11CheckInputs
public import CFSG.Sporadic.Schreier.J4SNoCompCover
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
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2S0LeQuotientTorus
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction
public import CFSG.Walter.Bender1970.S2
public import CFSG.Walter.Bender1970.S3.Basic
public import CFSG.Walter.Bender1970.S3.OStar
public import CFSG.Walter.PSL2Facts
public import CFSG.Walter.W67.W2Lemma26A
public import Certificates.Certificate110
public import Certificates.Certificate7000
public import Certificates.Certificate7001
public import Certificates.Certificate7002
public import Certificates.Certificate7003
public import Certificates.Certificate7004
public import Certificates.Certificate7005
public import Certificates.Certificate7006
public import Certificates.Certificate7007
public import Certificates.Certificate7008
public import Certificates.Certificate7009
public import Certificates.Certificate7010
public import Certificates.Certificate7011
public import Certificates.Certificate8046
public import Certificates.Certificate8049
public import Certificates.Certificate8052

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard CFSG.BenderSuzuki.PFAppendixIII

namespace VLike

theorem closure_sqMap_perp_eq_top' {a : ℕ} (ha : 1 ≤ a)
    [Fintype (BinaryGaloisField (2 * a + 1))]
    (hK : Fintype.card (BinaryGaloisField (2 * a + 1)) = 2 ^ (2 * a + 1))
    {Λ : AddSubgroup (BinaryGaloisField (2 * a + 1))} (hΛ : 4 ≤ Nat.card Λ)
    {c e : BinaryGaloisField (2 * a + 1)}
    {x : BinaryGaloisField (2 * a + 1) × BinaryGaloisField (2 * a + 1) ×
      BinaryGaloisField (2 * a + 1)}
    (hx : x.2.2 ∈ Λ) (hr : x.2.1 ≠ 0) (hQ : sqMap a c e x = 0) :
    AddSubgroup.closure (sqMap a c e '' perp a c Λ x) = ⊤ := by
  by_cases hRu : a = 1 ∧ Nat.card Λ = 4
  · obtain ⟨rfl, h4⟩ := hRu
    by_cases hc : c = 0
    · subst hc
      by_cases hu : x.1 = 0
      · exact closure_eq_top_c_eq_zero_u_eq_zero hK hu
      by_cases hs : x.2.2 = 0
      · exact closure_eq_top_c_eq_zero_s_eq_zero hu hs hQ
      · exact closure_eq_top_c_eq_zero_s_ne_zero ha hK hs
    by_cases hu : x.1 = 0
    · by_cases hs : x.2.2 = 0
      · exact closure_eq_top_c_ne_zero_u_eq_zero_s_eq_zero ha hK (by omega) hc hu hs hr
      · exact closure_eq_top_c_ne_zero_u_eq_zero_s_ne_zero ha hK (by omega) hc hu hs hr
    · exact closure_sqMap_perp_eq_top_of_card_four h4 hc hx hu hr hQ
  · exact closure_sqMap_perp_eq_top ha hK hΛ hRu hr hQ

end VLike

namespace Sec3.SzR

theorem not_isSylowOf_normalizer
    {G : Type} [Group G] [Finite G] {L T R R₂ : Subgroup G} {a : ℕ} {y d : G}
    (hM : SzMinCounter G L a) (hS : SzR G L T R a y d) (hR₂ : IsR₂ L T R R₂ d) :
    ¬ IsSylowOf 2 R (normalizer (R : Set G)) := by
  intro hRN
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRG : IsSylowOf 2 R ⊤ := isSylowOf_top_of_isSylowOf_normalizer' hRN
  have h34 : NoStronglyClosedAbelian G := fun S _ hAS hAab hA1 hcl =>
    hM.hyp.lemma34 S hAS hAab hA1 hcl
  obtain ⟨v, φ, c, e, Λ, hC⟩ := hS.exists_rCoords h34 hR₂
  have ha : 1 ≤ a := hM.one_le
  have : Fintype (BinaryGaloisField (2 * a + 1)) := Fintype.ofFinite _
  have hK : Fintype.card (BinaryGaloisField (2 * a + 1)) = 2 ^ (2 * a + 1) := by
    rw [← Nat.card_eq_fintype_card]
    simpa [BinaryGaloisField] using GaloisField.card 2 (2 * a + 1) (by omega)
  have hΛ4 : 4 ≤ Nat.card Λ := by
    rw [hC.card]
    obtain ⟨E, hE, -, hE4⟩ := hS.sec3.exists_four_le
    exact hE4 ▸ Subgroup.card_le_of_le hE
  obtain ⟨-, hR2, hRidx⟩ := isSylowOf_iff.mp hRG
  rw [relIndex_top_right] at hRidx
  let S : Sylow 2 G := hR2.toSylow hRidx
  have hSc : (S : Subgroup G) = R := IsPGroup.toSylow_coe hR2 hRidx
  have hAR : gmsA L T ≤ R := gmsA_le_T.trans hS.T_le
  have hA1 : gmsA L T ≠ ⊥ := by
    intro hb
    obtain ⟨b, hb', hvb⟩ := hC.v_surj 1
    rw [hb, mem_bot] at hb'
    have h0 : v 1 = 0 := by
      have := hC.v_mul 1 (one_mem _) 1 (one_mem _)
      rw [mul_one] at this
      exact left_eq_add.mp this
    rw [hb', h0] at hvb
    exact zero_ne_one hvb
  have hAab : IsMulCommutative (gmsA L T) := by
    obtain ⟨-, hVel, -, -, -⟩ := hS.facts.vFacts hS.sec3 hS.foundation
    exact (isElemAbelian_of_le hVel le_sup_left).1
  refine h34 S (gmsA L T) (hSc ▸ hAR) hAab hA1 fun b hb g hg => ?_
  by_contra hx
  have hxR : g⁻¹ * b * g ∈ R := hSc ▸ hg
  have hconj : g * (g⁻¹ * b * g) * g⁻¹ ∈ gmsA L T := by
    rw [show g * (g⁻¹ * b * g) * g⁻¹ = b by group]
    exact hb
  have hQ := hS.sqMap_eq_zero_of_conj_mem hC hxR hconj
  have hr := hS.snd_ne_zero_of_conj_mem h34 hR₂ hC hxR hx hconj
  exact hS.closure_sqMap_ne_top_of_conj_mem h34 hC hRG hxR hx hconj
    (VLike.closure_sqMap_perp_eq_top' ha hK hΛ4 (hC.mem _ hxR) hr hQ)

end Sec3.SzR

end CFSG.ComponentClassification.GMS78
