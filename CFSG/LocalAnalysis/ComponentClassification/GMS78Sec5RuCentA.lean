module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5CoordR
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5Push
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
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5Setup
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

namespace Sec3.SzR

variable {G : Type} [Group G] [Finite G] {L T R R₂ : Subgroup G} {y d : G}

theorem conj_mul_inv_mem_gmsA_of_commute
    (hS : SzR G L T R 1 y d)
    (h34 : NoStronglyClosedAbelian G) (hR₂ : IsR₂ L T R R₂ d)
    (h4 : Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 4) {g : G}
    (hgR : g ∈ normalizer (R : Set G)) (hgA : ∀ b ∈ gmsA L T, g * b = b * g) {x : G}
    (hx : x ∈ R) : g * x * g⁻¹ * x⁻¹ ∈ gmsA L T := by
  classical
  obtain ⟨v, φ, c, e, Λ, hC⟩ := hS.exists_rCoords h34 hR₂
  obtain ⟨X, hX⟩ := hS.exists_isX h34
  have hΛ : Nat.card Λ = 4 := by rw [hC.card, h4]
  have hAR : gmsA L T ≤ R := gmsA_le_T.trans hS.T_le
  have hgR' : ∀ x ∈ R, g * x * g⁻¹ ∈ R := fun x hx => (mem_normalizer_iff.mp hgR x).mp hx
  have hφ1 : φ 1 = 0 := (hC.ker 1 (one_mem _)).mpr (one_mem _)
  have hwd : ∀ x ∈ R, ∀ x' ∈ R, φ x = φ x' → φ (g * x * g⁻¹) = φ (g * x' * g⁻¹) := by
    intro x hx x' hx' h
    have ha : x * x'⁻¹ ∈ gmsA L T := by
      rw [← hC.ker _ (mul_mem hx (inv_mem hx')), hC.mul _ hx _ (inv_mem hx'), h,
        ← hC.mul _ hx' _ (inv_mem hx'), mul_inv_cancel, hφ1]
    have e1 : g * x * g⁻¹ = (x * x'⁻¹) * (g * x' * g⁻¹) := by
      calc g * x * g⁻¹ = g * (x * x'⁻¹) * x' * g⁻¹ := by group
        _ = (x * x'⁻¹) * g * x' * g⁻¹ := by rw [hgA _ ha]
        _ = (x * x'⁻¹) * (g * x' * g⁻¹) := by group
    rw [e1, hC.mul _ (hAR ha) _ (hgR' x' hx'), (hC.ker _ (hAR ha)).mpr ha, zero_add]
  let M : BinaryGaloisField (2 * 1 + 1) × BinaryGaloisField (2 * 1 + 1) ×
      BinaryGaloisField (2 * 1 + 1) → BinaryGaloisField (2 * 1 + 1) ×
      BinaryGaloisField (2 * 1 + 1) × BinaryGaloisField (2 * 1 + 1) := fun z =>
    if hz : z.2.2 ∈ Λ then φ (g * (hC.surj z hz).choose * g⁻¹) else z
  have hM : ∀ x ∈ R, M (φ x) = φ (g * x * g⁻¹) := by
    intro x hx
    have hz := hC.mem x hx
    have hspec := (hC.surj (φ x) hz).choose_spec
    simp only [M, hz, ↓reduceDIte]
    exact hwd _ hspec.1 _ hx hspec.2
  have hmem : ∀ z : BinaryGaloisField (2 * 1 + 1) × BinaryGaloisField (2 * 1 + 1) ×
      BinaryGaloisField (2 * 1 + 1), z.2.2 ∈ Λ → (M z).2.2 ∈ Λ := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := hC.surj z hz
    rw [hM x hx]
    exact hC.mem _ (hgR' x hx)
  have hadd : ∀ z w : BinaryGaloisField (2 * 1 + 1) × BinaryGaloisField (2 * 1 + 1) ×
      BinaryGaloisField (2 * 1 + 1), z.2.2 ∈ Λ → w.2.2 ∈ Λ → M (z + w) = M z + M w := by
    intro z w hz hw
    obtain ⟨x, hx, rfl⟩ := hC.surj z hz
    obtain ⟨x', hx', rfl⟩ := hC.surj w hw
    rw [← hC.mul _ hx _ hx', hM _ (mul_mem hx hx'), hM _ hx, hM _ hx',
      ← hC.mul _ (hgR' _ hx) _ (hgR' _ hx')]
    congr 1
    group
  have hQ : ∀ z : BinaryGaloisField (2 * 1 + 1) × BinaryGaloisField (2 * 1 + 1) ×
      BinaryGaloisField (2 * 1 + 1), z.2.2 ∈ Λ → VLike.sqMap 1 c e (M z) = VLike.sqMap 1 c e z := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := hC.surj z hz
    rw [hM _ hx, ← hC.sq _ (hgR' _ hx), ← hC.sq _ hx]
    congr 1
    have h2 := hS.sq_mem_gmsA_of_mem_R h34 hX hx
    calc (g * x * g⁻¹) ^ 2 = g * x ^ 2 * g⁻¹ := by rw [sq, sq]; group
      _ = x ^ 2 := by rw [hgA _ h2]; group
  have hfix := VLike.eq_self_of_card_four hΛ c e M hmem hadd hQ (φ x) (hC.mem x hx)
  rw [hM x hx] at hfix
  rw [← hC.ker _ (mul_mem (hgR' x hx) (inv_mem hx)), hC.mul _ (hgR' x hx) _ (inv_mem hx), hfix,
    ← hC.mul _ hx _ (inv_mem hx), mul_inv_cancel, hφ1]

theorem normalizer_inf_centralizer_eq
    (hS : SzR G L T R 1 y d)
    (h34 : NoStronglyClosedAbelian G) (hR₂ : IsR₂ L T R R₂ d)
    (h4 : Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 4)
    (hCV : centralizer (gmsV L T : Set G) = T) :
    normalizer (R : Set G) ⊓ centralizer (gmsA L T : Set G) = R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hVel, -, -, -⟩ := hS.facts.vFacts hS.sec3 hS.foundation
  set D := normalizer (R : Set G) ⊓ centralizer (gmsA L T : Set G) with hD
  have hgA : ∀ g ∈ D, ∀ b ∈ gmsA L T, g * b = b * g := fun g hg b hb =>
    (mem_centralizer_iff.mp (mem_inf.mp hg).2 b hb).symm
  have hcomm : ∀ g ∈ D, ∀ x ∈ R, g * x * g⁻¹ * x⁻¹ ∈ gmsA L T := fun g hg x hx =>
    hS.conj_mul_inv_mem_gmsA_of_commute h34 hR₂ h4 (mem_inf.mp hg).1 (hgA g hg) hx
  have hRD : R ≤ D := fun r hr => mem_inf.mpr ⟨le_normalizer hr,
    mem_centralizer_iff.mpr fun b hb => (hS.commute_gmsA hr hb).symm⟩
  have hDV : D ≤ normalizer (gmsV L T : Set G) := by
    intro g hg
    refine mem_normalizer_of_conj_mem_of_finite fun s hs => ?_
    have e1 : g * s * g⁻¹ = (g * s * g⁻¹ * s⁻¹) * s := by group
    rw [e1]
    exact mul_mem (mem_sup_left (hcomm g hg s (hS.gmsV_le_R hs))) hs
  have hodd : ∀ h ∈ D, Odd (orderOf h) → h = 1 := by
    intro h hh hn
    have hcent : ∀ x ∈ R, h * x = x * h := by
      intro x hx
      set a := h * x * h⁻¹ * x⁻¹ with ha_def
      have ha : a ∈ gmsA L T := hcomm h hh x hx
      have hpow : ∀ k : ℕ, h ^ k * x * (h ^ k)⁻¹ = a ^ k * x := by
        intro k
        induction k with
        | zero => simp
        | succ k ih =>
          calc h ^ (k + 1) * x * (h ^ (k + 1))⁻¹ = h * (h ^ k * x * (h ^ k)⁻¹) * h⁻¹ := by
                rw [pow_succ']; group
            _ = h * a ^ k * h⁻¹ * (h * x * h⁻¹) := by rw [ih]; group
            _ = a ^ k * (h * x * h⁻¹) := by
                rw [(Commute.pow_right (show Commute h a from hgA h hh a ha) k).eq]; group
            _ = a ^ (k + 1) * x := by rw [ha_def, pow_succ]; group
      have h1 := hpow (orderOf h)
      rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one] at h1
      have han : a ^ orderOf h = 1 := by
        have := congrArg (· * x⁻¹) h1
        simpa using this.symm
      have ha2 : a ^ 2 = 1 := hVel.2 a (mem_sup_left ha)
      obtain ⟨m, hm⟩ := hn
      have ha1 : a = 1 := by
        rw [hm, pow_succ, pow_mul, ha2, one_pow, one_mul] at han
        exact han
      have e2 : h * x = (h * x * h⁻¹ * x⁻¹) * x * h := by group
      rw [e2, ← ha_def, ha1, one_mul]
    have hhT : h ∈ T := by
      rw [← hCV]
      exact mem_centralizer_iff.mpr fun s hs => (hcent s (hS.gmsV_le_R hs)).symm
    obtain ⟨k, hk⟩ := (hS.isR.isPGroup.to_le hS.T_le) ⟨h, hhT⟩
    have hk' : h ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hdvd := orderOf_dvd_of_pow_eq_one hk'
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    rcases j with _ | j
    · rw [pow_zero] at hj
      exact orderOf_eq_one_iff.mp hj
    · rw [hj, pow_succ] at hn
      exact absurd hn (Nat.not_odd_iff_even.mpr (even_two.mul_left _))
  have hD2 : IsPGroup 2 D := by
    intro g
    have hg0 : orderOf (g : G) ≠ 0 := (orderOf_pos (g : G)).ne'
    obtain ⟨k, m, hm, hgm⟩ := Nat.exists_eq_two_pow_mul_odd hg0
    refine ⟨k, Subtype.ext ?_⟩
    have ho : orderOf ((g : G) ^ 2 ^ k) = m := by
      rw [orderOf_pow_of_dvd (pow_ne_zero k two_ne_zero) (by rw [hgm]; exact dvd_mul_right _ _),
        hgm, Nat.mul_div_cancel_left _ (pow_pos two_pos k)]
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
    exact hodd _ (pow_mem g.2 _) (ho ▸ hm)
  exact hS.isSylowOf_normalizer.eq_of_le hRD hDV hD2

end Sec3.SzR

end CFSG.ComponentClassification.GMS78
