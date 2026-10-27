module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5Swap
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

namespace Sec3.SzR

variable {G : Type} [Group G] [Finite G] {L T R R₂ : Subgroup G} {a : ℕ} {y d : G}

theorem exists_vLikeHyp
    (hS : SzR G L T R a y d) (h34 : NoStronglyClosedAbelian G) (hR₂ : IsR₂ L T R R₂ d)
    (h4 : 4 ≤ Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G))
    {v : G → BinaryGaloisField (2 * a + 1)}
    {φ : G → BinaryGaloisField (2 * a + 1) × BinaryGaloisField (2 * a + 1) ×
      BinaryGaloisField (2 * a + 1)}
    {c e : BinaryGaloisField (2 * a + 1)} {Λ : AddSubgroup (BinaryGaloisField (2 * a + 1))}
    (hC : RCoords L T R R₂ a v φ c e Λ) [Fintype (BinaryGaloisField (2 * a + 1))]
    (hK : Fintype.card (BinaryGaloisField (2 * a + 1)) = 2 ^ (2 * a + 1)) {g : G}
    (hg : g ∈ normalizer (R : Set G)) (hgV : rightConjugate (gmsV L T) g ≠ gmsV L T) :
    ∃ E : AddSubgroup (BinaryGaloisField (2 * a + 1) × BinaryGaloisField (2 * a + 1) ×
      BinaryGaloisField (2 * a + 1)), VLike.Hyp a c e Λ E := by
  obtain ⟨X, hX⟩ := hS.exists_isX h34
  obtain ⟨-, -, -, hVC, -⟩ := hS.facts.vFacts hS.sec3 hS.foundation
  have hT₀el := hS.sec3.isElemAbelian_T₀ hS.foundation
  have hcomm : ∀ x ∈ R, ∀ z ∈ R, x * z * x⁻¹ * z⁻¹ ∈ gmsA L T := fun x hx z hz =>
    hS.commutator_mem_gmsA h34 hx hz
  have hgN := hS.normalizer_le_normalizer_gmsA hR₂ hg
  have hgA : ∀ b ∈ gmsA L T, g * b * g⁻¹ ∈ gmsA L T := fun b hb =>
    (mem_normalizer_iff.mp hgN b).mp hb
  have hgR : ∀ x ∈ R, g⁻¹ * x * g ∈ R := fun x hx => by
    simpa using (mem_normalizer_iff.mp (inv_mem hg) x).mp hx
  have hgR' : ∀ x ∈ R, g * x * g⁻¹ ∈ R := fun x hx => (mem_normalizer_iff.mp hg x).mp hx
  have hT₀R : ∀ s ∈ T ⊓ centralizer (L : Set G), s ∈ R := fun s hs => hS.T_le (mem_inf.mp hs).1
  have hv1 : v 1 = 0 := by
    have h := hC.v_mul 1 (one_mem _) 1 (one_mem _)
    rw [mul_one] at h
    linear_combination -h
  have hφ1 : φ 1 = 0 := (hC.ker 1 (one_mem _)).mpr (one_mem _)
  have hφeq : ∀ x ∈ R, ∀ x' ∈ R, φ x = φ x' → x * x'⁻¹ ∈ gmsA L T := by
    intro x hx x' hx' h
    rw [← hC.ker _ (mul_mem hx (inv_mem hx')), hC.mul _ hx _ (inv_mem hx'), h,
      ← hC.mul _ hx' _ (inv_mem hx'), mul_inv_cancel, hφ1]
  obtain ⟨E, hE⟩ : ∃ E : AddSubgroup (BinaryGaloisField (2 * a + 1) ×
      BinaryGaloisField (2 * a + 1) × BinaryGaloisField (2 * a + 1)),
      ∀ z, z ∈ E ↔ ∃ s ∈ T ⊓ centralizer (L : Set G), φ (g⁻¹ * s * g) = z :=
    ⟨{ carrier := {z | ∃ s ∈ T ⊓ centralizer (L : Set G), φ (g⁻¹ * s * g) = z}
       add_mem' := by
         rintro _ _ ⟨s, hs, rfl⟩ ⟨s', hs', rfl⟩
         refine ⟨s * s', mul_mem hs hs', ?_⟩
         rw [← hC.mul _ (hgR _ (hT₀R s hs)) _ (hgR _ (hT₀R s' hs'))]
         congr 1
         group
       zero_mem' := ⟨1, one_mem _, by rw [show g⁻¹ * 1 * g = 1 by group, hφ1]⟩
       neg_mem' := by
         rintro _ ⟨s, hs, rfl⟩
         exact ⟨s, hs, Prod.ext (CharTwo.neg_eq _).symm
           (Prod.ext (CharTwo.neg_eq _).symm (CharTwo.neg_eq _).symm)⟩ }, fun z => Iff.rfl⟩
  have hφs0 : ∀ s ∈ T ⊓ centralizer (L : Set G), φ (g⁻¹ * s * g) = 0 → s = 1 := by
    intro s hs h0
    have hA := (hC.ker _ (hgR _ (hT₀R s hs))).mp h0
    have hsA : s ∈ gmsA L T := by simpa [mul_assoc] using hgA _ hA
    have hs' : s ∈ (T ⊓ centralizer (L : Set G)) ⊓ gmsA L T := mem_inf.mpr ⟨hs, hsA⟩
    rw [hS.lemma313.inf_gmsA_eq_bot mem_delta_T₀, mem_bot] at hs'
    exact hs'
  have hs1 : ∀ s ∈ T ⊓ centralizer (L : Set G), φ (g⁻¹ * s * g) ≠ 0 → s ≠ 1 := by
    rintro s - h rfl
    exact h (by rw [show g⁻¹ * 1 * g = 1 by group, hφ1])
  have htwo : ∃ z ∈ E, ∃ z' ∈ E, z ≠ 0 ∧ z' ≠ 0 ∧ z ≠ z' := by
    obtain ⟨s₁, hs₁, s₂, hs₂, h1, h2, h12⟩ := exists_two_ne_one_of_four_le h4
    refine ⟨_, (hE _).mpr ⟨s₁, hs₁, rfl⟩, _, (hE _).mpr ⟨s₂, hs₂, rfl⟩,
      fun h => h1 (hφs0 _ hs₁ h), fun h => h2 (hφs0 _ hs₂ h), fun h => h12 ?_⟩
    have h3 : φ (g⁻¹ * (s₁ * s₂) * g) = 0 := by
      rw [show g⁻¹ * (s₁ * s₂) * g = g⁻¹ * s₁ * g * (g⁻¹ * s₂ * g) by group,
        hC.mul _ (hgR _ (hT₀R _ hs₁)) _ (hgR _ (hT₀R _ hs₂)), h]
      exact Prod.ext (CharTwo.add_self_eq_zero _)
        (Prod.ext (CharTwo.add_self_eq_zero _) (CharTwo.add_self_eq_zero _))
    have h5 := hφs0 _ (mul_mem hs₁ hs₂) h3
    rw [eq_inv_of_mul_eq_one_right h5, inv_eq_of_mul_eq_one_right
      (by rw [← sq]; exact hT₀el.2 s₁ hs₁)]
  have hVgV : rightConjugate (gmsV L T) g ⊓ gmsV L T = gmsA L T :=
    (hS.rightConjugate_eq_or_inf_eq hR₂ hg).resolve_left hgV
  have hinf : ∀ z ∈ E, z.1 = 0 → z.2.1 = 0 → z = 0 := by
    intro z hz h1 h2
    obtain ⟨s, hs, rfl⟩ := (hE z).mp hz
    have hsR := hgR _ (hT₀R s hs)
    obtain ⟨s', hs', hs'φ⟩ := hC.T₀_surj _ (hC.mem _ hsR)
    have hmem := hφeq _ hsR _ (hT₀R s' hs') (by rw [hs'φ]; exact Prod.ext h1 (Prod.ext h2 rfl))
    have hV : g⁻¹ * s * g ∈ gmsV L T := by
      have e : g⁻¹ * s * g = g⁻¹ * s * g * s'⁻¹ * s' := by group
      rw [e]
      exact mul_mem (mem_sup_left hmem) (mem_sup_right hs')
    have hVg : g⁻¹ * s * g ∈ rightConjugate (gmsV L T) g := by
      rw [mem_rightConjugate_iff]
      simpa [mul_assoc] using (mem_sup_right hs : s ∈ gmsV L T)
    have hA : g⁻¹ * s * g ∈ gmsA L T := by rw [← hVgV]; exact mem_inf.mpr ⟨hVg, hV⟩
    exact (hC.ker _ hsR).mpr hA
  have hsq : ∀ z ∈ E, VLike.sqMap a c e z = 0 := by
    intro z hz
    obtain ⟨s, hs, rfl⟩ := (hE z).mp hz
    rw [← hC.sq _ (hgR _ (hT₀R s hs))]
    have e1 : (g⁻¹ * s * g) ^ 2 = 1 := by
      have e2 : (g⁻¹ * s * g) ^ 2 = g⁻¹ * s ^ 2 * g := by simp only [sq]; group
      rw [e2, hT₀el.2 s hs]
      group
    rw [e1, hv1]
  have hsurj : ∀ z ∈ E, z ≠ 0 → ∀ w, ∃ z' : BinaryGaloisField (2 * a + 1) ×
      BinaryGaloisField (2 * a + 1) × BinaryGaloisField (2 * a + 1),
      z'.2.2 ∈ Λ ∧ VLike.commMap a c z z' = w := by
    intro z hz hz0 w
    obtain ⟨s, hs, rfl⟩ := (hE z).mp hz
    obtain ⟨b, hb, hbw⟩ := hC.v_surj w
    obtain ⟨r, hr, hrb⟩ := hS.exists_commutator_eq hR₂ hs (hs1 s hs hz0) (hgA _ (inv_mem hb))
    have hrR := hR₂.le_R hr
    refine ⟨φ (g⁻¹ * r * g), hC.mem _ (hgR _ hrR), ?_⟩
    rw [← hC.comm _ (hgR _ (hT₀R s hs)) _ (hgR _ hrR)]
    have e1 : g⁻¹ * s * g * (g⁻¹ * r * g) * (g⁻¹ * s * g)⁻¹ * (g⁻¹ * r * g)⁻¹ =
        g⁻¹ * (r * s * r⁻¹ * s⁻¹)⁻¹ * g := by group
    rw [e1, hrb, show g⁻¹ * (g * b⁻¹ * g⁻¹)⁻¹ * g = b by group, hbw]
  have hker : ∀ z ∈ E, ∀ z' ∈ E, z ≠ 0 → z' ≠ 0 → ∀ x : BinaryGaloisField (2 * a + 1) ×
      BinaryGaloisField (2 * a + 1) × BinaryGaloisField (2 * a + 1), x.2.2 ∈ Λ →
      VLike.commMap a c z x = 0 → VLike.commMap a c z' x = 0 := by
    intro z hz z' hz' hz0 _ x hx h0
    obtain ⟨s, hs, rfl⟩ := (hE z).mp hz
    obtain ⟨s', hs', rfl⟩ := (hE z').mp hz'
    obtain ⟨w, hw, rfl⟩ := hC.surj x hx
    rw [← hC.comm _ (hgR _ (hT₀R s hs)) _ hw] at h0
    rw [← hC.comm _ (hgR _ (hT₀R s' hs')) _ hw]
    have h1 := hC.v_inj _ (hcomm _ (hgR _ (hT₀R s hs)) _ hw) h0
    have hc1 : g * w * g⁻¹ * s = s * (g * w * g⁻¹) := by
      have h3 : g⁻¹ * s * g * w = w * (g⁻¹ * s * g) := by
        calc g⁻¹ * s * g * w =
            g⁻¹ * s * g * w * (g⁻¹ * s * g)⁻¹ * w⁻¹ * (w * (g⁻¹ * s * g)) := by group
          _ = w * (g⁻¹ * s * g) := by rw [h1, one_mul]
      calc g * w * g⁻¹ * s = g * (w * (g⁻¹ * s * g)) * g⁻¹ := by group
        _ = g * (g⁻¹ * s * g * w) * g⁻¹ := by rw [h3]
        _ = s * (g * w * g⁻¹) := by group
    have hT := hS.mem_T_of_commute_T₀ hR₂ hs (hs1 s hs hz0) (hgR' _ hw) hc1
    have hc2 : g * w * g⁻¹ * s' = s' * (g * w * g⁻¹) :=
      mem_centralizer_iff.mp (hVC (mem_sup_right hs')) _ (by rw [hS.eq_gmsW] at hT; exact hT)
    have e1 : g⁻¹ * s' * g * w * (g⁻¹ * s' * g)⁻¹ * w⁻¹ = 1 := by
      calc g⁻¹ * s' * g * w * (g⁻¹ * s' * g)⁻¹ * w⁻¹ =
          g⁻¹ * (s' * (g * w * g⁻¹) * s'⁻¹ * (g * w * g⁻¹)⁻¹) * g := by group
        _ = g⁻¹ * (g * w * g⁻¹ * s' * s'⁻¹ * (g * w * g⁻¹)⁻¹) * g := by rw [← hc2]
        _ = 1 := by group
    rw [e1, hv1]
  exact ⟨E, ⟨hS.one_le, hK, by rw [hC.card]; exact h4,
    fun z hz => by obtain ⟨s, hs, rfl⟩ := (hE z).mp hz; exact hC.mem _ (hgR _ (hT₀R s hs)),
    htwo, hinf, hsq, hsurj, hker⟩⟩

theorem exists_mem_normalizer_ne
    (hS : SzR G L T R a y d) (hNS : ¬ IsSylowOf 2 R (normalizer (R : Set G))) :
    ∃ g ∈ normalizer (R : Set G), rightConjugate (gmsV L T) g ≠ gmsV L T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS', hRS⟩ := AS76b.exists_isSylowOf_le (le_normalizer : R ≤ normalizer (R : Set G))
    hS.isR.isPGroup
  have hne : R ≠ S := fun h => hNS (by subst h; exact hS')
  obtain ⟨z, hzS, hzR⟩ := IsConcreteLE.exists_of_lt (lt_of_le_of_ne hRS hne)
  refine ⟨z, hS'.le hzS, fun hzV => hzR ?_⟩
  have hzN : z ∈ normalizer (gmsV L T : Set G) := (rightConjugate_eq_self_iff _ z).mp hzV
  have hle : R ⊔ zpowers z ≤ S := sup_le hRS (zpowers_le.mpr hzS)
  have hP : IsPGroup 2 (R ⊔ zpowers z : Subgroup G) := hS'.isPGroup.to_le hle
  have hRV : R ≤ normalizer (gmsV L T : Set G) := hS.isR.le_normalizer_gmsV
  have hsup : R ⊔ zpowers z ≤ normalizer (gmsV L T : Set G) :=
    sup_le hRV (zpowers_le.mpr hzN)
  have heq := hS.isSylowOf_normalizer.eq_of_le le_sup_left hsup hP
  rw [← heq]
  exact mem_sup_right (mem_zpowers z)

theorem exists_special
    (hS : SzR G L T R 1 y d) (h34 : NoStronglyClosedAbelian G)
    (hR₂ : IsR₂ L T R R₂ d) (h4 : Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 4)
    (hNS : ¬ IsSylowOf 2 R (normalizer (R : Set G)))
    {v : G → BinaryGaloisField (2 * 1 + 1)}
    {φ : G → BinaryGaloisField (2 * 1 + 1) × BinaryGaloisField (2 * 1 + 1) ×
      BinaryGaloisField (2 * 1 + 1)}
    {c e : BinaryGaloisField (2 * 1 + 1)} {Λ : AddSubgroup (BinaryGaloisField (2 * 1 + 1))}
    (hC : RCoords L T R R₂ 1 v φ c e Λ) :
    ∃ c' e' p q : Fin 8, RuCode.toGF c' = c ∧ RuCode.toGF e' = e ∧
      CFSG.GMS78Ru.canon p q = true ∧
      (∀ t, RuCode.toGF t ∈ Λ ↔ t ∈ CFSG.GMS78Ru.lamList p q) ∧
      (c', e', p, q) ∈ CFSG.GMS78Ru.specialList := by
  have : Fintype (BinaryGaloisField (2 * 1 + 1)) := Fintype.ofFinite _
  have hK : Fintype.card (BinaryGaloisField (2 * 1 + 1)) = 2 ^ (2 * 1 + 1) := by
    rw [← Nat.card_eq_fintype_card]
    simpa [BinaryGaloisField] using GaloisField.card 2 (2 * 1 + 1) (by omega)
  have hΛ : Nat.card Λ = 4 := by rw [hC.card, h4]
  obtain ⟨g, hg, hgV⟩ := hS.exists_mem_normalizer_ne hNS
  obtain ⟨E, hE⟩ := hS.exists_vLikeHyp h34 hR₂ h4.ge hC hK hg hgV
  exact VLike.Hyp.special_of_card_four hΛ hE

end Sec3.SzR

end CFSG.ComponentClassification.GMS78
