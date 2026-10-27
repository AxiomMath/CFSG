module

public import CFSG.GH74.Uniqueness.SU.SU10Prod
public import CFSG.GH74.Uniqueness.SU.SU10BenderAbs
public import CFSG.GH74.Uniqueness.SU.SU10Fusion
public import CFSG.GH74.Uniqueness.SU.SU10Bar
public import CFSG.GH74.Uniqueness.SU.SU8Stmts
public import CFSG.CharacterTheory.TwoRankLowerBound.Helpers
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.CentralResidueMaps
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalizerClassLifting
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.PrincipalClassDefects
public import CFSG.CharacterTheory.Semidihedral.ElementStructure
public import CFSG.CharacterTheory.Semidihedral.Principal.DegreeZeroGram
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
public import CFSG.GH74.GLS.Defs
public import CFSG.GH74.GLS.Pattern
public import CFSG.GH74.L5U5.ModelsBridge
public import CFSG.GH74.Statements
public import CFSG.GH74.Uniqueness.SU.KInputs
public import CFSG.LieType.CurtisTits.Conclusion
public import CFSG.LinearAlgebra.LinearGroups.LinearTwo
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwo
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupExhaustion
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupRanks
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicFourLarge
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicTwoFourGenerators
public import CFSG.LocalAnalysis.LargeEvenClassification.MacWilliamsReduction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourFullObstruction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourProperSubgroups
public import CFSG.LocalAnalysis.SectionRank.CentralLift
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
public import CFSG.Walter.JRAssembly
public import CFSG.Walter.JRFacts
public import Certificates.Certificate1
public import Certificates.Certificate10
public import Certificates.Certificate100
public import Certificates.Certificate101
public import Certificates.Certificate102
public import Certificates.Certificate103
public import Certificates.Certificate104
public import Certificates.Certificate105
public import Certificates.Certificate106
public import Certificates.Certificate107
public import Certificates.Certificate108
public import Certificates.Certificate109
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
public import Certificates.Certificate96
public import Certificates.Certificate97
public import Certificates.Certificate98
public import Certificates.Certificate99

public section

namespace CFSG.GH74.Uniqueness.SU.SU10

open Subgroup CFSG.GH74.Uniqueness.SU.SU8 CFSG.GH74.Uniqueness.Bender

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem mem_zpowers_invol {w u : X} (hw : orderOf w = 2) (hu : u ∈ zpowers w) :
    u = 1 ∨ u = w := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
  have h : w ^ (k % 2) = w ^ k := by simpa [hw] using zpow_mod_orderOf w k
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · left
    rw [← h, h0, zpow_zero]
  · right
    rw [← h, h1, zpow_one]

theorem bender_config (T : Sylow 2 X) {K : Subgroup X} [K.Normal]
    (hK : CFSG.BenderSuzuki.IsBenderGroup ↥K) {w : X} (hw2 : orderOf w = 2)
    (hwc : ∀ x : X, x * w = w * x) (hwT : w ∈ (T : Subgroup X))
    (hC : Open.pRank 2 (centralizer (K : Set X)) = 1)
    (hle : Subgroup.closure {g : X | g ∈ (T : Subgroup X) ∧ g * g = 1} ≤
      K ⊔ centralizer (K : Set X)) :
    K ⊓ centralizer (K : Set X) = ⊥ ∧
    (∀ q ∈ (T : Subgroup X) ⊓ centralizer (K : Set X), q * q = 1 → q = 1 ∨ q = w) ∧
    (∀ t ∈ (T : Subgroup X), t * t = 1 → t ∈ K ∨ t * w ∈ K) ∧
    (∀ a ∈ (T : Subgroup X), ∀ b ∈ (T : Subgroup X), a * a = 1 → b * b = 1 → a * b = b * a) ∧
    ∃ (m : ℕ) (y : X), 1 ≤ m ∧ Nat.card (omegaOne (T : Subgroup X)) = 2 ^ (m + 1) ∧
      y ∈ normalizer ((omegaOne (T : Subgroup X) : Subgroup X) : Set X) ∧ y * w = w * y ∧
      ∀ a ∈ omegaOne (T : Subgroup X), ∀ b ∈ omegaOne (T : Subgroup X), a ≠ 1 → a ≠ w →
        b ≠ 1 → b ≠ w →
        ∃ j : ℤ, y ^ j * a * (y ^ j)⁻¹ = b ∨ y ^ j * a * (y ^ j)⁻¹ = b * w := by
  classical
  have hww : w * w = 1 := by
    have := pow_orderOf_eq_one w
    rwa [hw2, sq] at this
  have hw1 : w ≠ 1 := fun h => by
    rw [h, orderOf_one] at hw2
    exact absurd hw2 (by norm_num)
  have hwcomm : ∀ x : X, Commute x w := hwc
  obtain ⟨n, i, e, hB⟩ := isBenderGroup_iff_exists_benderType.mp hK
  have hsimple : IsSimpleGroup ↥K := hB.isSimple
  have hnc : ∃ a b : ↥K, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    exact hB.isSimpleBenderGroup.not_commutative hcon
  have hKC : K ⊓ centralizer (K : Set X) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxK, hxC⟩
    have hcen : (⟨x, hxK⟩ : ↥K) ∈ Subgroup.center ↥K := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC g g.2)
    rw [CFSG.TwoRankLowerBound.Helpers.center_eq_bot_of_nonabelian_simple ↥K hnc,
      Subgroup.mem_bot] at hcen
    have := congrArg Subtype.val hcen
    simpa using this
  have hwC : w ∈ centralizer (K : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h _
    exact hwc h
  have hwK : w ∉ K := fun h => hw1 (by
    have : w ∈ K ⊓ centralizer (K : Set X) := ⟨h, hwC⟩
    rw [hKC] at this
    simpa using this)
  have hKCcomm : ∀ a ∈ K, ∀ b ∈ centralizer (K : Set X), a * b = b * a :=
    fun a ha b hb => Subgroup.mem_centralizer_iff.mp hb a ha
  obtain ⟨Q, hQ⟩ := CFSG.Glauberman.sylow_inf_normal (p := 2) T (N := K)
  obtain ⟨hn2, Z, y, hZQ, hZel, hZcard, hZinv, hyN, hytrans⟩ := benderType_structure hB Q
  have hZ₀T : ∀ g ∈ Z.map K.subtype, g ∈ (T : Subgroup X) ∧ g ∈ K := by
    rintro _ ⟨z, hz, rfl⟩
    have h1 := hZQ hz
    rw [hQ, Subgroup.mem_subgroupOf] at h1
    exact ⟨h1.1, z.2⟩
  have hZ₀el : Open.IsElemAbelian 2 (Z.map K.subtype) := isElemAbelian_map hZel
  have hZ₀card : Nat.card (Z.map K.subtype) = 2 ^ n :=
    (Subgroup.card_map_of_injective K.subtype_injective).trans hZcard
  have hZ₀inv : ∀ g ∈ (T : Subgroup X) ⊓ K, g * g = 1 → g ∈ Z.map K.subtype := by
    rintro g ⟨hgT, hgK⟩ hg2
    have hgQ : (⟨g, hgK⟩ : ↥K) ∈ (Q : Subgroup ↥K) := by
      rw [hQ, Subgroup.mem_subgroupOf]
      exact ⟨hgT, hgK⟩
    have hg2' : (⟨g, hgK⟩ : ↥K) * ⟨g, hgK⟩ = 1 := Subtype.ext hg2
    exact ⟨⟨g, hgK⟩, hZinv _ hgQ hg2', rfl⟩
  have hy₀N : (y : X) ∈ normalizer ((Z.map K.subtype : Subgroup X) : Set X) :=
    Subgroup.le_normalizer_map K.subtype ⟨y, hyN, rfl⟩
  have hy₀trans : ∀ a ∈ Z.map K.subtype, ∀ b ∈ Z.map K.subtype, a ≠ 1 → b ≠ 1 →
      ∃ j : ℤ, (y : X) ^ j * a * ((y : X) ^ j)⁻¹ = b := by
    rintro _ ⟨a', ha', rfl⟩ _ ⟨b', hb', rfl⟩ ha1 hb1
    have ha1' : a' ≠ 1 := fun h => ha1 (by rw [h]; rfl)
    have hb1' : b' ≠ 1 := fun h => hb1 (by rw [h]; rfl)
    obtain ⟨j, hj⟩ := hytrans a' ha' b' hb' ha1' hb1'
    refine ⟨j, ?_⟩
    have := congrArg Subtype.val hj
    simpa using this
  set Z₀ : Subgroup X := Z.map K.subtype with hZ₀def
  have hq : ∀ q ∈ (T : Subgroup X) ⊓ centralizer (K : Set X), q * q = 1 → q = 1 ∨ q = w := by
    intro q hq hqq
    by_cases hq1 : q = 1
    · exact Or.inl hq1
    · right
      by_contra hqw
      have hq2 : orderOf q = 2 := orderOf_eq_prime (by rw [sq]; exact hqq) hq1
      have h2 := two_le_pRank_of_commuting_involutions (Q := centralizer (K : Set X)) hq.2 hwC hq2
        hw2 hqw (hwc q)
      omega
  have hinv : ∀ t ∈ (T : Subgroup X), t * t = 1 → ∃ ζ ∈ Z₀, t = ζ ∨ t = ζ * w := by
    intro t htT htt
    have htle : t ∈ K ⊔ centralizer (K : Set X) := hle (Subgroup.subset_closure ⟨htT, htt⟩)
    have hPS := isSylowIn_inf_normal T (K ⊔ centralizer (K : Set X))
    obtain ⟨r, hr, q, hq', hrq⟩ :=
      mem_sup_of_isSylowIn_commute hKCcomm hPS (t := t) ⟨htT, htle⟩
    have hcomm : r * q = q * r := hKCcomm r hr.2 q hq'.2
    have h1 : (r * r) * (q * q) = 1 := by
      calc (r * r) * (q * q) = r * (r * q) * q := by group
        _ = r * (q * r) * q := by rw [hcomm]
        _ = (r * q) * (r * q) := by group
        _ = 1 := by rw [hrq]; exact htt
    have h2 : r * r = (q * q)⁻¹ := mul_eq_one_iff_eq_inv.mp h1
    have h3 : r * r ∈ K ⊓ centralizer (K : Set X) :=
      Subgroup.mem_inf.mpr ⟨K.mul_mem hr.2 hr.2, by
        rw [h2]
        exact (centralizer (K : Set X)).inv_mem ((centralizer (K : Set X)).mul_mem hq'.2 hq'.2)⟩
    rw [hKC, Subgroup.mem_bot] at h3
    have h4 : q * q = 1 := by
      rw [h3, one_mul] at h1
      exact h1
    refine ⟨r, hZ₀inv r ⟨hr.1.1, hr.2⟩ h3, ?_⟩
    rcases hq q ⟨hq'.1.1, hq'.2⟩ h4 with hq1 | hqw
    · left
      rw [← hrq, hq1, mul_one]
    · right
      rw [← hrq, hqw]
  have hinvK : ∀ t ∈ (T : Subgroup X), t * t = 1 → t ∈ K ∨ t * w ∈ K := by
    intro t htT htt
    obtain ⟨ζ, hζ, h⟩ := hinv t htT htt
    rcases h with h | h
    · rw [h]
      exact Or.inl (hZ₀T ζ hζ).2
    · refine Or.inr ?_
      rw [h, mul_assoc, hww, mul_one]
      exact (hZ₀T ζ hζ).2
  have hZ₀comm := (SU1.isElemAbelian_iff.mp hZ₀el).1
  have hcommT : ∀ a ∈ (T : Subgroup X), ∀ b ∈ (T : Subgroup X), a * a = 1 → b * b = 1 →
      a * b = b * a := by
    intro a ha b hb haa hbb
    obtain ⟨ζ₁, hζ₁, h₁⟩ := hinv a ha haa
    obtain ⟨ζ₂, hζ₂, h₂⟩ := hinv b hb hbb
    have hZc : Commute ζ₁ ζ₂ := hZ₀comm ζ₁ hζ₁ ζ₂ hζ₂
    rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂ <;> rw [h₁, h₂]
    · exact hZc.eq
    · exact (Commute.mul_right hZc (hwcomm ζ₁)).eq
    · exact (Commute.mul_left hZc (hwcomm ζ₂).symm).eq
    · exact (Commute.mul_right (Commute.mul_left hZc (hwcomm ζ₂).symm)
        (Commute.mul_left (hwcomm ζ₁) (Commute.refl w))).eq
  refine ⟨hKC, hq, hinvK, hcommT, ?_⟩
  have hZwcomm : ∀ a ∈ Z₀, ∀ b ∈ zpowers w, a * b = b * a := by
    intro a _ b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact ((hwcomm a).zpow_right k).eq
  have hAeq : omegaOne (T : Subgroup X) = Z₀ ⊔ zpowers w := by
    unfold omegaOne
    apply le_antisymm
    · refine (Subgroup.closure_le _).mpr ?_
      rintro t ⟨htT, htt⟩
      obtain ⟨ζ, hζ, h⟩ := hinv t htT htt
      rcases h with rfl | rfl
      · exact Subgroup.mem_sup_left hζ
      · exact (Z₀ ⊔ zpowers w).mul_mem (Subgroup.mem_sup_left hζ)
          (Subgroup.mem_sup_right (Subgroup.mem_zpowers w))
    · refine sup_le ?_ ?_
      · intro ζ hζ
        refine Subgroup.subset_closure ⟨(hZ₀T ζ hζ).1, ?_⟩
        have := (SU1.isElemAbelian_iff.mp hZ₀el).2 ζ hζ
        simpa [sq] using this
      · rw [Subgroup.zpowers_le]
        exact Subgroup.subset_closure ⟨hwT, hww⟩
  have hZw : Z₀ ⊓ zpowers w = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxZ, hxw⟩
    rcases mem_zpowers_invol hw2 hxw with rfl | rfl
    · exact one_mem _
    · exact absurd (hZ₀T _ hxZ).2 hwK
  have hAcard : Nat.card (omegaOne (T : Subgroup X)) = 2 ^ (n + 1) := by
    rw [hAeq]
    obtain ⟨h, -⟩ := CFSG.Walter.W67.card_sup_mul_card_inf_of_commute Z₀ (zpowers w) hZwcomm
    rw [hZw, Subgroup.card_bot, mul_one] at h
    rw [h, hZ₀card, Nat.card_zpowers, hw2]
    ring
  have hyc : ∀ u ∈ zpowers w, (y : X) * u = u * (y : X) := by
    intro u hu
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    exact ((hwcomm (y : X)).zpow_right k).eq
  have hyw : ∀ u ∈ zpowers w, (y : X) * u * (y : X)⁻¹ = u := by
    intro u hu
    rw [hyc u hu, mul_inv_cancel_right]
  have hyw' : ∀ u ∈ zpowers w, (y : X)⁻¹ * u * (y : X) = u := by
    intro u hu
    calc (y : X)⁻¹ * u * (y : X) = (y : X)⁻¹ * (u * (y : X)) := mul_assoc _ _ _
      _ = (y : X)⁻¹ * ((y : X) * u) := by rw [hyc u hu]
      _ = u := inv_mul_cancel_left _ _
  have hyA : (y : X) ∈ normalizer ((omegaOne (T : Subgroup X) : Subgroup X) : Set X) := by
    rw [Subgroup.mem_normalizer_iff, hAeq]
    intro h
    have hyZ := Subgroup.mem_normalizer_iff.mp hy₀N
    constructor
    · intro hh
      obtain ⟨ζ, hζ, u, hu, rfl⟩ := SU1.mem_sup_of_commute hZwcomm hh
      have : (y : X) * (ζ * u) * (y : X)⁻¹ = ((y : X) * ζ * (y : X)⁻¹) * u := by
        calc (y : X) * (ζ * u) * (y : X)⁻¹
            = ((y : X) * ζ * (y : X)⁻¹) * ((y : X) * u * (y : X)⁻¹) := by group
          _ = ((y : X) * ζ * (y : X)⁻¹) * u := by rw [hyw u hu]
      rw [this]
      exact (Z₀ ⊔ zpowers w).mul_mem (Subgroup.mem_sup_left ((hyZ ζ).mp hζ))
        (Subgroup.mem_sup_right hu)
    · intro hh
      obtain ⟨ζ, hζ, u, hu, hζu⟩ := SU1.mem_sup_of_commute hZwcomm hh
      have hζ' : (y : X)⁻¹ * ζ * (y : X) ∈ Z₀ := by
        rw [hyZ]
        have : (y : X) * ((y : X)⁻¹ * ζ * (y : X)) * (y : X)⁻¹ = ζ := by group
        rw [this]
        exact hζ
      have hh' : h = ((y : X)⁻¹ * ζ * (y : X)) * u := by
        calc h = (y : X)⁻¹ * ((y : X) * h * (y : X)⁻¹) * (y : X) := by group
          _ = (y : X)⁻¹ * (ζ * u) * (y : X) := by rw [← hζu]
          _ = ((y : X)⁻¹ * ζ * (y : X)) * ((y : X)⁻¹ * u * (y : X)) := by group
          _ = ((y : X)⁻¹ * ζ * (y : X)) * u := by rw [hyw' u hu]
      rw [hh']
      exact (Z₀ ⊔ zpowers w).mul_mem (Subgroup.mem_sup_left hζ') (Subgroup.mem_sup_right hu)
  refine ⟨n, (y : X), by omega, hAcard, hyA, hwc (y : X), ?_⟩
  intro a ha b hb ha1 haw hb1 hbw
  rw [hAeq] at ha hb
  obtain ⟨ζ₁, hζ₁, u₁, hu₁, rfl⟩ := SU1.mem_sup_of_commute hZwcomm ha
  obtain ⟨ζ₂, hζ₂, u₂, hu₂, rfl⟩ := SU1.mem_sup_of_commute hZwcomm hb
  have hζ₁1 : ζ₁ ≠ 1 := by
    rintro rfl
    rcases mem_zpowers_invol hw2 hu₁ with rfl | rfl
    · exact ha1 (one_mul _)
    · exact haw (one_mul _)
  have hζ₂1 : ζ₂ ≠ 1 := by
    rintro rfl
    rcases mem_zpowers_invol hw2 hu₂ with rfl | rfl
    · exact hb1 (one_mul _)
    · exact hbw (one_mul _)
  obtain ⟨j, hj⟩ := hy₀trans ζ₁ hζ₁ ζ₂ hζ₂ hζ₁1 hζ₂1
  refine ⟨j, ?_⟩
  have hcen : ∀ u ∈ zpowers w, (y : X) ^ j * u * ((y : X) ^ j)⁻¹ = u := by
    intro u hu
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    have hc : Commute ((y : X) ^ j) (w ^ k) := ((hwcomm (y : X)).zpow_zpow j k)
    rw [hc.eq, mul_inv_cancel_right]
  have e1 : (y : X) ^ j * (ζ₁ * u₁) * ((y : X) ^ j)⁻¹ = ζ₂ * u₁ := by
    calc (y : X) ^ j * (ζ₁ * u₁) * ((y : X) ^ j)⁻¹
        = ((y : X) ^ j * ζ₁ * ((y : X) ^ j)⁻¹) * ((y : X) ^ j * u₁ * ((y : X) ^ j)⁻¹) := by group
      _ = ζ₂ * u₁ := by rw [hj, hcen u₁ hu₁]
  rw [e1]
  rcases mem_zpowers_invol hw2 hu₁ with rfl | rfl <;>
    rcases mem_zpowers_invol hw2 hu₂ with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (by rw [mul_assoc, hww])
  · exact Or.inr (by rw [mul_one])
  · exact Or.inl rfl

end CFSG.GH74.Uniqueness.SU.SU10
