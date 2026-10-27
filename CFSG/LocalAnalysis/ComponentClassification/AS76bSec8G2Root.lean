module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8Perfect
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8G2Defs
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma34
public import CFSG.LieType.Chevalley.AdjointCenter
public import Certificates.Certificate43
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
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate3951
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderAutLinear
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderSuzuki
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderUnitary
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitGlaubermanCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldUnitaryData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticRepresentationOdd
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExceptionalDefs
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUFieldOddCore
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.RankThree.PartOne.S11d.OutLinear
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public noncomputable section

namespace CFSG.ComponentClassification.RankTwoExceptional

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHull
open CFSG.ComponentClassification.RankTwoSporadic
open CFSG.ComponentClassification.RankTwoClassical (Sec3)
open CFSG.Blueprint.Chevalley CFSG.ComponentClassification.UnbalancedCatalog

section Conj

variable {G : Type} [Group G] [Finite G] {A R T : Subgroup G} {g : G}

theorem not_mem_centralizer_of_sec3 (hc : Sec3 A R T g) (h32 : Lemma32) {t : G} (ht : t ∈ T)
    (ht1 : t ≠ 1) : t ∉ centralizer (A : Set G) := by
  intro htK
  have hg : g ∉ normalizer (centralizer (A : Set G) : Set G) := by
    rw [normalizer_centralizer_eq hc.hyp.standard]
    exact hc.not_mem
  have hodd := (tightlyEmbedded_centralizer hc.hyp.standard).2 g hg
  refine ht1 (RankTwoL3Even.eq_one_of_odd_of_pow_two
    (RankTwoL3Even.odd_orderOf_of_mem hodd (mem_inf.2 ⟨htK, hc.sylowT.le ht⟩)) (k := 1) ?_)
  rw [pow_one]
  exact (hc.elemT h32).2 t ht

theorem sec3_conj (hc : Sec3 A R T g) {a : G} (ha : a ∈ A) :
    Sec3 A R (rightConjugate T a) (g * a) := by
  refine ⟨hc.hyp, hc.sylowR, fun h => hc.not_mem ?_, ?_, ?_⟩
  · have := mul_mem h (inv_mem (le_normalizer ha))
    rwa [mul_inv_cancel_right] at this
  · have := AschbacherTheorem3.isSylowOf_rightConjugate hc.sylowT a
    rwa [rightConjugate_mul] at this
  · intro x hx
    rw [mem_rightConjugate_iff] at hx
    rw [mem_centralizer_iff]
    intro r hr
    have h1 : r * (a * x * a⁻¹) = a * x * a⁻¹ * r :=
      mem_centralizer_iff.1 (hc.le_centralizer hx) r hr
    have h2 : a * r = r * a := mem_centralizer_iff.1 (hc.sylowR.le hr) a ha
    have h3 : a⁻¹ * r * a = r := by rw [mul_assoc, ← h2, ← mul_assoc, inv_mul_cancel, one_mul]
    calc r * x = a⁻¹ * r * a * x := by rw [h3]
      _ = a⁻¹ * (r * (a * x * a⁻¹)) * a := by group
      _ = a⁻¹ * (a * x * a⁻¹ * r) * a := by rw [h1]
      _ = x * (a⁻¹ * r * a) := by group
      _ = x * r := by rw [h3]

end Conj

section Inner

variable {G : Type} [Group G] [Finite G] {A R T : Subgroup G} {g : G}
  {X₀ : Type*} [Group X₀] {ψ : normalizer (A : Set G) →* MulAut X₀}

theorem exists_psi_eq_conj (hc : Sec3 A R T g) (h32 : Lemma32) (h4 : Asc75Theorem4)
    (h34 : Asc08Lemma34) (hψ : IsActionHom A (MulAut.conj : X₀ →* MulAut X₀).range ψ) {t : G}
    (ht : t ∈ T) (htN : t ∈ normalizer (A : Set G)) :
    ∃ x : X₀, ψ ⟨t, htN⟩ = MulAut.conj x := by
  obtain ⟨p, hp, htp⟩ := hc.exists_aPart h32 h4 h34 ht
  obtain ⟨x, hx⟩ := hψ.map_mem p hp
  refine ⟨x, ?_⟩
  have h1 : ψ ⟨t⁻¹ * p, mul_mem (inv_mem htN) (le_normalizer hp)⟩ = 1 :=
    (hψ.eq_one_iff _).2 (hc.sylowR.le htp)
  rw [psi_mul (inv_mem htN) (le_normalizer hp), psi_inv htN, inv_mul_eq_one] at h1
  rw [h1, hx]

theorem ne_one_of_psi_eq_conj (hc : Sec3 A R T g) (h32 : Lemma32)
    (hψ : IsActionHom A (MulAut.conj : X₀ →* MulAut X₀).range ψ) {t : G} (ht : t ∈ T)
    (ht1 : t ≠ 1) (htN : t ∈ normalizer (A : Set G)) {x : X₀}
    (hx : ψ ⟨t, htN⟩ = MulAut.conj x) : x ≠ 1 := by
  rintro rfl
  rw [map_one] at hx
  exact not_mem_centralizer_of_sec3 hc h32 ht ht1 ((hψ.eq_one_iff _).1 hx)

theorem sq_eq_one_of_psi_eq_conj (hZ : center X₀ = ⊥) (hc : Sec3 A R T g) (h32 : Lemma32)
    {t : G} (ht : t ∈ T) (htN : t ∈ normalizer (A : Set G)) {x : X₀}
    (hx : ψ ⟨t, htN⟩ = MulAut.conj x) : x ^ 2 = 1 := by
  apply RankTwoHypIIY.conj_injective_of_center_eq_bot hZ
  have h1 : (⟨t ^ 2, pow_mem htN 2⟩ : normalizer (A : Set G)) = 1 :=
    Subtype.ext ((hc.elemT h32).2 t ht)
  rw [map_pow, ← hx, ← psi_pow htN, h1, map_one, map_one]

theorem mem_centralizer_of_perfect (h4 : Asc75Theorem4) (h32 : Lemma32) (h34 : Asc08Lemma34)
    (hc : Sec3 A R T g) (hOut : Odd (Nat.card (commutator (outerAutomorphismGroup ↥A))))
    (hZ : center X₀ = ⊥) (hψ : IsActionHom A (MulAut.conj : X₀ →* MulAut X₀).range ψ) {t : G}
    (ht : t ∈ T) (ht1 : t ≠ 1) (htN : t ∈ normalizer (A : Set G)) {x : X₀}
    (hx : ψ ⟨t, htN⟩ = MulAut.conj x) {D : Subgroup X₀} (hD : ⁅D, D⁆ = D)
    (hDx : D ≤ centralizer {x}) {u : G} (hu : u ∈ T) (huN : u ∈ normalizer (A : Set G))
    {y : X₀} (hy : ψ ⟨u, huN⟩ = MulAut.conj y) : y ∈ centralizer (D : Set X₀) := by
  have hPX : D.map (MulAut.conj : X₀ →* MulAut X₀) ≤ (MulAut.conj : X₀ →* MulAut X₀).range :=
    map_le_range _ _
  have hP : ⁅D.map (MulAut.conj : X₀ →* MulAut X₀), D.map (MulAut.conj : X₀ →* MulAut X₀)⁆ =
      D.map (MulAut.conj : X₀ →* MulAut X₀) := by
    rw [← map_commutator, hD]
  have htP : ∀ s ∈ D.map (MulAut.conj : X₀ →* MulAut X₀), ψ ⟨t, htN⟩ * s = s * ψ ⟨t, htN⟩ := by
    rintro _ ⟨d, hd, rfl⟩
    rw [hx, ← map_mul, ← map_mul, (mem_centralizer_singleton_iff.1 (hDx hd)).symm]
  rw [mem_centralizer_iff]
  intro d hd
  have h := psi_commute_of_perfect h4 h32 h34 hc.hyp hc.sylowT ht ht1 hOut hψ htN hPX hP htP hu
    huN ⟨d, hd, rfl⟩
  rw [hy, ← map_mul, ← map_mul] at h
  exact (RankTwoHypIIY.conj_injective_of_center_eq_bot hZ h).symm

theorem eq_one_of_conj_mem_perfect (h4 : Asc75Theorem4) (h32 : Lemma32) (h34 : Asc08Lemma34)
    (hc : Sec3 A R T g) (hOut : Odd (Nat.card (commutator (outerAutomorphismGroup ↥A))))
    (hZA : Odd (Nat.card (center A)))
    (hψ : IsActionHom A (MulAut.conj : X₀ →* MulAut X₀).range ψ) {t : G} (ht : t ∈ T)
    (htA : t ∈ A) {x : X₀} (hx : ψ ⟨t, le_normalizer htA⟩ = MulAut.conj x) {D : Subgroup X₀}
    (hD : ⁅D, D⁆ = D) (hxD : x ∈ D) (hDx : D ≤ centralizer {x}) : t = 1 := by
  have hPX : D.map (MulAut.conj : X₀ →* MulAut X₀) ≤ (MulAut.conj : X₀ →* MulAut X₀).range :=
    map_le_range _ _
  have hP : ⁅D.map (MulAut.conj : X₀ →* MulAut X₀), D.map (MulAut.conj : X₀ →* MulAut X₀)⁆ =
      D.map (MulAut.conj : X₀ →* MulAut X₀) := by
    rw [← map_commutator, hD]
  refine eq_one_of_psi_mem_perfect h4 h32 h34 hc.hyp hc.sylowT hOut hZA hψ ht htA hPX hP ?_
    ⟨x, hxD, hx.symm⟩
  rintro _ ⟨d, hd, rfl⟩
  rw [hx, ← map_mul, ← map_mul, (mem_centralizer_singleton_iff.1 (hDx hd)).symm]

end Inner

section Sub

variable {M : Type*} [Group M] {C D : Subgroup M}

theorem commutator_subgroupOf_eq (hDC : D ≤ C) (hD : ⁅D, D⁆ = D) :
    ⁅D.subgroupOf C, D.subgroupOf C⁆ = D.subgroupOf C := by
  apply map_injective C.subtype_injective
  rw [map_commutator, subgroupOf_map_subtype, inf_of_le_left hDC, hD]

theorem coe_mem_inf_centralizer (hDC : D ≤ C) {y : C}
    (hy : y ∈ centralizer (D.subgroupOf C : Set C)) : (y : M) ∈ C ⊓ centralizer (D : Set M) := by
  refine mem_inf.2 ⟨y.2, mem_centralizer_iff.2 fun d hd => ?_⟩
  have h := mem_centralizer_iff.1 hy ⟨d, hDC hd⟩ (mem_subgroupOf.2 hd)
  exact congrArg Subtype.val h

theorem subgroupOf_le_centralizer {x : C} (hDx : D ≤ centralizer {(x : M)}) :
    D.subgroupOf C ≤ centralizer {x} := by
  intro d hd
  rw [mem_centralizer_singleton_iff]
  exact Subtype.ext (mem_centralizer_singleton_iff.1 (hDx (mem_subgroupOf.1 hd)))

end Sub

section G2

variable {G : Type} [Group G] [Finite G] {A R T : Subgroup G} {g : G}
  {K : Type} [Field K] [Finite K]

omit [Finite G] in
theorem exists_g2_isActionHom
    {A : Subgroup G} (hA : commutator A = ⊤)
    (e : RankTwoStandard.rankTwoQuot A ≃* Blueprint.AdjointQuotient .G2 K) :
    ∃ ψ : normalizer (A : Set G) →* MulAut ↥(adjointGroup .G2 K),
      IsActionHom A (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)).range
        ψ := by
  have hZ := LieType.Chevalley.center_adjointGroup_eq_bot (τ := .G2) (K := K)
  exact exists_isActionHom (RankTwoHypIIY.autModel_mulAut hZ) hA
    (e.trans ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot))

@[expose] def ActsIn (ψ : normalizer (A : Set G) →* MulAut ↥(adjointGroup .G2 K))
    (T : Subgroup G) (U : Subgroup (ModGL .G2 K)) : Prop :=
  ∀ u ∈ T, ∀ (huN : u ∈ normalizer (A : Set G)) (y : ↥(adjointGroup .G2 K)),
    ψ ⟨u, huN⟩ = MulAut.conj y → (y : ModGL .G2 K) ∈ U

variable {ψ : normalizer (A : Set G) →* MulAut ↥(adjointGroup .G2 K)}

omit [Finite K] in
theorem rootSubgroup_le_centralizer
    (α : Fin Tag.G2.rank → ℤ) :
    rootSubgroup .G2 K α ≤ centralizer {pinnedX .G2 K α 1} := by
  refine (closure_le _).2 ?_
  rintro _ ⟨s, rfl⟩
  rw [SetLike.mem_coe, mem_centralizer_singleton_iff, ← pinnedX_add, ← pinnedX_add, add_comm]

theorem actsIn_of_perfect
    (h4 : Asc75Theorem4) (h32 : Lemma32)
    (h34 : Asc08Lemma34) (hc : Sec3 A R T g)
    (hOut : Odd (Nat.card (commutator (outerAutomorphismGroup ↥A))))
    (hψ : IsActionHom A
      (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)).range ψ)
    {t : G} (ht : t ∈ T) (ht1 : t ≠ 1) (htN : t ∈ normalizer (A : Set G))
    {x : ↥(adjointGroup .G2 K)} (hx : ψ ⟨t, htN⟩ = MulAut.conj x) {D U : Subgroup (ModGL .G2 K)}
    (hDC : D ≤ adjointGroup .G2 K) (hD : ⁅D, D⁆ = D)
    (hDx : D ≤ centralizer {(x : ModGL .G2 K)})
    (hU : ∀ y ∈ g2Centralizer K (D : Set _), y ^ 2 = 1 → y ∈ U) :
    ActsIn ψ T U := by
  intro u hu huN y hy
  have hZ := LieType.Chevalley.center_adjointGroup_eq_bot (τ := .G2) (K := K)
  have h := mem_centralizer_of_perfect h4 h32 h34 hc hOut hZ hψ ht ht1 htN hx
    (commutator_subgroupOf_eq hDC hD) (subgroupOf_le_centralizer hDx) hu huN hy
  refine hU _ (coe_mem_inf_centralizer hDC h) ?_
  rw [← Subgroup.coe_pow, sq_eq_one_of_psi_eq_conj hZ hc h32 hu huN hy, OneMemClass.coe_one]

theorem g2_exists_sec3_root
    [CharP K 2] (h4 : Asc75Theorem4) (h32 : Lemma32)
    (h184 : G2Centr184) (h184s : G2Centr184s) (hc : Sec3 A R T g)
    (hOut : Odd (Nat.card (commutator (outerAutomorphismGroup ↥A)))) (hK4 : 4 ≤ Nat.card K)
    (hψ : IsActionHom A
      (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)).range ψ) :
    ∃ (T' : Subgroup G) (g' : G), Sec3 A R T' g' ∧
      (ActsIn ψ T' (rootSubgroup .G2 K g2c) ∨ ActsIn ψ T' (rootSubgroup .G2 K g2v)) := by
  have hZ := LieType.Chevalley.center_adjointGroup_eq_bot (τ := .G2) (K := K)
  have h34 : Asc08Lemma34 := asc08Lemma34
  obtain ⟨⟨t₀, ht₀⟩, ht₀1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hc.T_ne_bot
  have ht₀1' : t₀ ≠ 1 := fun h => ht₀1 (Subtype.ext h)
  have ht₀N := hc.le_normalizer ht₀
  obtain ⟨x₀, hx₀⟩ := exists_psi_eq_conj hc h32 h4 h34 hψ ht₀ ht₀N
  have hx₀1 := ne_one_of_psi_eq_conj hc h32 hψ ht₀ ht₀1' ht₀N hx₀
  have hx₀2 := sq_eq_one_of_psi_eq_conj hZ hc h32 ht₀ ht₀N hx₀
  have hord : orderOf x₀ = 2 := orderOf_eq_prime hx₀2 hx₀1
  have hchar : ringChar K = 2 := ringChar.eq K 2
  have key : ∀ z : ↥(adjointGroup .G2 K), IsConj x₀ z → ∃ (T' : Subgroup G) (g' : G),
      Sec3 A R T' g' ∧ ∃ t' ∈ T', t' ≠ 1 ∧ ∃ ht'N : t' ∈ normalizer (A : Set G),
        ψ ⟨t', ht'N⟩ = MulAut.conj z := by
    intro z hz
    obtain ⟨h, hh⟩ := isConj_iff.1 hz
    obtain ⟨a, ha, hψa⟩ := hψ.exists_eq (MulAut.conj h⁻¹) ⟨h⁻¹, rfl⟩
    have haN := le_normalizer ha
    refine ⟨rightConjugate T a, g * a, sec3_conj hc ha, a⁻¹ * t₀ * a, ?_, ?_, ?_, ?_⟩
    · rw [mem_rightConjugate_iff]
      simpa [mul_assoc] using ht₀
    · intro h1
      apply ht₀1'
      calc t₀ = a * (a⁻¹ * t₀ * a) * a⁻¹ := by group
        _ = 1 := by rw [h1, mul_one, mul_inv_cancel]
    · exact mul_mem (mul_mem (inv_mem haN) ht₀N) haN
    · rw [psi_mul (mul_mem (inv_mem haN) ht₀N) haN, psi_mul (inv_mem haN) ht₀N, psi_inv haN,
        hψa, hx₀, ← hh, ← map_inv, ← map_mul, ← map_mul, inv_inv]
  rcases UnbalancedCatalog.even_G2_involutions_conjugate_to_root_elements K hchar x₀ hord with
    hlong | hshort
  · obtain ⟨T', g', hc', t', ht', ht'1, ht'N, hψt'⟩ := key _ hlong
    obtain ⟨hperf, hcent⟩ := h184 K hK4
    refine ⟨T', g', hc', Or.inl ?_⟩
    refine actsIn_of_perfect h4 h32 h34 hc' hOut hψ ht' ht'1 ht'N hψt' inf_le_left hperf ?_
      fun y hy _ => hcent ▸ hy
    exact inf_le_right
  · obtain ⟨T', g', hc', t', ht', ht'1, ht'N, hψt'⟩ := key _ hshort
    obtain ⟨hperf, -, hcent⟩ := h184s K hK4
    refine ⟨T', g', hc', Or.inr ?_⟩
    refine actsIn_of_perfect h4 h32 h34 hc' hOut hψ ht' ht'1 ht'N hψt'
      (((commutator_le).2 fun a ha b hb => RankTwoL3Even.commutatorElement_mem' ha hb).trans
        inf_le_left) hperf ?_ hcent
    exact ((commutator_le).2 fun a ha b hb => RankTwoL3Even.commutatorElement_mem' ha hb).trans
      inf_le_right

theorem g2_inf_eq_bot_of_long
    [CharP K 2] (h4 : Asc75Theorem4) (h32 : Lemma32)
    (h184 : G2Centr184) (hc : Sec3 A R T g)
    (hOut : Odd (Nat.card (commutator (outerAutomorphismGroup ↥A))))
    (hZA : Odd (Nat.card (center A))) (hK4 : 4 ≤ Nat.card K)
    (hψ : IsActionHom A
      (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)).range ψ)
    (hlong : ActsIn ψ T (rootSubgroup .G2 K g2c)) : T ⊓ A = ⊥ := by
  have h34 : Asc08Lemma34 := asc08Lemma34
  obtain ⟨hperf, hcent⟩ := h184 K hK4
  have hDC : g2LongCent K ≤ adjointGroup .G2 K := inf_le_left
  rw [eq_bot_iff]
  intro t ht
  rw [mem_bot]
  obtain ⟨htT, htA⟩ := mem_inf.1 ht
  obtain ⟨x, hx⟩ := exists_psi_eq_conj hc h32 h4 h34 hψ htT (le_normalizer htA)
  have hxU := hlong t htT (le_normalizer htA) x hx
  have hxC : (x : ModGL .G2 K) ∈ g2Centralizer K (g2LongCent K : Set (ModGL .G2 K)) := by
    rw [hcent]
    exact hxU
  have hxD : x ∈ (g2LongCent K).subgroupOf (adjointGroup .G2 K) :=
    mem_subgroupOf.2 (mem_inf.2 ⟨x.2, rootSubgroup_le_centralizer (K := K) g2c hxU⟩)
  have hDx : g2LongCent K ≤ centralizer {(x : ModGL .G2 K)} := fun d hd =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 (mem_inf.1 hxC).2 d hd)
  exact eq_one_of_conj_mem_perfect h4 h32 h34 hc hOut hZA hψ htT htA hx
    (commutator_subgroupOf_eq hDC hperf) hxD (subgroupOf_le_centralizer hDx)

end G2

end CFSG.ComponentClassification.RankTwoExceptional
