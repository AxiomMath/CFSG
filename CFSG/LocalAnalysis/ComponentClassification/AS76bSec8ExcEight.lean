module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcJ
public import CFSG.ClassicalInvolution.QuaternionStructure
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8Perfect
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8Swap
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8TwoLift
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
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalLevi
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExceptionalDefs
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUFieldOddCore
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.RankThree.PartOne.S11d.OutLinear
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
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.ComponentClassification.RankTwoExceptional.Exc

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoSporadic
open CFSG.ComponentClassification.RankTwoClassical (Sec3 JData)
open CFSG.ComponentClassification.AS76b.Lemma36 (ConjData PairData)

section Eight

variable {G : Type} [Group G] [Finite G] {A R T : Subgroup G} {g : G} {C : Type} [Group C]
  {ψ : normalizer (A : Set G) →* MulAut C}
  (hZC : center C = ⊥) (hψ : IsActionHom A (MulAut.conj : C →* MulAut C).range ψ)
include hZC hψ

omit [Finite G] in
theorem actsIn_of_le_sup (hR : IsSylowOf 2 R (centralizer (A : Set G)))
    (hZ : Odd (Nat.card (A ⊓ centralizer (A : Set G) : Subgroup G))) {U : Subgroup C}
    (hUc : ∀ u ∈ U, ∀ v ∈ U, u * v = v * u) {T' : Subgroup G} (hT' : T' ≤ R ⊔ lift2 ψ U) :
    ActsIn ψ T' U := by
  have hinj := RankTwoHypIIY.conj_injective_of_center_eq_bot hZC
  have hRN : R ≤ normalizer (lift2 ψ U : Set G) := fun r hr =>
    centralizer_le_normalizer _ (hR.le.trans (centralizer_le lift2_le) hr)
  rw [actsIn_iff]
  intro t ht htN c hc
  have ht' : t ∈ ((R ⊔ lift2 ψ U : Subgroup G) : Set G) := hT' ht
  rw [coe_mul_of_left_le_normalizer_right R _ hRN] at ht'
  obtain ⟨r, hr, j, hj, hrj⟩ := ht'
  have hrj' : r * j = t := hrj
  obtain ⟨w, hw, hjw⟩ := exists_of_mem_lift2 hψ hZ hUc hj
  have hrN : r ∈ normalizer (A : Set G) := centralizer_le_normalizer _ (hR.le hr)
  have hjN := le_normalizer (lift2_le hj)
  have e : (⟨t, htN⟩ : normalizer (A : Set G)) = ⟨r, hrN⟩ * ⟨j, hjN⟩ := Subtype.ext hrj'.symm
  have h1 : ψ ⟨t, htN⟩ = MulAut.conj w := by
    rw [e, map_mul, (hψ.eq_one_iff ⟨r, hrN⟩).2 (hR.le hr), one_mul]
    exact hjw
  rw [hinj (hc.symm.trans h1)]
  exact hw

omit [Finite G] hZC hψ in
theorem sup_inf_centralizer (hR : IsSylowOf 2 R (centralizer (A : Set G)))
    (hZ : Odd (Nat.card (A ⊓ centralizer (A : Set G) : Subgroup G))) {J : Subgroup G}
    (hJA : J ≤ A) (hJ2 : ∀ j ∈ J, j ^ 2 = 1) :
    (R ⊔ J) ⊓ centralizer (A : Set G) = R := by
  have hRN : R ≤ normalizer (J : Set G) := fun r hr =>
    centralizer_le_normalizer _ (hR.le.trans (centralizer_le hJA) hr)
  refine le_antisymm (fun v hv => ?_) (le_inf le_sup_left hR.le)
  obtain ⟨hvV, hvK⟩ := mem_inf.1 hv
  have hv' : v ∈ ((R ⊔ J : Subgroup G) : Set G) := hvV
  rw [coe_mul_of_left_le_normalizer_right R _ hRN] at hv'
  obtain ⟨r, hr, j, hj, hrj⟩ := hv'
  have hrj' : r * j = v := hrj
  have hjK : j ∈ centralizer (A : Set G) := by
    have h1 := mul_mem (inv_mem (hR.le hr)) hvK
    rwa [← hrj', inv_mul_cancel_left] at h1
  have hj1 : j = 1 := RankTwoL3Even.eq_one_of_odd_of_pow_two
    (RankTwoL3Even.odd_orderOf_of_mem hZ (mem_inf.2 ⟨hJA hj, hjK⟩)) (k := 1)
    (by rw [pow_one]; exact hJ2 j hj)
  rw [← hrj', hj1, mul_one]
  exact hr

theorem main_of_reps (h4 : Asc75Theorem4) (h32 : Lemma32) (h34 : Asc08Lemma34)
    (hc : Sec3 A R T g) (hZA : Odd (Nat.card (center A))) {reps : List C}
    (hcover : ClassesCover reps)
    (hJ : ∀ y ∈ reps, ∃ Z u, CentreData y Z ∧ Regular Z u ∧ SylowData y Z)
    (hact : ∀ (R' T' : Subgroup G) (g' : G), Sec3 A R' T' g' → ∀ t ∈ T', t ≠ 1 →
      ∀ (htN : t ∈ normalizer (A : Set G)) (x : C), ψ ⟨t, htN⟩ = MulAut.conj x →
        ActsIn ψ T' (zx x)) :
    (T = sec3V R T ⊓ A ∧ ∀ x : G, rightConjugate R x ≤ sec3V R T →
        rightConjugate R x = R ∨ rightConjugate R x = T) ∨
      (sec3V R T ⊓ A = sec3V R T ⊓ rightConjugate A g ∧
        (∀ v ∈ sec3V R T, v ∉ A ↔
          ∃ x : G, rightConjugate R x ≤ sec3V R T ∧ v ∈ rightConjugate R x ∧ v ≠ 1) ∧
        ∀ x₁ x₂ x₁' x₂' : G, rightConjugate R x₁ ≤ sec3V R T → rightConjugate R x₂ ≤ sec3V R T →
          rightConjugate R x₁' ≤ sec3V R T → rightConjugate R x₂' ≤ sec3V R T →
          rightConjugate R x₁ ≠ rightConjugate R x₂ →
          rightConjugate R x₁' ≠ rightConjugate R x₂' →
          ∃ n ∈ normalizer (sec3V R T : Set G),
            rightConjugate (rightConjugate R x₁) n = rightConjugate R x₁' ∧
              rightConjugate (rightConjugate R x₂) n = rightConjugate R x₂') := by
  classical
  have hinj := RankTwoHypIIY.conj_injective_of_center_eq_bot hZC
  have hZ : Odd (Nat.card (A ⊓ centralizer (A : Set G) : Subgroup G)) := by
    rwa [RankTwoL3Even.card_inf_centralizer_eq]
  have hpick : ∀ (R' T' : Subgroup G) (g' : G), Sec3 A R' T' g' →
      ∃ t ∈ T', t ≠ 1 ∧ ∃ (htN : t ∈ normalizer (A : Set G)) (x : C),
        ψ ⟨t, htN⟩ = MulAut.conj x := by
    intro R' T' g' hc'
    obtain ⟨⟨t, ht⟩, ht1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hc'.T_ne_bot
    obtain ⟨x, hx⟩ := exists_conj_of_mem hψ hc' h32 h4 h34 ht (hc'.le_normalizer ht)
    exact ⟨t, ht, fun h => ht1 (Subtype.ext h), hc'.le_normalizer ht, x, hx⟩
  have hjdata : ∀ (R' T' : Subgroup G) (g' : G), Sec3 A R' T' g' →
      ∃ (x : C) (p û : G), (∃ t ∈ T', t ≠ 1 ∧ ∃ htN : t ∈ normalizer (A : Set G),
        ψ ⟨t, htN⟩ = MulAut.conj x) ∧ JData A R' T' p (lift2 ψ (zx x)) û := by
    intro R' T' g' hc'
    obtain ⟨t, ht, ht1, htN, x, hx⟩ := hpick R' T' g' hc'
    obtain ⟨p, û, hJd⟩ := exists_jData hZC hψ h4 h32 h34 hc' hZA hcover hJ ht ht1 htN hx
      (hact R' T' g' hc' t ht ht1 htN x hx)
    exact ⟨x, p, û, ⟨t, ht, ht1, htN, hx⟩, hJd⟩
  obtain ⟨x₀, p₀, û₀, ⟨t₀, ht₀, ht₀1, ht₀N, hx₀⟩, hJ₀⟩ := hjdata R T g hc
  obtain ⟨x₁, p₁, û₁, -, hJ₁⟩ := hjdata _ _ _ hc.swap
  obtain ⟨u₀, hcd₀, hreg₀, -⟩ := exists_classData_of_reps hcover hJ
    (involution_of_conj hZC hψ hc h32 ht₀ ht₀N hx₀).1
    ((involution_of_conj hZC hψ hc h32 ht₀ ht₀N hx₀).2 ht₀1)
  have hUc : ∀ u ∈ zx x₀, ∀ v ∈ zx x₀, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hcd₀.elem.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have hVeq := hc.sec3V_eq_sup h32 h4 h34 hJ₀
  set V := sec3V R T with hV
  obtain ⟨xT, hxT, hAxT⟩ := Lemma36.exists_conj_eq hc.sylowR hc.sylowT
  have hVK : V ⊓ centralizer (A : Set G) = R := by
    rw [hVeq]
    exact sup_inf_centralizer hc.sylowR hZ lift2_le
      (fun j hj => sq_eq_one_of_mem_lift2 hψ hZ hUc hj)
  have hRV : R ≤ V := (le_sec3V_of ⟨xT, hxT⟩).trans' le_sup_left
  have hTV : T ≤ V := (le_sec3V_of ⟨xT, hxT⟩).trans' le_sup_right
  have hex : ∀ x : G, rightConjugate R x ≤ V → ∃ y : G,
      ConjData V (rightConjugate R x) (rightConjugate A x) y ∧
        ∀ z ∈ normalizer (rightConjugate A x : Set G) ⊓ normalizer (V : Set G),
          z⁻¹ * y * z ∈ zpowers y ⊔ centralizer (V : Set G) := by
    intro x hx
    by_cases hxN : x ∈ normalizer (A : Set G)
    · have hAx : rightConjugate A x = A := (rightConjugate_eq_self_iff A x).2 hxN
      have hKx : rightConjugate (centralizer (A : Set G)) x = centralizer (A : Set G) := by
        rw [← centralizer_rightConjugate, hAx]
      have hRx : rightConjugate R x = R := by
        have h1 : rightConjugate R x ≤ V ⊓ centralizer (A : Set G) :=
          le_inf hx (hKx ▸ map_mono hc.sylowR.le)
        rw [hVK] at h1
        exact eq_of_le_of_card_ge h1 (by rw [rightConjugate_card])
      refine ⟨û₀, ?_, ?_⟩
      · rw [hRx, hAx]
        exact hc.conjData_R h32 h4 h34 hJ₀
      · rw [hAx]
        exact hc.normalizer_R h32 h4 h34 hJ₀
    · have hVc : V ≤ centralizer (V : Set G) :=
        le_centralizer_self_of_isElemAbelian
          (isElemAbelian_sec3V (hc.elemR h32) hc.le_centralizer ⟨xT, hxT⟩)
      have hsec : Sec3 A R (rightConjugate R x) x :=
        ⟨hc.hyp, hc.sylowR, hxN, AschbacherTheorem3.isSylowOf_rightConjugate hc.sylowR x,
          hx.trans (hVc.trans (centralizer_le hRV))⟩
      obtain ⟨x₂, p₂, û₂, ⟨t₂, ht₂, ht₂1, ht₂N, hx₂⟩, hJ₂⟩ := hjdata _ _ _ hsec
      obtain ⟨x₃, p₃, û₃, -, hJ₃⟩ := hjdata _ _ _ hsec.swap
      have hzx : zx x₂ = zx x₀ := by
        have hact₂ : ActsIn ψ (rightConjugate R x) (zx x₀) :=
          actsIn_of_le_sup hZC hψ hc.sylowR hZ hUc (hx.trans hVeq.le)
        have hx₂Z : x₂ ∈ zx x₀ := (actsIn_iff.1 hact₂) t₂ ht₂ ht₂N x₂ hx₂
        have hx₂1 : x₂ ≠ 1 := (involution_of_conj hZC hψ hsec h32 ht₂ ht₂N hx₂).2 ht₂1
        rw [zx_eq_of_centreData hcd₀] at hx₂Z ⊢
        exact zx_eq_of_mem hcd₀ hreg₀ hx₂Z hx₂1
      have hV₂ : sec3V R (rightConjugate R x) = V := by
        rw [hsec.sec3V_eq_sup h32 h4 h34 hJ₂, hzx, ← hVeq]
      refine ⟨x⁻¹ * û₃ * x, ?_, ?_⟩
      · have h1 := hsec.conjData_T h32 h4 h34 hJ₃
        rwa [hV₂] at h1
      · have h1 := hsec.normalizer_T h32 h4 h34 hJ₃
        rwa [hV₂] at h1
  let y : G → G := fun x => if hx : rightConjugate R x ≤ V then (hex x hx).choose else 1
  have hy : ∀ x (hx : rightConjugate R x ≤ V),
      ConjData V (rightConjugate R x) (rightConjugate A x) (y x) ∧
        ∀ z ∈ normalizer (rightConjugate A x : Set G) ⊓ normalizer (V : Set G),
          z⁻¹ * y x * z ∈ zpowers (y x) ⊔ centralizer (V : Set G) := by
    intro x hx
    have h1 := (hex x hx).choose_spec
    simp only [y, hx, ↓reduceDIte]
    exact h1
  have hRneT : R ≠ T := by
    intro h
    apply hc.R_ne_bot
    have h1 := hc.inf_eq_bot
    rwa [← h, inf_idem] at h1
  have hmain := Lemma36.main_of_data (y := y) hxT hAxT hRV hTV hRneT
    (fun x hx => (hy x hx).1)
    (fun x₁ x₂ hx₁ hx₂ hne => Lemma36.pairData hc.hyp hc.sylowR (hy x₁ hx₁).1 (hy x₂ hx₂).1
      (hy x₁ hx₁).2 (hy x₂ hx₂).2 hne)
  have hR1 : rightConjugate R 1 ≤ V := by
    rw [rightConjugate_one]
    exact hRV
  have dR := (hy 1 hR1).1
  rw [rightConjugate_one, rightConjugate_one] at dR
  have hT1 : rightConjugate R xT ≤ V := by
    rw [← hxT]
    exact hTV
  have dT := (hy xT hT1).1
  rw [← hxT, hAxT] at dT
  rw [dR.commutator_eq, dT.commutator_eq] at hmain
  rcases hmain with ⟨h1, -, h3⟩ | ⟨h1, h2, h3⟩
  · exact Or.inl ⟨h1.symm, h3⟩
  · refine Or.inr ⟨h1, fun v hv => ?_, h3⟩
    rw [← h2 v hv]
    exact ⟨fun h hv' => h (mem_inf.1 hv').2, fun h hvA => h (mem_inf.2 ⟨hv, hvA⟩)⟩

end Eight

end CFSG.ComponentClassification.RankTwoExceptional.Exc
