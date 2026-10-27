module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7QPUCat
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafEvenNoComponent
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafEven
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedReverse
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTILinear
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTISymplectic
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUAlmostSimple
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogOmegaAlmostSimple
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aOddQuotTools
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aFStar
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7Inst
public import CFSG.LocalAnalysis.ComponentInitial.LinearFieldFourWitnesses
public import CFSG.LocalAnalysis.SectionRank.NativeKGroup
public import CFSG.RankThree.PartOne.S12.Sec1511SPEFStar
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4Transport
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4Outer
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4TwoComp
import CFSG.Adapters.StatedPSLTwo
public import CFSG.Assembly.QuasithinDefs
public import CFSG.GH74.GLS.Classes
public import CFSG.GH74.Generic.Shapes
public import CFSG.GH74.Statements
public import CFSG.LieType.Chevalley.C2E6StandardFixedData
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import CFSG.LieType.Chevalley.E6SecondGraphFullCentralizer
public import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCover
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafOddB
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB83Setup
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB8Statements
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCriticalStandard
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNormalTwoFixedPointHull
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointFullTransport
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFourPresentation
public import CFSG.LocalAnalysis.SectionRank.BruhatLift
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SLTwo
public import CFSG.LocalAnalysis.SectionRank.LargeReeCover
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureConjugation
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperPair
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyData
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyProper
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.Sporadic.Schreier.J1QT
public import CFSG.Sporadic.Schreier.TitsOther
public import CFSG.StronglyEmbedded.ParityCriterion

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup

namespace QPUJ.Even

theorem pPrimeCore_eq_bot_of_le {G : Type*} [Group G] {C Q : Subgroup G} [Finite C]
    (hQC : Q ≤ C) (hQp : IsPGroup 2 Q) (hnorm : ∀ c ∈ C, ∀ q ∈ Q, c * q * c⁻¹ ∈ Q)
    (hcen : ∀ c ∈ C, (∀ q ∈ Q, c * q = q * c) → c ∈ Q) : pPrimeCore 2 ↥C = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR : IsPGroup 2 (Q.subgroupOf C) := hQp.comap_of_injective C.subtype C.subtype_injective
  have hRO := OddQuot.inf_pPrimeCore_eq_bot hR
  rw [eq_bot_iff]
  intro x hx
  have hxQ : (x : G) ∈ Q := by
    refine hcen x x.2 fun q hq => ?_
    set q' : ↥C := ⟨q, hQC hq⟩
    have hc : x * q' * x⁻¹ * q'⁻¹ ∈ Q.subgroupOf C ⊓ pPrimeCore 2 ↥C := by
      refine mem_inf.mpr ⟨?_, ?_⟩
      · rw [mem_subgroupOf]
        exact mul_mem (hnorm x x.2 q hq) (inv_mem hq)
      · rw [show x * q' * x⁻¹ * q'⁻¹ = x * (q' * x⁻¹ * q'⁻¹) by group]
        exact mul_mem hx ((CFSG.pPrimeCore_normal (p := 2) (G := ↥C)).conj_mem _ (inv_mem hx) q')
    rw [hRO, mem_bot] at hc
    have h1 : x * q' = q' * x := by
      calc x * q' = x * q' * x⁻¹ * q'⁻¹ * (q' * x) := by group
        _ = q' * x := by rw [hc, one_mul]
    exact congrArg Subtype.val h1
  have h2 : x ∈ Q.subgroupOf C ⊓ pPrimeCore 2 ↥C := mem_inf.mpr ⟨hxQ, hx⟩
  rw [hRO] at h2
  exact h2

section Linear

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.ComponentClassification.UnbalancedCatalog.EvenLinearSL

theorem linear_pPrimeCore_eq_bot {f n : ℕ} (hf : 1 ≤ f) (hn : 2 ≤ n) {k : Type*} [Field k]
    (hk : Nat.card k = 2 ^ f) (t : projectiveSL n k) (ht : orderOf t = 2) :
    pPrimeCore 2 ↥(centralizer ({t} : Set (projectiveSL n k))) = ⊥ := by
  classical
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have : CharP k 2 := finite_field_prime_power_characteristic Nat.prime_two hf hk
  have : NeZero n := ⟨by omega⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (SpecialLinearGroup (Fin n) k) := inferInstance
  have : Finite (centralizer ({t} : Set (projectiveSL n k))) := inferInstance
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  obtain ⟨s, rfl, hs⟩ := OutcomeLocal.exists_sl_lift t htt
  have hs1 : s ≠ 1 := by
    rintro rfl
    rw [map_one, orderOf_one] at ht
    exact absurd ht (by norm_num)
  set U := flagKernel (OutcomeLocal.dispRange s) (OutcomeLocal.dispKer s)
    (OutcomeLocal.dispRange_le_dispKer hs)
  set Q := U.map (proj n k)
  have hlift : ∀ c ∈ centralizer ({proj n k s} : Set (projectiveSL n k)),
      ∃ A : SpecialLinearGroup (Fin n) k, proj n k A = c ∧ A * s = s * A := by
    intro c hc
    obtain ⟨A, rfl⟩ := proj_surjective n k c
    exact ⟨A, rfl, OutcomeLocal.commute_of_proj_commute hs (mem_centralizer_singleton_iff.mp hc)⟩
  have hQC : Q ≤ centralizer ({proj n k s} : Set (projectiveSL n k)) := by
    rintro _ ⟨u, hu, rfl⟩
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      OutcomeLocal.commute_of_mem_flagKernel hs hu]
  have hQp : IsPGroup 2 Q := isPGroup_flagKernel.map (proj n k)
  have hnorm : ∀ c ∈ centralizer ({proj n k s} : Set (projectiveSL n k)), ∀ q ∈ Q,
      c * q * c⁻¹ ∈ Q := by
    intro c hc q hq
    obtain ⟨A, rfl, hAs⟩ := hlift c hc
    obtain ⟨u, hu, rfl⟩ := hq
    exact ⟨A * u * A⁻¹, OutcomeLocal.conj_mem_flagKernel hs hAs hu,
      by rw [map_mul, map_mul, map_inv]⟩
  refine pPrimeCore_eq_bot_of_le hQC hQp hnorm fun c hc hcQ => ?_
  obtain ⟨A, rfl, hAs⟩ := hlift c hc
  rcases Nat.lt_or_ge n 3 with hn3 | hn3
  · obtain rfl : n = 2 := by omega
    exact ⟨A, OutcomeLocal.mem_flagKernel_of_commute_two hs hs1 hAs, rfl⟩
  · exact OutcomeLocal.mem_map_flagKernel_of_commute hn3 hf hk (OutcomeLocal.dispRange_ne_bot hs1)
      (OutcomeLocal.dispRange_le_dispKer hs) (OutcomeLocal.dispKer_ne_top hs1)
      fun u hu => hcQ _ ⟨u, hu, rfl⟩

end Linear

section Symplectic

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticFlag SymplecticHigher
open CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain

theorem symplectic_pPrimeCore_eq_bot {f r : ℕ} (hf : 1 ≤ f) (hr : 1 ≤ r) {k : Type} [Field k]
    (hk : Nat.card k = 2 ^ f) (t : StatedProj (StatedSp r k)) (ht : orderOf t = 2) :
    pPrimeCore 2 ↥(Subgroup.centralizer ({t} : Set (StatedProj (StatedSp r k)))) = ⊥ := by
  classical
  have : CharP k 2 := finite_field_prime_power_characteristic Nat.prime_two hf hk
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have : NeZero r := ⟨by omega⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hbij := UnitaryHigher.proj_bijective_of_charTwo (r := r) (K := k)
  have hιinj := spInner_injective (r := r) (K := k)
  have : Finite (StatedSp r k) := inferInstance
  have : Finite (StatedProj (StatedSp r k)) := Finite.of_surjective _ hbij.2
  have : Finite (Subgroup.centralizer ({t} : Set (StatedProj (StatedSp r k)))) := inferInstance
  obtain ⟨s, rfl⟩ := hbij.2 t
  have hsord : orderOf s = 2 := by rw [← orderOf_injective _ hbij.1 s, ht]
  have hs : s * s = 1 := by rw [← sq, ← hsord, pow_orderOf_eq_one]
  have hs1 : s ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hsord
    exact absurd hsord (by norm_num)
  set W := displacement s
  set L := (pairedSympForm k r).orthogonal W
  set R := flagKernel W L
  have hW0 : W ≠ ⊥ := by
    intro hbot
    refine hs1 (statedSp_ext fun v => ?_)
    have h1 : spMat s *ᵥ v - v ∈ W := mem_displacement.mpr ⟨v, rfl⟩
    rw [hbot, Submodule.mem_bot, sub_eq_zero] at h1
    rw [h1]
    exact (one_mulVec v).symm
  obtain ⟨-, hRp, hnorm, hcentEq, -⟩ :=
    even_symplectic_isotropic_radical_centralizer hr hf hk W hW0
      (isTotallyIsotropic_displacement hs)
  set Q := R.map (proj r k)
  have hlift : ∀ c ∈ Subgroup.centralizer ({proj r k s} : Set (StatedProj (StatedSp r k))),
      ∃ g : StatedSp r k, proj r k g = c ∧ g * s = s * g := by
    intro c hc
    obtain ⟨g, rfl⟩ := hbij.2 c
    refine ⟨g, rfl, hbij.1 ?_⟩
    rw [map_mul, map_mul]
    exact Subgroup.mem_centralizer_singleton_iff.mp hc
  have hQC : Q ≤ Subgroup.centralizer ({proj r k s} : Set (StatedProj (StatedSp r k))) := by
    rintro _ ⟨h, hh, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      commute_of_mem_flagKernel hs hh]
  have hQp : IsPGroup 2 Q := hRp.map (proj r k)
  have hconjR : ∀ g : StatedSp r k, g * s = s * g → ∀ h ∈ R, g * h * g⁻¹ ∈ R := by
    intro g hgs h hh
    have hgW : ∀ w ∈ W, ((g : GL (Fin r ⊕ Fin r) k) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k)
        *ᵥ (fun i => (1 : k ≃+* k) (w i)) ∈ W := by
      intro w hw
      obtain ⟨v, rfl⟩ := mem_displacement.mp hw
      refine mem_displacement.mpr ⟨spMat g *ᵥ v, ?_⟩
      change spMat s *ᵥ (spMat g *ᵥ v) - spMat g *ᵥ v = spMat g *ᵥ (spMat s *ᵥ v - v)
      rw [mulVec_sub, ← spMat_mul_mulVec, ← spMat_mul_mulVec, hgs]
    have hgn := hnorm g 1 hgW
    rw [map_one, mul_one] at hgn
    have hmem : spInner r k g * spInner r k h * (spInner r k g)⁻¹ ∈ R.map (spInner r k) :=
      (Subgroup.mem_normalizer_iff.mp hgn _).mp ⟨h, hh, rfl⟩
    obtain ⟨h', hh', hh'eq⟩ := hmem
    rw [← map_inv, ← map_mul, ← map_mul] at hh'eq
    rw [← hιinj hh'eq]
    exact hh'
  have hnormQ : ∀ c ∈ Subgroup.centralizer ({proj r k s} : Set (StatedProj (StatedSp r k))),
      ∀ q ∈ Q, c * q * c⁻¹ ∈ Q := by
    intro c hc q hq
    obtain ⟨g, rfl, hgs⟩ := hlift c hc
    obtain ⟨h, hh, rfl⟩ := hq
    exact ⟨g * h * g⁻¹, hconjR g hgs h hh, by rw [map_mul, map_mul, map_inv]⟩
  refine pPrimeCore_eq_bot_of_le hQC hQp hnormQ fun c hc hcQ => ?_
  obtain ⟨g, rfl, -⟩ := hlift c hc
  have hgR : ∀ h ∈ R, g * h = h * g := by
    intro h hh
    exact hbij.1 (by rw [map_mul, map_mul]; exact hcQ _ ⟨h, hh, rfl⟩)
  have hmem : spInner r k g ∈ spSemilinearAutGroup r k ⊓ Subgroup.centralizer
      ((R.map (spInner r k) : Subgroup (MulAut (StatedProj (StatedSp r k)))) : Set _) := by
    refine Subgroup.mem_inf.mpr ⟨spInner_mem_spSemilinearAutGroup g,
      Subgroup.mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨h, hh, rfl⟩
    rw [← map_mul, ← map_mul, hgR h hh]
  rw [hcentEq] at hmem
  obtain ⟨z, -, hz⟩ := hmem
  have hzg : (z : StatedSp r k) = g := hιinj hz
  exact ⟨z, hzg ▸ z.2, by rw [hzg]⟩

end Symplectic

set_option linter.unusedVariables false in
theorem isSimpleGroup_of_lieModel_psl_two {X : Type} [Group X] {p f : ℕ} (h5 : 5 ≤ p ^ f)
    (h : Blueprint.LieModel X .PSL 2 p f) : IsSimpleGroup X :=
  CFSG.Blueprint.LieModel.isSimpleGroup_psl_two h

theorem oddCore_eq_pPrimeCore_two (X : Type*) [Group X] : CFSG.oddCore X = pPrimeCore 2 X := by
  unfold CFSG.oddCore pPrimeCore
  congr 1
  ext K
  simp only [Set.mem_ofPred_eq, Nat.coprime_two_left]

theorem pPrimeCore_centralizer_eq_bot_of_mulEquiv {S T : Type*} [Group S] [Group T] (e : S ≃* T)
    {t : S} (h : pPrimeCore 2 ↥(centralizer ({e t} : Set T)) = ⊥) :
    pPrimeCore 2 ↥(centralizer ({t} : Set S)) = ⊥ := by
  let φ : centralizer ({t} : Set S) ≃* centralizer ({e t} : Set T) :=
    ((centralizer ({t} : Set S)).equivMapOfInjective e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr (CatFactsSp4.map_centralizer_singleton e t))
  have h1 := pPrimeCore_map_iso 2 φ
  rw [h] at h1
  exact (map_eq_bot_iff_of_injective _ φ.injective).mp h1

theorem classical_facts {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hnonab : ∃ a b : S, a * b ≠ b * a) {τ : Assembly.LowTwoRank.StatedLieTag} {n e : ℕ}
    (h : Assembly.LowTwoRank.StatedClassicalModel S τ n 2 e) :
    CatLeaf.InvolutionCentralizersComponentFree S ∧
      ∀ t : S, orderOf t = 2 → pPrimeCore 2 ↥(centralizer ({t} : Set S)) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hFt : GeneralizedFitting.subgroup S = ⊤ :=
    CatLeaf.generalizedFitting_subgroup_eq_top_of_simple
  have hF : CFSG.generalizedFitting S = GeneralizedFitting.subgroup S :=
    CFSG.generalizedFitting_eq_componentClassification S
  let eG : GeneralizedFitting.subgroup S ≃* S := (MulEquiv.subgroupCongr hFt).trans topEquiv
  have hsimple : IsSimpleGroup (GeneralizedFitting.subgroup S) := eG.isSimpleGroup
  have hnonab₁ : ∃ a b : GeneralizedFitting.subgroup S, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnonab
    exact ⟨eG.symm a, eG.symm b, fun h1 => hab (eG.symm.injective (by rw [map_mul, map_mul, h1]))⟩
  have hsimple' : IsSimpleGroup (CFSG.generalizedFitting S) := hF ▸ hsimple
  have hnonab' : ∃ a b : CFSG.generalizedFitting S, a * b ≠ b * a := hF ▸ hnonab₁
  have hF' : ∀ {τ' : Assembly.LowTwoRank.StatedLieTag},
      Assembly.LowTwoRank.StatedClassicalModel S τ' n 2 e →
      Assembly.LowTwoRank.StatedClassicalModel (CFSG.generalizedFitting S) τ' n 2 e := fun h1 =>
    hF ▸ SectionRank.statedClassicalModel_of_mulEquiv eG h1
  cases τ
  ·
    refine ⟨CatLeaf.involutionCentralizersComponentFree_psl h, fun t ht => ?_⟩
    have hn : 2 ≤ n := h.1.2.2.1
    have hf : 1 ≤ e := h.1.2.1
    obtain ⟨-, ⟨θ⟩⟩ := ClassicalModelStatedBridge.classicalModel_psl_of_stated h
    let θ' :=
      θ.trans (LocalAnalysis.ComponentInitial.LinearFieldFour.pslModelEquivProjectiveSL n 2 e)
    exact pPrimeCore_centralizer_eq_bot_of_mulEquiv θ' (linear_pPrimeCore_eq_bot hf hn
      (GaloisField.card 2 e (by omega)) (θ' t) (by rw [MulEquiv.orderOf_eq, ht]))
  ·
    refine ⟨CatLeaf.involutionCentralizersComponentFree_psu h, fun t ht => ?_⟩
    rw [← oddCore_eq_pPrimeCore_two]
    exact (UnbalancedCatalog.even_unitary_almost_simple_odd_core_vanishing hnonab' (hF' h)).2 t ht
  ·
    refine ⟨CatLeaf.involutionCentralizersComponentFree_psp h, fun t ht => ?_⟩
    obtain ⟨⟨-, hf, hn, -⟩, K, _, _, hK, ⟨θ⟩⟩ := h
    exact pPrimeCore_centralizer_eq_bot_of_mulEquiv θ (symplectic_pPrimeCore_eq_bot hf
      (by omega) hK (θ t) (by rw [MulEquiv.orderOf_eq, ht]))
  ·
    exact absurd rfl h.1.2.2.2
  ·
    refine ⟨CatLeaf.involutionCentralizersComponentFree_orthogonal (.inl rfl) h, fun t ht => ?_⟩
    rw [← oddCore_eq_pPrimeCore_two]
    exact (UnbalancedCatalog.even_orthogonal_almost_simple_odd_core_vanishing hnonab' _ (.inl rfl)
      (hF' h)).2 t ht
  ·
    refine ⟨CatLeaf.involutionCentralizersComponentFree_orthogonal (.inr rfl) h, fun t ht => ?_⟩
    rw [← oddCore_eq_pPrimeCore_two]
    exact (UnbalancedCatalog.even_orthogonal_almost_simple_odd_core_vanishing hnonab' _ (.inr rfl)
      (hF' h)).2 t ht
  all_goals exact h.2.elim

theorem false_of_config {M : Type} [Group M] [Finite M] {p' f' p f : ℕ}
    (hc : QPUJConfig M p' f' p f) {τ : Assembly.LowTwoRank.StatedLieTag} {n e : ℕ}
    (hM : Assembly.LowTwoRank.StatedClassicalModel (M ⧸ center M) τ n 2 e) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hq, hZ2, -, -, -, -, -, -, -, h5, -, -, -, -, t, J, -, -, -, -, -, -, -, ht2, htZ, hJC,
    hJpc, hJLie, -, -, -⟩ := hc
  have : IsSimpleGroup (M ⧸ center M) := hq.2.1
  obtain ⟨hcomp, hodd⟩ := classical_facts hq.2.2 hM
  set ρ := QuotientGroup.mk' (center M)
  have hρ : Function.Surjective ρ := QuotientGroup.mk'_surjective _
  have ht1 : ρ t ≠ 1 := by
    intro h1
    apply htZ
    rw [← QuotientGroup.ker_mk' (center M)]
    exact h1
  have htt : orderOf (ρ t) = 2 :=
    orderOf_eq_prime (by rw [pow_two, ← map_mul, ht2, map_one]) ht1
  have hJp : Group.IsPerfect ↥J := B5a.isPerfect_of_isPComponent_subgroupOf hJC hJpc
  have hJZ : J ⊓ center M = ⊥ := by
    have := isSimpleGroup_of_lieModel_psl_two h5 hJLie
    have : Group.IsPerfect (↥J ⧸ pPrimeCore 2 ↥J) :=
      Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
    have hZq : center (↥J ⧸ pPrimeCore 2 ↥J) = ⊥ := Seven.center_eq_bot_of_isPerfect
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨hzJ, hzZ⟩ := mem_inf.mp hz
    set z' : ↥J := ⟨z, hzJ⟩
    have hz'c : QuotientGroup.mk' (pPrimeCore 2 ↥J) z' ∈ center (↥J ⧸ pPrimeCore 2 ↥J) := by
      rw [mem_center_iff]
      intro u
      obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥J) u
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (mem_center_iff.mp hzZ w)
    rw [hZq, mem_bot, ← MonoidHom.mem_ker, QuotientGroup.ker_mk'] at hz'c
    have hR : IsPGroup 2 ((center M).subgroupOf J) := hZ2.comap_subtype
    have h1 : z' ∈ (center M).subgroupOf J ⊓ pPrimeCore 2 ↥J := mem_inf.mpr ⟨hzZ, hz'c⟩
    rw [OddQuot.inf_pPrimeCore_eq_bot hR, mem_bot] at h1
    exact mem_bot.mpr (congrArg Subtype.val h1)
  set C := centralizer ({t} : Set M)
  set Cb := centralizer ({ρ t} : Set (M ⧸ center M))
  set H := Cb.comap ρ
  have hCH : C ≤ H := fun c hc => by
    show ρ c ∈ Cb
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul, mem_centralizer_singleton_iff.mp hc]
  have hCn : (C.subgroupOf H).Normal := by
    constructor
    intro c hc h
    rw [mem_subgroupOf] at hc ⊢
    have hh : ρ (h : M) * ρ t = ρ t * ρ (h : M) := mem_centralizer_singleton_iff.mp h.2
    set z := (h : M) * t * (h : M)⁻¹ * t⁻¹ with hzdef
    have hz1 : ρ z = 1 := by
      rw [hzdef, map_mul, map_mul, map_mul, map_inv, map_inv, hh]
      group
    have hz : z ∈ center M := by
      rw [← QuotientGroup.ker_mk' (center M)]
      exact hz1
    have hzc : ∀ g : M, g * z = z * g := mem_center_iff.mp hz
    have hzc' : ∀ g : M, g * z⁻¹ = z⁻¹ * g := mem_center_iff.mp (inv_mem hz)
    have h1 : (h : M) * t * (h : M)⁻¹ = z * t := by
      rw [hzdef]
      group
    have h2 : t = z * ((h : M)⁻¹ * t * h) := by
      calc t = (h : M)⁻¹ * ((h : M) * t * (h : M)⁻¹) * h := by group
        _ = (h : M)⁻¹ * (z * t) * h := by rw [h1]
        _ = (h : M)⁻¹ * z * (t * h) := by group
        _ = z * (h : M)⁻¹ * (t * h) := by rw [hzc (h : M)⁻¹]
        _ = z * ((h : M)⁻¹ * t * h) := by group
    have hu : (h : M)⁻¹ * t * h = z⁻¹ * t := by
      calc (h : M)⁻¹ * t * h = z⁻¹ * (z * ((h : M)⁻¹ * t * h)) := by group
        _ = z⁻¹ * t := by rw [← h2]
    have hct : (c : M) * t = t * c := mem_centralizer_singleton_iff.mp hc
    show (h : M) * c * (h : M)⁻¹ ∈ C
    rw [mem_centralizer_singleton_iff]
    calc (h : M) * c * (h : M)⁻¹ * t = h * c * ((h : M)⁻¹ * t * h) * (h : M)⁻¹ := by group
      _ = h * c * (z⁻¹ * t) * (h : M)⁻¹ := by rw [hu]
      _ = h * ((c : M) * z⁻¹) * t * (h : M)⁻¹ := by group
      _ = h * (z⁻¹ * c) * t * (h : M)⁻¹ := by rw [hzc' (c : M)]
      _ = h * z⁻¹ * ((c : M) * t) * (h : M)⁻¹ := by group
      _ = h * z⁻¹ * (t * c) * (h : M)⁻¹ := by rw [hct]
      _ = h * (z⁻¹ * t) * c * (h : M)⁻¹ := by group
      _ = h * ((h : M)⁻¹ * t * h) * c * (h : M)⁻¹ := by rw [hu]
      _ = t * (h * c * (h : M)⁻¹) := by group
  obtain ⟨-, -, hJs, -⟩ := id hJpc
  have hJH : J ≤ H := hJC.trans hCH
  have hJ1s : (J.subgroupOf H).IsSubnormal := by
    have hle : J.subgroupOf H ≤ C.subgroupOf H := fun x hx => hJC hx
    refine Subgroup.IsSubnormal.trans hle ?_ hCn.isSubnormal
    have heq : (J.subgroupOf C).map (subgroupOfEquivOfLe hCH).symm.toMonoidHom =
        (J.subgroupOf H).subgroupOf (C.subgroupOf H) := by
      ext x
      rw [mem_map]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hx
        exact ⟨subgroupOfEquivOfLe hCH x, hx, (subgroupOfEquivOfLe hCH).symm_apply_apply x⟩
    rw [← heq]
    exact hJs.map (subgroupOfEquivOfLe hCH).symm.surjective
  let ρH : ↥H →* ↥Cb := (ρ.comp H.subtype).codRestrict Cb fun h => h.2
  have hρH : Function.Surjective ρH := by
    intro c
    obtain ⟨m, hm⟩ := hρ (c : M ⧸ center M)
    have hmH : m ∈ H := by
      show ρ m ∈ Cb
      rw [hm]
      exact c.2
    exact ⟨⟨m, hmH⟩, Subtype.ext hm⟩
  let g : ↥(J.subgroupOf H) →* ↥Cb := ρH.comp (J.subgroupOf H).subtype
  have hg : Function.Injective g := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : ((x : H) : M) ∈ J ⊓ center M := by
      refine mem_inf.mpr ⟨x.2, ?_⟩
      rw [← QuotientGroup.ker_mk' (center M), MonoidHom.mem_ker]
      exact congrArg Subtype.val hx
    rw [hJZ, mem_bot] at h1
    exact Subtype.ext (Subtype.ext h1)
  have hJbs : g.range.IsSubnormal := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    exact hJ1s.map hρH
  have hO : pPrimeCore 2 ↥g.range = ⊥ := by
    have hNs : ((pPrimeCore 2 ↥g.range).map g.range.subtype).IsSubnormal := by
      refine Subgroup.IsSubnormal.trans (map_subtype_le _) ?_ hJbs
      rw [show ((pPrimeCore 2 ↥g.range).map g.range.subtype).subgroupOf g.range =
          pPrimeCore 2 ↥g.range from comap_map_eq_self_of_injective g.range.subtype_injective _]
      exact (CFSG.pPrimeCore_normal (p := 2) (G := ↥g.range)).isSubnormal
    have hcop : Nat.Coprime 2 (Nat.card ↥((pPrimeCore 2 ↥g.range).map g.range.subtype)) := by
      rw [card_map_of_injective g.range.subtype_injective]
      exact CFSG.pPrimeCore_coprime_card
    have h1 := RankThree.PartOne.Sec1511.le_pPrimeCore_of_isSubnormal_p hNs hcop
    rw [hodd (ρ t) htt, le_bot_iff] at h1
    exact (map_eq_bot_iff_of_injective _ g.range.subtype_injective).mp h1
  have hq1 : IsQuasisimple (↥(J.subgroupOf C) ⧸ pPrimeCore 2 ↥(J.subgroupOf C)) :=
    ((CatalogueBPrimeJoin.pComponent_iff_subnormal_generated_quasisimple 2 _).mp hJpc).2.2
  let e2 : ↥(J.subgroupOf C) ≃* ↥g.range :=
    ((subgroupOfEquivOfLe hJC).trans (subgroupOfEquivOfLe hJH).symm).trans
      (MonoidHom.ofInjective hg)
  have hO' : pPrimeCore 2 ↥(J.subgroupOf C) = ⊥ := by
    have h1 := pPrimeCore_map_iso 2 e2
    rw [hO] at h1
    exact (map_eq_bot_iff_of_injective _ e2.injective).mp h1
  have hqJb : IsQuasisimple ↥g.range :=
    (LocalAnalysis.ComponentInitial.isQuasisimple_congr
      (((QuotientGroup.quotientMulEquivOfEq hO').trans QuotientGroup.quotientBot).trans e2)).1 hq1
  exact hcomp (ρ t) htt g.range ⟨hqJb, hJbs⟩

end QPUJ.Even

@[expose] def CFQPUJCrossCharOdd : Prop :=
  ∀ (M : Type) [Group M] [Finite M] (p' f' p f : ℕ), QPUJConfig M p' f' p f →
    ¬ ∃ (t : Assembly.LowTwoRank.StatedLieTag) (n r f'' : ℕ), r ≠ p' ∧ r ≠ 2 ∧
      Assembly.LowTwoRank.StatedClassicalModel (M ⧸ center M) t n r f''

theorem cfQPUJCrossChar_of_odd (h : CFQPUJCrossCharOdd) : CFQPUJCrossChar := by
  intro M _ _ p' f' p f hc ⟨τ, n, r, f'', hr, hmod⟩
  by_cases hr2 : r = 2
  · subst hr2
    exact QPUJ.Even.false_of_config hc hmod
  · exact h M p' f' p f hc ⟨τ, n, r, f'', hr, hr2, hmod⟩

end CFSG.ComponentClassification.GSThmB
