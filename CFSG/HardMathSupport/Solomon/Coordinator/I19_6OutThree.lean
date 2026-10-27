module

public import CFSG.HardMathSupport.Solomon.Coordinator.I19_6Red
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.DefCharExceptional
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.DefCharOrth
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.CentralResidueMaps
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalizerClassLifting
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.PrincipalClassDefects
public import CFSG.CharacterTheory.Semidihedral.ElementStructure
public import CFSG.CharacterTheory.Semidihedral.Principal.DegreeZeroGram
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma32
public import CFSG.HardMathSupport.Solomon.LocalBalance.Prop22
public import CFSG.HardMathSupport.Timmesfeld.Proving.ExistsOrderPCentralizer
public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPrimeCoreCentralizer
public import CFSG.LieType.Chevalley.EvenRootCommutatorF4
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
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
public import CFSG.Walter.Ree.Model.JTHyp
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

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open (IsElemAbelian)
open CFSG.HardMathSupport.Timmesfeld.DefChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
open CFSG.HardMathSupport.Solomon.LocalBalance (innerAut)

set_option linter.unusedSectionVars false

open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedLieTag StatedProj StatedOmega
  StatedQuadOdd StatedQuadPlus StatedQuadMinus)
open Matrix Subgroup QuadraticMap CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinearFiltration
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
  CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit
  (orthogonal_geometry_plus_point_family_orbit)
local notation "Inn" => CFSG.ComponentClassification.OuterAutomorphisms.inner
open CFSG.RankThree.PartOne.OutStructure (OutPChain OutPNice instFiniteMulAut')
open scoped Pointwise commutatorElement

section Orth

theorem i196_exists_inner_of_tower_le {G : Type*} [Group G] [Finite G] {I D E X : Subgroup G}
    {p m : ℕ} (hp : p.Prime) (hDn : (D.subgroupOf E).Normal)
    (hidx : E.index ≤ m) (g : G) (hgE : g ∈ E) (hg : ∀ e ∈ E, ∃ k : ℤ, g ^ k * e ∈ D)
    (hDI : ∀ δ ∈ D, δ ^ p = 1 → δ ∈ I) (hexp : ∀ x ∈ X, x ^ p = 1)
    (hcard : m * p < Nat.card X) : ∃ x ∈ X ⊓ I, x ≠ 1 := by
  classical
  have hY : E.relIndex X ≤ m := by
    refine (Subgroup.relIndex_le_of_le_right le_top ?_).trans ?_
    · rw [Subgroup.relIndex_top_right]
      exact Subgroup.index_ne_zero_of_finite
    · rwa [Subgroup.relIndex_top_right]
  have hmul : E.relIndex X * Nat.card (E ⊓ X : Subgroup G) = Nat.card X :=
    Subgroup.relIndex_mul_card E X
  have hYX : E ⊓ X ≤ E := inf_le_left
  have hcyc : IsCyclic (E ⧸ D.subgroupOf E) := by
    refine ⟨⟨QuotientGroup.mk ⟨g, hgE⟩, fun y => ?_⟩⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨k, hk⟩ := hg x x.2
    refine ⟨-k, ?_⟩
    change (QuotientGroup.mk (⟨g, hgE⟩ : E) : E ⧸ D.subgroupOf E) ^ (-k) = QuotientGroup.mk x
    rw [← QuotientGroup.mk_zpow, QuotientGroup.eq, Subgroup.mem_subgroupOf, _root_.zpow_neg, inv_inv,
      Subgroup.coe_mul, Subgroup.coe_zpow]
    exact hk
  let α : (E ⊓ X : Subgroup G) →* E ⧸ D.subgroupOf E :=
    (QuotientGroup.mk' (D.subgroupOf E)).comp (Subgroup.inclusion hYX)
  have hexpα : Monoid.exponent α.range ∣ p := by
    refine Monoid.exponent_dvd_of_forall_pow_eq_one fun y => ?_
    obtain ⟨x, rfl⟩ := α.rangeRestrict_surjective y
    have : (x : (E ⊓ X : Subgroup G)) ^ p = 1 :=
      Subtype.ext (hexp x (x.2.2))
    rw [← map_pow, this, map_one]
  have := hcyc
  have : IsCyclic α.range := inferInstance
  rw [IsCyclic.exponent_eq_card] at hexpα
  have hsplit : Nat.card (E ⊓ X : Subgroup G) = Nat.card α.range * Nat.card α.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup α.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange α).toEquiv]
  have hrle : Nat.card α.range ≤ p := Nat.le_of_dvd hp.pos hexpα
  have hYpos : 0 < Nat.card (E ⊓ X : Subgroup G) := Nat.card_pos
  have hYgt : p < Nat.card (E ⊓ X : Subgroup G) := by
    by_contra hle
    push Not at hle
    have h1 : Nat.card X ≤ m * p := by
      rw [← hmul]
      exact Nat.mul_le_mul hY hle
    omega
  have hk1 : 1 < Nat.card α.ker := by
    by_contra hle
    push Not at hle
    have h1 : Nat.card (E ⊓ X : Subgroup G) ≤ p * 1 := by
      rw [hsplit]
      exact Nat.mul_le_mul hrle hle
    omega
  have : Nontrivial α.ker := Finite.one_lt_card_iff_nontrivial.1 hk1
  obtain ⟨⟨d, hdk⟩, hd1⟩ := exists_ne (1 : α.ker)
  have hd1' : d ≠ 1 := fun h => hd1 (Subtype.ext h)
  have hdX : (d : G) ∈ X := d.2.2
  have hdD : (d : G) ∈ D := by
    have h : α d = 1 := hdk
    change QuotientGroup.mk (Subgroup.inclusion hYX d) = (1 : E ⧸ D.subgroupOf E) at h
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h
    exact h
  have hdp : (d : G) ^ p = 1 := hexp _ hdX
  exact ⟨d, ⟨hdX, hDI _ hdD hdp⟩, fun h => hd1' (Subtype.ext h)⟩

theorem i196_exists_inner_of_matrixProjectiveDerived_le {K : Type} [Field K] [Finite K] {d : ℕ}
    (Q : QuadraticForm K (Fin d → K)) (hQ : Q ≠ 0)
    (hab : ∃ m : ℕ, Nat.card (Abelianization (matrixIsometries Q)) = 2 ^ m)
    {p m : ℕ} (hidx : (matrixProjectiveImage Q).index ≤ m) (hp : p.Prime) (hp2 : p ≠ 2)
    (X : Subgroup (MulAut (matrixProjectiveDerived Q))) (hexp : ∀ x ∈ X, x ^ p = 1)
    (hcard : m * p < Nat.card X) :
    ∃ x ∈ X ⊓ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (matrixProjectiveDerived Q), x ≠ 1 := by
  have hQv := exists_nonzero_value Q hQ
  have hDE : (linearConjugationHom Q).range ≤ matrixProjectiveImage Q := by
    rintro _ ⟨g, rfl⟩
    exact (mem_matrixProjectiveImage_iff Q _).mpr ⟨g.val, rfl⟩
  have hcomm : ∀ g h : similarityPairs Q,
      ⁅matrixProjectiveConjugationHom Q g, matrixProjectiveConjugationHom Q h⁆ ∈
        (linearConjugationHom Q).range := fun g h => by
    rw [← map_commutatorElement]
    exact ⟨⟨⁅g, h⁆, similarity_commutator_le_linear Q
      (Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top h))⟩, rfl⟩
  have hDn : ((linearConjugationHom Q).range.subgroupOf (matrixProjectiveImage Q)).Normal := by
    refine ⟨fun n hn e => ?_⟩
    obtain ⟨g, hg⟩ := (mem_matrixProjectiveImage_iff Q ((e : matrixProjectiveImage Q) :
      MulAut (matrixProjectiveDerived Q))).mp e.2
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨h, hh⟩ := hn
    have hcn : ⁅((e : matrixProjectiveImage Q) : MulAut (matrixProjectiveDerived Q)),
        ((n : matrixProjectiveImage Q) : MulAut (matrixProjectiveDerived Q))⁆ ∈
        (linearConjugationHom Q).range := by
      rw [← hg, ← hh]
      exact hcomm g h.val
    have : (((e * n * e⁻¹ : matrixProjectiveImage Q)) : MulAut (matrixProjectiveDerived Q)) =
        ⁅((e : matrixProjectiveImage Q) : MulAut (matrixProjectiveDerived Q)),
        ((n : matrixProjectiveImage Q) : MulAut (matrixProjectiveDerived Q))⁆ *
          ((n : matrixProjectiveImage Q) : MulAut (matrixProjectiveDerived Q)) := by
      simp [commutatorElement_def, mul_assoc]
    rw [this]
    exact (linearConjugationHom Q).range.mul_mem hcn (hh ▸ ⟨h, rfl⟩)
  obtain ⟨g₀, hg₀⟩ : ∃ g₀ : similarityPairs Q, ∀ h : similarityPairs Q, ∃ k : ℤ,
      g₀ ^ k * h ∈ linearSimilarityPairs Q := by
    have hcyc := fieldQuotient_cyclic Q
    obtain ⟨γ, hγ⟩ := hcyc.exists_generator
    obtain ⟨g₀, rfl⟩ := QuotientGroup.mk_surjective γ
    refine ⟨g₀, fun h => ?_⟩
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hγ (QuotientGroup.mk h))
    refine ⟨-m, ?_⟩
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_zpow,
      _root_.zpow_neg, ← hm]
    simp
  have hgE : matrixProjectiveConjugationHom Q g₀ ∈ matrixProjectiveImage Q :=
    (mem_matrixProjectiveImage_iff Q _).mpr ⟨g₀, rfl⟩
  have hDI : ∀ δ ∈ (linearConjugationHom Q).range, δ ^ p = 1 →
      δ ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner (matrixProjectiveDerived Q) := by
    intro δ hδ hδp
    set D := (linearConjugationHom Q).range with hD
    set I := CFSG.ComponentClassification.OuterAutomorphisms.inner (matrixProjectiveDerived Q)
      with hI
    set x : D ⧸ I.subgroupOf D := QuotientGroup.mk (⟨δ, hδ⟩ : D) with hx
    have hxk : x ^ p = 1 := by
      rw [hx, ← QuotientGroup.mk_pow]
      have : (⟨δ, hδ⟩ : D) ^ p = 1 := Subtype.ext hδp
      rw [this]
      rfl
    have hcard : Nat.card (D ⧸ I.subgroupOf D) = I.relIndex D :=
      (Subgroup.index_eq_card _).symm
    have hdvd1 : orderOf x ∣ p := orderOf_dvd_of_pow_eq_one hxk
    have hdvd2 : orderOf x ∣ I.relIndex D := hcard ▸ orderOf_dvd_natCard x
    have hcop : Nat.Coprime p (I.relIndex D) :=
      (Nat.Prime.coprime_iff_not_dvd hp).mpr
        (not_dvd_relIndex_inner_linearRange Q hQv hab hp hp2)
    have hx1 : orderOf x = 1 := Nat.eq_one_of_dvd_coprimes hcop hdvd1 hdvd2
    have : x = 1 := orderOf_eq_one_iff.mp hx1
    have hmem := (QuotientGroup.eq_one_iff (⟨δ, hδ⟩ : D)).mp this
    exact Subgroup.mem_subgroupOf.mp hmem
  have hfin : Finite (MulAut (matrixProjectiveDerived Q)) := inferInstance
  refine i196_exists_inner_of_tower_le (E := matrixProjectiveImage Q) hp hDn hidx
    (matrixProjectiveConjugationHom Q g₀) hgE ?_ hDI hexp hcard
  intro e he
  obtain ⟨h, rfl⟩ := (mem_matrixProjectiveImage_iff Q e).mp he
  obtain ⟨k, hk⟩ := hg₀ h
  refine ⟨k, ⟨⟨g₀ ^ k * h, hk⟩, ?_⟩⟩
  change matrixProjectiveConjugationHom Q (g₀ ^ k * h) = _
  rw [map_mul, map_zpow]
  rfl

theorem i196_meetsInnerTwo_POmegaOdd_one {T : Type} [Group T] [Finite T] {n ℓ f : ℕ}
    (hm : StatedClassicalModel T .POmegaOdd n ℓ f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    MeetsInnerTwo p T := by
  have h0 := hm
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h0
  have hab := orthogonal_model_isometry_abelianization_order_bound T .POmegaOdd (.inl rfl)
    n ℓ f hm K hK (quadOdd n K) (coe_quadOdd n K) e
  have hE : matrixProjectiveImage (coordinateQuadOdd n K) = ⊤ := by
    rw [← ((orthogonal_geometry_model_stabilizer_preserving_image T .POmegaOdd (.inl rfl) n ℓ
      f hm) K hK e).1]
    exact ((OrthogonalTail.orthogonal_geometry_tail_model_point_family_invariant T .POmegaOdd
      (.inl rfl) n ℓ f hm) K hK).2
  refine MeetsInnerTwo.of_mulEquiv (coordinateOddWitnessEquiv K e) fun X hX hcard => ?_
  exact i196_exists_inner_of_matrixProjectiveDerived_le (m := 1) _
    (coordinate_model_intrinsic_odd hm K hK e).1
    (exists_two_pow_card_abelianization (oddIndexEquiv n) (quadOdd n K) hab)
    (le_of_eq (by rw [hE, Subgroup.index_top])) hp hp2 X hX.2
    (by rw [hcard, one_mul]; exact lt_pow_two_of_prime hp)

theorem i196_meetsInnerTwo_POmegaPlus_one {T : Type} [Group T] [Finite T] {n ℓ f : ℕ}
    (hm : StatedClassicalModel T .POmegaPlus n ℓ f) (h5 : 5 ≤ n) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) : MeetsInnerTwo p T := by
  have h0 := hm
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h0
  have hab := orthogonal_model_isometry_abelianization_order_bound T .POmegaPlus
    (.inr (.inl rfl)) n ℓ f hm K hK (quadPlus n K) (coe_quadPlus n K) e
  have hEA := ((orthogonal_geometry_model_stabilizer_preserving_image T .POmegaPlus
    (.inr (.inl rfl)) n ℓ f hm) K hK e).1
  have horbit := orthogonal_geometry_plus_point_family_orbit hm hK e
  have hidx : (matrixProjectiveImage (coordinateQuadPlus n K)).index ≤ 1 := by
    rw [← hEA, horbit.2.2.2.2.1 h5, Subgroup.index_top]
  refine MeetsInnerTwo.of_mulEquiv (coordinatePlusWitnessEquiv K e) fun X hX hcard => ?_
  exact i196_exists_inner_of_matrixProjectiveDerived_le (m := 1) _
    (coordinate_model_intrinsic_plus hm K hK e).1
    (exists_two_pow_card_abelianization (plusIndexEquiv n) (quadPlus n K) hab) hidx hp hp2 X hX.2
    (by rw [hcard, one_mul]; exact lt_pow_two_of_prime hp)

theorem i196_meetsInnerTwo_POmegaMinus_one {T : Type} [Group T] [Finite T] {n ℓ f : ℕ}
    (hm : StatedClassicalModel T .POmegaMinus n ℓ f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    MeetsInnerTwo p T := by
  have hn1 : 1 ≤ n := by
    have := hm.1.2.2
    omega
  have h0 := hm
  obtain ⟨-, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := h0
  have hab := orthogonal_model_isometry_abelianization_order_bound T .POmegaMinus
    (.inr (.inr rfl)) n ℓ f hm K hK b c hirr (quadMinus n K b c) (coe_quadMinus n K b c) e
  have hE : matrixProjectiveImage (coordinateQuadMinus n K hn1 b c) = ⊤ := by
    rw [← ((orthogonal_geometry_model_stabilizer_preserving_image T .POmegaMinus
      (.inr (.inr rfl)) n ℓ f hm) hn1 K hK b c hirr e).1]
    exact ((OrthogonalTail.orthogonal_geometry_tail_model_point_family_invariant T
      .POmegaMinus (.inr rfl) n ℓ f hm) hn1 K hK b c hirr).2
  refine MeetsInnerTwo.of_mulEquiv (coordinateMinusWitnessEquiv K hn1 b c e) fun X hX hcard => ?_
  exact i196_exists_inner_of_matrixProjectiveDerived_le (m := 1) _
    (coordinate_model_intrinsic_minus hm K hK b c hirr e).1
    (exists_two_pow_card_abelianization (minusIndexEquiv n hn1) (quadMinus n K b c) hab)
    (le_of_eq (by rw [hE, Subgroup.index_top])) hp hp2 X hX.2
    (by rw [hcard, one_mul]; exact lt_pow_two_of_prime hp)

end Orth


section Families


@[expose] def i196_OuterTwoThreeFam (k : DefCharFamily) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ idx : TauCeti.ValidLieTypeIndex, k.Matches idx.1 →
      (¬ ∃ q : TauCeti.PrimePower, idx.1 = .D 4 q) →
      Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group) →
      ∀ p : ℕ, p.Prime → p = 3 → idx.1.characteristic = p →
        ∀ D : Subgroup (MulAut S), IsElemAbelian p D → Nat.card D = p ^ 2 →
          ∃ x ∈ D ⊓ innerAut S, x ≠ 1

theorem i196_outerTwoThreeFamA : i196_OuterTwoThreeFam .A := by
  intro S _ _ hS hnab idx hk _ hidx p hp hp3 hch D hD hcard
  obtain ⟨r, q, hrq⟩ := hk
  have hv := idx.2
  rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff, hrq] at hv
  have hr1 : 1 ≤ r := hv.1.1
  have hlt : p < Nat.card D := by rw [hcard]; exact lt_pow_two_of_prime hp
  have hp2 : p ≠ 2 := by omega
  by_cases hr : r = 1
  · exact outerRank_A_one idx ⟨q, hrq.trans (by rw [hr])⟩ hidx hp hp2 hch D hD hlt
  · exact outerRank_A_of_two_le idx ⟨r, q, hrq, by omega⟩ hidx hp hp2 hch D hD hlt

theorem i196_outerTwoThreeFamC : i196_OuterTwoThreeFam .C := by
  intro S _ _ hS hnab idx hk _ hidx p hp hp3 hch D hD hcard
  exact outerRank_C idx hk hidx hp hch D hD (by rw [hcard]; exact lt_pow_two_of_prime hp)

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag in
theorem i196_outerTwoThreeFamTwistedA : i196_OuterTwoThreeFam .twistedA := by
  intro S _ _ hS' hnab idx hidx _ hS p hp hp3 hch D hD hcard
  have hlt : p < Nat.card D := by rw [hcard]; exact lt_pow_two_of_prime hp
  obtain ⟨r, q, hr⟩ := hidx
  obtain ⟨d, hv⟩ := idx
  simp only at hr
  subst hr
  obtain ⟨e0⟩ := hS
  have hpq : p = q.p := by simpa using hch.symm
  have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e0
  obtain ⟨⟨hℓ, hf, hn, hq⟩, K, _, _, hK, ⟨eT⟩⟩ := hm
  have h : UnitaryFieldData q.p q.exponent K := ⟨hℓ, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have hq' : ¬(r + 1 = 3 ∧ q.p ^ q.exponent = 2) := fun ⟨h1, h2⟩ => hq (by rw [h1, h2])
  obtain ⟨eP⟩ := nonempty_primeFormP_mulEquiv h (isPrimeFormGram_one (n := r + 1) (K := K))
  let e : S ≃* primeFormP h ((1 : GL (Fin (r + 1)) K) : Matrix (Fin (r + 1)) (Fin (r + 1)) K) :=
    (eT.trans (unitaryPSUEquiv h (by omega)).symm).trans eP.symm
  have hpq' : p = q.p := hpq
  subst hpq'
  have hndvd : ¬ q.p ∣ q.p ^ q.exponent + 1 := by
    intro hd
    have h1 : q.p ∣ q.p ^ q.exponent := dvd_pow_self _ q.exponent_pos.ne'
    exact hp.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right h1).1 hd))
  exact exists_inner_transport_lt e D (fun a ha => hD.2 a ha) hlt fun D' hexp hc =>
    exists_inner_of_elemAbelian_primeFormP h (n := r + 1) (by omega) hq' hp hndvd D' hexp hc

open TauCeti in
theorem i196_outerTwoThreeFamB : i196_OuterTwoThreeFam .B := by
  intro S _ _ _ _ idx hidx _ hS p hp hp3 hch D hD hcard
  obtain ⟨r, q, hr⟩ := hidx
  obtain ⟨d, hv⟩ := idx
  simp only at hr hch
  subst hr
  obtain ⟨e⟩ := hS
  have hpq : p = q.p := by simpa using hch.symm
  have hp2 : p ≠ 2 := by omega
  have hqp2 : q.p ≠ 2 := hpq ▸ hp2
  have hr2 : 2 ≤ r := ((LieTypeIndex.inStandardRange_iff _).mp ((LieTypeIndex.valid_iff _).mp hv).1).1
  rcases Nat.eq_or_lt_of_le hr2 with h2 | h3
  · subst h2
    exact meetsInnerTwo_PSp_two hqp2
      (CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e) hp hp2 D hD hcard
  · exact i196_meetsInnerTwo_POmegaOdd_one (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_odd r q
      hv hqp2 h3 e) hp hp2 D hD hcard

open TauCeti in
theorem i196_outerTwoThreeFamD : i196_OuterTwoThreeFam .D := by
  intro S _ _ _ _ idx hidx hnD4 hS p hp hp3 hch D hD hcard
  obtain ⟨r, q, hr⟩ := hidx
  have h5 : 5 ≤ r := by
    have hv := idx.2
    rw [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff, hr] at hv
    have h4 : 4 ≤ r := hv.1
    by_contra h
    exact hnD4 ⟨q, by rw [hr, show r = 4 by omega]⟩
  obtain ⟨d, hv⟩ := idx
  simp only at hr
  subst hr
  obtain ⟨e⟩ := hS
  exact i196_meetsInnerTwo_POmegaPlus_one
    (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD r q hv e) h5 hp (by omega) D hD hcard

open TauCeti in
theorem i196_outerTwoThreeFamTwistedD : i196_OuterTwoThreeFam .twistedD := by
  intro S _ _ _ _ idx hidx _ hS p hp hp3 hch D hD hcard
  obtain ⟨r, q, hr⟩ := hidx
  obtain ⟨d, hv⟩ := idx
  simp only at hr
  subst hr
  obtain ⟨e⟩ := hS
  exact i196_meetsInnerTwo_POmegaMinus_one
    (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD r q hv e) hp (by omega) D hD hcard

section E

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Open

theorem i196_outerTwoThreeFamE6 : i196_OuterTwoThreeFam .E6 := by
  intro S _ _ _ _ idx hidx _ hS p hp hp3 hch D hD hcard
  obtain ⟨q, hq⟩ := hidx
  obtain ⟨d, hv⟩ := idx
  simp only at hq
  subst hq
  obtain ⟨e0⟩ := hS
  have hpq : p = q.p := by simpa using hch.symm
  exact exists_inner_of_bridge_E_lt (Or.inl rfl) CFSG.TauCetiBridge.chevalleyBridges.e6 q hv S e0
    hp (by omega) hpq D hD (by rw [hcard]; exact lt_pow_two_of_prime hp)

theorem i196_outerTwoThreeFamE7 : i196_OuterTwoThreeFam .E7 := by
  intro S _ _ _ _ idx hidx _ hS p hp hp3 hch D hD hcard
  obtain ⟨q, hq⟩ := hidx
  obtain ⟨d, hv⟩ := idx
  simp only at hq
  subst hq
  obtain ⟨e0⟩ := hS
  have hpq : p = q.p := by simpa using hch.symm
  exact exists_inner_of_bridge_E_lt (Or.inr (Or.inl rfl))
    CFSG.TauCetiBridge.chevalleyBridges.e7 q hv S e0 hp (by omega) hpq D hD
    (by rw [hcard]; exact lt_pow_two_of_prime hp)

theorem i196_outerTwoThreeFamE8 : i196_OuterTwoThreeFam .E8 := by
  intro S _ _ _ _ idx hidx _ hS p hp hp3 hch D hD hcard
  obtain ⟨q, hq⟩ := hidx
  obtain ⟨d, hv⟩ := idx
  simp only at hq
  subst hq
  obtain ⟨e0⟩ := hS
  have hpq : p = q.p := by simpa using hch.symm
  exact exists_inner_of_bridge_E_lt (Or.inr (Or.inr rfl))
    CFSG.TauCetiBridge.chevalleyBridges.e8 q hv S e0 hp (by omega) hpq D hD
    (by rw [hcard]; exact lt_pow_two_of_prime hp)

end E

section F4G2

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree

theorem i196_outerTwoThreeFamF4 : i196_OuterTwoThreeFam .F4 := by
  intro S _ _ _ _ idx hidx _ hS p hp hp3 hch D hD hcard
  have hp2 : p ≠ 2 := by omega
  obtain ⟨q, hq⟩ := hidx
  obtain ⟨d, hv⟩ := idx
  simp only at hq
  subst hq
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  obtain ⟨e0⟩ := hS
  have hpq : p = q.p := by simpa using hch.symm
  subst hpq
  set K := GaloisField q.p q.exponent
  have hK : Nat.card K = q.p ^ q.exponent := GaloisField.card _ _ q.exponent_pos.ne'
  have hK' : Nat.card K = q.card := by rw [hK, TauCeti.PrimePower.card_def]
  obtain ⟨b⟩ := (CFSG.TauCetiBridge.Even.chevalleyBridgesAll).f4 q hv K hK'
  let e : S ≃* adjointGroup .F4 K :=
    e0.trans (b.symm.trans ((QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans
      QuotientGroup.quotientBot))
  obtain ⟨-, Θ, -, -, hker, -⟩ := odd_F4_and_nonexceptional_G2_automorphism_normal_form hp hp2
    q.exponent_pos K hK .F4 (Or.inl rfl)
  have := CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic K
  have : Finite (K ≃+* K) :=
    Finite.of_injective (fun σ : K ≃+* K => (σ : K → K)) DFunLike.coe_injective
  exact exists_inner_of_cyclic_quotient e Θ hker hp D hD.2
    (by rw [hcard]; exact lt_pow_two_of_prime hp)

theorem i196_outerTwoThreeFamG2 : i196_OuterTwoThreeFam .G2 := by
  intro S _ _ _ _ idx hidx _ hS p hp hp3 hch D hD hcard
  obtain ⟨q, hq⟩ := hidx
  obtain ⟨d, hv⟩ := idx
  simp only at hq
  subst hq
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  obtain ⟨e0⟩ := hS
  have hpq : p = q.p := by simpa using hch.symm
  subst hpq
  set K := GaloisField q.p q.exponent
  have hK : Nat.card K = q.p ^ q.exponent := GaloisField.card _ _ q.exponent_pos.ne'
  have hK' : Nat.card K = q.card := by rw [hK, TauCeti.PrimePower.card_def]
  obtain ⟨b⟩ := (CFSG.TauCetiBridge.Even.chevalleyBridgesAll).g2 q hv K hK'
  let e : S ≃* adjointGroup .G2 K :=
    e0.trans (b.symm.trans ((QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans
      QuotientGroup.quotientBot))
  have hchar : CharP K ReeTag.G2.prime := by
    have : CharP K q.p := inferInstance
    rw [show ReeTag.G2.prime = 3 from rfl, ← hp3]
    exact this
  have hK3 : Nat.card K = 3 ^ q.exponent := by rw [hK, hp3]
  obtain ⟨-, -, ⟨Θ, -, -, hker⟩, -⟩ := G2_three_exact_automorphism_normal_form q.exponent_pos K hK3
  have : NeZero (2 * q.exponent) := ⟨by have := q.exponent_pos; omega⟩
  have : IsCyclic (Multiplicative (ZMod (2 * q.exponent))) := inferInstance
  exact exists_inner_of_cyclic_quotient (A := Multiplicative (ZMod (2 * q.exponent)))
    e Θ hker hp D hD.2 (by rw [hcard]; exact lt_pow_two_of_prime hp)

end F4G2

section Twisted

open CFSG.Open CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem i196_outerTwoThreeFamTrialityD4 : i196_OuterTwoThreeFam .trialityD4 := by
  intro S _ _ _ _ idx hidx _ hS p hp hp3 hch D hD hcard
  have hp2 : p ≠ 2 := by omega
  have hlt : p < Nat.card D := by rw [hcard]; exact lt_pow_two_of_prime hp
  obtain ⟨q, hr⟩ := hidx
  obtain ⟨d, hv⟩ := idx
  simp only at hr
  subst hr
  obtain ⟨e0⟩ := hS
  have hpq : p = q.p := by simpa using hch.symm
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  let K := GaloisField q.p (3 * q.exponent)
  have hf : 1 ≤ q.exponent := q.exponent_pos
  have hKc : Nat.card K = (q.p ^ q.exponent) ^ TwistTag.D4.order := by
    change Nat.card (GaloisField q.p (3 * q.exponent)) = _
    rw [GaloisField.card _ _ (by have := q.exponent_pos; omega)]
    change _ = (q.p ^ q.exponent) ^ 3
    rw [← pow_mul, mul_comm]
  obtain ⟨σ, hσ, -⟩ := finite_graph_field_parameter_fields TwistTag.D4 q.prime_p hf K hKc
  subst hpq
  have hK3 : Nat.card K = (q.p ^ q.exponent) ^ 3 := hKc
  obtain ⟨-, -, ⟨Θ, -, -, hΘker, -⟩, hcyc, -, -, -, ⟨eC⟩⟩ :=
    odd_triality_exact_automorphism_normal_form q.prime_p hp2 hf K hK3 σ hσ
  have hqc : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
  obtain ⟨eB⟩ := CFSG.TauCetiBridge.Even.chevalleyBridgesAll.trialityD4 q hv K
    (by rw [hqc]; exact hK3) σ.toRingHom (fun x => by rw [hqc]; exact hσ x)
  have e : S ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    e0.trans (eB.symm.trans eC)
  exact exists_inner_transport_lt e D (fun a ha => hD.2 a ha) hlt
    (fun D' hexp hc => exists_inner_of_cyclic_hom Θ hp
      (fun x hx _ => by
        have : x ∈ Θ.ker := hx
        rw [hΘker] at this
        exact this)
      D' hexp hc)

theorem i196_outerTwoThreeFamTwistedE6 : i196_OuterTwoThreeFam .twistedE6 := by
  intro S _ _ _ _ idx hidx _ hS p hp hp3 hch D hD hcard
  have hp2 : p ≠ 2 := by omega
  have hlt : p < Nat.card D := by rw [hcard]; exact lt_pow_two_of_prime hp
  obtain ⟨q, hr⟩ := hidx
  obtain ⟨d, hv⟩ := idx
  simp only at hr
  subst hr
  obtain ⟨e0⟩ := hS
  have hpq : p = q.p := by simpa using hch.symm
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  let K := GaloisField q.p (2 * q.exponent)
  have hf : 1 ≤ q.exponent := q.exponent_pos
  have hKc : Nat.card K = (q.p ^ q.exponent) ^ TwistTag.E6.order := by
    change Nat.card (GaloisField q.p (2 * q.exponent)) = _
    rw [GaloisField.card _ _ (by have := q.exponent_pos; omega)]
    change _ = (q.p ^ q.exponent) ^ 2
    rw [← pow_mul, mul_comm]
  obtain ⟨σ, hσ, -⟩ := finite_graph_field_parameter_fields TwistTag.E6 q.prime_p hf K hKc
  subst hpq
  have hK2 : Nat.card K = (q.p ^ q.exponent) ^ 2 := hKc
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, -, -, hΘker, -, -, -⟩, -, -, -, ⟨eC⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form q.prime_p hf K hK2 σ hσ
  have hqc : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
  obtain ⟨eB⟩ := CFSG.TauCetiBridge.Even.chevalleyBridgesAll.twistedE6 q hv K
    (by rw [hqc]; exact hK2) σ.toRingHom (fun x => by rw [hqc]; exact hσ x)
  have e : S ≃* graphFixedRootGroup TwistTag.E6 K σ.toRingHom :=
    e0.trans (eB.symm.trans eC)
  have hcyc : IsCyclic (K ≃+* K) :=
    CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic K
  have hpK : ¬ q.p ∣ Nat.card K - 1 := by
    intro h
    have h1 : q.p ∣ Nat.card K := by
      rw [hK2]; exact dvd_pow (dvd_pow_self _ q.exponent_pos.ne') (by norm_num)
    have hpos : 1 ≤ Nat.card K := Nat.card_pos
    have h2 := (Nat.dvd_add_right h).1 (by rwa [Nat.sub_add_cancel hpos])
    exact hp.one_lt.ne' (Nat.dvd_one.1 h2)
  exact exists_inner_transport_lt e D (fun a ha => hD.2 a ha) hlt
    (fun D' hexp hc => exists_inner_of_cyclic_hom Θ hp
      (fun x hx hxp => by
        have : x ∈ Θ.ker := hx
        rw [hΘker] at this
        exact mem_inner_of_mem_inn_sup_diag_E6 σ hp hpK this hxp)
      D' hexp hc)

end Twisted

section Ree

open CFSG.Open CFSG.Blueprint
open CFSG.LieType.Ree (ReeTag)
open CFSG.ComponentClassification.LiteratureLocal.SmallRee (frobeniusΓ
  exists_eq_conj_mul_frobeniusΓ_pow)

theorem i196_outerTwoThreeFamReeG2 : i196_OuterTwoThreeFam .reeG2 := by
  intro S _ _ _ _ idx hidx _ hS p hp hp3 hch D hD hcard
  have hlt : p < Nat.card D := by rw [hcard]; exact lt_pow_two_of_prime hp
  obtain ⟨d, hv⟩ := idx
  obtain ⟨m, rfl⟩ := hidx
  obtain ⟨e0⟩ := hS
  have hm1 : 1 ≤ m :=
    (TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK : Nat.card (GaloisField 3 (2 * m + 1)) = 3 ^ (2 * m + 1) :=
    GaloisField.card 3 (2 * m + 1) (by omega)
  have : CharP (GaloisField 3 (2 * m + 1)) ReeTag.G2.prime :=
    (inferInstance : CharP (GaloisField 3 (2 * m + 1)) 3)
  obtain ⟨b⟩ := CFSG.TauCetiBridge.reeG2Bridge m hv (GaloisField 3 (2 * m + 1)) hK
  have e1 : DerivedCentralQuotient (reeFixedGroup .G2 (GaloisField 3 (2 * m + 1)) reeG2Perm
      fun i => if i ∈ reeG2Long then 3 ^ m else 3 ^ (m + 1)) ≃*
        DerivedCentralQuotient (ReeTag.G2.reeGamma (GaloisField 3 (2 * m + 1)) m) := by
    rw [ReeTag.reeGamma_eq_reeFixedGroup]
    exact MulEquiv.refl _
  obtain ⟨E⟩ := ReeTag.nonempty_derivedCentralQuotient_mulEquiv_reeGamma_G2
    (K := GaloisField 3 (2 * m + 1)) hm1 hK
  let e : S ≃* ReeTag.G2.reeGamma (GaloisField 3 (2 * m + 1)) m :=
    ((e0.trans b.symm).trans e1).trans E
  exact exists_inner_transport_lt e D (fun a ha => hD.2 a ha) hlt
    (fun D' hexp hc => exists_inner_of_elemAbelian_of_outerCyclic
      (frobeniusΓ : MulAut (ReeTag.G2.reeGamma (GaloisField 3 (2 * m + 1)) m))
      (exists_eq_conj_mul_frobeniusΓ_pow hm1 hK) hp D' hexp hc)

end Ree

theorem defCharOuterRankTwoThreeNonD4_proved : DefCharOuterRankTwoThreeNonD4 := by
  intro S _ _ hS hnab idx hnD4 hidx hch D hD hcard
  have hne : idx.1.characteristic ≠ 2 := by rw [hch]; norm_num
  obtain ⟨k, hk⟩ := exists_family_of_characteristic_ne_two idx.1 hne
  have key : ∀ {k : DefCharFamily}, i196_OuterTwoThreeFam k → k.Matches idx.1 →
      ∃ x ∈ D ⊓ innerAut S, x ≠ 1 := fun h hk =>
    h S hS hnab idx hk hnD4 hidx 3 Nat.prime_three rfl hch D hD hcard
  cases k with
  | A => exact key i196_outerTwoThreeFamA hk
  | twistedA => exact key i196_outerTwoThreeFamTwistedA hk
  | B => exact key i196_outerTwoThreeFamB hk
  | C => exact key i196_outerTwoThreeFamC hk
  | D => exact key i196_outerTwoThreeFamD hk
  | twistedD => exact key i196_outerTwoThreeFamTwistedD hk
  | E6 => exact key i196_outerTwoThreeFamE6 hk
  | E7 => exact key i196_outerTwoThreeFamE7 hk
  | E8 => exact key i196_outerTwoThreeFamE8 hk
  | F4 => exact key i196_outerTwoThreeFamF4 hk
  | G2 => exact key i196_outerTwoThreeFamG2 hk
  | twistedE6 => exact key i196_outerTwoThreeFamTwistedE6 hk
  | trialityD4 => exact key i196_outerTwoThreeFamTrialityD4 hk
  | reeG2 => exact key i196_outerTwoThreeFamReeG2 hk

end Families

end CFSG.HardMathSupport.Solomon.Coordinator
