module

public import CFSG.HardMathSupport.Timmesfeld.DefChar.Families
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalModelOuterTwoPart
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearFiltrationField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearFiltrationQuotient
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearFiltrationMultiplier
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelImage
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelIntrinsic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbitModel
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailModelFamily
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinBOdd
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinDOdd
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDOdd
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2Carrier
public import CFSG.RankThree.PartOne.AUTSL.SpTwoAut
public import CFSG.RankThree.PartOne.S11d.OutAbstract
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.Foundations
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.Universal.Spin.Roots
public import CFSG.LieType.Universal.SpinOmega
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoProjectiveFormulas
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.GLTheoremB.BarXTools
public import CFSG.LocalAnalysis.GLTheoremB.QuotientTools
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement
public import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials
public import TauCeti.LinearAlgebra.QuadraticForm.Prod

public section

namespace CFSG.HardMathSupport.Timmesfeld.DefChar

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


theorem exists_inner_of_tower {G : Type*} [Group G] [Finite G] {I D E X : Subgroup G}
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hDn : (D.subgroupOf E).Normal)
    (hidx : E.index ≤ 3) (g : G) (hgE : g ∈ E) (hg : ∀ e ∈ E, ∃ k : ℤ, g ^ k * e ∈ D)
    (hDI : ∀ δ ∈ D, δ ^ p = 1 → δ ∈ I) (hexp : ∀ x ∈ X, x ^ p = 1)
    (hcard : Nat.card X = p ^ 3) : ∃ x ∈ X ⊓ I, x ≠ 1 := by
  classical
  have hY : E.relIndex X ≤ 3 := by
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
    have h1 : p ^ 3 ≤ 3 * p := by
      rw [← hcard, ← hmul]
      exact Nat.mul_le_mul hY hle
    have : 3 * p < p ^ 3 := by
      have h9 : 9 ≤ p * p := by nlinarith
      calc 3 * p < p * p * p := by nlinarith
        _ = p ^ 3 := by ring
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
  have hdE : (d : G) ∈ E := d.2.1
  have hdX : (d : G) ∈ X := d.2.2
  have hdD : (d : G) ∈ D := by
    have h : α d = 1 := hdk
    change QuotientGroup.mk (Subgroup.inclusion hYX d) = (1 : E ⧸ D.subgroupOf E) at h
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h
    exact h
  have hdp : (d : G) ^ p = 1 := hexp _ hdX
  exact ⟨d, ⟨hdX, hDI _ hdD hdp⟩, fun h => hd1' (Subtype.ext h)⟩


theorem not_dvd_relIndex_inner_linearRange {K : Type} [Field K] [Finite K] {d : ℕ}
    (Q : QuadraticForm K (Fin d → K)) (hQ : ∃ v, Q v ≠ 0)
    (hab : ∃ m : ℕ, Nat.card (Abelianization (matrixIsometries Q)) = 2 ^ m) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ p ∣ (CFSG.ComponentClassification.OuterAutomorphisms.inner
      (matrixProjectiveDerived Q)).relIndex (linearConjugationHom Q).range := by
  have h1 : CFSG.ComponentClassification.OuterAutomorphisms.inner (matrixProjectiveDerived Q) ≤
      (isometryConjugationHom Q).range := by
    rw [inner_eq_map_commutator Q]
    exact Subgroup.map_le_range _ _
  have h2 : (isometryConjugationHom Q).range ≤ (linearConjugationHom Q).range :=
    isometryConjugationHom_range_le Q
  rw [← Subgroup.relIndex_mul_relIndex _ _ _ h1 h2]
  intro hdvd
  have hp2' : ¬ p ∣ 2 := fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h)
  rcases (Nat.Prime.dvd_mul hp).mp hdvd with h | h
  · obtain ⟨m, hm⟩ := hab
    have h3 := h.trans (relIndex_inner_dvd Q)
    rw [hm] at h3
    exact hp2' (hp.dvd_of_dvd_pow h3)
  · have h3 := h.trans (relIndex_isometryRange_dvd Q hQ)
    have hsq : (powMonoidHom 2 : Kˣ →* Kˣ).range.index = Nat.gcd (Nat.card K - 1) 2 := by
      rw [IsCyclic.index_powMonoidHom_range, Nat.card_units]
    rw [hsq] at h3
    exact hp2' (h3.trans (Nat.gcd_dvd_right _ _))

theorem exists_inner_of_matrixProjectiveDerived {K : Type} [Field K] [Finite K] {d : ℕ}
    (Q : QuadraticForm K (Fin d → K)) (hQ : Q ≠ 0)
    (hab : ∃ m : ℕ, Nat.card (Abelianization (matrixIsometries Q)) = 2 ^ m)
    (hidx : (matrixProjectiveImage Q).index ≤ 3) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (X : Subgroup (MulAut (matrixProjectiveDerived Q))) (hexp : ∀ x ∈ X, x ^ p = 1)
    (hcard : Nat.card X = p ^ 3) :
    ∃ x ∈ X ⊓ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (matrixProjectiveDerived Q), x ≠ 1 := by
  have hQv := exists_nonzero_value Q hQ
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
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
  refine exists_inner_of_tower (E := matrixProjectiveImage Q) hp hp3 hDn hidx
    (matrixProjectiveConjugationHom Q g₀) hgE ?_ hDI hexp hcard
  intro e he
  obtain ⟨h, rfl⟩ := (mem_matrixProjectiveImage_iff Q e).mp he
  obtain ⟨k, hk⟩ := hg₀ h
  refine ⟨k, ⟨⟨g₀ ^ k * h, hk⟩, ?_⟩⟩
  change matrixProjectiveConjugationHom Q (g₀ ^ k * h) = _
  rw [map_mul, map_zpow]
  rfl


@[expose] def MeetsInner (p : ℕ) (T : Type) [Group T] : Prop :=
  ∀ X : Subgroup (MulAut T), CFSG.Open.IsElemAbelian p X → Nat.card X = p ^ 3 →
    ∃ x ∈ X ⊓ Inn T, x ≠ 1

theorem MeetsInner.of_mulEquiv {p : ℕ} {T H : Type} [Group T] [Group H] (φ : T ≃* H)
    (h : MeetsInner p H) : MeetsInner p T := by
  intro X hX hcard
  have hcard' : Nat.card (X.map (MulAut.congr φ).toMonoidHom) = p ^ 3 := by
    rw [Subgroup.card_map_of_injective (MulAut.congr φ).injective]
    exact hcard
  obtain ⟨y, ⟨hyX, hyI⟩, hy1⟩ := h (X.map (MulAut.congr φ).toMonoidHom)
    ⟨by
      have := hX.1
      infer_instance, by
      rintro _ ⟨a, ha, rfl⟩
      change MulAut.congr φ a ^ p = 1
      rw [← map_pow, hX.2 a ha, map_one]⟩ hcard'
  obtain ⟨x, hxX, rfl⟩ := hyX
  rw [← CFSG.ComponentClassification.OuterAutomorphisms.inner_map_congr φ] at hyI
  obtain ⟨x', hx', hxx'⟩ := hyI
  have : x' = x := (MulAut.congr φ).injective hxx'
  subst this
  exact ⟨x', ⟨hxX, hx'⟩, fun h' => hy1 (by rw [h']; exact map_one _)⟩

theorem exists_two_pow_card_abelianization {K : Type} [Field K] [Finite K] {ℓ : ℕ} {ι : Type} [Fintype ι]
    [DecidableEq ι] {d : ℕ} (e : ι ≃ Fin d) (Q₀ : QuadraticForm K (ι → K))
    (hab : IsometryAbelianizationBound ℓ Q₀) :
    ∃ m : ℕ, Nat.card (Abelianization (matrixIsometries (reindexQuadraticForm e Q₀))) = 2 ^ m := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hab.1
  exact IsPGroup.iff_card.mp ((CFSG.IsElementaryAbelian.isPGroup 2 _).of_equiv
    (MulEquiv.abelianizationCongr (matrixIsometriesReindexEquiv e Q₀)).symm)

theorem meetsInner_POmegaOdd {T : Type} [Group T] [Finite T] {n ℓ f : ℕ}
    (hm : StatedClassicalModel T .POmegaOdd n ℓ f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    MeetsInner p T := by
  have h0 := hm
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h0
  have hab := orthogonal_model_isometry_abelianization_order_bound T .POmegaOdd (.inl rfl)
    n ℓ f hm K hK (quadOdd n K) (coe_quadOdd n K) e
  have hE : matrixProjectiveImage (coordinateQuadOdd n K) = ⊤ := by
    rw [← ((orthogonal_geometry_model_stabilizer_preserving_image T .POmegaOdd (.inl rfl) n ℓ
      f hm) K hK e).1]
    exact ((OrthogonalTail.orthogonal_geometry_tail_model_point_family_invariant T .POmegaOdd
      (.inl rfl) n ℓ f hm) K hK).2
  refine MeetsInner.of_mulEquiv (coordinateOddWitnessEquiv K e) fun X hX hcard => ?_
  exact exists_inner_of_matrixProjectiveDerived _ (coordinate_model_intrinsic_odd hm K hK e).1
    (exists_two_pow_card_abelianization (oddIndexEquiv n) (quadOdd n K) hab)
    (by rw [hE, Subgroup.index_top]; norm_num) hp hp2 X hX.2 hcard

theorem meetsInner_POmegaPlus {T : Type} [Group T] [Finite T] {n ℓ f : ℕ}
    (hm : StatedClassicalModel T .POmegaPlus n ℓ f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    MeetsInner p T := by
  have h0 := hm
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h0
  have hn : 4 ≤ n := hm.1.2.2
  have hab := orthogonal_model_isometry_abelianization_order_bound T .POmegaPlus
    (.inr (.inl rfl)) n ℓ f hm K hK (quadPlus n K) (coe_quadPlus n K) e
  have hEA := ((orthogonal_geometry_model_stabilizer_preserving_image T .POmegaPlus
    (.inr (.inl rfl)) n ℓ f hm) K hK e).1
  have horbit := orthogonal_geometry_plus_point_family_orbit hm hK e
  have hidx : (matrixProjectiveImage (coordinateQuadPlus n K)).index ≤ 3 := by
    rcases (show n = 4 ∨ 5 ≤ n by omega) with h4 | h5
    · have hst : (projectivePointFamilyAut (coordinateQuadPlus n K)).index =
          (MulAction.orbit (MulAut (matrixProjectiveDerived (coordinateQuadPlus n K)))
            (projectivePointFamily (coordinateQuadPlus n K))).ncard :=
        MulAction.index_stabilizer _ _
      rw [← hEA, hst]
      exact (horbit.2.2.2.2.2 h4).2
    · rw [← hEA, horbit.2.2.2.2.1 h5, Subgroup.index_top]
      norm_num
  refine MeetsInner.of_mulEquiv (coordinatePlusWitnessEquiv K e) fun X hX hcard => ?_
  exact exists_inner_of_matrixProjectiveDerived _ (coordinate_model_intrinsic_plus hm K hK e).1
    (exists_two_pow_card_abelianization (plusIndexEquiv n) (quadPlus n K) hab) hidx hp hp2 X hX.2
    hcard

theorem meetsInner_POmegaMinus {T : Type} [Group T] [Finite T] {n ℓ f : ℕ}
    (hm : StatedClassicalModel T .POmegaMinus n ℓ f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    MeetsInner p T := by
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
  refine MeetsInner.of_mulEquiv (coordinateMinusWitnessEquiv K hn1 b c e) fun X hX hcard => ?_
  exact exists_inner_of_matrixProjectiveDerived _
    (coordinate_model_intrinsic_minus hm K hK b c hirr e).1
    (exists_two_pow_card_abelianization (minusIndexEquiv n hn1) (quadMinus n K b c) hab)
    (by rw [hE, Subgroup.index_top]; norm_num) hp hp2 X hX.2 hcard


theorem meetsInner_of_outPChain {p : ℕ} (hp : p.Prime) {X : Type} [Group X] [Finite X]
    (h : OutPChain p X) : MeetsInner p X := by
  intro D hD hcard
  by_contra hno
  push Not at hno
  have hD1 : ∀ x ∈ D, x ∈ Inn X → x = 1 := fun x hx hI => hno x ⟨hx, hI⟩
  have hpD : ∀ x ∈ D, x ^ p ∈ Inn X := fun x hx => by
    rw [hD.2 x hx]
    exact (Inn X).one_mem
  have hcomm : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hD.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hfin : Finite D := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero 3 hp.ne_zero)
  have hnt : Nontrivial D := Finite.one_lt_card_iff_nontrivial.1 (by
    rw [hcard]
    exact Nat.one_lt_pow (by norm_num) hp.one_lt)
  obtain ⟨⟨a, haD⟩, ha1⟩ := exists_ne (1 : D)
  have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
  have hord : orderOf a = p := by
    have hdvd : orderOf a ∣ p := orderOf_dvd_of_pow_eq_one (hD.2 a haD)
    rcases (Nat.dvd_prime hp).1 hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) ha1'
    · exact h
  have hcz : ∀ x : MulAut X, x ≠ 1 → x ^ p = 1 → Nat.card (Subgroup.zpowers x) = p := by
    intro x hx1 hxp
    rw [Nat.card_zpowers]
    rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one hxp) with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hx1
    · exact h
  have hza : Nat.card (Subgroup.zpowers a) = p := hcz a ha1' (hD.2 a haD)
  obtain ⟨b, hbD, hba⟩ : ∃ b ∈ D, b ∉ Subgroup.zpowers a := by
    by_contra hall
    push Not at hall
    have hle : D ≤ Subgroup.zpowers a := fun x hx => hall x hx
    have := Subgroup.card_le_of_le hle
    rw [hcard, hza] at this
    have h2 : p < p ^ 3 := by
      calc p = p ^ 1 := (pow_one p).symm
        _ < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    omega
  rcases (OutPChain.comparable h (hcomm a haD b hbD) (k := 1) (l := 1) (by simpa using hpD a haD)
    (by simpa using hpD b hbD)) with ⟨m, hm⟩ | ⟨m, hm⟩
  ·
    have h1 : a * b ^ m = 1 :=
      hD1 _ (D.mul_mem haD (D.zpow_mem hbD m)) hm
    have hb1 : b ≠ 1 := fun hb => ha1' (by rw [hb, _root_.one_zpow, mul_one] at h1; exact h1)
    have hzb : Nat.card (Subgroup.zpowers b) = p := hcz b hb1 (hD.2 b hbD)
    have hab : a ∈ Subgroup.zpowers b := by
      have : a = (b ^ m)⁻¹ := eq_inv_of_mul_eq_one_left h1
      rw [this]
      exact (Subgroup.zpowers b).inv_mem (Subgroup.zpow_mem _ (Subgroup.mem_zpowers b) m)
    have hle : Subgroup.zpowers a ≤ Subgroup.zpowers b := by
      rw [Subgroup.zpowers_le]
      exact hab
    have heq : Subgroup.zpowers a = Subgroup.zpowers b :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hza, hzb])
    exact hba (heq ▸ Subgroup.mem_zpowers b)
  · have h1 : b * a ^ m = 1 :=
      hD1 _ (D.mul_mem hbD (D.zpow_mem haD m)) hm
    have : b = (a ^ m)⁻¹ := eq_inv_of_mul_eq_one_left h1
    exact hba (by
      rw [this]
      exact (Subgroup.zpowers a).inv_mem (Subgroup.zpow_mem _ (Subgroup.mem_zpowers a) m))

theorem meetsInner_PSp_two {T : Type} [Group T] [Finite T] {ℓ f : ℕ} (hℓ : ℓ ≠ 2)
    (hm : StatedClassicalModel T .PSp 2 ℓ f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    MeetsInner p T :=
  meetsInner_of_outPChain hp
    (CFSG.RankThree.PartOne.AUTSL.SpTwo.outPNice_PSp_two_odd hp hp2 hℓ hm).toChain

open TauCeti in
theorem defCharOuterRankFamB : DefCharOuterRankFam .B := by
  intro S _ _ _ _ idx hidx hS p hp hp2 hch D hD hcard
  obtain ⟨r, q, hr⟩ := hidx
  obtain ⟨d, hv⟩ := idx
  simp only at hr hch
  subst hr
  obtain ⟨e⟩ := hS
  have hpq : p = q.p := by simpa using hch.symm
  have hqp2 : q.p ≠ 2 := hpq ▸ hp2
  have hr2 : 2 ≤ r := ((LieTypeIndex.inStandardRange_iff _).mp ((LieTypeIndex.valid_iff _).mp hv).1).1
  rcases Nat.eq_or_lt_of_le hr2 with h2 | h3
  · subst h2
    exact meetsInner_PSp_two hqp2 (CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e)
      hp hp2 D hD hcard
  · exact meetsInner_POmegaOdd (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_odd r q hv
      hqp2 h3 e) hp hp2 D hD hcard

open TauCeti in
theorem defCharOuterRankFamD : DefCharOuterRankFam .D := by
  intro S _ _ _ _ idx hidx hS p hp hp2 hch D hD hcard
  obtain ⟨r, q, hr⟩ := hidx
  obtain ⟨d, hv⟩ := idx
  simp only at hr
  subst hr
  obtain ⟨e⟩ := hS
  exact meetsInner_POmegaPlus (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD r q hv e)
    hp hp2 D hD hcard

open TauCeti in
theorem defCharOuterRankFamTwistedD : DefCharOuterRankFam .twistedD := by
  intro S _ _ _ _ idx hidx hS p hp hp2 hch D hD hcard
  obtain ⟨r, q, hr⟩ := hidx
  obtain ⟨d, hv⟩ := idx
  simp only at hr
  subst hr
  obtain ⟨e⟩ := hS
  exact meetsInner_POmegaMinus
    (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD r q hv e) hp hp2 D hD hcard

end CFSG.HardMathSupport.Timmesfeld.DefChar
