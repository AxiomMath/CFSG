module

public import CFSG.HardMathSupport.Timmesfeld.DefChar.OuterOrth
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.Tables112Lie
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.GH74.GLS.Classes
public import CFSG.GH74.Generic.Certificates
public import CFSG.GH74.Statements
public import CFSG.LieType.CurtisTits.Conclusion
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianIsometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.GL83PartI.I_22_5.Setup
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
public import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard

public section

namespace CFSG.HardMathSupport.Timmesfeld.DFour

open Subgroup

section Abstract

variable {G : Type*} [Group G] [Finite G]

theorem relIndex_le_three {E : Subgroup G} (hidx : E.index ≤ 3) (X : Subgroup G) :
    E.relIndex X ≤ 3 := by
  refine (Subgroup.relIndex_le_of_le_right le_top ?_).trans ?_
  · rw [Subgroup.relIndex_top_right]
    exact Subgroup.index_ne_zero_of_finite
  · rwa [Subgroup.relIndex_top_right]

theorem exists_inner_of_index_le_three {I D E X : Subgroup G} {p : ℕ} (hp3 : 3 ≤ p)
    (hidx : E.index ≤ 3) (hED : ∀ y ∈ E, y ^ p = 1 → y ∈ D)
    (hDI : ∀ δ ∈ D, δ ^ p = 1 → δ ∈ I) (hexp : ∀ x ∈ X, x ^ p = 1)
    (hcard : Nat.card X = p ^ 2) : ∃ x ∈ X ⊓ I, x ≠ 1 := by
  have hmul : E.relIndex X * Nat.card (E ⊓ X : Subgroup G) = Nat.card X :=
    Subgroup.relIndex_mul_card E X
  have hY := relIndex_le_three hidx X
  have h1 : 1 < Nat.card (E ⊓ X : Subgroup G) := by
    by_contra h
    push Not at h
    have h9 : 9 ≤ p ^ 2 := by nlinarith
    have h3 : Nat.card X ≤ 3 := by
      rw [← hmul]
      calc E.relIndex X * Nat.card (E ⊓ X : Subgroup G) ≤ 3 * 1 := Nat.mul_le_mul hY h
        _ = 3 := by norm_num
    omega
  have : Nontrivial (E ⊓ X : Subgroup G) := Finite.one_lt_card_iff_nontrivial.1 h1
  obtain ⟨⟨y, hy⟩, hy1⟩ := exists_ne (1 : (E ⊓ X : Subgroup G))
  obtain ⟨hyE, hyX⟩ := Subgroup.mem_inf.mp hy
  have hy1' : y ≠ 1 := fun h => hy1 (Subtype.ext h)
  have hyp := hexp y hyX
  exact ⟨y, Subgroup.mem_inf.mpr ⟨hyX, hDI y (hED y hyE hyp) hyp⟩, hy1'⟩

theorem card_le_of_tower {I D E X : Subgroup G} {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p)
    (hDn : (D.subgroupOf E).Normal) (hidx : E.index ≤ 3) (g : G) (hgE : g ∈ E)
    (hg : ∀ e ∈ E, ∃ k : ℤ, g ^ k * e ∈ D) (hDI : ∀ δ ∈ D, δ ^ p = 1 → δ ∈ I)
    (hexp : ∀ x ∈ X, x ^ p = 1) :
    Nat.card (E ⊓ X : Subgroup G) ≤ p * Nat.card (X ⊓ I : Subgroup G) ∧
      Nat.card X ≤ p * p * Nat.card (X ⊓ I : Subgroup G) := by
  classical
  have hY := relIndex_le_three hidx X
  have hmul : E.relIndex X * Nat.card (E ⊓ X : Subgroup G) = Nat.card X :=
    Subgroup.relIndex_mul_card E X
  have hYX : E ⊓ X ≤ E := inf_le_left
  have hcyc : IsCyclic (E ⧸ D.subgroupOf E) := by
    refine ⟨⟨QuotientGroup.mk ⟨g, hgE⟩, fun y => ?_⟩⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨k, hk⟩ := hg x x.2
    refine ⟨-k, ?_⟩
    change (QuotientGroup.mk (⟨g, hgE⟩ : E) : E ⧸ D.subgroupOf E) ^ (-k) = QuotientGroup.mk x
    rw [← QuotientGroup.mk_zpow, QuotientGroup.eq, Subgroup.mem_subgroupOf, _root_.zpow_neg,
      inv_inv, Subgroup.coe_mul, Subgroup.coe_zpow]
    exact hk
  let α : (E ⊓ X : Subgroup G) →* E ⧸ D.subgroupOf E :=
    (QuotientGroup.mk' (D.subgroupOf E)).comp (Subgroup.inclusion hYX)
  have hexpα : Monoid.exponent α.range ∣ p := by
    refine Monoid.exponent_dvd_of_forall_pow_eq_one fun y => ?_
    obtain ⟨x, rfl⟩ := α.rangeRestrict_surjective y
    have : (x : (E ⊓ X : Subgroup G)) ^ p = 1 :=
      Subtype.ext (hexp x (Subgroup.mem_inf.mp x.2).2)
    rw [← map_pow, this, map_one]
  have := hcyc
  have : IsCyclic α.range := inferInstance
  rw [IsCyclic.exponent_eq_card] at hexpα
  have hsplit : Nat.card (E ⊓ X : Subgroup G) = Nat.card α.range * Nat.card α.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup α.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange α).toEquiv]
  have hrle : Nat.card α.range ≤ p := Nat.le_of_dvd hp.pos hexpα
  have hker : Nat.card α.ker ≤ Nat.card (X ⊓ I : Subgroup G) := by
    have hmem : ∀ d : α.ker, ((d : (E ⊓ X : Subgroup G)) : G) ∈ X ⊓ I := by
      intro d
      have hdX : ((d : (E ⊓ X : Subgroup G)) : G) ∈ X := (Subgroup.mem_inf.mp d.1.2).2
      have hdD : ((d : (E ⊓ X : Subgroup G)) : G) ∈ D := by
        have h : α d = 1 := d.2
        change QuotientGroup.mk (Subgroup.inclusion hYX d) = (1 : E ⧸ D.subgroupOf E) at h
        rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h
        exact h
      exact Subgroup.mem_inf.mpr ⟨hdX, hDI _ hdD (hexp _ hdX)⟩
    refine Nat.card_le_card_of_injective (fun d => ⟨_, hmem d⟩) fun a b h => ?_
    have h' : ((a : (E ⊓ X : Subgroup G)) : G) = ((b : (E ⊓ X : Subgroup G)) : G) :=
      congrArg (fun z : (X ⊓ I : Subgroup G) => (z : G)) h
    exact Subtype.ext (Subtype.ext h')
  have hEX : Nat.card (E ⊓ X : Subgroup G) ≤ p * Nat.card (X ⊓ I : Subgroup G) := by
    rw [hsplit]
    exact Nat.mul_le_mul hrle hker
  refine ⟨hEX, ?_⟩
  rw [← hmul]
  calc E.relIndex X * Nat.card (E ⊓ X : Subgroup G)
      ≤ 3 * (p * Nat.card (X ⊓ I : Subgroup G)) := Nat.mul_le_mul hY hEX
    _ ≤ p * (p * Nat.card (X ⊓ I : Subgroup G)) := Nat.mul_le_mul_right _ hp3
    _ = p * p * Nat.card (X ⊓ I : Subgroup G) := by ring

end Abstract

section Coordinate

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinearFiltration
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
open scoped commutatorElement

local notation "Inn" => CFSG.ComponentClassification.OuterAutomorphisms.inner

variable {K : Type} [Field K] {d : ℕ} (Q : QuadraticForm K (Fin d → K))

theorem inner_le_linearRange :
    Inn (matrixProjectiveDerived Q) ≤ (linearConjugationHom Q).range := by
  have h1 : Inn (matrixProjectiveDerived Q) ≤ (isometryConjugationHom Q).range := by
    rw [inner_eq_map_commutator Q]
    exact Subgroup.map_le_range _ _
  exact h1.trans (isometryConjugationHom_range_le Q)

theorem linearRange_le_image : (linearConjugationHom Q).range ≤ matrixProjectiveImage Q := by
  rintro _ ⟨g, rfl⟩
  exact (mem_matrixProjectiveImage_iff Q _).mpr ⟨g.val, rfl⟩

variable [Finite K]

theorem linearRange_normal :
    ((linearConjugationHom Q).range.subgroupOf (matrixProjectiveImage Q)).Normal := by
  have hcomm : ∀ g h : similarityPairs Q,
      ⁅matrixProjectiveConjugationHom Q g, matrixProjectiveConjugationHom Q h⁆ ∈
        (linearConjugationHom Q).range := fun g h => by
    rw [← map_commutatorElement]
    exact ⟨⟨⁅g, h⁆, similarity_commutator_le_linear Q
      (Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top h))⟩, rfl⟩
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

theorem exists_gen_image :
    ∃ g ∈ matrixProjectiveImage Q, ∀ e ∈ matrixProjectiveImage Q,
      ∃ k : ℤ, g ^ k * e ∈ (linearConjugationHom Q).range := by
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
  refine ⟨matrixProjectiveConjugationHom Q g₀, (mem_matrixProjectiveImage_iff Q _).mpr
    ⟨g₀, rfl⟩, fun e he => ?_⟩
  obtain ⟨h, rfl⟩ := (mem_matrixProjectiveImage_iff Q e).mp he
  obtain ⟨k, hk⟩ := hg₀ h
  refine ⟨k, ⟨⟨g₀ ^ k * h, hk⟩, ?_⟩⟩
  change matrixProjectiveConjugationHom Q (g₀ ^ k * h) = _
  rw [map_mul, map_zpow]
  rfl

theorem mem_inner_of_mem_linearRange (hQ : ∃ v, Q v ≠ 0)
    (hab : ∃ m : ℕ, Nat.card (Abelianization (matrixIsometries Q)) = 2 ^ m) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {δ : MulAut (matrixProjectiveDerived Q)}
    (hδ : δ ∈ (linearConjugationHom Q).range) (hδp : δ ^ p = 1) :
    δ ∈ Inn (matrixProjectiveDerived Q) := by
  set D := (linearConjugationHom Q).range with hD
  set I := Inn (matrixProjectiveDerived Q) with hI
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
      (CFSG.HardMathSupport.Timmesfeld.DefChar.not_dvd_relIndex_inner_linearRange Q hQ hab hp
        hp2)
  have hx1 : orderOf x = 1 := Nat.eq_one_of_dvd_coprimes hcop hdvd1 hdvd2
  have : x = 1 := orderOf_eq_one_iff.mp hx1
  have hmem := (QuotientGroup.eq_one_iff (⟨δ, hδ⟩ : D)).mp this
  exact Subgroup.mem_subgroupOf.mp hmem

theorem mem_linearRange_of_pow_eq_one {r f p : ℕ} (hr : r.Prime) (hK : Nat.card K = r ^ f)
    (hpf : Nat.Coprime p f) {y : MulAut (matrixProjectiveDerived Q)}
    (hy : y ∈ matrixProjectiveImage Q) (hyp : y ^ p = 1) :
    y ∈ (linearConjugationHom Q).range := by
  obtain ⟨g, hg⟩ := (mem_matrixProjectiveImage_iff Q y).mp hy
  set σ := fieldProjection Q g with hσ
  have hcard : Nat.card (K ≃+* K) = f := (card_ringAut_and_isCyclic hr K hK).1
  have hcop : Nat.Coprime p (orderOf σ) :=
    Nat.Coprime.coprime_dvd_right (hcard ▸ orderOf_dvd_natCard σ) hpf
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  have hlin : g ^ (p * m) * g⁻¹ ∈ linearSimilarityPairs Q := by
    change fieldProjection Q (g ^ (p * m) * g⁻¹) = 1
    rw [map_mul, map_inv, map_pow, pow_mul, ← hσ, hm, mul_inv_cancel]
  have hκ : linearConjugationHom Q ⟨_, hlin⟩ = y⁻¹ := by
    change matrixProjectiveConjugationHom Q (g ^ (p * m) * g⁻¹) = y⁻¹
    rw [map_mul, map_inv, map_pow, pow_mul]
    change ((matrixProjectiveConjugation Q g) ^ p) ^ m * (matrixProjectiveConjugation Q g)⁻¹ =
      y⁻¹
    rw [hg, hyp, one_pow, one_mul]
  have : y⁻¹ ∈ (linearConjugationHom Q).range := ⟨_, hκ⟩
  simpa using this

theorem exists_inner_of_not_dvd (hQ : Q ≠ 0)
    (hab : ∃ m : ℕ, Nat.card (Abelianization (matrixIsometries Q)) = 2 ^ m)
    (hidx : (matrixProjectiveImage Q).index ≤ 3) {r f p : ℕ} (hr : r.Prime)
    (hK : Nat.card K = r ^ f) (hp : p.Prime) (hp2 : p ≠ 2) (hpf : ¬ p ∣ f)
    (X : Subgroup (MulAut (matrixProjectiveDerived Q))) (hexp : ∀ x ∈ X, x ^ p = 1)
    (hcard : Nat.card X = p ^ 2) :
    ∃ x ∈ X ⊓ Inn (matrixProjectiveDerived Q), x ≠ 1 := by
  have hQv := exists_nonzero_value Q hQ
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hcop : Nat.Coprime p f := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpf
  exact exists_inner_of_index_le_three hp3 hidx
    (fun y hy hyp => mem_linearRange_of_pow_eq_one Q hr hK hcop hy hyp)
    (fun δ hδ hδp => mem_inner_of_mem_linearRange Q hQv hab hp hp2 hδ hδp) hexp hcard

end Coordinate

section Model

open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedLieTag)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
  CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal
open scoped Pointwise
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit
  (orthogonal_geometry_plus_point_family_orbit)

local notation "Inn" => CFSG.ComponentClassification.OuterAutomorphisms.inner

theorem meets_of_mulEquiv {p k : ℕ} {T H : Type} [Group T] [Group H] (φ : T ≃* H)
    (h : ∀ X : Subgroup (MulAut H), CFSG.Open.IsElemAbelian p X → Nat.card X = p ^ k →
      ∃ x ∈ X ⊓ Inn H, x ≠ 1) :
    ∀ X : Subgroup (MulAut T), CFSG.Open.IsElemAbelian p X → Nat.card X = p ^ k →
      ∃ x ∈ X ⊓ Inn T, x ≠ 1 := by
  intro X hX hcard
  have hcard' : Nat.card (X.map (MulAut.congr φ).toMonoidHom) = p ^ k := by
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

theorem coordinate_facts_four {T : Type} [Group T] {r f : ℕ}
    (hm : StatedClassicalModel T .POmegaPlus 4 r f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = r ^ f)
    (e : T ≃* CFSG.Assembly.LowTwoRank.StatedProj
      (CFSG.Assembly.LowTwoRank.StatedOmega (CFSG.Assembly.LowTwoRank.StatedQuadPlus 4 K))) :
    coordinateQuadPlus 4 K ≠ 0 ∧
      (∃ m : ℕ, Nat.card (Abelianization (matrixIsometries (coordinateQuadPlus 4 K))) = 2 ^ m) ∧
      (matrixProjectiveImage (coordinateQuadPlus 4 K)).index ≤ 3 := by
  have hab := orthogonal_model_isometry_abelianization_order_bound T .POmegaPlus
    (.inr (.inl rfl)) 4 r f hm K hK (quadPlus 4 K) (coe_quadPlus 4 K) e
  have hEA := ((orthogonal_geometry_model_stabilizer_preserving_image T .POmegaPlus
    (.inr (.inl rfl)) 4 r f hm) K hK e).1
  have horbit := orthogonal_geometry_plus_point_family_orbit hm hK e
  have hidx : (matrixProjectiveImage (coordinateQuadPlus 4 K)).index ≤ 3 := by
    have hst : (projectivePointFamilyAut (coordinateQuadPlus 4 K)).index =
        (MulAction.orbit (MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)))
          (projectivePointFamily (coordinateQuadPlus 4 K))).ncard :=
      MulAction.index_stabilizer _ _
    rw [← hEA, hst]
    exact (horbit.2.2.2.2.2 rfl).2
  exact ⟨(coordinate_model_intrinsic_plus hm K hK e).1,
    CFSG.HardMathSupport.Timmesfeld.DefChar.exists_two_pow_card_abelianization (plusIndexEquiv 4)
      (quadPlus 4 K) hab, hidx⟩

theorem pRank_mulAut_le_of_not_dvd {T : Type} [Group T] [Finite T] {r f : ℕ}
    (hm : StatedClassicalModel T .POmegaPlus 4 r f) (hcen : Subgroup.center T = ⊥)
    (hf : ¬ 3 ∣ f) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut T)) ≤ CFSG.Open.pRank 3 (⊤ : Subgroup T) + 1 := by
  have h0 := hm
  obtain ⟨⟨hr, -, -⟩, K, _, _, hK, ⟨e⟩⟩ := h0
  obtain ⟨hQ, hab, hidx⟩ := coordinate_facts_four hm K hK e
  have hmeet := meets_of_mulEquiv (p := 3) (k := 2) (coordinatePlusWitnessEquiv K e)
    fun X hX hc => exists_inner_of_not_dvd _ hQ hab hidx hr hK Nat.prime_three (by norm_num) hf
      X hX.2 hc
  exact CFSG.HardMathSupport.Timmesfeld.Coordinator.pRank_mulAut_le_of_meets Nat.prime_three
    hcen 1 fun D hD hc => hmeet D hD (by simpa using hc)

end Model

end CFSG.HardMathSupport.Timmesfeld.DFour
