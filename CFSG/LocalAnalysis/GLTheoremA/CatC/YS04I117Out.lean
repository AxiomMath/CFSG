module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS04I117Defs
public import CFSG.LocalAnalysis.GLTheoremA.PartI.KDOut.Orth
public import CFSG.LocalAnalysis.ComponentClassification.GSFMMaximal
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeSteps
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3A75Defs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3FGDefs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3FGFourDefs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3OQOrth
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3Props
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitFrontier46
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitKGFieldClass
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLit39b
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCriticalStandard
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFourPresentation
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.Open.GorensteinHaradaSectionalRankFourMilestoneDefs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinearFiltration
open CFSG.ComponentClassification.HarrisLit.T1.F3FG
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
open CFSG.HardMathSupport.Timmesfeld.DFour
open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.ComponentClassification.PerfectAutomorphisms
open CFSG.ComponentClassification.OuterAutomorphisms (centerQuotient_conj)
open scoped commutatorElement
local notation "Inn" => CFSG.ComponentClassification.OuterAutomorphisms.inner

section Abstract
variable {G : Type*} [Group G] [Finite G]
theorem conj_mem_of_index_le_three {H : Subgroup G} (hH : H.index ≤ 3) {p : G} (hp : p ∈ H) {k : ℕ}
    (hk : p ^ (3 ^ k) = 1) (g : G) : g⁻¹ * p * g ∈ H := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hpg : IsPGroup 3 (Subgroup.zpowers p) :=
    IsPGroup.of_card_dvd_pow (n := k) (by rw [Nat.card_zpowers]; exact orderOf_dvd_of_pow_eq_one hk)
  have hmod := hpg.card_modEq_card_fixedPoints (G ⧸ H)
  have hcard : Nat.card (G ⧸ H) = H.index := (Subgroup.index_eq_card H).symm
  have hbase : (↑(1 : G) : G ⧸ H) ∈ MulAction.fixedPoints (Subgroup.zpowers p) (G ⧸ H) := by
    rintro ⟨q, hq⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hq
    change ((p ^ n * 1 : G) : G ⧸ H) = ((1 : G) : G ⧸ H)
    rw [QuotientGroup.eq]
    simpa using H.inv_mem (H.zpow_mem hp n)
  have hle : Nat.card (MulAction.fixedPoints (Subgroup.zpowers p) (G ⧸ H)) ≤ Nat.card (G ⧸ H) :=
    Nat.card_le_card_of_injective (fun x => x.1) Subtype.val_injective
  have hpos : 1 ≤ Nat.card (MulAction.fixedPoints (Subgroup.zpowers p) (G ⧸ H)) :=
    Nat.card_pos_iff.2 ⟨⟨⟨_, hbase⟩⟩, inferInstance⟩
  have heq : Nat.card (MulAction.fixedPoints (Subgroup.zpowers p) (G ⧸ H)) = Nat.card (G ⧸ H) := by
    rw [hcard] at hle hmod ⊢
    have h3 : H.index ≤ 3 := hH
    unfold Nat.ModEq at hmod
    interval_cases hi : H.index <;> omega
  have hS : (MulAction.fixedPoints (Subgroup.zpowers p) (G ⧸ H) : Set (G ⧸ H)) = Set.univ := by
    apply Set.eq_of_subset_of_ncard_le (Set.subset_univ _)
    rw [Set.ncard_univ, ← Nat.card_coe_set_eq]
    exact heq.ge
  have hfix : (⟨p, Subgroup.mem_zpowers p⟩ : Subgroup.zpowers p) • (g : G ⧸ H) = (g : G ⧸ H) := by
    have : (g : G ⧸ H) ∈ (MulAction.fixedPoints (Subgroup.zpowers p) (G ⧸ H) : Set (G ⧸ H)) := by
      rw [hS]; trivial
    exact this ⟨p, Subgroup.mem_zpowers p⟩
  have h1 : (((p * g : G)) : G ⧸ H) = (g : G ⧸ H) := hfix
  have h2 := QuotientGroup.eq.1 h1
  have h3 : g⁻¹ * p * g = ((p * g)⁻¹ * g)⁻¹ := by group
  rw [h3]
  exact H.inv_mem h2

end Abstract

theorem conj_mem_map_of_normal {A B : Type*} [Group A] [Group B] (κ : A →* B) (H : Subgroup A)
    [H.Normal] (g : A) {y : B} (hy : y ∈ H.map κ) : κ g * y * (κ g)⁻¹ ∈ H.map κ := by
  obtain ⟨h, hh, rfl⟩ := hy
  exact ⟨g * h * g⁻¹, ‹H.Normal›.conj_mem h hh g, by simp⟩

variable {K : Type} [Field K] [Finite K] {d : ℕ} (Q : QuadraticForm K (Fin d → K))


theorem layers_conj {e : MulAut (matrixProjectiveDerived Q)} (he : e ∈ matrixProjectiveImage Q) :
    (∀ y ∈ (specialIsometries Q).map (isometryConjugationHom Q),
      e * y * e⁻¹ ∈ (specialIsometries Q).map (isometryConjugationHom Q)) ∧
    (∀ y ∈ (isometryConjugationHom Q).range, e * y * e⁻¹ ∈ (isometryConjugationHom Q).range) ∧
    (∀ y ∈ (linearConjugationHom Q).range, e * y * e⁻¹ ∈ (linearConjugationHom Q).range) := by
  obtain ⟨g, rfl⟩ := (mem_matrixProjectiveImage_iff Q e).1 he
  have h1 : (specialIsometries Q).map (isometryConjugationHom Q) =
      ((specialIsometries Q).map (matrixIsometryInclusion Q)).map
        (matrixProjectiveConjugationHom Q) := by
    rw [Subgroup.map_map]
    rfl
  have h2 : (isometryConjugationHom Q).range =
      (matrixIsometryPairs Q).map (matrixProjectiveConjugationHom Q) := by
    rw [isometryConjugationHom, MonoidHom.range_comp]
    rfl
  have h3 : (linearConjugationHom Q).range =
      (linearSimilarityPairs Q).map (matrixProjectiveConjugationHom Q) := by
    rw [linearConjugationHom, MonoidHom.range_comp, Subgroup.range_subtype]
  haveI := specialPairs_normal Q
  haveI := matrixIsometryPairs_normal Q
  refine ⟨fun y hy => ?_, fun y hy => ?_, fun y hy => ?_⟩
  · rw [h1] at hy ⊢
    exact conj_mem_map_of_normal (matrixProjectiveConjugationHom Q) _ g hy
  · rw [h2] at hy ⊢
    exact conj_mem_map_of_normal (matrixProjectiveConjugationHom Q) _ g hy
  · rw [h3] at hy ⊢
    exact conj_mem_map_of_normal (matrixProjectiveConjugationHom Q) _ g hy

theorem comm_mem_linearRange {e₁ e₂ : MulAut (matrixProjectiveDerived Q)}
    (h₁ : e₁ ∈ matrixProjectiveImage Q) (h₂ : e₂ ∈ matrixProjectiveImage Q) :
    ⁅e₁, e₂⁆ ∈ (linearConjugationHom Q).range := by
  obtain ⟨g, hgE, hg⟩ := exists_gen_image Q
  haveI := linearRange_normal Q
  set D' := (linearConjugationHom Q).range.subgroupOf (matrixProjectiveImage Q) with hD'
  have hcyc : IsCyclic (↥(matrixProjectiveImage Q) ⧸ D') := by
    refine ⟨⟨QuotientGroup.mk ⟨g, hgE⟩, fun y => ?_⟩⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨k, hk⟩ := hg x x.2
    refine ⟨-k, ?_⟩
    change (QuotientGroup.mk (⟨g, hgE⟩ : ↥(matrixProjectiveImage Q)) :
      ↥(matrixProjectiveImage Q) ⧸ D') ^ (-k) = QuotientGroup.mk x
    rw [← QuotientGroup.mk_zpow, QuotientGroup.eq, Subgroup.mem_subgroupOf, _root_.zpow_neg,
      inv_inv, Subgroup.coe_mul, Subgroup.coe_zpow]
    exact hk
  let a : ↥(matrixProjectiveImage Q) := ⟨e₁, h₁⟩
  let b : ↥(matrixProjectiveImage Q) := ⟨e₂, h₂⟩
  have hcomm : Commute (QuotientGroup.mk a : ↥(matrixProjectiveImage Q) ⧸ D')
      (QuotientGroup.mk b) := (IsCyclic.commGroup (α := ↥(matrixProjectiveImage Q) ⧸ D')).mul_comm _ _
  have h1 : (QuotientGroup.mk' D' ⁅a, b⁆ : ↥(matrixProjectiveImage Q) ⧸ D') = 1 := by
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_commute.2 hcomm
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hD', Subgroup.mem_subgroupOf] at h1
  exact h1

theorem le_inner_of_commutator_eq_self
    (hnd : (QuadraticMap.polarBilin Q).Nondegenerate) (hQ : ∃ v, Q v ≠ 0)
    (hab : Nat.card (Abelianization (matrixIsometries Q)) ≤ 4)
    (hneg : ∃ A : matrixIsometries Q, isometryDet Q A ≠ 1)
    (hidx : (matrixProjectiveImage Q).index ≤ 3)
    {P T : Subgroup (MulAut (matrixProjectiveDerived Q))}
    (hP3 : ∀ p ∈ P, ∃ k : ℕ, p ^ (3 ^ k) = 1) (hPE : P ≤ matrixProjectiveImage Q)
    (hTP : (⁅T, P⁆ : Subgroup (MulAut (matrixProjectiveDerived Q))) = T) :
    T ≤ Inn (matrixProjectiveDerived Q) := by
  haveI : Finite (MulAut (matrixProjectiveDerived Q)) := inferInstance
  have hNK : Inn (matrixProjectiveDerived Q) ≤
      (specialIsometries Q).map (isometryConjugationHom Q) := by
    rw [inner_eq_map_commutator Q]
    exact Subgroup.map_mono (Abelianization.commutator_subset_ker (isometryDet Q))
  have hKO : (specialIsometries Q).map (isometryConjugationHom Q) ≤
      (isometryConjugationHom Q).range := Subgroup.map_le_range _ _
  have hOD : (isometryConjugationHom Q).range ≤ (linearConjugationHom Q).range :=
    isometryConjugationHom_range_le Q
  have hDE := linearRange_le_image Q
  have h1 := relIndex_inner_specialRange_le_two Q hab hneg
  have h2 := relIndex_specialRange_isometryRange_le_two Q hnd
  have h3 := relIndex_isometryRange_linearRange_le_two Q hQ
  have hTE : T ≤ matrixProjectiveImage Q := by
    rw [← hTP, Subgroup.commutator_le]
    intro t _ p hp
    obtain ⟨k, hk⟩ := hP3 p hp
    have := conj_mem_of_index_le_three hidx (hPE hp) hk t⁻¹
    rw [inv_inv] at this
    rw [commutatorElement_def]
    exact (matrixProjectiveImage Q).mul_mem this ((matrixProjectiveImage Q).inv_mem (hPE hp))
  have hTD : T ≤ (linearConjugationHom Q).range := by
    rw [← hTP, Subgroup.commutator_le]
    intro t ht p hp
    exact comm_mem_linearRange Q (hTE ht) (hPE hp)
  rw [← hTP, Subgroup.commutator_le]
  intro t ht p hp
  obtain ⟨k, hk⟩ := hP3 p hp
  have hc := commutator_mem_of_chain_three (N := Inn (matrixProjectiveDerived Q)) hNK hKO hOD
    (fun o ho k' hk' => (layers_conj Q (hDE (hOD ho))).1 k' hk')
    (fun d hd o ho => (layers_conj Q (hDE hd)).2.1 o ho) h1 h2 h3 hk
    (fun x hx => (layers_conj Q (hPE hp)).1 x hx) (fun x hx => (layers_conj Q (hPE hp)).2.1 x hx)
    (fun x hx => (layers_conj Q (hPE hp)).2.2 x hx) (hTD ht)
  have hinv : ⁅t, p⁆ = (p * t * p⁻¹ * t⁻¹)⁻¹ := by
    rw [commutatorElement_def]
    group
  rw [hinv]
  exact (Inn (matrixProjectiveDerived Q)).inv_mem hc


theorem d4Facts {K : Type} [Field K] [Finite K] {r f : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hf : 1 ≤ f) (hK : Nat.card K = r ^ f) :
    (QuadraticMap.polarBilin (coordinateQuadPlus 4 K)).Nondegenerate ∧
      (∃ v, coordinateQuadPlus 4 K v ≠ 0) ∧
      Nat.card (Abelianization (matrixIsometries (coordinateQuadPlus 4 K))) ≤ 4 ∧
      (∃ A : matrixIsometries (coordinateQuadPlus 4 K), isometryDet (coordinateQuadPlus 4 K) A ≠ 1) ∧
      (matrixProjectiveImage (coordinateQuadPlus 4 K)).index ≤ 3 := by
  let e : D4Model K ≃* StatedProj (StatedOmega (StatedQuadPlus 4 K)) :=
    (statedProjectiveReindexEquiv (plusIndexEquiv 4) (quadPlus 4 K) (coe_quadPlus 4 K)).symm
  have hm : StatedClassicalModel (D4Model K) .POmegaPlus 4 r f :=
    ⟨⟨hr, hf, le_refl 4⟩, K, inferInstance, inferInstance, hK, ⟨e⟩⟩
  obtain ⟨hchar, hnd, hT, -⟩ := coordinate_model_witness_plus hm K hK e
  have h2 : ringChar K ≠ 2 := by rw [hchar]; exact hr2
  obtain ⟨hQ0, -, hidx⟩ := coordinate_facts_four hm K hK e
  have hab := orthogonal_model_isometry_abelianization_order_bound (D4Model K) .POmegaPlus
    (.inr (.inl rfl)) 4 r f hm K hK (quadPlus 4 K) (coe_quadPlus 4 K) e
  have hab' := CFSG.RankThree.Automorphisms.card_abelianization_le_four_of_bound
    (plusIndexEquiv 4) (quadPlus 4 K) hab
  have hneg := exists_isometryDet_ne_one_of_swap (coordinateQuadPlus 4 K) h2
    (a := plusIndexEquiv 4 (.inl ⟨0, by omega⟩)) (b := plusIndexEquiv 4 (.inr ⟨0, by omega⟩))
    (by simp) (coordinateQuadPlus_comp_swap 4 K _)
  exact ⟨hnd, CFSG.RankThree.PartOne.KCOrthComm.exists_ne_zero_of_nondegenerate hnd hT, hab', hneg,
    hidx⟩


section Final

variable {G : Type} [Group G]

theorem inducesInnerMod_of_inner' {p : ℕ} {J : Subgroup G} [Group.IsPerfect (PQuot p J)] {g : G}
    (hg : g ∈ Subgroup.normalizer (J : Set G))
    (h : centerQuotientHom (PQuot p J) (barAut p J ⟨g⁻¹, Subgroup.inv_mem _ hg⟩) ∈
      Inn (PSimple p J)) : InducesInnerMod p J g := by
  obtain ⟨m, hm⟩ := h
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center (PQuot p J)) m
  have hu : barAut p J ⟨g⁻¹, Subgroup.inv_mem _ hg⟩ = MulAut.conj u :=
    (centerQuotientHom_injective (PQuot p J)) (hm.symm.trans (centerQuotient_conj u).symm)
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective u
  set γ : ↥(Subgroup.normalizer (J : Set G)) := ⟨g⁻¹, Subgroup.inv_mem _ hg⟩ with hγ
  refine ⟨((w : ↥J) : G)⁻¹, J.inv_mem w.2, fun y hy => ?_⟩
  have hs : ∀ y : ↥J, ((J.normalizerMonoidHom γ y : ↥J) : G) = g⁻¹ * y * g := fun y => by
    change (g⁻¹ : G) * y * (g⁻¹)⁻¹ = _
    rw [inv_inv]
  have h1 : barAut p J γ (QuotientGroup.mk ⟨y, hy⟩) =
      QuotientGroup.mk (w * ⟨y, hy⟩ * w⁻¹) := by
    rw [hu, MulAut.conj_apply]
    rfl
  rw [barAut_mk] at h1
  have h2 : (((w * ⟨y, hy⟩ * w⁻¹)⁻¹ * J.normalizerMonoidHom γ ⟨y, hy⟩ : ↥J) : G) ∈
      GLAPPrimeCoreOf p J :=
    Subgroup.mem_map_of_mem J.subtype (QuotientGroup.eq.1 h1.symm)
  have h3 : (((w * ⟨y, hy⟩ * w⁻¹)⁻¹ * J.normalizerMonoidHom γ ⟨y, hy⟩ : ↥J) : G) =
      (((w : G)⁻¹)⁻¹ * y * (w : G)⁻¹)⁻¹ * (g⁻¹ * y * g) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hs, inv_inv]
  rwa [h3] at h2

theorem i117D4UsedAt_of_noTriality [Finite G] (hN : NoTrialityOddAt G) : I117D4UsedAt G := by
  intro B x J S hB hx hJ hBJ hD hS hSC hSJ hBS hSB s hs
  have hq : CFSG.Open.IsQuasisimple (PQuot 3 J) :=
    isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hJ
  haveI : Group.IsPerfect (PQuot 3 J) := ⟨hq.1⟩
  have hSN : S ≤ Subgroup.normalizer (J : Set G) := hSJ
  set N : Subgroup G := Subgroup.normalizer (J : Set G) with hN'
  have hBnorm : B.subgroupOf N ≤ Subgroup.normalizer (S.subgroupOf N : Set ↥N) := by
    rw [Subgroup.le_normalizer_iff]
    intro b hb t ht
    exact (Subgroup.mem_normalizer_iff.1 (hBS (Subgroup.mem_subgroupOf.1 hb))
      (t : G)).1 (Subgroup.mem_subgroupOf.1 ht)
  have hSB' : (⁅S.subgroupOf N, B.subgroupOf N⁆ : Subgroup ↥N) = S.subgroupOf N := by
    apply Subgroup.map_injective N.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hSN,
      Subgroup.map_subgroupOf_eq_of_le hBJ]
    exact hSB
  obtain ⟨K, _, _, r, f, e, hr, hr2, hf, hK, hPE⟩ := hN B x J hB hx hJ hBJ hD
  obtain ⟨hnd, hQ, hab, hneg, hidx⟩ := d4Facts hr hr2 hf hK
  set T : Subgroup (MulAut (PSimple 3 J)) := (S.subgroupOf N).map (actHom 3 J) with hT
  set P : Subgroup (MulAut (PSimple 3 J)) := actImage 3 J B with hP
  have hTT : (⁅T, P⁆ : Subgroup (MulAut (PSimple 3 J))) = T := by
    rw [hT, hP, actImage, ← Subgroup.map_commutator, hSB']
  have hP3 : ∀ p ∈ P.map (MulAut.congr e).toMonoidHom, ∃ k : ℕ, p ^ (3 ^ k) = 1 := by
    rintro _ ⟨_, ⟨b, hb, rfl⟩, rfl⟩
    refine ⟨1, ?_⟩
    have hb3 : (b : G) ^ 3 = 1 := hB.1.2 _ (Subgroup.mem_subgroupOf.1 hb)
    have : b ^ 3 = 1 := Subtype.ext (by simpa using hb3)
    rw [pow_one, ← map_pow, ← map_pow, this, map_one, map_one]
  have hTinn : T.map (MulAut.congr e).toMonoidHom ≤ Inn (matrixProjectiveDerived (coordinateQuadPlus 4 K)) :=
    le_inner_of_commutator_eq_self (coordinateQuadPlus 4 K) hnd hQ hab hneg hidx hP3
      ((Subgroup.map_le_iff_le_comap).2 hPE)
      (by rw [← Subgroup.map_commutator, hTT])
  rw [← CFSG.ComponentClassification.OuterAutomorphisms.inner_map_congr e] at hTinn
  have hTI : T ≤ Inn (PSimple 3 J) :=
    (Subgroup.map_le_map_iff_of_injective (MulAut.congr e).injective).1 hTinn
  have hsN : s⁻¹ ∈ N := N.inv_mem (hSN hs)
  have hsT : actHom 3 J ⟨s⁻¹, hsN⟩ ∈ T :=
    ⟨⟨s⁻¹, hsN⟩, Subgroup.mem_subgroupOf.2 (S.inv_mem hs), rfl⟩
  exact inducesInnerMod_of_inner' (hSN hs) (hTI hsT)

end Final

end CFSG.LocalAnalysis.GLTheoremA
