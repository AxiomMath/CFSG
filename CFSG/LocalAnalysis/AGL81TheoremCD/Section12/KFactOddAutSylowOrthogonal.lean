module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.KFactOddAutParabolicReduce
public import CFSG.Open.StatedDefs
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrOrth
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrR2PlusSyl
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEndFieldAut
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightTriality
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldOmegaOrder
import CFSG.RankThree.PartOne.AUTSL.OmegaOut
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrR2MinusA
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldOmegaConjLabels
public import CFSG.LocalAnalysis.AGLEmbedding.D1GlobalU
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrR2PlusAut
public import CFSG.LocalAnalysis.AGLEmbedding.Reduction
public import CFSG.LocalAnalysis.AGLEmbedding.TwoCoreObstruction
public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergOmegaMinus
import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcLevi
import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorEvenTriality
import CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupLinearThreeFour
import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
import CFSG.LocalAnalysis.SectionRank.TitsCover
import CFSG.LocalAnalysis.SeitzReduction.E6PilotHR4
import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviPerp
import CFSG.LocalAnalysis.SeitzReduction.E7PilotFieldNormalizeAutMain
import CFSG.LocalAnalysis.SeitzReduction.E8PilotQ2PositionWork
import CFSG.LocalAnalysis.SeitzReduction.E8PilotSwapLift
import CFSG.LocalAnalysis.SeitzReduction.EPilotEndGraphE6
import CFSG.LocalAnalysis.SeitzReduction.EPilotEndGraphTwistedXi
import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenClassical
import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenExc
import CFSG.LocalAnalysis.SeitzReduction.F4PilotEndField
import CFSG.LocalAnalysis.SeitzReduction.F4PilotFieldNeighbourFix
import CFSG.LocalAnalysis.SeitzReduction.F4PilotFieldNeighbourLift
import CFSG.LocalAnalysis.SeitzReduction.F4PilotInnerField
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotWeakCTGlobal
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotBLiftAniso
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCatCovers
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightAutMain
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotFiveMain
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusCoverHR8
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusCoverHR8Global
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotPlusFourF6
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotPlusFourGlobal
import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotUniqueTypeGraph
import CFSG.Quasithin.Background.A3Components
import CFSG.Quasithin.Background.A3ComponentsAmbient
import CFSG.Quasithin.Background.G11Stmts
import CFSG.RankThree.Chevalley.SteinbergCEF4EvenQPlusWeyl
import CFSG.RankThree.Chevalley.SteinbergCFEvenF4PointwiseInner

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

section OddAutOmegaPlus

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusBorel
  CFSG.AGLEmbedding.ParabAutIrr
  CFSG.RankThree.PartOne.AUTSL
  CFSG.StandardType.RecipeFieldOmega

private theorem congr_derivedProjEquiv_conjAct_pomegaPlus {K : Type} [Field K] [CharP K 2] {d : ℕ}
    (Q : QuadraticForm K (Fin d → K)) (hQ : ∃ v, Q v ≠ 0) (g : similarityPairs Q) :
    MulAut.congr (derivedProjEquiv Q hQ) (conjAct Q g) =
      matrixProjectiveConjugationHom Q g := by
  refine MulEquiv.ext fun x => ?_
  obtain ⟨A, rfl⟩ := matrixProjectiveProjection_surjective Q x
  rw [← derivedProjEquiv_apply Q hQ A]
  rw [congr_apply_apply', derivedProjEquiv_apply, conjAct_apply]
  exact matrixProjectiveConjugation_mk Q g A

private theorem matrixProjectiveImage_index_le_three_pomegaPlus {K : Type} [Field K] [Finite K]
    {n f : ℕ} (hK : Nat.card K = 2 ^ f) (hn4 : 4 ≤ n) :
    (matrixProjectiveImage (coordinateQuadPlus n K)).index ≤ 3 := by
  rcases Nat.eq_or_lt_of_le hn4 with rfl | hn5
  · have hf : 1 ≤ f := by
      rcases Nat.eq_zero_or_pos f with rfl | h
      · exfalso
        have h2 : 1 < Nat.card K := Finite.one_lt_card
        rw [pow_zero] at hK
        omega
      · exact h
    have hC : CFSG.Open.StatedClassicalModel
        (CFSG.Open.StatedProj (CFSG.Open.StatedOmega (CFSG.Open.StatedQuadPlus 4 K)))
        .POmegaPlus 4 2 f :=
      ⟨⟨Nat.prime_two, hf, by norm_num⟩, K, inferInstance, inferInstance, hK,
        ⟨MulEquiv.refl _⟩⟩
    exact plus_four_index hC K hK (MulEquiv.refl _)
  · rw [CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_plus K n hn5]
    simp

private theorem exists_field_coordinate_pomegaPlus {K : Type} [Field K] [Finite K]
    [CharP K 2] {n : ℕ} (hn4 : 4 ≤ n) :
    ∃ Φ : MulAut (matrixProjectiveDerived (coordinateQuadPlus n K)) →* (K ≃+* K),
      (∀ g, Φ (MulAut.conj g) = 1) ∧
      (∀ σ : K ≃+* K, Φ (matrixProjectiveConjugationHom (coordinateQuadPlus n K)
        (plusFieldHom n σ)) = σ) := by
  rcases Nat.eq_or_lt_of_le hn4 with rfl | hn5
  · obtain ⟨Φ, -, hΦInn, hΦs, -⟩ :=
      CFSG.SeitzReduction.OmegaPilot.omegaPlusFourAutNormalFormInput_holds K
    exact ⟨Φ, hΦInn, fun σ => by
      simpa [CFSG.SeitzReduction.OmegaPilot.fieldAutHom,
        CFSG.RankThree.PartOne.KCOrthogonalSubfield.fieldAutT, plusFieldHom] using hΦs σ⟩
  · obtain ⟨Φ, -, hΦInn, hΦs, -, -, -⟩ :=
      CFSG.SeitzReduction.OmegaPilot.omegaPlusAutNormalFormInput_holds K n hn5
    exact ⟨Φ, hΦInn, fun σ => by
      simpa [CFSG.SeitzReduction.OmegaPilot.fieldAutHom,
        CFSG.RankThree.PartOne.KCOrthogonalSubfield.fieldAutT, plusFieldHom] using hΦs σ⟩

private theorem transport_conjAct_mul_fieldPair_pomegaPlus {K : Type} [Field K] [CharP K 2]
    {n : ℕ} (hQ : ∃ v, coordinateQuadPlus n K v ≠ 0)
    (α : MulAut (matrixDerived (coordinateQuadPlus n K)))
    {x : matrixProjectiveDerived (coordinateQuadPlus n K)} {σ : K ≃+* K}
    (hβ : MulAut.congr (derivedProjEquiv (coordinateQuadPlus n K) hQ) α =
      MulAut.conj x * matrixProjectiveConjugationHom (coordinateQuadPlus n K)
        (plusFieldHom n σ)) :
    α = MulAut.conj ((derivedProjEquiv (coordinateQuadPlus n K) hQ).symm x) *
      conjAct (coordinateQuadPlus n K) (plusFieldHom n σ) := by
  let Q := coordinateQuadPlus n K
  let Φ := derivedProjEquiv Q hQ
  have hconj : MulAut.congr Φ.symm (MulAut.conj x) = MulAut.conj (Φ.symm x) := by
    refine MulEquiv.ext fun z => ?_
    have h := congr_apply_apply' Φ.symm (MulAut.conj x) (Φ z)
    rw [MulEquiv.symm_apply_apply] at h
    rw [h, MulAut.conj_apply, MulAut.conj_apply]
    simp only [map_mul, map_inv, MulEquiv.symm_apply_apply]
  have hsymm : MulAut.congr Φ.symm
      (matrixProjectiveConjugationHom Q (plusFieldHom n σ)) =
      conjAct Q (plusFieldHom n σ) := by
    rw [← congr_derivedProjEquiv_conjAct_pomegaPlus Q hQ (plusFieldHom n σ)]
    exact MulEquiv.symm_apply_apply (MulAut.congr Φ) _
  calc α = MulAut.congr Φ.symm (MulAut.congr Φ α) :=
        (MulEquiv.symm_apply_apply (MulAut.congr Φ) α).symm
    _ = MulAut.congr Φ.symm (MulAut.conj x *
          matrixProjectiveConjugationHom Q (plusFieldHom n σ)) := by rw [hβ]
    _ = MulAut.congr Φ.symm (MulAut.conj x) *
          MulAut.congr Φ.symm (matrixProjectiveConjugationHom Q (plusFieldHom n σ)) :=
        map_mul _ _ _
    _ = MulAut.conj (Φ.symm x) * conjAct Q (plusFieldHom n σ) := by rw [hconj, hsymm]

private theorem exists_conjAct_mul_fieldPair_pomegaPlus {K : Type} [Field K] [Finite K]
    [CharP K 2] {n r k : ℕ} (hn : 1 ≤ n)
    (hnd : (coordinateQuadPlus n K).polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin (2 * n) → K), Module.finrank K T = 3 ∧
      ∀ x ∈ T, coordinateQuadPlus n K x = 0)
    (himg : (matrixProjectiveImage (coordinateQuadPlus n K)).index ≤ 3)
    (hr : r.Prime) (hr5 : 5 ≤ r)
    (α : MulAut (matrixDerived (coordinateQuadPlus n K))) (hα : orderOf α = r ^ k) :
    ∃ (γ : matrixDerived (coordinateQuadPlus n K)) (σ : K ≃+* K),
      α = MulAut.conj γ * conjAct (coordinateQuadPlus n K) (plusFieldHom n σ) := by
  let Q := coordinateQuadPlus n K
  have hQ : ∃ v, Q v ≠ 0 := by
    refine exists_ne_zero_of_polar_nondegenerate (d := 2 * n) (by omega) Q ?_
    simpa [Q] using hnd
  let Φ := derivedProjEquiv Q hQ
  let β : MulAut (matrixProjectiveDerived Q) := MulAut.congr Φ α
  have hβord : orderOf β = r ^ k := by
    change orderOf (MulAut.congr Φ α) = r ^ k
    rw [MulEquiv.orderOf_eq, hα]
  have hβE : β ∈ matrixProjectiveImage Q := by
    refine CFSG.RankThree.PartOne.OutStructure.mem_of_pow_mem_of_index_le_three
      (p := r) (k := k) _ himg hr (by omega) ?_
    rw [← hβord, pow_orderOf_eq_one]
    exact one_mem _
  have hodd : Odd (r ^ k) := (Nat.Prime.odd_of_ne_two hr (by omega)).pow
  obtain ⟨x, σ, hβ⟩ := exists_conj_mul_plusFieldAut (K := K) n hn (by simpa [Q] using hnd)
    (by simpa [Q] using hT) hβE (e := r ^ k) hodd (by
      rw [← hβord, pow_orderOf_eq_one]
      exact one_mem _)
  exact ⟨Φ.symm x, σ, transport_conjAct_mul_fieldPair_pomegaPlus hQ α hβ⟩

private theorem congr_conj_pomegaPlus {G H : Type} [Group G] [Group H] (e : G ≃* H) (g : G) :
    MulAut.congr e (MulAut.conj g) = MulAut.conj (e g) := by
  refine MulEquiv.ext fun z => ?_
  obtain ⟨w, rfl⟩ := e.surjective z
  rw [congr_apply_apply', MulAut.conj_apply, MulAut.conj_apply, map_mul, map_inv]
  simp

private theorem plusStatedAut_map_plusProjectiveUnipotent_pomegaPlus {K : Type} [Field K]
    [Finite K] {n : ℕ} (hn3 : 3 ≤ n) (σ : K ≃+* K) :
    (plusProjectiveUnipotent n K).map (plusStatedAut n σ).toMonoidHom =
      plusProjectiveUnipotent n K := by
  ext w
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact (plusStatedAut_mem_unipotent_iff n hn3 σ v).mp hv
  · intro hw
    refine ⟨(plusStatedAut n σ).symm w, ?_, by simp⟩
    exact (plusStatedAut_mem_unipotent_iff n hn3 σ
      ((plusStatedAut n σ).symm w)).mpr (by simpa using hw)

private theorem comp_derivedProjEquiv_conjAct_pomegaPlus {K : Type} [Field K] [CharP K 2]
    {d : ℕ} (Q : QuadraticForm K (Fin d → K)) (hQ : ∃ v, Q v ≠ 0)
    (g : similarityPairs Q) :
    (derivedProjEquiv Q hQ).toMonoidHom.comp (conjAct Q g).toMonoidHom =
      (matrixProjectiveConjugationHom Q g).toMonoidHom.comp
        (derivedProjEquiv Q hQ).toMonoidHom := by
  ext z
  have h := congr_apply_apply' (derivedProjEquiv Q hQ) (conjAct Q g) z
  rw [congr_derivedProjEquiv_conjAct_pomegaPlus Q hQ g] at h
  exact h.symm

private theorem comp_plusProjReindex_plusStatedAut_pomegaPlus {K : Type} [Field K] {n : ℕ}
    (σ : K ≃+* K) :
    (matrixProjectiveConjugationHom (coordinateQuadPlus n K) (plusFieldHom n σ)).toMonoidHom.comp
        (plusProjReindex n).toMonoidHom =
      (plusProjReindex n).toMonoidHom.comp (plusStatedAut n σ).toMonoidHom := by
  have hcongr : MulAut.congr (plusProjReindex n) (plusStatedAut n σ) =
      matrixProjectiveConjugationHom (coordinateQuadPlus n K) (plusFieldHom n σ) := by
    rw [plusStatedAut]
    exact MulEquiv.apply_symm_apply (MulAut.congr (plusProjReindex n)) _
  ext z
  have h := congr_apply_apply' (plusProjReindex n) (plusStatedAut n σ) z
  rw [hcongr] at h
  exact h

private theorem exists_field_stable_sylow_pomegaPlus {K : Type} [Field K] [Finite K] [CharP K 2]
    {n : ℕ} (hn4 : 4 ≤ n) :
    ∃ S₀ : Sylow 2 (matrixDerived (coordinateQuadPlus n K)),
      ∀ σ : K ≃+* K,
        (S₀ : Subgroup (matrixDerived (coordinateQuadPlus n K))).map
          (conjAct (coordinateQuadPlus n K) (plusFieldHom n σ)).toMonoidHom = S₀ := by
  let Q := coordinateQuadPlus n K
  have hn3 : 3 ≤ n := by omega
  have hreg := regular_coordinateQuadPlus n K hn3
  have hQ : ∃ v, Q v ≠ 0 :=
    exists_ne_zero_of_polar_nondegenerate (d := 2 * n) (by omega) Q hreg.1
  obtain ⟨S_U, hS_U⟩ := plusProjectiveUnipotent_isSylow (n := n) (K := K) (p := 2) hn3
  let p : CFSG.Open.StatedProj (CFSG.Open.StatedOmega (CFSG.Open.StatedQuadPlus n K)) ≃*
      matrixProjectiveDerived Q := plusProjReindex n
  have hp_surj : Function.Surjective p.toMonoidHom := fun y => ⟨p.symm y, by simp⟩
  let S_M : Sylow 2 (matrixProjectiveDerived Q) :=
    Sylow.mapSurjective (f := p.toMonoidHom) hp_surj S_U
  have hS_M : (S_M : Subgroup (matrixProjectiveDerived Q)) =
      (plusProjectiveUnipotent n K).map p.toMonoidHom := by
    change (Sylow.mapSurjective (f := p.toMonoidHom) hp_surj S_U :
      Subgroup (matrixProjectiveDerived Q)) = _
    rw [Sylow.coe_mapSurjective, hS_U]
  let Φ : matrixDerived Q ≃* matrixProjectiveDerived Q := derivedProjEquiv Q hQ
  have hΦ_surj : Function.Surjective Φ.symm.toMonoidHom := fun y => ⟨Φ y, by simp⟩
  let S₀ : Sylow 2 (matrixDerived Q) :=
    Sylow.mapSurjective (f := Φ.symm.toMonoidHom) hΦ_surj S_M
  have hS₀ : (S₀ : Subgroup (matrixDerived Q)) =
      (plusProjectiveUnipotent n K).map (p.trans Φ.symm).toMonoidHom := by
    change (Sylow.mapSurjective (f := Φ.symm.toMonoidHom) hΦ_surj S_M :
      Subgroup (matrixDerived Q)) = _
    rw [Sylow.coe_mapSurjective, hS_M, Subgroup.map_map]
    rfl
  refine ⟨S₀, ?_⟩
  intro σ
  have hΦS : (S₀ : Subgroup (matrixDerived Q)).map Φ.toMonoidHom =
      (plusProjectiveUnipotent n K).map p.toMonoidHom := by
    rw [hS₀, Subgroup.map_map]
    congr 1
    ext z
    simp
  apply Subgroup.map_injective (f := Φ.toMonoidHom) Φ.injective
  rw [Subgroup.map_map, comp_derivedProjEquiv_conjAct_pomegaPlus Q hQ (plusFieldHom n σ),
    ← Subgroup.map_map, hΦS, Subgroup.map_map,
    comp_plusProjReindex_plusStatedAut_pomegaPlus σ, ← Subgroup.map_map,
    plusStatedAut_map_plusProjectiveUnipotent_pomegaPlus hn3 σ]

private theorem isIsoPair_plusFieldHom_pomegaPlus {K : Type} [Field K] {n : ℕ}
    (σ : K ≃+* K) :
    IsIsoPair (coordinateQuadPlus n K) (plusFieldHom n σ).val := by
  intro v
  have h1 : coordinateSemilinearMap (plusFieldHom n σ).val v =
      coordinateFieldMap (2 * n) σ v := by
    funext i
    simp [plusFieldHom, CFSG.RankThree.PartOne.KCOrthogonalSubfield.fieldPair,
      coordinateSemilinearMap_apply, coordinateFieldMap_apply]
  rw [h1, plusFieldHom_right]
  exact coordinateQuadPlus_fieldMap n σ v

private theorem exists_fixed_nonsingular_vector_pomegaPlus {K : Type} [Field K] {n : ℕ}
    (hn1 : 1 ≤ n) (σ : K ≃+* K) :
    ∃ w : Fin (2 * n) → K, coordinateQuadPlus n K w ≠ 0 ∧
      coordinateSemilinearMap (plusFieldHom n σ).val w = w := by
  refine ⟨plusVec n hn1, ?_, ?_⟩
  · rw [coordinateQuadPlus_plusVec]
    exact one_ne_zero
  · have h1 : coordinateSemilinearMap (plusFieldHom n σ).val (plusVec n hn1) =
        coordinateFieldMap (2 * n) σ (plusVec n hn1) := by
      funext i
      simp [plusFieldHom, CFSG.RankThree.PartOne.KCOrthogonalSubfield.fieldPair,
        coordinateSemilinearMap_apply, coordinateFieldMap_apply]
    rw [h1, coordinateFieldMap_plusVec]

private theorem exists_field_part_odd_pomegaPlus {K : Type} [Field K] [Finite K] [CharP K 2]
    {n r k : ℕ} (hn1 : 1 ≤ n)
    (hnd : (coordinateQuadPlus n K).polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin (2 * n) → K), Module.finrank K T = 3 ∧
      ∀ x ∈ T, coordinateQuadPlus n K x = 0)
    (himg : (matrixProjectiveImage (coordinateQuadPlus n K)).index ≤ 3)
    (hr : r.Prime) (hr5 : 5 ≤ r)
    {Φc : MulAut (matrixProjectiveDerived (coordinateQuadPlus n K)) →* (K ≃+* K)}
    (hΦInn : ∀ g, Φc (MulAut.conj g) = 1)
    (hΦfield : ∀ σ, Φc (matrixProjectiveConjugationHom (coordinateQuadPlus n K)
      (plusFieldHom n σ)) = σ)
    (α : MulAut (matrixDerived (coordinateQuadPlus n K))) (hα : orderOf α = r ^ k) :
    ∃ (γ : matrixDerived (coordinateQuadPlus n K)) (σ : K ≃+* K),
      α = MulAut.conj γ * conjAct (coordinateQuadPlus n K) (plusFieldHom n σ) ∧
        Odd (orderOf σ) := by
  let Q := coordinateQuadPlus n K
  have hQ : ∃ v, Q v ≠ 0 :=
    exists_ne_zero_of_polar_nondegenerate (d := 2 * n) (by omega) Q
      (by simpa [Q] using hnd)
  obtain ⟨γ, σ, hαeq⟩ :=
    exists_conjAct_mul_fieldPair_pomegaPlus hn1 hnd hT himg hr hr5 α hα
  refine ⟨γ, σ, hαeq, ?_⟩
  have hσdvd : orderOf σ ∣ r ^ k := by
    let Φd := derivedProjEquiv Q hQ
    let β : MulAut (matrixProjectiveDerived Q) := MulAut.congr Φd α
    have hβ : β = MulAut.conj (Φd γ) *
        matrixProjectiveConjugationHom Q (plusFieldHom n σ) := by
      rw [show β = MulAut.congr Φd α from rfl, hαeq, map_mul, congr_conj_pomegaPlus,
        congr_derivedProjEquiv_conjAct_pomegaPlus Q hQ (plusFieldHom n σ)]
    have hΦβ : Φc β = σ := by
      rw [hβ, map_mul, hΦInn (Φd γ), one_mul, hΦfield σ]
    have hordβ : orderOf β = r ^ k := by
      rw [show β = MulAut.congr Φd α from rfl, MulEquiv.orderOf_eq, hα]
    have hdvd := orderOf_map_dvd Φc β
    rw [hΦβ, hordβ] at hdvd
    exact hdvd
  exact ((Nat.Prime.odd_of_ne_two hr (by omega)).pow).of_dvd_nat hσdvd

private theorem pow_field_part_eq_one_pomegaPlus {K : Type} [Field K] [Finite K]
    {n : ℕ} {α : MulAut (matrixDerived (coordinateQuadPlus n K))}
    (γ : matrixDerived (coordinateQuadPlus n K)) (σ : K ≃+* K)
    (hαeq : α = MulAut.conj γ * conjAct (coordinateQuadPlus n K) (plusFieldHom n σ))
    (hinn : Subgroup.zpowers α ⊓
      CFSG.ComponentClassification.OuterAutomorphisms.inner
        (matrixDerived (coordinateQuadPlus n K)) = ⊥) :
    α ^ orderOf σ = 1 := by
  let Q := coordinateQuadPlus n K
  let f := conjAct Q (plusFieldHom n σ)
  have hfp : f ^ orderOf σ = 1 := by
    rw [show f = conjAct Q (plusFieldHom n σ) from rfl, ← map_pow, ← map_pow,
      pow_orderOf_eq_one, map_one, map_one]
  have him : (MulAut.conj γ * f) ^ orderOf σ ∈
      CFSG.ComponentClassification.OuterAutomorphisms.inner (matrixDerived Q) := by
    have hq : QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner
        (matrixDerived Q)) ((MulAut.conj γ * f) ^ orderOf σ) = 1 := by
      rw [map_pow, map_mul]
      have hc : QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner
          (matrixDerived Q)) (MulAut.conj γ) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr ⟨γ, rfl⟩
      rw [hc, one_mul, ← map_pow, hfp, map_one]
    exact (QuotientGroup.eq_one_iff _).mp hq
  have hzp : (MulAut.conj γ * f) ^ orderOf σ ∈ Subgroup.zpowers α := by
    change (MulAut.conj γ * conjAct Q (plusFieldHom n σ)) ^ orderOf σ ∈
      Subgroup.zpowers α
    rw [← hαeq]
    exact Subgroup.npow_mem_zpowers α _
  have hbot : (MulAut.conj γ * f) ^ orderOf σ ∈
      (⊥ : Subgroup (MulAut (matrixDerived Q))) := by
    rw [← hinn]
    exact Subgroup.mem_inf.mpr ⟨hzp, him⟩
  have h1 := Subgroup.mem_bot.mp hbot
  rw [hαeq]
  exact h1

private theorem oddAutSylowFixAt_matrixDerived_pomegaPlus {K : Type} [Field K] [Finite K]
    [CharP K 2] {n f r : ℕ} (hK : Nat.card K = 2 ^ f) (hn4 : 4 ≤ n) (hr : r.Prime)
    (hr5 : 5 ≤ r) :
    OddAutSylowFixAt r (matrixDerived (coordinateQuadPlus n K)) := by
  let Q := coordinateQuadPlus n K
  have hn3 : 3 ≤ n := by omega
  have hn1 : 1 ≤ n := by omega
  have hreg := regular_coordinateQuadPlus n K hn3
  have hnd : Q.polarBilin.Nondegenerate := hreg.1
  obtain ⟨T, hTfin, hTs⟩ := hreg.2
  have hT : ∃ T : Submodule K (Fin (2 * n) → K), Module.finrank K T = 3 ∧
      ∀ x ∈ T, Q x = 0 := ⟨T, hTfin, hTs⟩
  have hAP : CFSG.ComponentClassification.CatalogueBOrthogonalPointAction.ActionProperties Q
      (projectivePointAction Q) := coordinate_plus_point_action_properties n K hn3
  have himg : (matrixProjectiveImage Q).index ≤ 3 :=
    matrixProjectiveImage_index_le_three_pomegaPlus hK hn4
  obtain ⟨Φc, hΦInn, hΦfield⟩ := exists_field_coordinate_pomegaPlus (K := K) (n := n) hn4
  obtain ⟨S₀, hpres⟩ := exists_field_stable_sylow_pomegaPlus (K := K) (n := n) hn4
  refine OddAutSylowFixAt.of_conj S₀ ?_
  intro α k hα hinn
  obtain ⟨γ, σ, hαeq, hpodd⟩ := exists_field_part_odd_pomegaPlus hn1 hnd hT himg hr hr5
    hΦInn hΦfield α hα
  have hαp := pow_field_part_eq_one_pomegaPlus γ σ hαeq hinn
  obtain ⟨w, hw, hSw⟩ := exists_fixed_nonsingular_vector_pomegaPlus hn1 σ
  have hfp : conjAct Q (plusFieldHom n σ) ^ orderOf σ = 1 := by
    rw [← map_pow, ← map_pow, pow_orderOf_eq_one, map_one, map_one]
  have hord : (MulAut.conj γ * conjAct Q (plusFieldHom n σ)) ^ orderOf σ = 1 := by
    rw [← hαeq]
    exact hαp
  obtain ⟨u', hu', heq⟩ := exists_conj_of_isIsoPair_odd hn1 hnd hT hAP hpodd
    (S := plusFieldHom n σ) (isIsoPair_plusFieldHom_pomegaPlus σ)
    (by rw [plusFieldHom_right]) hw hSw γ hord hfp
  refine ⟨u', conjAct Q (plusFieldHom n σ), ?_, hpres σ⟩
  rw [hαeq, heq]

end OddAutOmegaPlus

theorem oddAutSylowFixAt_pomegaPlus {Y : Type} [Group Y] [Finite Y] {n f r : ℕ}
    (hC : CFSG.Open.StatedClassicalModel Y .POmegaPlus n 2 f) (hr : r.Prime) (hr5 : 5 ≤ r) :
    OddAutSylowFixAt r Y := by
  obtain ⟨hadm, K, hfield, hfinite, hK, ⟨e⟩⟩ := hC
  let _ : Field K := hfield
  let _ : Finite K := hfinite
  have _ : Fintype K := Fintype.ofFinite K
  have _ : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := f)
    (by simpa [Nat.card_eq_fintype_card] using hK)
  have hn4 : 4 ≤ n := hadm.2.2
  have hn3 : 3 ≤ n := by omega
  let Q := CFSG.ComponentClassification.CatalogueBOrthogonalPointData.coordinateQuadPlus n K
  have hQ : ∃ v, Q v ≠ 0 :=
    CFSG.RankThree.PartOne.AUTSL.exists_ne_zero_of_polar_nondegenerate (d := 2 * n)
      (by omega) Q
      (CFSG.ComponentClassification.CatalogueBOrthogonalPointData.regular_coordinateQuadPlus
        n K hn3).1
  let e' := (CFSG.ComponentClassification.CatalogueBOrthogonalPointData.coordinatePlusWitnessEquiv
    K e).symm
  exact OddAutSylowFixAt.of_mulEquiv e'
    (OddAutSylowFixAt.of_mulEquiv (CFSG.RankThree.PartOne.AUTSL.derivedProjEquiv Q hQ)
      (oddAutSylowFixAt_matrixDerived_pomegaPlus hK hn4 hr hr5))

section PomegaMinus

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.RankThree.PartOne.AUTSL
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
  CFSG.AGLEmbedding.ParabAutIrr CFSG.StandardType

private theorem exists_sylow_mnTauE_mem_iff {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hn4 : 4 ≤ n) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ∃ S : Sylow 2 (orthElementaryGroup (quadTail (n - 1) (minusTailForm K b c))),
      ∀ w, w ∈ S ↔ mnTauE n hn4 b c hirr w ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := finite_tailEquiv (K := K) (n - 1)
  obtain ⟨⟨S, hS⟩, -⟩ := orthogonal_geometry_tail_Sylow_flag_normalizer (p := 2)
    (show 3 ≤ n - 1 by omega) (anisotropic_minusTailForm hirr) (nondegenerate_minusTailForm hirr)
    (Or.inr finrank_fin_two_fun)
  refine ⟨S, fun w => ?_⟩
  change w ∈ (S : Subgroup _) ↔ mnTauE n hn4 b c hirr w ∈ (S : Subgroup _)
  rw [hS]
  exact mn_mem_iff_of_aut_mem (fun w hw => mnTauE_mem_tailUnipotent n hn4 b c hirr w hw) w

private theorem exists_sylow_map_frobAut_pow_minus {K : Type} [Field K] [Finite K] [CharP K 2]
    {n : ℕ} (hn4 : 4 ≤ n) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ∃ S₀ : Sylow 2 (matrixDerived (Qm n hn4 b c)), ∀ j : ℕ,
      (S₀ : Subgroup (matrixDerived (Qm n hn4 b c))).map
        (AutOm.frobAut hn4 hirr ^ j).toMonoidHom = S₀ := by
  obtain ⟨S, hS⟩ := exists_sylow_mnTauE_mem_iff hn4 hirr
  set Φ := mnPhi n hn4 b c hirr
  let S₀ : Sylow 2 (matrixDerived (Qm n hn4 b c)) :=
    S.comapOfInjective Φ.toMonoidHom Φ.injective fun x _ => ⟨Φ.symm x, Φ.apply_symm_apply x⟩
  have h1 : ∀ x, x ∈ S₀ ↔ AutOm.frobAut hn4 hirr x ∈ S₀ := fun x => by
    change Φ x ∈ S ↔ Φ (AutOm.frobAut hn4 hirr x) ∈ S
    have e : Φ (AutOm.frobAut hn4 hirr x) = mnTauE n hn4 b c hirr (Φ x) := by
      change _ = Φ (mnTau n hn4 b c hirr (Φ.symm (Φ x)))
      rw [MulEquiv.symm_apply_apply]
      rfl
    rw [e]
    exact hS (Φ x)
  have hpow : ∀ j x, x ∈ S₀ ↔ (AutOm.frobAut hn4 hirr ^ j) x ∈ S₀ := by
    intro j
    induction j with
    | zero => exact fun x => Iff.rfl
    | succ j ih => exact fun x => (h1 x).trans (by rw [pow_succ, MulAut.mul_apply]; exact ih _)
  refine ⟨S₀, fun j => le_antisymm ?_ fun x hx => ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact (hpow j y).1 hy
  · refine ⟨(AutOm.frobAut hn4 hirr ^ j).symm x, (hpow j _).2 ?_, ?_⟩
    · rw [MulEquiv.apply_symm_apply]
      exact hx
    · simp

private theorem odd_orderOf_frobenius_pow_minus {K : Type} [Field K] [Finite K] [CharP K 2]
    {n : ℕ} (hn4 : 4 ≤ n) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {f : ℕ}
    (hf : Nat.card K = 2 ^ f) (hf1 : 1 ≤ f) {j m : ℕ} (hm : Odd m)
    (hjm : (AutOm.frobAut hn4 hirr ^ j) ^ m = 1) :
    Odd (orderOf (frobeniusEquiv K 2 ^ j)) ∧
      (AutOm.frobAut hn4 hirr ^ j) ^ orderOf (frobeniusEquiv K 2 ^ j) = 1 := by
  obtain ⟨σ, hσ, hord, -⟩ :=
    finite_field_automorphism_fixed_field_cardinality Nat.prime_two hf1 hf
  have hσφ : σ = frobeniusEquiv K 2 := RingEquiv.ext fun a => by
    rw [hσ, frobeniusEquiv_apply, frobenius_def]
  have hφ : orderOf (frobeniusEquiv K 2) = f := hσφ ▸ hord
  have hfjm : f ∣ j * m := AutOm.dvd_of_frobAut_pow_mem_inner hn4 hirr hf hf1
    (by rw [pow_mul, hjm]; exact one_mem _)
  have hpm : orderOf (frobeniusEquiv K 2 ^ j) ∣ m := orderOf_dvd_of_pow_eq_one (by
    rw [← pow_mul]
    exact orderOf_dvd_iff_pow_eq_one.1 (hφ ▸ hfjm))
  refine ⟨hm.of_dvd_nat hpm, ?_⟩
  set p := orderOf (frobeniusEquiv K 2 ^ j)
  obtain ⟨t, ht⟩ : f ∣ j * p := by
    rw [← hφ]
    exact orderOf_dvd_of_pow_eq_one (by rw [pow_mul]; exact pow_orderOf_eq_one _)
  have h2 : ((AutOm.frobAut hn4 hirr ^ j) ^ p) ^ 2 = 1 := by
    rw [← pow_mul, ← pow_mul, ← mul_assoc, ht, mul_right_comm, mul_comm f 2, pow_mul,
      AutOm.frobAut_pow_two_mul hn4 hirr hf, one_pow]
  have hm' : ((AutOm.frobAut hn4 hirr ^ j) ^ p) ^ m = 1 := by
    rw [← pow_mul, mul_comm p m, pow_mul, hjm, one_pow]
  have h := pow_gcd_eq_one.2 ⟨h2, hm'⟩
  rwa [Nat.Coprime.gcd_eq_one (Nat.coprime_two_left.2 hm), pow_one] at h

private theorem exists_inner_conj_frobAut_pow_minus {K : Type} [Field K] [Finite K] [CharP K 2]
    {n : ℕ} (hn4 : 4 ≤ n) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (γ : matrixDerived (Qm n hn4 b c)) {j p : ℕ} (hpodd : Odd p)
    (hσ : orderOf (frobeniusEquiv K 2 ^ j) = p)
    (hord : (MulAut.conj γ * AutOm.frobAut hn4 hirr ^ j) ^ p = 1)
    (hfp : (AutOm.frobAut hn4 hirr ^ j) ^ p = 1) :
    ∃ u ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner (matrixDerived (Qm n hn4 b c)),
      MulAut.conj γ * AutOm.frobAut hn4 hirr ^ j = u * AutOm.frobAut hn4 hirr ^ j * u⁻¹ := by
  have hn : 1 ≤ n := by omega
  have hb := ne_zero_of_irreducible_tail b c hirr
  obtain ⟨hnd, hT3⟩ := regular_coordinateQuadMinus n K b c hn4 hirr
  have hAP := coordinate_minus_point_action_properties n K b c hn4 hirr
  have hτS : AutOm.frobAut hn4 hirr ^ j = conjAct (Qm n hn4 b c) (frobPair n hn b c hb ^ j) := by
    rw [map_pow]
    rfl
  have hS : RecipeFieldOmega.IsIsoPair (Qm n hn4 b c) (frobPair n hn b c hb ^ j).val := by
    rw [SubmonoidClass.coe_pow]
    exact (RecipeFieldOmega.isIsoPair_frobPair hn hb).pow j
  have hSr : (frobPair n hn b c hb ^ j).val.right = frobeniusEquiv K 2 ^ j := by
    rw [SubmonoidClass.coe_pow, RecipeFieldOmega.right_pow, frobPair_right]
  rw [hτS] at hord hfp ⊢
  exact RecipeFieldOmega.exists_conj_of_isIsoPair_odd hn hnd hT3 hAP hpodd hS (hSr ▸ hσ)
    (AutOm.tailVec_form_ne_zero n hn b c) (RecipeFieldOmega.frobPair_pow_tailVec hn hb j) γ hord
    hfp

private theorem exists_inner_conj_frobAut_pow_of_orderOf_minus {K : Type} [Field K] [Finite K]
    [CharP K 2] {n : ℕ} (hn4 : 4 ≤ n) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {f : ℕ}
    (hf : Nat.card K = 2 ^ f) (hf1 : 1 ≤ f) {r : ℕ} (hr : Odd r)
    (α : MulAut (matrixDerived (Qm n hn4 b c))) (k : ℕ) (hα : orderOf α = r ^ k)
    (hinn : Subgroup.zpowers α ⊓
      CFSG.ComponentClassification.OuterAutomorphisms.inner (matrixDerived (Qm n hn4 b c)) = ⊥) :
    ∃ u ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner (matrixDerived (Qm n hn4 b c)),
      ∃ j : ℕ, α = u * AutOm.frobAut hn4 hirr ^ j * u⁻¹ := by
  obtain ⟨ι, ⟨γ, rfl⟩, j, rfl⟩ := AutOm.exists_inner_mul_frobAut_pow hn4 hirr hf α
  have hαk : (MulAut.conj γ * AutOm.frobAut hn4 hirr ^ j) ^ (r ^ k) = 1 :=
    hα ▸ pow_orderOf_eq_one _
  have hτk : (AutOm.frobAut hn4 hirr ^ j) ^ (r ^ k) = 1 := by
    have h : (AutOm.frobAut hn4 hirr ^ j) ^ (r ^ k) ∈
        CFSG.ComponentClassification.OuterAutomorphisms.inner (matrixDerived (Qm n hn4 b c)) ⊓
          Subgroup.zpowers (AutOm.frobAut hn4 hirr) :=
      ⟨RecipeFieldOmega.pow_mem_inner_of_mul_pow_eq_one ⟨γ, rfl⟩ hαk,
        by rw [← pow_mul]; exact Subgroup.npow_mem_zpowers _ _⟩
    rwa [AutOm.inner_inf_zpowers_frobAut hn4 hirr hf hf1, Subgroup.mem_bot] at h
  obtain ⟨hpodd, hfp⟩ := odd_orderOf_frobenius_pow_minus hn4 hirr hf hf1 hr.pow hτk
  have hord : (MulAut.conj γ * AutOm.frobAut hn4 hirr ^ j) ^
      orderOf (frobeniusEquiv K 2 ^ j) = 1 := by
    obtain ⟨d, hd, hdp⟩ := RecipeFieldOmega.exists_mul_pow_eq
      (CFSG.ComponentClassification.OuterAutomorphisms.inner (matrixDerived (Qm n hn4 b c)))
      (f := AutOm.frobAut hn4 hirr ^ j) ⟨γ, rfl⟩ (orderOf (frobeniusEquiv K 2 ^ j))
    rw [hfp, mul_one] at hdp
    have h : (MulAut.conj γ * AutOm.frobAut hn4 hirr ^ j) ^ orderOf (frobeniusEquiv K 2 ^ j) ∈
        Subgroup.zpowers (MulAut.conj γ * AutOm.frobAut hn4 hirr ^ j) ⊓
          CFSG.ComponentClassification.OuterAutomorphisms.inner (matrixDerived (Qm n hn4 b c)) :=
      ⟨Subgroup.npow_mem_zpowers _ _, hdp ▸ hd⟩
    rwa [hinn, Subgroup.mem_bot] at h
  obtain ⟨u, hu, heq⟩ := exists_inner_conj_frobAut_pow_minus hn4 hirr γ hpodd rfl hord hfp
  exact ⟨u, hu, j, heq⟩

private theorem oddAutSylowFixAt_matrixDerived_minus {K : Type} [Field K] [Finite K] [CharP K 2]
    {n : ℕ} (hn4 : 4 ≤ n) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {f : ℕ}
    (hf : Nat.card K = 2 ^ f) (hf1 : 1 ≤ f) {r : ℕ} (hr : Odd r) :
    OddAutSylowFixAt r (matrixDerived (Qm n hn4 b c)) := by
  obtain ⟨S₀, hS₀⟩ := exists_sylow_map_frobAut_pow_minus hn4 hirr
  refine OddAutSylowFixAt.of_conj S₀ fun α k hα hinn => ?_
  obtain ⟨u, -, j, rfl⟩ :=
    exists_inner_conj_frobAut_pow_of_orderOf_minus hn4 hirr hf hf1 hr α k hα hinn
  exact ⟨u, AutOm.frobAut hn4 hirr ^ j, rfl, hS₀ j⟩

theorem oddAutSylowFixAt_pomegaMinus {Y : Type} [Group Y] [Finite Y] {n f r : ℕ}
    (hC : CFSG.Open.StatedClassicalModel Y .POmegaMinus n 2 f) (hr : r.Prime) (hr5 : 5 ≤ r) :
    OddAutSylowFixAt r Y := by
  have hn4 : 4 ≤ n := hC.1.2.2
  have hf1 : 1 ≤ f := hC.1.2.1
  obtain ⟨-, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := id hC
  obtain ⟨hchar, hnd, hT, -⟩ := coordinate_model_witness_minus hC K hK b c hirr e
  have : CharP K 2 := ringChar.of_eq hchar
  have hQ := CFSG.RankThree.PartOne.KCOrthComm.exists_ne_zero_of_nondegenerate hnd hT
  let eΓ : Y ≃* matrixDerived (Qm n hn4 b c) :=
    (coordinateMinusWitnessEquiv K (by omega) b c e).trans (derivedProjEquiv _ hQ).symm
  exact OddAutSylowFixAt.of_mulEquiv eΓ.symm
    (oddAutSylowFixAt_matrixDerived_minus hn4 hirr hK hf1 (hr.odd_of_ne_two (by omega)))

end PomegaMinus

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12

end
