module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.Bridges
public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergTrialityModel
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.D4XF

open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S9
open CFSG.Assembly.LowTwoRank CFSG.Open

theorem statedModel_of_d4two {K : Type} [Group K] (h : catalogIs K S9.isD4two) :
    StatedClassicalModel K .POmegaPlus 4 2 1 := by
  obtain ⟨q, hv, hq, ⟨e⟩⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.lieIndex_isD4two h
  obtain ⟨h1, h2⟩ := CFSG.LocalAnalysis.GLTheoremA.primePower_eq_of_card_eq Nat.prime_two (s := 1)
    (by norm_num) (hq.trans (by norm_num))
  have hm := CFSG.Models.lieModel_D 4 q hv e
  rw [h1, h2] at hm
  exact hm.statedClassicalModel (by decide)

theorem matrixDerivedScalars_eq_bot {K₀ : Type} [Field K₀] {d : ℕ} (hu : Subsingleton K₀ˣ)
    (Q : QuadraticForm K₀ (Fin d → K₀)) :
    CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear.matrixDerivedScalars Q = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨c, hc⟩ := (CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear.mem_matrixDerivedScalars_iff
    Q A).1 hA
  rw [Subgroup.mem_bot]
  have hc1 : c = 1 := Subsingleton.elim c 1
  apply Subtype.ext
  rw [← hc, hc1, map_one]
  rfl

theorem equiv_triality_of_statedProj {K : Type} [Group K] {K₀ : Type} [Field K₀]
    (hu : Subsingleton K₀ˣ)
    (e : K ≃* StatedProj (StatedOmega (StatedQuadPlus 4 K₀))) :
    Nonempty (K ≃* CFSG.StandardType.Triality.Om8 K₀) := by
  have hS := matrixDerivedScalars_eq_bot hu
    (CFSG.ComponentClassification.CatalogueBOrthogonalPointData.coordinateQuadPlus 4 K₀)
  exact ⟨(CFSG.ComponentClassification.CatalogueBOrthogonalPointData.coordinatePlusWitnessEquiv K₀ e).trans
    ((QuotientGroup.quotientMulEquivOfEq hS).trans QuotientGroup.quotientBot)⟩

theorem equiv_projOmegaPlus_of_statedProj {K : Type} [Group K] {K₀ : Type} [Field K₀]
    (hK₀ : Nat.card K₀ = 2) (e : K ≃* StatedProj (StatedOmega (StatedQuadPlus 4 K₀))) :
    Nonempty (K ≃* CFSG.PGLModel.projOmegaPlus 4 (GaloisField 2 1)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite K₀ := Nat.finite_of_card_ne_zero (by omega)
  haveI : Fintype K₀ := Fintype.ofFinite K₀
  haveI : Fintype (GaloisField 2 1) := Fintype.ofFinite _
  have hF : Nat.card (GaloisField 2 1) = 2 := by
    rw [GaloisField.card 2 1 (by norm_num)]
    norm_num
  have hcard : Fintype.card K₀ = Fintype.card (GaloisField 2 1) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK₀, hF]
  let ψ : K₀ ≃+* GaloisField 2 1 := FiniteField.ringEquivOfCardEq hcard
  let Φ := CFSG.Adapters.RankTwoModelTransports.statedProjCongr
    (CFSG.Adapters.RankTwoModelTransports.glCongr (ι := Fin 4 ⊕ Fin 4) ψ)
    (CFSG.LocalAnalysis.GLTheoremA.CatB.glCongr_statedOmega_plus ψ 4)
    (CFSG.Adapters.RankTwoModelTransports.glCongr_statedScalars ψ)
  exact ⟨e.trans (Φ.trans (StatedAPI.mapMkEquivStatedProj
    (StatedOmega (StatedQuadPlus 4 (GaloisField 2 1)))).symm)⟩

theorem equiv_projOmegaPlus {K : Type} [Group K] (h : catalogIs K S9.isD4two) :
    Nonempty (K ≃* CFSG.PGLModel.projOmegaPlus 4 (GaloisField 2 1)) := by
  obtain ⟨-, K₀, _, _, hK₀, ⟨e⟩⟩ := statedModel_of_d4two h
  exact equiv_projOmegaPlus_of_statedProj (by rw [hK₀]; norm_num) e

end CFSG.LocalAnalysis.GLTheoremA.D4XF
