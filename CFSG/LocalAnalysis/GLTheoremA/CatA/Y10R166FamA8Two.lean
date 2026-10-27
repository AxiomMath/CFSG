module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166F2Blocks
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Cases
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Label
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Mult
public import CFSG.Adapters.LinearFieldTransport
public import CFSG.LocalAnalysis.ComponentClassification.GoldschmidtTDGriess
public import CFSG.Adapters.StatedQuasisimple

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.StandardType CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Census

local notation "𝔽₂" => ZMod 2

theorem hasLabel_statedSL_zmod_two (n : ℕ) (hn : 3 ≤ n) :
    HasLabel ↥(StatedSL n (ZMod 2)) (· = ⟨.A, n - 1, 1⟩) := by
  have hQ : CFSG.IsQuasisimple ↥(StatedSL n (ZMod 2)) := by
    have h := CFSG.Open.StatedAPI.isQuasisimple_statedSL_of_two_le (m := n - 1)
      (K := ZMod 2) (by omega)
    have hn1 : n - 1 + 1 = n := Nat.sub_add_cancel (by omega : 1 ≤ n)
    exact hn1 ▸ h
  have hcenter : Subgroup.center ↥(StatedSL n (ZMod 2)) =
      (StatedScalars (Fin n) (ZMod 2)).subgroupOf (StatedSL n (ZMod 2)) := by
    rw [← map_center_eq_statedScalars n (ZMod 2), Subgroup.map_center_eq]
  have hbot : Subgroup.center ↥(StatedSL n (ZMod 2)) = ⊥ := by
    rw [hcenter, CFSG.Open.StatedAPI.statedScalars_eq_bot_of_card_two (by norm_num) (Fin n),
      Subgroup.bot_subgroupOf]
  have hadm : StatedLieAdmissible .PSL n 2 1 := by
    refine ⟨Nat.prime_two, le_rfl, by omega, ?_, by simp⟩
    intro h
    have h1 : n = 2 := by simpa using congrArg Prod.fst h
    omega
  have hSC : StatedClassicalModel (↥(StatedSL n (ZMod 2)) ⧸
      Subgroup.center ↥(StatedSL n (ZMod 2))) .PSL n 2 1 := by
    refine ⟨hadm, ZMod 2, inferInstance, inferInstance, by simp, ?_⟩
    exact ⟨QuotientGroup.quotientMulEquivOfEq hcenter⟩
  have hn1 : n - 1 + 1 = n := Nat.sub_add_cancel (by omega : 1 ≤ n)
  have h := hasLabel_of_statedClassicalModel_PSL (J := ↥(StatedSL n (ZMod 2)))
    (r := n - 1) (n := 1) hQ (by simpa only [hn1] using hSC)
  exact hn1 ▸ h

theorem hasLabel_specialLinear_zmod_two (n : ℕ) (hn : 3 ≤ n) :
    HasLabel (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) (· = ⟨.A, n - 1, 1⟩) :=
  (hasLabel_congr (specialLinearGroupEquivStatedSL n (ZMod 2)) _).2
    (hasLabel_statedSL_zmod_two n hn)

namespace SLNineTwo

theorem hasLabel_f2Model :
    HasLabel (Matrix.SpecialLinearGroup Ix 𝔽₂) (· = ⟨.A, 8, 1⟩) := by
  let e : Fin 9 ≃ Ix := (Fintype.equivFinOfCardEq (by simp [Ix])).symm
  have h := hasLabel_specialLinear_zmod_two 9 (by norm_num)
  have h' : HasLabel (Matrix.SpecialLinearGroup (Fin 9) (ZMod 2)) (· = ⟨.A, 8, 1⟩) := by
    simpa using h
  exact (hasLabel_congr (slReindex (ZMod 2) e) _).1 h'

end SLNineTwo

theorem statedClassicalModel_statedSL_zmod_two (n : ℕ) (hn : 3 ≤ n) :
    StatedClassicalModel ↥(StatedSL n (ZMod 2)) .PSL n 2 1 := by
  have hadm : StatedLieAdmissible .PSL n 2 1 := by
    refine ⟨Nat.prime_two, le_rfl, by omega, ?_, by simp⟩
    intro h
    have h1 : n = 2 := by simpa using congrArg Prod.fst h
    omega
  exact ⟨hadm, ZMod 2, inferInstance, inferInstance, by simp,
    ⟨CFSG.Open.StatedAPI.statedSLZModTwoEquivStatedProj n⟩⟩

section MultiplierCerts


theorem trivialMultiplierT_statedSL_nine : TrivialMultiplierT ↥(StatedSL 9 (ZMod 2)) := by
  have hM : CFSG.Models.LieModel ↥(StatedSL 9 (ZMod 2)) .PSL 9 2 1 :=
    ⟨(statedClassicalModel_statedSL_zmod_two 9 (by norm_num)).1,
      Or.inl (statedClassicalModel_statedSL_zmod_two 9 (by norm_num))⟩
  have h1 : Nat.card (CFSG.Blueprint.Multiplier.generic .PSL 9 2 1 ×
      CFSG.Blueprint.Multiplier.exceptional .PSL 9 2 1) = 1 := by
    simp [CFSG.Blueprint.Multiplier.generic, CFSG.Blueprint.Multiplier.exceptional,
      CFSG.Blueprint.Multiplier.genericOrders, CFSG.Blueprint.Multiplier.exceptionalOrders,
      Nat.card_prod, ZMod.card]
  exact trivialMultiplierT_of_lieModel CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds
    hM h1

namespace SLNineTwo

theorem trivialMultiplierT_f2Model :
    TrivialMultiplierT (Matrix.SpecialLinearGroup Ix 𝔽₂) := by
  let eIdx : Fin 9 ≃ Ix := (Fintype.equivFinOfCardEq (by simp [Ix])).symm
  let e : ↥(StatedSL 9 (ZMod 2)) ≃* Matrix.SpecialLinearGroup Ix 𝔽₂ :=
    (specialLinearGroupEquivStatedSL 9 (ZMod 2)).symm.trans (slReindex (ZMod 2) eIdx)
  exact (trivialMultiplier_congr e).1 trivialMultiplierT_statedSL_nine

theorem famA8Two_equiv_model {K : Type} [Group K] [Finite K]
    (hK : HasLabel K (· = ⟨.A, 8, 1⟩)) :
    Nonempty (K ≃* Matrix.SpecialLinearGroup Ix 𝔽₂) := by
  obtain ⟨hQ, hlab, hM⟩ := quasisimple_markedModel_of_isLabel (K := K) (lab := ⟨.A, 8, 1⟩) hK
  have hM' : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .PSL 9 2 1 := by
    simpa [CFSG.StandardType.MarkedModel, CFSG.StandardType.markTag,
      CFSG.StandardType.markRank, CFSG.StandardType.markChar,
      CFSG.StandardType.markDeg] using hM
  have hm : CFSG.Models.LieModel (K ⧸ Subgroup.center K) .PSL 9 2 1 :=
    CFSG.Models.LieModel.of_blueprint_of_ne_zero (by omega) hM'
  obtain ⟨-, K', hfield, hfin, hcard, ⟨eK'⟩⟩ := hm.statedClassicalModel (by decide)
  letI : Field K' := hfield
  letI : Finite K' := hfin
  letI : Fintype K' := Fintype.ofFinite K'
  have hcard2 : Nat.card K' = 2 := by simpa using hcard
  have hFcard : Fintype.card K' = Fintype.card (ZMod 2) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcard2]
    simp
  let eField : K' ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq hFcard
  let eSL : StatedProj (StatedSL 9 K') ≃* StatedProj (StatedSL 9 (ZMod 2)) :=
    (projectiveSpecialLinearGroupEquivStatedProj 9 K').symm.trans
      ((CFSG.ClassicalModels.projectiveSpecialLinearFieldEquiv eField (Fin 9)).trans
        (projectiveSpecialLinearGroupEquivStatedProj 9 (ZMod 2)))
  let eIdx : Fin 9 ≃ Ix := (Fintype.equivFinOfCardEq (by simp [Ix])).symm
  let eProjSL : StatedProj (StatedSL 9 (ZMod 2)) ≃* Matrix.SpecialLinearGroup Ix 𝔽₂ :=
    (CFSG.Open.StatedAPI.statedSLZModTwoEquivStatedProj 9).symm.trans
      ((specialLinearGroupEquivStatedSL 9 (ZMod 2)).symm.trans (slReindex (ZMod 2) eIdx))
  let eTotal : K ⧸ Subgroup.center K ≃* Matrix.SpecialLinearGroup Ix 𝔽₂ :=
    eK'.trans (eSL.trans eProjSL)
  have hTMq : TrivialMultiplierT (K ⧸ Subgroup.center K) :=
    (trivialMultiplier_congr eTotal).2 trivialMultiplierT_f2Model
  have hZbot : Subgroup.center K = ⊥ :=
    center_eq_bot_of_trivialMultiplierT_quotient_center hQ.1.commutator_eq_top hTMq
  refine ⟨?_⟩
  exact ((QuotientGroup.quotientMulEquivOfEq hZbot).trans QuotientGroup.quotientBot).symm.trans
    eTotal

end SLNineTwo

end MultiplierCerts

namespace SLNineTwo

theorem hasLabel_J : HasLabel ↥J (· = ⟨.A, 6, 1⟩) := by
  let eIdx : Fin 7 ≃ W7 := (Fintype.equivFinOfCardEq (by simp [W7])).symm
  have h7 : HasLabel (Matrix.SpecialLinearGroup (Fin 7) (ZMod 2)) (· = ⟨.A, 6, 1⟩) := by
    simpa using hasLabel_specialLinear_zmod_two 7 (by norm_num)
  have hW : HasLabel (Matrix.SpecialLinearGroup W7 𝔽₂) (· = ⟨.A, 6, 1⟩) :=
    (hasLabel_congr (slReindex (ZMod 2) eIdx) _).1 h7
  have eJ : Matrix.SpecialLinearGroup W7 𝔽₂ ≃* ↥J :=
    MonoidHom.ofInjective (f := jHom) jHom_injective
  exact (hasLabel_congr eJ _).1 hW

section QuasisimpleJ


theorem isQuasisimple_J : CFSG.IsQuasisimple ↥J :=
  (quasisimple_markedModel_of_isLabel (K := ↥J) (lab := ⟨.A, 6, 1⟩) hasLabel_J).1

end QuasisimpleJ

end SLNineTwo

end CFSG.LocalAnalysis.GLTheoremA.Y10F
