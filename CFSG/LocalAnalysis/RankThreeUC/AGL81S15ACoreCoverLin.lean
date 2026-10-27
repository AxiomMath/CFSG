module

public import CFSG.Open.StatedDefs
public import CFSG.Open.GriessAllModelsStatement
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15ACoreCoverLinGen
import CFSG.RankThree.PartOne.N143.Inspect613Even
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsLie
import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42Mult
import CFSG.Adapters.StatedSLPerfect
import CFSG.Assembly.OrderReductions.LinearOrders
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.Open.Defs
import CFSG.Blueprint.LieModelAPI
import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
import CFSG.RankThree.LocalRank.SelectorCases

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.ACore

open CFSG.Open CFSG.RankThree.PerfectCover

theorem card_scalars_statedSL {n : ℕ} (hn : 0 < n) (F : Type) [Field F] [Finite F] :
    Nat.card ((StatedScalars (Fin n) F).subgroupOf (StatedSL n F)) =
      Nat.gcd n (Nat.card F - 1) := by
  rw [← CFSG.Assembly.LowTwoRank.map_center_eq_statedScalars n F,
    Subgroup.card_map_of_injective
      (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL n F).injective,
    CFSG.OrderReductions.LinearOrders.card_specialLinear_center F n hn]

theorem card_hopfMultiplier_psl_char_two (hG : CFSG.Open.GriessAllModelsStatement) {l f : ℕ}
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2 ^ f)
    (hadm : StatedLieAdmissible .PSL (l + 1) 2 f) :
    ∃ k : ℕ, Nat.card (hopfMultiplier (StatedProj (StatedSL (l + 1) F))) =
      Nat.card ((StatedScalars (Fin (l + 1)) F).subgroupOf (StatedSL (l + 1) F)) * 2 ^ k := by
  have hLM : CFSG.Models.LieModel (StatedProj (StatedSL (l + 1) F)) .PSL (l + 1) 2 f :=
    ⟨hadm, Or.inl ⟨hadm, F, inferInstance, inferInstance, hF, ⟨MulEquiv.refl _⟩⟩⟩
  obtain ⟨k, hk⟩ := ksm_exc_two .PSL (l + 1) f
  refine ⟨k, ?_⟩
  have h1 : Nat.card (hopfMultiplier (StatedProj (StatedSL (l + 1) F))) =
      (CFSG.Blueprint.Multiplier.genericOrders .PSL (l + 1) 2 f).1 *
        (CFSG.Blueprint.Multiplier.genericOrders .PSL (l + 1) 2 f).2 *
        ((CFSG.Blueprint.Multiplier.exceptionalOrders .PSL (l + 1) 2 f).1 *
          (CFSG.Blueprint.Multiplier.exceptionalOrders .PSL (l + 1) 2 f).2) := by
    rw [CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.card_hopfMultiplier_of_griess hG _ _ _ _ _ hLM]
    unfold CFSG.Blueprint.Multiplier.generic CFSG.Blueprint.Multiplier.exceptional
    simp only [Nat.card_prod, Nat.card_congr (Multiplicative.toAdd : _ ≃ _), Nat.card_zmod]
  have hgen : CFSG.Blueprint.Multiplier.genericOrders .PSL (l + 1) 2 f =
      (Nat.gcd (l + 1) (2 ^ f - 1), 1) := rfl
  rw [h1, hgen, hk, card_scalars_statedSL (by omega) F, hF, mul_one]

theorem coverIdLin (hG : CFSG.Open.GriessAllModelsStatement) {K : Type} [Group K] [Finite K]
    (hq : CFSG.Open.IsQuasisimple K) {l : ℕ} (hl : 2 ≤ l) {Q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.A l Q).Valid) (hQ : Q.p = 2)
    (e : (K ⧸ Subgroup.center K) ≃* TauCeti.ValidLieTypeIndex.Group ⟨.A l Q, hv⟩) :
    ∃ (F : Type) (_ : Field F) (_ : Fintype F) (Z₀ : Subgroup (StatedSL (l + 1) F))
      (_ : Z₀.Normal) (j : ℕ), Fintype.card F = Q.card ∧
      Z₀ ≤ (StatedScalars (Fin (l + 1)) F).subgroupOf (StatedSL (l + 1) F) ∧
      Nat.card (Subgroup.center K) = 2 ^ j *
        (Nat.card ((StatedScalars (Fin (l + 1)) F).subgroupOf (StatedSL (l + 1) F)) /
          Nat.card Z₀) ∧
      ∀ r : ℕ, r.Prime → r ≠ 2 → CFSG.Open.pRank r (⊤ : Subgroup K) =
        CFSG.Open.pRank r (⊤ : Subgroup (↥(StatedSL (l + 1) F) ⧸ Z₀)) := by
  obtain ⟨hadm, F, instF, instFin, hcardF, ⟨φ⟩⟩ :=
    CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e
  rw [hQ] at hadm hcardF
  haveI : Group.IsPerfect K := Group.isPerfect_def.mpr hq.1
  haveI : Fintype F := Fintype.ofFinite F
  obtain ⟨k, hM⟩ := card_hopfMultiplier_psl_char_two hG hcardF hadm
  let ρ : K →* StatedProj (StatedSL (l + 1) F) :=
    φ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  have hρs : Function.Surjective ρ := φ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hρk : ρ.ker = Subgroup.center K := by
    rw [MonoidHom.ker_comp_of_injective _ _ φ.injective, QuotientGroup.ker_mk']
  obtain ⟨Z₀, hZn, j, hZD, hZK, hrank⟩ := coverId_of_two_index
    (CFSG.Open.StatedAPI.isPerfect_statedSL_of_three_le (n := l + 1) (by omega) F) inferInstance
    ((StatedScalars (Fin (l + 1)) F).subgroupOf (StatedSL (l + 1) F))
    (CFSG.Open.StatedAPI.statedScalars_subgroupOf_le_center _) ρ hρs hρk hM
  refine ⟨F, instF, inferInstance, Z₀, hZn, j, ?_, hZD, hZK, hrank⟩
  rw [Fintype.card_eq_nat_card, hcardF, TauCeti.PrimePower.card_def, hQ]

end CFSG.LocalAnalysis.RankThreeUC.S15.ACore
