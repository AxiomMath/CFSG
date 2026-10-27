module

public import CFSG.Open.StatedDefs
public import CFSG.Open.GriessAllModelsStatement
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15ACoreCoverLinGen
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsLie
import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42Mult
import CFSG.LinearAlgebra.LinearGroups.UnitaryScalarKernel
import CFSG.ClassicalGroups.Unitary.Finite
import CFSG.Open.StatedAPI
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.Open.Defs
import CFSG.Blueprint.LieModelAPI
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianIsometry
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.ACore

open CFSG.Open CFSG.RankThree.PerfectCover

theorem card_hopfMultiplier_psu_char_two (hG : CFSG.Open.GriessAllModelsStatement) {l f q : ℕ}
    (hq : q = 2 ^ f) {F : Type} [Field F] [Finite F] (hF : Nat.card F = q ^ 2)
    (hadm : StatedLieAdmissible .PSU (l + 1) 2 f) :
    ∃ k : ℕ, Nat.card (hopfMultiplier (StatedProj (StatedSU (l + 1) q F))) =
      Nat.card ((StatedScalars (Fin (l + 1)) F).subgroupOf (StatedSU (l + 1) q F)) * 2 ^ k := by
  subst hq
  have hLM : CFSG.Models.LieModel (StatedProj (StatedSU (l + 1) (2 ^ f) F)) .PSU (l + 1) 2 f :=
    ⟨hadm, Or.inl ⟨hadm, F, inferInstance, inferInstance, hF, ⟨MulEquiv.refl _⟩⟩⟩
  obtain ⟨k, hk⟩ := ksm_exc_two .PSU (l + 1) f
  refine ⟨k, ?_⟩
  have h1 : Nat.card (hopfMultiplier (StatedProj (StatedSU (l + 1) (2 ^ f) F))) =
      (CFSG.Blueprint.Multiplier.genericOrders .PSU (l + 1) 2 f).1 *
        (CFSG.Blueprint.Multiplier.genericOrders .PSU (l + 1) 2 f).2 *
        ((CFSG.Blueprint.Multiplier.exceptionalOrders .PSU (l + 1) 2 f).1 *
          (CFSG.Blueprint.Multiplier.exceptionalOrders .PSU (l + 1) 2 f).2) := by
    rw [CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.card_hopfMultiplier_of_griess hG _ _ _ _ _ hLM]
    unfold CFSG.Blueprint.Multiplier.generic CFSG.Blueprint.Multiplier.exceptional
    simp only [Nat.card_prod, Nat.card_congr (Multiplicative.toAdd : _ ≃ _), Nat.card_zmod]
  have hgen : CFSG.Blueprint.Multiplier.genericOrders .PSU (l + 1) 2 f =
      (Nat.gcd (l + 1) (2 ^ f + 1), 1) := rfl
  rw [h1, hgen, hk, (CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_two hF (by omega)).2.2,
    mul_one]

theorem coverIdUni (hG : CFSG.Open.GriessAllModelsStatement) {K : Type} [Group K] [Finite K]
    (hq : CFSG.Open.IsQuasisimple K) {l : ℕ} (hl : 2 ≤ l) {Q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedA l Q).Valid) (hQ : Q.p = 2)
    (e : (K ⧸ Subgroup.center K) ≃* TauCeti.ValidLieTypeIndex.Group ⟨.twistedA l Q, hv⟩) :
    ∃ (F : Type) (_ : Field F) (_ : Fintype F) (Z₀ : Subgroup (StatedSU (l + 1) Q.card F))
      (_ : Z₀.Normal) (j : ℕ), Fintype.card F = Q.card ^ 2 ∧
      Z₀ ≤ (StatedScalars (Fin (l + 1)) F).subgroupOf (StatedSU (l + 1) Q.card F) ∧
      Nat.card (Subgroup.center K) = 2 ^ j *
        (Nat.card ((StatedScalars (Fin (l + 1)) F).subgroupOf (StatedSU (l + 1) Q.card F)) /
          Nat.card Z₀) ∧
      ∀ r : ℕ, r.Prime → r ≠ 2 → CFSG.Open.pRank r (⊤ : Subgroup K) =
        CFSG.Open.pRank r (⊤ : Subgroup (↥(StatedSU (l + 1) Q.card F) ⧸ Z₀)) := by
  rw [TauCeti.PrimePower.card_def]
  obtain ⟨hadm, F, instF, instFin, hcardF, ⟨φ⟩⟩ :=
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA l Q hv e
  haveI : Fact Q.p.Prime := ⟨Q.prime_p⟩
  haveI : Group.IsPerfect K := Group.isPerfect_def.mpr hq.1
  haveI : Fintype F := Fintype.ofFinite F
  have hS₀ : Group.IsPerfect (StatedSU (l + 1) (Q.p ^ Q.exponent) F) := by
    obtain ⟨-, -, -, hnq⟩ := hadm
    exact CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hcardF (n := l + 1) (by omega) hnq
  have hq2 : Q.p ^ Q.exponent = 2 ^ Q.exponent := by rw [hQ]
  rw [hQ] at hadm
  obtain ⟨k, hM⟩ := card_hopfMultiplier_psu_char_two hG hq2 hcardF hadm
  let ρ : K →* StatedProj (StatedSU (l + 1) (Q.p ^ Q.exponent) F) :=
    φ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  have hρs : Function.Surjective ρ := φ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hρk : ρ.ker = Subgroup.center K := by
    rw [MonoidHom.ker_comp_of_injective _ _ φ.injective, QuotientGroup.ker_mk']
  obtain ⟨Z₀, hZn, j, hZD, hZK, hrank⟩ := coverId_of_two_index hS₀ inferInstance
    ((StatedScalars (Fin (l + 1)) F).subgroupOf (StatedSU (l + 1) (Q.p ^ Q.exponent) F))
    (CFSG.Open.StatedAPI.statedScalars_subgroupOf_le_center _) ρ hρs hρk hM
  refine ⟨F, instF, inferInstance, Z₀, hZn, j, ?_, hZD, hZK, hrank⟩
  rw [Fintype.card_eq_nat_card, hcardF]

end CFSG.LocalAnalysis.RankThreeUC.S15.ACore
