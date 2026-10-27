module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.LowerSymplecticOrth
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase
public import CFSG.Monster.B.Fischer.Fi22Order
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open
open CFSG.LieType.Universal.Spin (quadPlus quadMinus)

namespace OmFam

theorem genericOrders_pomegaMinus_eq_one {ℓ n : ℕ} (hn : 1 ≤ n) (hℓ : 1 ≤ ℓ) :
    CFSG.Blueprint.Multiplier.genericOrders .POmegaMinus ℓ 2 n = (1, 1) := by
  simp only [CFSG.Blueprint.Multiplier.genericOrders]
  rw [show ((2 : ℕ) ^ n) ^ ℓ = 2 ^ (n * ℓ) by rw [← pow_mul]]
  have hodd : Odd (2 ^ (n * ℓ) + 1) := by
    refine Even.add_one (even_iff_two_dvd.mpr (dvd_pow_self 2 ?_))
    exact Nat.mul_ne_zero (by omega) (by omega)
  have hco : Nat.Coprime 4 (2 ^ (n * ℓ) + 1) := by
    simpa using Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hodd)
  rw [Nat.coprime_iff_gcd_eq_one.mp hco]

end OmFam

section Certificate

theorem exists_mulEquiv_statedOmega_plus_of_hasLabel {K : Type} [Group K] [Finite K]
    {ℓ n : ℕ} (hℓ : 4 ≤ ℓ)
    (hK : HasLabel K (fun l : GLALabel => l = ⟨.D, ℓ, n⟩))
    (hZ : Subgroup.center K = ⊥) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
      Nat.card F = 2 ^ n ∧ Nonempty (K ≃* StatedOmega (StatedQuadPlus ℓ F)) := by
  obtain ⟨-, -, hM⟩ := quasisimple_markedModel_of_isLabel hK
  have hℓ3 : ℓ ≠ 3 := by omega
  have hM' : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .POmegaPlus ℓ 2 n := by
    simpa [CFSG.StandardType.MarkedModel, CFSG.StandardType.markTag,
      CFSG.StandardType.markRank, CFSG.StandardType.markChar,
      CFSG.StandardType.markDeg, if_neg hℓ3] using hM
  obtain ⟨-, F, hfield, hfinite, hcard, ⟨e⟩⟩ := hM'.statedClassicalModel (by decide)
  letI : Field F := hfield
  letI : Finite F := hfinite
  haveI : Fintype F := Fintype.ofFinite F
  have hcard' : Fintype.card F = 2 ^ n := by
    rw [← Nat.card_eq_fintype_card]
    exact hcard
  haveI : CharP F 2 := charP_of_card_eq_prime_pow hcard'
  have hZΩ : Subgroup.center (StatedOmega (StatedQuadPlus ℓ F)) =
      (StatedScalars (Fin ℓ ⊕ Fin ℓ) F).subgroupOf
        (StatedOmega (StatedQuadPlus ℓ F)) :=
    CFSG.LieType.Universal.Spin.center_statedOmega_quadPlus (K := F) (n := ℓ) (by omega)
  have hZbot : Subgroup.center (StatedOmega (StatedQuadPlus ℓ F)) = ⊥ := by
    rw [hZΩ]
    exact CFSG.SectionRank.EvenCover.statedScalars_subgroupOf_statedOmega_eq_bot
      (Q := quadPlus ℓ F) (Q₀ := StatedQuadPlus ℓ F)
      (CFSG.LieType.Universal.Spin.coe_quadPlus ℓ F)
      (CFSG.RankThree.CentralLift.exists_quadPlus_ne_zero (K := F) (n := ℓ) (by omega))
  let eProj : StatedProj (StatedOmega (StatedQuadPlus ℓ F)) ≃*
      StatedOmega (StatedQuadPlus ℓ F) :=
    (QuotientGroup.quotientMulEquivOfEq hZΩ).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hZbot).trans QuotientGroup.quotientBot)
  let eZ : K ≃* K ⧸ Subgroup.center K :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm
  exact ⟨F, hfield, hfinite, inferInstance, hcard, ⟨eZ.trans (e.trans eProj)⟩⟩

theorem exists_mulEquiv_statedOmega_minus_of_hasLabel {K : Type} [Group K] [Finite K]
    {ℓ n : ℕ} (hℓ : 4 ≤ ℓ)
    (hK : HasLabel K (fun l : GLALabel => l = ⟨.twD, ℓ, n⟩))
    (hZ : Subgroup.center K = ⊥) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (b c : F),
      Nat.card F = 2 ^ n ∧ (∀ s : F, s ^ 2 + b * s + c ≠ 0) ∧
        Nonempty (K ≃* StatedOmega (StatedQuadMinus ℓ F b c)) := by
  obtain ⟨-, -, hM⟩ := quasisimple_markedModel_of_isLabel hK
  have hℓ2 : ℓ ≠ 2 := by omega
  have hℓ3 : ℓ ≠ 3 := by omega
  have hM' : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .POmegaMinus ℓ 2 n := by
    simpa [CFSG.StandardType.MarkedModel, CFSG.StandardType.markTag,
      CFSG.StandardType.markRank, CFSG.StandardType.markChar,
      CFSG.StandardType.markDeg, if_neg hℓ2, if_neg hℓ3] using hM
  obtain ⟨-, F, hfield, hfinite, hcard, b, c, hirr, ⟨e⟩⟩ :=
    hM'.statedClassicalModel (by decide)
  letI : Field F := hfield
  letI : Finite F := hfinite
  haveI : Fintype F := Fintype.ofFinite F
  have hcard' : Fintype.card F = 2 ^ n := by
    rw [← Nat.card_eq_fintype_card]
    exact hcard
  haveI : CharP F 2 := charP_of_card_eq_prime_pow hcard'
  have hZΩ : Subgroup.center (StatedOmega (StatedQuadMinus ℓ F b c)) =
      (StatedScalars (Fin (ℓ - 1) ⊕ Fin (ℓ - 1) ⊕ Fin 2) F).subgroupOf
        (StatedOmega (StatedQuadMinus ℓ F b c)) :=
    CFSG.LieType.Universal.Spin.center_statedOmega_quadMinus (K := F) (n := ℓ)
      (b := b) (c := c) (by omega) hirr
  have hZbot : Subgroup.center (StatedOmega (StatedQuadMinus ℓ F b c)) = ⊥ := by
    rw [hZΩ]
    refine CFSG.SectionRank.EvenCover.statedScalars_subgroupOf_statedOmega_eq_bot
      (Q := quadMinus ℓ F b c) (Q₀ := StatedQuadMinus ℓ F b c)
      (CFSG.LieType.Universal.Spin.coe_quadMinus ℓ F b c) ?_
    refine ⟨Pi.single (Sum.inr (Sum.inr 0)) 1, ?_⟩
    rw [CFSG.LieType.Universal.Spin.quadMinus_apply]
    simp
  let eProj : StatedProj (StatedOmega (StatedQuadMinus ℓ F b c)) ≃*
      StatedOmega (StatedQuadMinus ℓ F b c) :=
    (QuotientGroup.quotientMulEquivOfEq hZΩ).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hZbot).trans QuotientGroup.quotientBot)
  let eZ : K ≃* K ⧸ Subgroup.center K :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm
  exact ⟨F, hfield, hfinite, inferInstance, b, c, hcard, hirr,
    ⟨eZ.trans (e.trans eProj)⟩⟩

end Certificate

end CFSG.LocalAnalysis.GLTheoremA.Y10F
