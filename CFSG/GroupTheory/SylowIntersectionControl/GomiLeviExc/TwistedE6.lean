module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiLeviExc.Transfer
public import CFSG.GroupTheory.SylowIntersectionControl.GomiLeviExc.SLChevTwo
public import CFSG.LocalAnalysis.AGLEmbeddingD2.ParabLeviComponents
public import CFSG.LieType.Steinberg.TwistedE6.Defs
public import Certificates.Certificate43
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate123
import CFSG.ClassicalInvolution.ModelFacts.LinearAutLift
import CFSG.LocalAnalysis.AGLEmbeddingD2.SquareUnitary
import CFSG.LieType.Steinberg.CentralExt.FieldFourMultiplier
import CFSG.LieType.Steinberg.CentralExt.TwistedE6Torus
import CFSG.ClassicalInvolution.Models.LinearPairs.Pairs
import CFSG.ClassicalInvolution.WeakCT.TwistedE6Levi
import CFSG.ClassicalInvolution.WeakCT.TwistedE6Model
public import CFSG.Adapters.ClassicalCatalogLinearUnitary
public import CFSG.CharacterTheory.Blocks.BrauerInduction
public import CFSG.CharacterTheory.Semidihedral.Principal.PrimeOrderSylowColumn
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
public import CFSG.CharacterTheory.TwoRankLowerBound.NormalComplementCharacterSpace
public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.CentralLift
public import CFSG.LocalAnalysis.AGLEmbedding.D1GlobalU
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThreeSL
public import CFSG.LocalAnalysis.AGLEmbedding.Reduction
public import CFSG.LocalAnalysis.AGLEmbedding.TwoCoreObstruction
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianIsometry
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporJ4Quot
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3NoProper
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2
public import CFSG.LocalAnalysis.StandardType.GGLatDefs
public import CFSG.Open.SplitBNPair
public import CFSG.Quasithin.Background.B1
public import CFSG.Quasithin.Background.C1GNC124
public import CFSG.Quasithin.Background.C1PackS1531Top
public import CFSG.Quasithin.Background.E2Statements
public import CFSG.Quasithin.Background.E2Three
public import CFSG.Quasithin.Background.FFC7G
public import CFSG.Quasithin.EmptyFaithful.R3c20A
public import CFSG.Quasithin.EmptyFaithful.R3c21A
public import CFSG.Quasithin.EmptyFaithful.S151YC
public import CFSG.Quasithin.EmptyFaithful.S151cA2
public import CFSG.Quasithin.EmptyFaithful.S151cCases
public import CFSG.Quasithin.EmptyFaithful.S153D44
public import CFSG.Quasithin.EmptyFaithful.S153H32
public import CFSG.Quasithin.EmptyFaithful.SBc5Aut
public import CFSG.Quasithin.EmptyFaithful.T1515Top9
public import CFSG.Quasithin.EmptyFaithful.T1531Cat
public import CFSG.Quasithin.EmptyFaithful.T1531Final
public import CFSG.Quasithin.EmptyFaithful.T1531InspStmt
public import CFSG.Quasithin.H13.J4Classes
public import CFSG.Quasithin.H13.J4Core
public import CFSG.Quasithin.Recognition.CertTwoLocalPair
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS2
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS3
public import CFSG.Sporadic.Schreier.TitsOther
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement
import CFSG.ClassicalInvolution.WeakCT.Main
import CFSG.LieType.Steinberg.CentralExt.F4E8Multiplier
import CFSG.LocalAnalysis.ComponentInitial.CentralCoverAbelian

public section

namespace CFSG.GroupTheory.GomiLeviExc.TwistedE6

open Subgroup CFSG.Blueprint.Chevalley CFSG.AGLEmbeddingD2.ParabLevi
  CFSG.LieType.Steinberg.TwistedE6
open CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.Models.TwistedPairs
  CFSG.ClassicalInvolution.ModelFacts.LinearAut CFSG.LieType.CurtisTits CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Minuscule

local instance twistedE6LeviNeZeroRank : NeZero (Tag.rank .F4) := ⟨by decide⟩

variable {k : Type} [Field k] [Finite k] [CharP k 2] {θ : k →+* k} {q : ℕ}

omit [Finite k] [CharP k 2] in
private theorem range_emb_eq_leviM_zero_one
    (emb : Matrix.SpecialLinearGroup (Fin 3) (fixedField θ) →* fixedGroup k θ)
    (h0 : emb.comp (blk (fixedField θ) 0) = CFSG.ClassicalInvolution.WeakCT.nodeHom0 θ)
    (h1 : emb.comp (blk (fixedField θ) 1) = CFSG.ClassicalInvolution.WeakCT.nodeHom1 θ) :
    emb.range = leviM (twistedDatum k θ) ({0, 1} : Set (Fin (Tag.rank .F4))) := by
  have hpair : leviM (twistedDatum k θ) ({0, 1} : Set (Fin (Tag.rank .F4))) =
      rankOne (twistedDatum k θ).rootGroup (nf 0) ⊔
        rankOne (twistedDatum k θ).rootGroup (nf 1) :=
    CFSG.AGLEmbeddingD2.SquareUnitary.leviM_pair (twistedDatum k θ) (nf 0) (nf 1)
  rw [hpair]
  rw [CFSG.ClassicalInvolution.WeakCT.rankOne_twistedE6_zero,
      CFSG.ClassicalInvolution.WeakCT.rankOne_twistedE6_one]
  rw [← h0, ← h1]
  calc
    emb.range = Subgroup.map emb ⊤ := by rw [MonoidHom.range_eq_map]
    _ = ((blk (fixedField θ) 0).range ⊔ (blk (fixedField θ) 1).range).map emb := by
      rw [← CFSG.ClassicalInvolution.Models.B12_sup_B23]
      rfl
    _ = (blk (fixedField θ) 0).range.map emb ⊔
        (blk (fixedField θ) 1).range.map emb := by
      rw [Subgroup.map_sup]
    _ = (emb.comp (blk (fixedField θ) 0)).range ⊔
        (emb.comp (blk (fixedField θ) 1)).range := by
      rw [MonoidHom.range_comp, MonoidHom.range_comp]

omit [Finite k] [CharP k 2] in
private theorem range_emb_eq_leviM_two_three
    (hθ2 : ∀ c, θ (θ c) = c)
    (emb : Matrix.SpecialLinearGroup (Fin 3) k →* fixedGroup k θ)
    (h0 : emb.comp (blk k 0) = CFSG.ClassicalInvolution.WeakCT.nodeHom2 θ hθ2)
    (h1 : emb.comp (blk k 1) = CFSG.ClassicalInvolution.WeakCT.nodeHom3 θ hθ2) :
    emb.range = leviM (twistedDatum k θ) ({2, 3} : Set (Fin (Tag.rank .F4))) := by
  have hpair : leviM (twistedDatum k θ) ({2, 3} : Set (Fin (Tag.rank .F4))) =
      rankOne (twistedDatum k θ).rootGroup (nf 2) ⊔
        rankOne (twistedDatum k θ).rootGroup (nf 3) :=
    CFSG.AGLEmbeddingD2.SquareUnitary.leviM_pair (twistedDatum k θ) (nf 2) (nf 3)
  rw [hpair]
  rw [CFSG.ClassicalInvolution.WeakCT.rankOne_twistedE6_two θ hθ2,
      CFSG.ClassicalInvolution.WeakCT.rankOne_twistedE6_three θ hθ2]
  rw [← h0, ← h1]
  calc
    emb.range = Subgroup.map emb ⊤ := by rw [MonoidHom.range_eq_map]
    _ = ((blk k 0).range ⊔ (blk k 1).range).map emb := by
      rw [← CFSG.ClassicalInvolution.Models.B12_sup_B23]
      rfl
    _ = (blk k 0).range.map emb ⊔ (blk k 1).range.map emb := by
      rw [Subgroup.map_sup]
    _ = (emb.comp (blk k 0)).range ⊔ (emb.comp (blk k 1)).range := by
      rw [MonoidHom.range_comp, MonoidHom.range_comp]

section SpecialLinear

omit [CharP k 2] in
private theorem gomiLeviFactor_of_sl_three {F : Type} [Field F] [Finite F] [CharP F 2]
    (emb : Matrix.SpecialLinearGroup (Fin 3) F →* fixedGroup k θ) (hinj : Function.Injective emb)
    {I : Set (Fin (Tag.rank .F4))} (hrange : emb.range = leviM (twistedDatum k θ) I) :
    GomiLeviFactor ↥(leviM (twistedDatum k θ) I) := by
  have hZ : Odd (Nat.card (center (Matrix.SpecialLinearGroup (Fin 3) F))) :=
    Nat.not_even_iff_odd.mp fun h =>
      not_dvd_card_center_specialLinearGroup (p := 2) (even_iff_two_dvd.mp h)
  have : Finite ↥(e6Data_valid.minGroup k) :=
    CFSG.LieType.Steinberg.CentralExt.FieldFour.finite_minGroup' e6Data_valid
  exact gomiLeviFactor_of_injective
    (CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.isChevComponent_sl (k := 3) (F := F)
      (Or.inl le_rfl)).1 hZ (isChevTwo_psl F (Or.inl le_rfl)) emb hinj hrange

theorem gomiLeviFactor_leviM_zero_one :
    GomiLeviFactor ↥(leviM (twistedDatum k θ) ({0, 1} : Set (Fin (Tag.rank .F4)))) := by
  obtain ⟨emb, hinj, h0, h1⟩ := exists_levi01 θ
  exact gomiLeviFactor_of_sl_three emb hinj (range_emb_eq_leviM_zero_one emb h0 h1)

theorem gomiLeviFactor_leviM_two_three (hk : Nat.card k = q ^ 2) (hθ : ∀ c, θ c = c ^ q) :
    GomiLeviFactor ↥(leviM (twistedDatum k θ) ({2, 3} : Set (Fin (Tag.rank .F4)))) := by
  have hθ2 := CFSG.LieType.Steinberg.CentralExt.TwistedE6Closed.theta_theta_of_card hk hθ
  obtain ⟨emb, hinj, h0, h1⟩ := exists_levi23 (θ := θ) hθ2
  exact gomiLeviFactor_of_sl_three emb hinj (range_emb_eq_leviM_two_three hθ2 emb h0 h1)

end SpecialLinear

end CFSG.GroupTheory.GomiLeviExc.TwistedE6
