module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcThreeE7
public import CFSG.LocalAnalysis.StandardType.GGTableBExcThreeE8
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6Basic
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwE7Model
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwE8Model
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerResiduals
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwE6
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwF4
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Reduction
public import CFSG.LieType.Chevalley.EvenTrialityOuterInvolutions
public import CFSG.LieType.Chevalley.OddTrialityCosetInvolutions
public import CFSG.LieType.SeitzGeneration.ExtSeitzReeF4Cyclic
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsCentModel
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFieldAut
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueUStatement
public import CFSG.LocalAnalysis.ComponentClassification.GSLitType
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
public import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
public import CFSG.RankThree.Chevalley.SteinbergBTTwistedCosetDescent
public import CFSG.RankThree.Classical.SteinbergBJSymplecticSquareZeroCentralizer
public import CFSG.RankThree.PartOne.BRANCH.RankRee
public import CFSG.RankThree.PartOne.CTP.StrongPBridgeRest
public import CFSG.RankThree.PartOne.KC.LinearCommutatorOdd
public import CFSG.RankThree.PartOne.KC.LinearDegreeFive
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessEven
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessOdd
public import CFSG.RankThree.PartOne.KC.UnitaryHigherCrossPrimeTorus
public import CFSG.RankThree.PartOne.KC.UnitaryPlaneEndpoints
public import CFSG.RankThree.PartOne.KD4T.Certs
public import CFSG.RankThree.PartOne.KE.StabGeneral
public import CFSG.RankThree.PartOne.N143.Weyl613Defs
public import CFSG.RankThree.PartOne.N143X.KF64WSimple
public import CFSG.RankThree.PartOne.S11d.OutExceptional
public import CFSG.RankThree.PartOne.S11d.OutLinear
public import CFSG.RankThree.PartTwo.KFacts.KS14SzLie
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
public import Certificates.Certificate1
public import Certificates.Certificate2

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.BadExc

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.CentralCover
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.StandardType CFSG.StandardType.TableBExc CFSG.StandardType.TableBExc.Three
open CFSG.Timmesfeld.ExceptionalOrders (geomSum)

section Torus

variable {τ : Tag} {K : Type} [Field K]

theorem rootDiagUnit_mem_torusGroup_of_pow_eq {B : Matrix (Fin τ.rank) (Fin τ.rank) ℤ} {N : ℕ}
    (hB : B * τ.cartan = (N : ℤ) • 1) (a s : Fin τ.rank → Kˣ) (hs : ∀ l, s l ^ N = a l) :
    rootDiagUnit τ a ∈ torusGroup τ K := by
  classical
  set c : Fin τ.rank → Kˣ := fun j => ∏ m, s m ^ B m j with hcdef
  have hc : cartanChar c = a := by
    funext l
    have h1 : ∀ j, (∏ m, s m ^ B m j) ^ τ.cartan j l = ∏ m, s m ^ (B m j * τ.cartan j l) := by
      intro j
      rw [← Finset.prod_zpow]
      exact Finset.prod_congr rfl fun m _ => (zpow_mul _ _ _).symm
    simp only [cartanChar, hcdef, h1]
    rw [Finset.prod_comm]
    have h2 : ∀ m, ∏ j, s m ^ (B m j * τ.cartan j l) = s m ^ ((N : ℤ) • (1 : Matrix
        (Fin τ.rank) (Fin τ.rank) ℤ)) m l := fun m => by
      rw [CFSG.HardMathSupport.Timmesfeld.CrossChar.prod_zpow_eq_zpow_sum'', ← hB,
        Matrix.mul_apply]
    simp only [h2, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [Finset.prod_eq_single l (fun m _ hm => by simp [hm])
      (fun h => absurd (Finset.mem_univ l) h)]
    simp [hs l]
  rw [← hc, ← list_prod_torusElt_eq_rootDiagUnit]
  refine Subgroup.list_prod_mem _ fun g hg => ?_
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hg
  exact torusElt_mem_torusGroup i _

theorem rootDiagUnit_mem_torusGroup_E7_of_pow_three (a : Fin Tag.E7.rank → Kˣ)
    (ha : ∀ i, a i ^ 3 = 1) : rootDiagUnit .E7 a ∈ torusGroup .E7 K :=
  rootDiagUnit_mem_torusGroup_of_pow_eq
    CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_mul_cartan_E7.choose_spec a
    (fun l => a l ^ 2) fun l => by
      rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, ha l, one_mul, pow_one]

theorem card_torusPow_E7_three [Finite K] (h3 : 3 ∣ Nat.card K - 1) :
    Nat.card (torusPow .E7 K 3) = 3 ^ 7 :=
  card_torusPow_of_fullp rootDiagUnit_mem_torusGroup_E7_of_pow_three Nat.prime_three h3

theorem card_torusPow_E8_of_dvd [Finite K] {p : ℕ} (hp : p.Prime) (hpq : p ∣ Nat.card K - 1) :
    Nat.card (torusPow .E8 K p) = p ^ 8 :=
  card_torusPow_of_full
    (fun a => CFSG.HardMathSupport.Timmesfeld.CrossChar.rootDiagUnit_mem_torusGroup_E8 a) hp hpq

end Torus

section T

variable {K : Type} [Field K]

theorem card_adjointGroup_E7_eq_torus_mul [Finite K] :
    Nat.card (adjointGroup .E7 K) =
      Nat.card (torusGroup .E7 K) * (Nat.card K ^ 63 * prodE7 (Nat.card K)) := by
  have hq : 1 ≤ Nat.card K := Nat.card_pos
  have hH := CFSG.Timmesfeld.ExceptionalOrders.card_torusGroup_E7 (K := K)
  have hg : Nat.gcd 2 (Nat.card K - 1) = (Nat.card K - 1).gcd 2 := Nat.gcd_comm _ _
  have hgpos : 0 < (Nat.card K - 1).gcd 2 := Nat.gcd_pos_of_pos_right _ (by norm_num)
  rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_E7, CFSG.Open.ordE7, hg,
    ← CFSG.Timmesfeld.ExceptionalOrders.ordE7_mul _ hq, ← hH, prodE7]
  refine Nat.div_eq_of_eq_mul_left hgpos ?_
  ring

theorem not_three_dvd_index_weylX_E7 [Finite K] (h3 : 3 ∣ Nat.card K - 1) :
    ¬ 3 ∣ (weylX .E7 K modelHomE7.range).index := by
  have hq : 1 ≤ Nat.card K := Nat.card_pos
  have hq3 := mod_eq_one_of_dvd_sub_one (by norm_num) hq h3
  have hq1 : (Nat.card K : ZMod 3) = 1 := cast_eq_one_of_dvd_sub_one hq h3
  have hG3 := geomSum_three_mod hq3
  have hG9 := geomSum_nine_mod hq3
  have hG34 := geomSum_three_four_mod hq3
  have hm3 := cast_div_eq (p := 3) (c := 1) (by norm_num) (by norm_num) hG3
  have hm34 := cast_div_eq (p := 3) (c := 1) (by norm_num) (by norm_num) hG34
  have hm9 := cast_div_nine_eq hG9
  have hGm3 : geomSum 3 1 (Nat.card K) = 3 * (geomSum 3 1 (Nat.card K) / 3) := by omega
  have hGm34 : geomSum 3 4 (Nat.card K) = 3 * (geomSum 3 4 (Nat.card K) / 3) := by omega
  have hGm9 : geomSum 9 1 (Nat.card K) = 9 * (geomSum 9 1 (Nat.card K) / 9) := by omega
  set M := Nat.card K ^ 63 * (geomSum 2 1 (Nat.card K) * (geomSum 3 1 (Nat.card K) / 3) *
      geomSum 4 1 (Nat.card K) * geomSum 5 1 (Nat.card K) *
      (geomSum 2 3 (Nat.card K) * geomSum 8 1 (Nat.card K)) *
      ((geomSum 9 1 (Nat.card K) / 9) * (geomSum 3 4 (Nat.card K) / 3)) *
      (geomSum 2 5 (Nat.card K) * geomSum 2 9 (Nat.card K) * geomSum 14 1 (Nat.card K))) with hM
  have hC : Nat.card (adjointGroup .E7 K) =
      Nat.card modelHomE7.range * Nat.card (torusGroup .E7 K) * M := by
    rw [card_adjointGroup_E7_eq_torus_mul, prodE7, card_range_modelHomE7, hM]
    nth_rewrite 1 [hGm3]
    nth_rewrite 1 [hGm9]
    nth_rewrite 1 [hGm34]
    ring
  rw [index_weylX_eq hC]
  apply not_dvd_of_cast_ne_zero
  rw [hM]
  push_cast
  simp only [hq1, hm3, hm34, hm9, geomSum_cast hq1, one_pow, Nat.cast_one]
  decide

theorem ggExcToralRankInput_E7_three_of_dvd [Finite K] (h3 : 3 ∣ Nat.card K - 1) :
    GGExcToralRankInput .E7 K 3 :=
  ggExcToralRankInput_of_noOffender Nat.prime_three h3
    (isUnit_det_cartan_of_eq Nat.prime_three det_cartan_E7 (by norm_num))
    (card_torusPow_E7_three h3) cartan_symm_E7 (not_three_dvd_index_weylX_E7 h3)
    noOffender_E7

theorem ggExcToralRankInput_E8_three_of_dvd [Finite K] (h3 : 3 ∣ Nat.card K - 1) :
    GGExcToralRankInput .E8 K 3 :=
  ggExcToralRankInput_of_noOffender Nat.prime_three h3
    (isUnit_det_cartan_of_eq Nat.prime_three det_cartan_E8 (by norm_num))
    (card_torusPow_E8_of_dvd Nat.prime_three h3) cartan_symm_E8 (not_three_dvd_index_E8 h3)
    noOffender_E8

end T

end CFSG.LocalAnalysis.GLTheoremA.S267.BadExc
