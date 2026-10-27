module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD1912Core
public import CFSG.HardMathSupport.Dickson.Bal207.LocalBalClassicalOrthTwoProj
public import CFSG.HardMathSupport.Dickson.Bal207.LocalBalD4Eight
public import CFSG.LieType.ChevTwo.OutDataOrth
public import CFSG.GroupTheory.CenterlessInnerCentralizer

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD1912

open CFSG.Open
open CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
open CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
open CFSG.LieType.Universal.Spin
open CFSG.RankThree.Classical2
open Module

section Certificates

theorem outTwoNilpConcl_matrixProjectiveDerived_four {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) :
    CFSG.LieType.ChevTwo.OutTwoNilpConcl (matrixProjectiveDerived (coordinateQuadPlus 4 K)) := by
  have hmodel : StatedClassicalModel (matrixProjectiveDerived (coordinateQuadPlus 4 K))
      .POmegaPlus 4 2 1 := by
    refine ⟨⟨Nat.prime_two, le_rfl, by norm_num⟩, K, inferInstance, inferInstance, ?_, ?_⟩
    · simpa using hK
    · exact ⟨(statedProjectiveReindexEquiv (plusIndexEquiv 4) (quadPlus 4 K)
        (coe_quadPlus 4 K)).symm⟩
  exact CFSG.Quasithin.H13.OutTwoNilp.outTwoNilpotent_of_twoNilpotent_outer
    (CFSG.LieType.ChevTwo.twoNilpotent_outer_of_POmegaPlus_four hmodel)

theorem gLAPPrimeCoreOf_fixSub_matrixProjectiveDerived_four_eq_bot {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = 2)
    {x : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K))} (hx3 : x ^ 3 = 1)
    (hx1 : x ≠ 1) : GLAPPrimeCoreOf 3 (fixSub x) = ⊥ := by
  haveI : CharP K 2 := CFSG.HardMathSupport.Dickson.Bal207.OrthRow.Two.charP_two hK
  have hd : 0 < 2 * 4 := by norm_num
  obtain ⟨hQ, hT⟩ := regular_coordinateQuadPlus 4 K (by norm_num)
  have hpar : CFSG.GroupTheory.WeirSylow.IsPlusType (coordinateQuadPlus 4 K) ↔
      Even (finrank K (Fin (2 * 4) → K) / 2) :=
    iff_of_true
      ((CFSG.GroupTheory.WeirSylow.isPlusType_congr (coordinatePlusIsometry 4 K)).1
        (CFSG.GroupTheory.WeirSylow.isPlusType_quadPlus K 4))
      (by rw [Module.finrank_fin_fun]; decide)
  let φ := CFSG.RankThree.PartOne.KCOrthogonalAut.coordBridge (coordinateQuadPlus 4 K) hd
  have hE : ∀ g : MulAut (ProjOrthDerived (coordinateQuadPlus 4 K)),
      Nat.Coprime 3 (orderOf g) →
        ∃ β : MulAut (ProjOrthDerived (coordinateQuadPlus 4 K)),
          MulAut.congr φ.symm (β⁻¹ * g * β) ∈
            matrixProjectiveImage (coordinateQuadPlus 4 K) := by
    intro g hg
    obtain ⟨β₀, hβ₀⟩ :=
      CFSG.HardMathSupport.Dickson.Bal207.exists_conj_mem_matrixProjectiveImage_four
        (K := K) (g := MulAut.congr φ.symm g) (by rwa [MulEquiv.orderOf_eq])
    refine ⟨MulAut.congr φ β₀, ?_⟩
    rwa [map_mul, map_mul, map_inv,
      CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.congr_symm_congr]
  have hcore : NoNormalCop 3 (fixSub x) := by
    by_cases hxE : x ∈ matrixProjectiveImage (coordinateQuadPlus 4 K)
    · exact (CFSG.HardMathSupport.Dickson.Bal207.OrthRow.Two.coreFreeAt_of_mem_matrixProjectiveImage
        hK hd hQ hT hpar (by norm_num) hE hxE hx3 hx1).1
    · exact (CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.d4TrialityCoreFree_holds
        K (by rw [hK]; decide) x hx3 hxE).1
  exact CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.core_eq_bot_of_noNormalPPrime
    Nat.prime_three hcore

theorem oddCoreFact_three_matrixProjectiveDerived_four {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) :
    OddCoreFact 3 (matrixProjectiveDerived (coordinateQuadPlus 4 K)) := by
  have hd : 0 < 2 * 4 := by norm_num
  obtain ⟨hQ, hT⟩ := regular_coordinateQuadPlus 4 K (by norm_num)
  have hZ : Subgroup.center (matrixProjectiveDerived (coordinateQuadPlus 4 K)) = ⊥ :=
    CFSG.RankThree.PartOne.KCOrthogonalSubfield.center_matrix_eq_bot
      (Q' := coordinateQuadPlus 4 K) hd hQ hT
  refine ⟨outTwoNilpConcl_matrixProjectiveDerived_four hK, fun x hx => ?_⟩
  have hx3 : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hx
    omega
  have hbot : GLAPPrimeCoreOf 3 (fixSub x) = ⊥ :=
    gLAPPrimeCoreOf_fixSub_matrixProjectiveDerived_four_eq_bot hK hx3 hx1
  rw [CFSG.odd_card_gLAPPrimeCoreOf_innerAut_inf_centralizer_iff hZ 3 x]
  change Odd (Nat.card (GLAPPrimeCoreOf 3 (fixSub x)))
  rw [hbot, Subgroup.card_bot]
  exact odd_one

end Certificates

theorem oddCoreFact_three_of_D4_two
    {S : Type} [Group S] [Finite S]
    (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.D 4 q).Valid) (hq : q.card = 2)
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.D 4 q, hv⟩).Group) :
    OddCoreFact 3 S := by
  have hp : q.p = 2 := by
    have h1 : q.p ∣ q.p ^ q.exponent := dvd_pow_self q.p q.exponent_pos.ne'
    rw [← TauCeti.PrimePower.card_def, hq] at h1
    exact (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).1 h1
  have he : q.exponent = 1 := by
    have h2 : 2 ^ q.exponent = 2 ^ 1 := by
      have h3 := hq
      rw [TauCeti.PrimePower.card_def, hp] at h3
      rw [h3]
      norm_num
    exact Nat.pow_right_injective (le_refl 2) h2
  have hm := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD 4 q hv e
  rw [hp, he] at hm
  obtain ⟨-, K, _, _, hK, ⟨eK⟩⟩ := hm
  have hK2 : Nat.card K = 2 := by rw [hK]; norm_num
  have eT : S ≃* matrixProjectiveDerived (coordinateQuadPlus 4 K) :=
    coordinatePlusWitnessEquiv K eK
  exact (oddCoreFact_congr (p := 3) eT).mpr
    (oddCoreFact_three_matrixProjectiveDerived_four hK2)

end CFSG.LocalAnalysis.GLTheoremA.KD1912
