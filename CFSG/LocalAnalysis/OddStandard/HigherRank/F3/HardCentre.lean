module

public import CFSG.Models.Blueprint
public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.HardDefs

public section

namespace CFSG.OddStandard.HigherRank.F3

open CFSG
open Subgroup

private lemma generic_exceptional_mul_self (n : ℕ) (hn : n = 4 ∨ n = 6) :
    ∀ g : Blueprint.Multiplier.generic .POmegaPlus n 3 1 ×
        Blueprint.Multiplier.exceptional .POmegaPlus n 3 1, g * g = 1 := by
  rcases hn with rfl | rfl
  · change ∀ g : (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) ×
        (Multiplicative (ZMod 1) × Multiplicative (ZMod 1)), g * g = 1
    decide +kernel
  · change ∀ g : (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) ×
        (Multiplicative (ZMod 1) × Multiplicative (ZMod 1)), g * g = 1
    decide +kernel

theorem pOmegaPlusCentreExpTwo_of_griess (hGr : CFSG.Open.GriessAllModelsStatement) :
    POmegaPlusCentreExpTwo := by
  intro K _ _ hK n hn hm x hx
  haveI : Group.IsPerfect K := hK.1
  let e : K ⧸ center K ≃* K ⧸ center K := MulEquiv.refl _
  let q : K →* K ⧸ center K := CFSG.RankThree.PerfectCover.centralQuotientMap e
  have hq : Function.Surjective q := CFSG.RankThree.PerfectCover.centralQuotientMap_surjective e
  have hker : q.ker = center K := CFSG.RankThree.PerfectCover.centralQuotientMap_ker e
  have hkerle : q.ker ≤ center K := le_of_eq hker
  obtain ⟨-, ⟨φ⟩⟩ := hGr (K ⧸ center K) .POmegaPlus n 3 1
    (CFSG.Models.LieModel.of_blueprint (by decide) hm)
  let ψ : CFSG.RankThree.PerfectCover.hopfMultiplier (K ⧸ center K) ≃*
      Blueprint.Multiplier.generic .POmegaPlus n 3 1 ×
        Blueprint.Multiplier.exceptional .POmegaPlus n 3 1 :=
    (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess (K ⧸ center K)).symm.trans φ
  have hsq : ∀ m : CFSG.RankThree.PerfectCover.hopfMultiplier (K ⧸ center K), m * m = 1 := by
    intro m
    apply ψ.injective
    rw [map_mul, map_one]
    exact generic_exceptional_mul_self n hn (ψ m)
  obtain ⟨m, hm⟩ := CFSG.RankThree.PerfectCover.hopfMultiplierToKer_surjective q hq hkerle
    ⟨x, by rw [hker]; exact hx⟩
  have hxval : CFSG.RankThree.PerfectCover.hopfLift q hq hkerle m = x := by
    have h := congrArg Subtype.val hm
    rwa [CFSG.RankThree.PerfectCover.hopfMultiplierToKer_apply] at h
  have hmm : (↑m * ↑m : CFSG.RankThree.PerfectCover.HopfCover (K ⧸ center K)) = 1 := by
    rw [← Subgroup.coe_mul, hsq m]
    rfl
  calc x * x = CFSG.RankThree.PerfectCover.hopfLift q hq hkerle m *
        CFSG.RankThree.PerfectCover.hopfLift q hq hkerle m := by rw [hxval]
    _ = CFSG.RankThree.PerfectCover.hopfLift q hq hkerle (m * m) := by rw [map_mul]
    _ = 1 := by rw [hmm, map_one]

end CFSG.OddStandard.HigherRank.F3
