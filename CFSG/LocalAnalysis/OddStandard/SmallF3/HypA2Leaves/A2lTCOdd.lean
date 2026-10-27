module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lTCBasic
public import CFSG.LocalAnalysis.ComponentClassification.GS82PumpP1Defs

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open Subgroup CFSG.Blueprint CFSG.ComponentClassification CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.GS82PumpInputs
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem a2l_odd_arm (hGLS : GLS3OddLieAutComponentsInput) (hO : LieOrderFormulasInput)
    (hC : OddLieCharUnique) {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hq : FixedTwoComponentsQuasisimple S) (ho : OddLieType S) {σ : MulAut S} {P : Subgroup S}
    (h : ProperFixedComponent σ P) (hS : TCSmall (↥P ⧸ Open.fusionZStar ↥P)) :
    HarrisLit.IsSimpleChevalleyOver 3 S := by
  have hσ1 := h.ne_one
  have hσσ : σ * σ = 1 := MulEquiv.ext fun y => h.1 y
  have hσ2 : orderOf σ = 2 := orderOf_eq_prime (by rw [sq]; exact hσσ) hσ1
  have hqP : IsQuasisimple (P.subgroupOf (fixedSubgroup σ)) := hq σ hσσ hσ1 _ h.2.2.1
  obtain ⟨hcomp, ⟨eZ⟩⟩ := h.fusionZStar_equiv_of_quasisimple hqP
  obtain ⟨τ0, n0, f0, hY0⟩ : HarrisLit.IsSimpleChevalleyOver 3 (↥P ⧸ Open.fusionZStar ↥P) := by
    rcases hS with h | h | h
    · exact ⟨.PSL, 2, 2, h⟩
    · exact ⟨.PSU, 3, 1, h⟩
    · exact ⟨.PSp, 2, 1, h⟩
  obtain ⟨t, n, p, f, hp, hp2, hadm, hm⟩ := ho
  have hp3 : p = 3 := by
    rcases hGLS S t n p f hp hp2 hadm hm σ hσ2 _ hcomp with ⟨τ', n', f', -, hm'⟩ |
        ⟨-, -, -, h8⟩
    · exact hC _ τ' n' p f' τ0 n0 3 f0 hp2 (by norm_num) (LieModel.of_mulEquiv eZ.symm hm') hY0
    · exfalso
      have h504 : Nat.card (P.subgroupOf (fixedSubgroup σ)) = 504 := by
        obtain ⟨-, hord, -⟩ := hO _ .PSL 2 2 3 (LieModel.admissible h8) h8
        simp only [lieOrderNumerator, lieOrderDivisor] at hord
        norm_num [Finset.Icc_self] at hord
        omega
      have hdvd : Nat.card (↥P ⧸ Open.fusionZStar ↥P) ∣ 1008 := by
        rw [Nat.card_congr eZ.toEquiv]
        exact (Subgroup.card_quotient_dvd_card _).trans (by rw [h504]; norm_num)
      rcases a2l_card_tcSmall hS with hc | hc | hc <;> rw [hc] at hdvd <;>
        exact absurd hdvd (by decide)
  subst hp3
  exact ⟨t, n, f, hm⟩

end CFSG.OddStandard.SmallF3.HypA2Leaves
