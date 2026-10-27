module

import CFSG.LocalAnalysis.ComponentClassification.StandardSubgroupAPI
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitInputs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Monster.B.TwoA.Census.PermClasses
public import CFSG.Open.StandardComponentRecognitionMilestoneDefs

public section

namespace CFSG.OddStandard

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

section Standard

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem exists_involution_of_standard (hL : standardComponentIsStandard L) :
    ∃ t : G, t ∈ centralizer (L : Set G) ∧ orderOf t = 2 :=
  hL.exists_involution_centralizer

theorem even_card_of_standard (hL : standardComponentIsStandard L) : Even (Nat.card L) := by
  have hq : CFSG.IsQuasisimple L :=
    (ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mp hL.1
  obtain ⟨-, hs, hnab⟩ := hq
  have heven := (ComponentClassification.SimpleEvenOrder.nonabelian_simple_even hnab).1
  obtain ⟨k, hk⟩ := Subgroup.card_quotient_dvd_card (center L)
  rw [hk]
  exact heven.mul_right k

theorem quotient_pPrimeCore_equiv_he (hL : standardComponentIsStandard L) (hZ : center L = ⊥)
    (hHe : IsSporadic (L ⧸ center L) .He) :
    Nonempty (L ⧸ CFSG.pPrimeCore 2 L ≃* NativeSporadic.He) := by
  obtain ⟨e⟩ : Nonempty ((L ⧸ center L) ≃* NativeSporadic.He) := hHe
  obtain ⟨-, hs⟩ := hL.1
  let eL : L ⧸ center L ≃* L :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have : IsSimpleGroup L := eL.symm.isSimpleGroup
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hbot : CFSG.pPrimeCore 2 L = ⊥ := by
    refine (IsSimpleGroup.eq_bot_or_eq_top_of_normal (CFSG.pPrimeCore 2 L)).resolve_right
      fun htop => ?_
    have hodd : Odd (Nat.card (CFSG.pPrimeCore 2 L)) :=
      Nat.coprime_two_left.1 CFSG.pPrimeCore_coprime_card
    rw [htop, Subgroup.card_top] at hodd
    exact (Nat.not_even_iff_odd.2 hodd) (even_card_of_standard hL)
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hbot).trans
    (QuotientGroup.quotientBot.trans (eL.symm.trans e))⟩

end Standard

section Balanced

variable {G : Type} [Group G] [Finite G]

theorem wGroup_eq_bot_of_balanced
    (hbal : ∀ z : G, orderOf z = 2 → CFSG.oddCore (centralizer ({z} : Set G)) = ⊥)
    (A : Subgroup G) : ComponentClassification.GrSLit.wGroup A = ⊥ := by
  refine le_bot_iff.1 (iSup_le fun B => iSup_le fun _ => iSup_le fun h4 => iSup_le fun h2 => ?_)
  have : Nontrivial B := Finite.one_lt_card_iff_nontrivial.1 (by omega)
  obtain ⟨⟨b, hbB⟩, hb1⟩ := exists_ne (1 : B)
  have hb1' : b ≠ 1 := fun h => hb1 (Subtype.ext h)
  have hb : orderOf b = 2 := orderOf_eq_prime (by rw [sq]; exact h2 b hbB) hb1'
  have hcore : CFSG.pPrimeCore 2 (centralizer ({b} : Set G)) = ⊥ := by
    rw [CFSG.pPrimeCore_eq_piCore, ← CFSG.oddCore_eq_piCore]
    exact hbal b hb
  refine (iInf_le_of_le b (iInf_le_of_le hbB (iInf_le_of_le hb1' le_rfl))).trans ?_
  rw [hcore, Subgroup.map_bot]

theorem locallyTwoBalanced_of_balanced
    (hbal : ∀ z : G, orderOf z = 2 → CFSG.oddCore (centralizer ({z} : Set G)) = ⊥) :
    ComponentClassification.GrSLit.LocallyTwoBalanced G := by
  intro J _ a _ _ E _ _
  rw [wGroup_eq_bot_of_balanced hbal E, bot_inf_eq, Subgroup.commutator_bot_right]
  exact bot_le

end Balanced

end CFSG.OddStandard
