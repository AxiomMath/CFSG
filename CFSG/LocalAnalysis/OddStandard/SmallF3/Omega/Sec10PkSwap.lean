module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10PkTA

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint CFSG.GH74.KGroups CFSG.Sporadic.Schreier
  CFSG.ComponentClassification.CatFactsSmall.PSp43 CFSG.ClassicalInvolution.Q3.TA3.Check

local notation "P45" => Equiv.Perm (Fin 45)

local notation "SL23" => Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)

namespace Pk

theorem odd_orderOf_of_pow_three {x : P45} (h : x ^ 3 = 1) : Odd (orderOf x) :=
  Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one h)

theorem oTwoRes_Cs :
    oTwoRes Cs = KA ⊔ KB := by
  apply le_antisymm
  · rw [oTwoRes, Subgroup.closure_le]
    rintro x ⟨hx, ho⟩
    exact odd_mem_E hx ho
  · have hA := sl23_facts isSL23Mod_KA
      (oddCore_eq_bot_of_subnormal KA_le noOdd_Cs subnormal_KA)
    have hB := sl23_facts sl23Pocket_KB.2.2.2
      (oddCore_eq_bot_of_subnormal KB_le noOdd_Cs sl23Pocket_KB.2.2.1)
    exact sup_le
      (hA.2 _ fun x hx hx3 => Subgroup.subset_closure ⟨KA_le hx, odd_orderOf_of_pow_three hx3⟩)
      (hB.2 _ fun x hx hx3 => Subgroup.subset_closure ⟨KB_le hx, odd_orderOf_of_pow_three hx3⟩)

theorem conjugate_KA_eq {x : P45}
    (hx : x ∈ Cs) (hE : x ∉ KA ⊔ KB) : CFSG.conjugate KA x = KB := by
  have hnot : ¬ ∃ A B : SL23, rhoF A * Certificates.OmegaPk.cj gz (rhoF B) = x :=
    fun h => hE (mem_E_iff.2 h)
  have h1 : ∀ A : SL23, ∃ B : SL23, Certificates.OmegaPk.cj gz (rhoF B) = x⁻¹ * rhoF A * x :=
    (facts.e.2.1 x hx hnot).1
  refine Subgroup.eq_of_le_of_card_ge (fun y hy => ?_) ?_
  · rw [mem_conjugate_iff'] at hy
    obtain ⟨A, hA⟩ := mem_KA.1 hy
    obtain ⟨B, hB⟩ := h1 A
    refine mem_KB.2 ⟨B, ?_⟩
    rw [hB, hA]
    group
  · rw [card_KB, CFSG.conjugate,
      Subgroup.card_map_of_injective (MulAut.conj x⁻¹).injective, card_KA]

theorem commutator_KAB : ⁅KA, KB⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro a ha
  exact Subgroup.mem_centralizer_iff.2 fun b hb => (comm_KAB ha hb).symm

end Pk

end CFSG.OddStandard.SmallF3.Omega
