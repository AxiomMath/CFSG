module

public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.Chev2
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.ClassicalRankOne
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.SLCore
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.FormFamilies
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.D4

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ

open CFSG.Open CFSG.LieType.BorelTits

set_option linter.unusedSectionVars false

section Classical


theorem radRigid_classical (S : Type) [Group S] [Finite S] (hs : IsSimpleGroup S)
    (t : StatedLieTag) (n f : ℕ) (ht : ClassicalTagTwo t) (h : StatedClassicalModel S t n 2 f)
    (hBT : HoldsTits S 2) : RadRigid 2 S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases ht with rfl | rfl | rfl | rfl | rfl
  ·
    obtain ⟨-, hf1, hn2, hne2, hne3⟩ := h.1
    by_cases hn : n = 2
    · subst hn
      exact radRigid_of_fusionIsBenderGroup hs hBT (fusionIsBenderGroup_of_statedPSL_two h)
    · have hn3 : 3 ≤ n := by omega
      obtain ⟨-, K, hKf, hKfin, hcard, ⟨e⟩⟩ := h
      haveI : CharP K 2 := charP_of_natCard_eq (p := 2) (f := f) hcard
      exact (radRigid_PSL n rigidSLCore hn3).of_mulEquiv e.symm
  ·
    obtain ⟨-, hf1, hn3, hne⟩ := h.1
    by_cases hn : n = 3
    · subst hn
      exact radRigid_of_fusionIsBenderGroup hs hBT (fusionIsBenderGroup_of_statedPSU_three h)
    · have hn4 : 4 ≤ n := by omega
      obtain ⟨-, K, hKf, hKfin, hcard, ⟨e⟩⟩ := h
      haveI : CharP K 2 := charP_of_natCard_eq (p := 2) (f := f * 2) (by rw [hcard, pow_mul])
      exact (radRigid_PSU K f hcard n hn4).of_mulEquiv e.symm
  ·
    obtain ⟨-, hf1, hn2, hne⟩ := h.1
    obtain ⟨-, K, hKf, hKfin, hcard, ⟨e⟩⟩ := h
    haveI : CharP K 2 := charP_of_natCard_eq (p := 2) (f := f) hcard
    have hF : 4 ≤ Nat.card K ∨ 3 ≤ n := by
      by_cases h3 : 3 ≤ n
      · exact Or.inr h3
      · left
        obtain rfl : n = 2 := by omega
        have hf2 : 2 ≤ f := by
          by_contra hlt
          obtain rfl : f = 1 := by omega
          exact hne (by simp)
        rw [hcard]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
    exact (radRigid_PSp K n hn2 hF).of_mulEquiv e.symm
  ·
    obtain ⟨-, hf1, hn4⟩ := h.1
    obtain ⟨-, K, hKf, hKfin, hcard, ⟨e⟩⟩ := h
    haveI : CharP K 2 := charP_of_natCard_eq (p := 2) (f := f) hcard
    by_cases hn : n = 4
    · subst hn
      exact (radRigid_POmegaPlus_four (F := K)).of_mulEquiv e.symm
    · exact (radRigid_POmegaPlus K n (by omega)).of_mulEquiv e.symm
  ·
    obtain ⟨-, hf1, hn4⟩ := h.1
    obtain ⟨-, K, hKf, hKfin, hcard, b, c, hirr, ⟨e⟩⟩ := h
    haveI : CharP K 2 := charP_of_natCard_eq (p := 2) (f := f) hcard
    exact (radRigid_POmegaMinus K n hn4 b c hirr).of_mulEquiv e.symm

end Classical

end CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ
