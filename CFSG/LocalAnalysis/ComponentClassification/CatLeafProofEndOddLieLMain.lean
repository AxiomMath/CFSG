module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEndOddLieLPsl
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEndOddLieLPsu
public import Certificates.Kernel.ThCent.Leaves

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof.EndOddLin

open CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification.CatLeafProof.EndOddCore

theorem endOddLieInputFor_PSL_PSU : Sol78.F514.EndOddLieInputFor {.PSL, .PSU} := by
  refine endOddLieInputFor_of_config {.PSL, .PSU} ?_
  intro X _ _ _ τ n p f hτ hp hp2 hadm hmod z L D h
  rw [Finset.mem_insert, Finset.mem_singleton] at hτ
  rcases hτ with rfl | rfl
  ·
    obtain ⟨K, _, _, hKc, ⟨θ⟩⟩ :=
      LocalAnalysis.ComponentInitial.LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hmod
    have hn : 2 ≤ n := hadm.2.2.1
    have : Fintype K := Fintype.ofFinite K
    have : Fact p.Prime := ⟨hp⟩
    have : CharP K p := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
    have hK : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
    exact false_of_config_psl hK hn (h.map θ)
  ·
    rcases hmod with ⟨-, hc⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩
    · obtain ⟨⟨hp', hf, hn, -⟩, K, _, _, hKc, ⟨θ⟩⟩ := hc
      have hu : UnitaryFieldData p f K := ⟨hp', hf, by rw [hKc, ← pow_mul, mul_comm]⟩
      exact false_of_config_psu hu hp2 hn (h.map θ)
    · exact absurd htag (by decide)
    · exact absurd htag (by decide)
    · exact absurd htag (by decide)

end CFSG.ComponentClassification.CatLeafProof.EndOddLin
