module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthPlusLink
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockFieldIndexFiveAbstract
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.FieldIndexP

open Matrix CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbedding.LeviBlock
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.FieldIndex
open CFSG.AGLEmbedding.ParabPrime (perfectJoin)
open CFSG.RankThree.PartOne.OutStructure (OutPNice Inn)
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (flagStabilizer)

theorem outPNiceP_of_index_two (p : ℕ) [OddPrime p] {X : Type*} [Group X]
    (h : (Inn X).index = 2) : OutPNice p X := by
  refine ⟨⊤, ⊤, le_top, fun δ _ k hk => ?_, fun _ _ => Subgroup.mem_top _,
    fun _ _ _ => Subgroup.mem_top _, fun _ _ _ _ _ _ => Or.inl ⟨0, Subgroup.mem_top _⟩⟩
  have h2 : δ ^ 2 ∈ Inn X := h ▸ Subgroup.pow_index_mem (Inn X) δ
  obtain ⟨m, hm⟩ : Odd (p ^ k) := OddPrime.odd_pow p k
  have hδ : δ = ((δ ^ 2) ^ m)⁻¹ * δ ^ (p ^ k) := by
    rw [hm, ← pow_mul, pow_succ, ← mul_assoc, inv_mul_cancel, one_mul]
  rw [hδ]
  exact (Inn X).mul_mem ((Inn X).inv_mem ((Inn X).pow_mem h2 m)) hk

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.FieldIndexP
