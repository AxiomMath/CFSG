module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockFieldIndexOrthMinus
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockFieldIndexFiveLevi
import CFSG.Fischer.Classification.Recognition.PSU6

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.FieldIndexP

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbedding.LeviBlock CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
open CFSG.AGLEmbedding.ParabPrime (perfectJoin)
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.FieldIndex
open scoped commutatorElement

theorem orthMinus_blockOK_of_sq_memP (p : ℕ) [OddPrime p] {G : Type*} [Group G] {H S : Subgroup G}
    (hsq : ∀ g ∈ H, g ^ 2 ∈ S) : BlockOKP p H S := by
  intro g hg hn k hk
  left
  have hodd : Odd (p ^ k) := OddPrime.odd_pow p k
  obtain ⟨b, hb⟩ := hodd.add_one
  refine ⟨g ^ (p ^ k + 1), ?_, fun s hs => ?_⟩
  · rw [hb, ← two_mul, pow_mul]
    exact S.pow_mem (hsq g hg) b
  · have h1 := hk _ (hn s hs)
    calc g * s * g⁻¹ = g ^ p ^ k * (g * s * g⁻¹) * (g ^ p ^ k)⁻¹ := h1.symm
      _ = g ^ (p ^ k + 1) * s * (g ^ (p ^ k + 1))⁻¹ := by
        rw [pow_succ, mul_inv_rev]
        simp only [mul_assoc]

theorem orthMinus_blockOK_orthResDerP (p : ℕ) [OddPrime p] {K : Type} [Field K] [Finite K]
    [CharP K 2] {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (m : ℕ)
    (hq : CFSG.Open.IsQuasisimple ↥(orthResDer K b c m)) :
    BlockOKP p (TauCeti.QuadraticMap.orthogonalGroup (quadTail m (minusTailForm K b c)))
      (orthResDer K b c m) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact absurd hq (orthMinus_not_isQuasisimple_of_comm (comm_orthResDer_zero hirr))
  · exact orthMinus_blockOK_of_sq_memP p fun g hg => orthMinus_sq_mem_orthResDer hirr hm hg

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.FieldIndexP
