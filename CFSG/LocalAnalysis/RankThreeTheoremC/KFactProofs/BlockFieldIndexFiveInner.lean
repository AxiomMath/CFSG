module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockFieldIndexTypes
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticPerfectCoverOuterPrime
public import CFSG.RankThree.PartOne.S11d.OutAbstract

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.FieldIndexP

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbedding.ParabPrime
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockFieldIndex
open CFSG.RankThree.PartOne.OutStructure (Inn)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open scoped commutatorElement

section OutFacts

theorem inn_statedProj_sp_two {K : Type} [Field K] [Finite K] {r : ℕ} (hr : 3 ≤ r)
    (hK : Nat.card K = 2) (β : MulAut (StatedProj (StatedSp r K))) :
    β ∈ Inn (StatedProj (StatedSp r K)) := by
  have : NeZero r := ⟨by omega⟩
  have : Fintype K := Fintype.ofFinite K
  have hchar : CharP K 2 := charP_of_card_eq_prime_pow (f := 1) (by
    rw [← Nat.card_eq_fintype_card, hK, pow_one])
  obtain ⟨A, σ, hβ⟩ := (automorphism_generation (K := K) hr).2 β
  have hσ : σ = 1 := by
    refine RingEquiv.ext fun x => ?_
    obtain ⟨y, hy, huniq⟩ := (Nat.card_eq_two_iff' (0 : K)).1 hK
    by_cases hx : x = 0
    · rw [hx]
      exact map_zero σ
    · have h1 : x = y := huniq x hx
      have h2 : (1 : K) = y := huniq 1 one_ne_zero
      rw [h1, ← h2]
      exact map_one σ
  rw [hβ, hσ, map_one, mul_one]
  exact conjAut_mem_inner_of_isSquare
    (FiniteField.isSquare_of_char_two (ringChar.eq K 2) (multiplier r K A : K))

end OutFacts

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.FieldIndexP
