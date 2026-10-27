module

public import CFSG.GH74.Generic.BProg.B2.GenLocU4SuCaseA
public import CFSG.GH74.Generic.BProg.B2.GenLocU4SuCaseB

public section

namespace CFSG.GH74.Generic.BProg.B2.GenLocU4Su

open Matrix CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models
  CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary CFSG.LieType.BorelTits
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem exists_sqrt_neg_one (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) :
    ∃ ι : K, ι * ι = -1 ∧
      (unitaryInvolution K p f ι = ι ∨ unitaryInvolution K p f ι = -ι) := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨ω, hω⟩ : ∃ ω : K, ω * ω = -1 := by
    have hsq : IsSquare (-1 : K) := by
      rw [FiniteField.isSquare_neg_one_iff, ← Nat.card_eq_fintype_card, hK]
      have hodd : Odd (p ^ f) := (Fact.out (p := p.Prime)).odd_of_ne_two hp |>.pow
      obtain ⟨k, hk⟩ := hodd
      rw [hk]
      ring_nf
      omega
    obtain ⟨ω, hω⟩ := hsq
    exact ⟨ω, hω.symm⟩
  have hσω2 : unitaryInvolution K p f ω * unitaryInvolution K p f ω = -1 := by
    rw [← map_mul, hω, map_neg, map_one]
  refine ⟨ω, hω, ?_⟩
  have : (unitaryInvolution K p f ω - ω) * (unitaryInvolution K p f ω + ω) = 0 := by
    linear_combination hσω2 - hω
  rcases mul_eq_zero.mp this with h | h
  · left
    linear_combination h
  · right
    linear_combination h

theorem su4_core (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (A A' : Su K p f 2) (hA : suMat A * suMat A = -1) (hA' : suMat A' * suMat A' = -1) :
    Subgroup.centralizer ({xU K p f} : Set (Su K p f 4)) ⊔
      Subgroup.centralizer ({phiU K p f (A, A')} : Set (Su K p f 4)) ⊔
      Subgroup.centralizer ({xU K p f * phiU K p f (A, A')} : Set (Su K p f 4)) = ⊤ := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_charP_ne_two (K := K) hp
  obtain ⟨ι, hι, hcase⟩ := exists_sqrt_neg_one hK hp
  rcases hcase with h | h
  · exact su4_caseB hK h2 hι h A A' hA hA'
  · exact su4_caseA hK (by omega) h2 hι h A A' hA hA'

end CFSG.GH74.Generic.BProg.B2.GenLocU4Su
