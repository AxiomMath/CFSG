module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneOddStabilizerReduction
public import CFSG.LocalAnalysis.SeitzReduction.RankOneHallTwoArithCatalog

public section

namespace CFSG.SeitzReduction.RankOne

open Equiv MulAction CFSG.Assembly.LowTwoRank CFSG.Blueprint

theorem odd_stabilizer_two_transitive_catalog_of_dvd {Ω : Type} [Finite Ω]
    (N : Subgroup (Perm Ω))
    (h2 : ∀ a b c d : Ω, a ≠ b → c ≠ d → ∃ x ∈ N, x a = c ∧ x b = d)
    {n : ℕ} (hn : 1 ≤ n) (hΩ : Nat.card Ω = 2 ^ n) (α : Ω)
    (hodd : Odd (Nat.card ↥(N ⊓ stabilizer (Perm Ω) α)))
    (hdvd : Nat.card ↥(N ⊓ stabilizer (Perm Ω) α) ∣ (2 ^ n - 1) * n)
    (hcat : ∀ S : Subgroup (Perm Ω), S ≤ N → (S.subgroupOf N).Normal → IsSimpleGroup S →
      (∃ a b : S, a * b ≠ b * a) → Catalog S) :
    (∃ A : Subgroup (Perm Ω), A ≤ N ∧ (A.subgroupOf N).Normal ∧
        (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧ (∀ a ∈ A, a ^ 2 = 1) ∧ Nat.card A = 2 ^ n ∧
        ∀ β γ : Ω, ∃! a : A, (a : Perm Ω) β = γ) ∨
    (n = 3 ∧ Nat.card ↥(N ⊓ stabilizer (Perm Ω) α) = 21 ∧ Nat.card N = 168 ∧
      IsSimpleGroup N ∧ (∃ a b : N, a * b ≠ b * a) ∧ ⁅N, N⁆ = N ∧
      StatedClassicalModel N .PSL 3 2 1 ∧ LieModel N .PSL 3 2 1) := by
  rcases regular_or_simple_of_odd_stabilizer_of_dvd N h2 hn hΩ α hodd hdvd with hA |
    ⟨S, hSN, hSn, hs, hnab, -, h, hcard, hh, hhdvd⟩
  · exact Or.inl hA
  right
  obtain ⟨hmodel, rfl, rfl⟩ := catalog_hallTwoArith (hcat S hSN hSn hs hnab) hnab hcard hn hh hhdvd
  obtain ⟨rfl, h21, h168⟩ := eq_of_card_eq_168 (exists_apply_eq_of_two_transitive h2) hΩ α
    (by simpa using hdvd) hSN hcard
  exact ⟨rfl, h21, h168, hs, hnab, commutator_eq_self_of_isSimpleGroup_of_exists_mul_ne hs hnab,
    hmodel, Or.inl ⟨by decide, hmodel⟩⟩

end CFSG.SeitzReduction.RankOne
