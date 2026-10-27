module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Asc77.AscR10Sy
public import CFSG.ClassicalInvolution.Asc77.AscT3Basic
public import CFSG.ClassicalInvolution.Asc77.AscT3TypedG2Gen
public import CFSG.ClassicalInvolution.Uniform.UTwinSolv
public import Certificates.Data.ExceptionalSL3

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3MT

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3Typed CFSG.ClassicalInvolution.Uniform
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.RouteD
  CFSG.LieType.Universal CFSG.ClassicalInvolution.ModelFacts
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open scoped MatrixGroups commutatorElement



@[expose] def StdDich3Lin (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n : ℕ) : Prop :=
  ∀ R₁ ∈ ModelFacts.longestFundamental (Generic.modelUniv t n 3 1 Nat.prime_three).D,
  ∀ R₂ ∈ ModelFacts.longestFundamental (Generic.modelUniv t n 3 1 Nat.prime_three).D,
  ∀ c₁ c₂ : (Generic.modelUniv t n 3 1 Nat.prime_three).K, c₁ ∈ R₁ → c₂ ∈ R₂ →
    orderOf c₁ = 2 → orderOf c₂ = 2 → c₁ * c₂ = c₂ * c₁ →
      R₁ = R₂ ∨ Commutes R₁ R₂ ∨ ∃ W, LinearBlockStandardPair (GaloisField 3 1) W R₁ R₂

@[expose] def StdDich3Triv (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n : ℕ) : Prop :=
  ∀ R₁ ∈ ModelFacts.longestFundamental (Generic.modelUniv t n 3 1 Nat.prime_three).D,
  ∀ R₂ ∈ ModelFacts.longestFundamental (Generic.modelUniv t n 3 1 Nat.prime_three).D,
  ∀ c₁ c₂ : (Generic.modelUniv t n 3 1 Nat.prime_three).K, c₁ ∈ R₁ → c₂ ∈ R₂ →
    orderOf c₁ = 2 → orderOf c₂ = 2 → c₁ * c₂ = c₂ * c₁ → R₁ = R₂ ∨ Commutes R₁ R₂

theorem stdDich3Lin_psl {n : ℕ} (hadm : StatedLieAdmissible .PSL n 3 1) :
    StdDich3Lin .PSL n := by
  intro R₁ hR₁ R₂ hR₂ c₁ c₂ hc₁ hc₂ ho₁ ho₂ hc
  have hn : 2 ≤ n := hadm.2.2.1
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hodd : Odd (Nat.card (GaloisField 3 1)) := by
    rw [GaloisField.card 3 1 (by norm_num)]; decide
  have h2 : (2 : GaloisField 3 1) ≠ 0 := ModelFacts.two_ne_zero_galoisField 1 (by norm_num)
  obtain ⟨i₁, hi₁⟩ : R₁ ∈ longRootSet (K := GaloisField 3 1) hn :=
    fundamentalSubgroups_psl_subset hn (longestFundamental_subset .PSL _ hR₁)
  obtain ⟨i₂, hi₂⟩ : R₂ ∈ longRootSet (K := GaloisField 3 1) hn :=
    fundamentalSubgroups_psl_subset hn (longestFundamental_subset .PSL _ hR₂)
  have e₁ : c₁ = i₁ := (hi₁.isClassicalSL2 h2).eq_of_orderOf_eq_two hodd hc₁ ho₁
  have e₂ : c₂ = i₂ := (hi₂.isClassicalSL2 h2).eq_of_orderOf_eq_two hodd hc₂ ho₂
  subst e₁ e₂
  by_cases hn3 : 3 ≤ m + 1
  · by_cases hne : c₁ = c₂
    · exact Or.inl (by rw [hi₁.eq_longRootGroup h2, hi₂.eq_longRootGroup h2, hne])
    · rcases commute_or_linearBlockStandardPair h2 hn3 hi₁ hi₂ hc hne with h | ⟨-, h⟩
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨_, h⟩)
  · obtain rfl : m = 1 := by omega
    have k₁ := longRootSet_two_subset (F := GaloisField 3 1) hn ⟨_, hi₁⟩
    have k₂ := longRootSet_two_subset (F := GaloisField 3 1) hn ⟨_, hi₂⟩
    exact Or.inl ((Set.mem_singleton_iff.mp k₁).trans (Set.mem_singleton_iff.mp k₂).symm)

section Symplectic

open CFSG.ClassicalInvolution.Models.SymplecticPairs (IsHyperbolicPlane planeGroup IsLongRootSp2
  exists_isLongRootSp2_iff)

theorem stdDich3Triv_psp {n : ℕ} (hadm : StatedLieAdmissible .PSp n 3 1) :
    StdDich3Triv .PSp n := by
  intro R₁ hR₁ R₂ hR₂ c₁ c₂ hc₁ hc₂ ho₁ ho₂ hc
  have hodd : Odd (Nat.card (GaloisField 3 1)) := by
    rw [GaloisField.card 3 1 (by norm_num)]; decide
  have h2 : (2 : GaloisField 3 1) ≠ 0 := ModelFacts.two_ne_zero_galoisField 1 (by norm_num)
  have hmem : ∀ R ∈ longestFundamental (Generic.modelUniv .PSp n 3 1 Nat.prime_three).D,
      ∃ P, IsHyperbolicPlane P ∧ R = planeGroup P := fun R hR => by
    have := longestFundamental_subset .PSp _ hR
    rw [fundamentalSubgroups_psp_eq hadm] at this
    exact this
  obtain ⟨P₁, hP₁, rfl⟩ := hmem R₁ hR₁
  obtain ⟨P₂, hP₂, rfl⟩ := hmem R₂ hR₂
  obtain ⟨i₁, hi₁⟩ := (exists_isLongRootSp2_iff h2 _).mpr ⟨P₁, hP₁, rfl⟩
  obtain ⟨i₂, hi₂⟩ := (exists_isLongRootSp2_iff h2 _).mpr ⟨P₂, hP₂, rfl⟩
  have e₁ : c₁ = i₁ := hi₁.eq_of_orderOf_eq_two h2 hc₁ ho₁
  have e₂ : c₂ = i₂ := hi₂.eq_of_orderOf_eq_two h2 hc₂ ho₂
  subst e₁ e₂
  by_cases hne : c₁ = c₂
  · exact Or.inl (by rw [hi₁.eq_longRootGroup h2, hi₂.eq_longRootGroup h2, hne])
  · exact Or.inr (hi₁.commute_of_commute h2 hi₂ hc hne)

end Symplectic

end CFSG.ClassicalInvolution.Q3.Q3MT
