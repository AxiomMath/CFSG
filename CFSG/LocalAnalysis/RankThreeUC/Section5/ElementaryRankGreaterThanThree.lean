module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.CharacteristicPrimeCoreDetectingAction
public import CFSG.LinearAlgebra.CoprimeActions.BinaryMersennePrimeGreaterThanThree
public import CFSG.LinearAlgebra.CoprimeActions.SmallFaithfulTwoGroups

public section

namespace CFSG.LocalAnalysis.RankThreeUC.Section5.ElementaryRankGreaterThanThree

open CFSG.LocalAnalysis.RankThreeUC.Section5

theorem three_lt_pRank {p : ℕ} [hp : Fact p.Prime] {G : Type} [Group G] [Finite G]
    {P T B : Subgroup G} {e : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (h51 : OddPrimeClassTwoAction G p P T B e) (h53 : FaithfulBinaryIrreducibleAction G p P T B ρ)
    (hEA : CFSG.Open.IsElemAbelian p P) : 3 < CFSG.Open.pRank p P := by
  by_contra hle
  push Not at hle
  obtain ⟨q, hq, hq3, hqd⟩ :=
    CFSG.LinearAlgebra.CoprimeActions.BinaryMersennePrimeGreaterThanThree.exists_prime_gt_three e h51.two_lt
  have hqB : q ∈ piOf B := by
    rw [h51.pi_eq]; exact ⟨hq, hqd⟩
  obtain ⟨J, _, _, W, _, _, _, τ, f, ι, hτ, -, hdim, -, -, -, -, E, D, hE, hE2, hD, hED, -, -⟩ :=
    CharacteristicPrimeCoreDetectingAction.exists_detecting_action h51 h53 hEA hqB hq3
  have hp2 : p ≠ 2 := by
    have := h51.setting.odd
    rintro rfl
    exact absurd this (by decide)
  haveI : CharP (AlgebraicClosure (ZMod p)) p :=
    charP_of_injective_algebraMap (algebraMap (ZMod p) _).injective p
  have hF : (2 : AlgebraicClosure (ZMod p)) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : AlgebraicClosure (ZMod p)) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff _ p] at h'
    have := (Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 h'
    exact hp2 this
  exact CFSG.LinearAlgebra.CoprimeActions.SmallFaithfulTwoGroups.false_of_dim_le_three hF τ hτ
    (hdim ▸ hle) E D hE hE2 q hq hq3 hD hED

end CFSG.LocalAnalysis.RankThreeUC.Section5.ElementaryRankGreaterThanThree
