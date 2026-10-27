module

public import CFSG.ClassicalInvolution.Generic.Induction

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

variable (p : ℕ) [Fact p.Prime]

@[expose] def S26Aut164L : Prop :=
  ∀ (e : ℕ), StatedLieAdmissible .PSL 3 p e → p ^ e % 4 = 3 →
    ∀ (Y : Type) [Group Y] (ψ : (modelUniv .PSL 3 p e Fact.out).K →* Y),
      ψ.ker ≤ Subgroup.center (modelUniv .PSL 3 p e Fact.out).K → Function.Surjective ψ →
        ∀ R ∈ fundamentalSubgroups .PSL (modelUniv .PSL 3 p e Fact.out).D, ∀ s ∈ R, ∀ n : ℕ,
          1 ≤ n → orderOf (ψ s) = 2 ^ (n + 1) →
            ∀ β : MulAut Y, β (ψ s) = ψ s → β ^ 2 ^ (n + 1) = 1 →
              β ^ 2 ^ n = 1 ∨ β ^ 2 ^ n = MulAut.conj (ψ s ^ 2 ^ n)

@[expose] def S26Aut164U : Prop :=
  ∀ (e : ℕ), StatedLieAdmissible .PSU 3 p e → p ^ e % 4 = 1 →
    ∀ (Y : Type) [Group Y] (ψ : (modelUniv .PSU 3 p e Fact.out).K →* Y),
      ψ.ker ≤ Subgroup.center (modelUniv .PSU 3 p e Fact.out).K → Function.Surjective ψ →
        ∀ R ∈ fundamentalSubgroups .PSU (modelUniv .PSU 3 p e Fact.out).D, ∀ s ∈ R, ∀ n : ℕ,
          1 ≤ n → orderOf (ψ s) = 2 ^ (n + 1) →
            (Nat.card SL(2, GaloisField p e)).factorization 2 = n + 2 →
              ∀ β : MulAut Y, β (ψ s) = ψ s → β ^ 2 ^ (n + 1) = 1 →
                β ^ 2 ^ n = 1 ∨ β ^ 2 ^ n = MulAut.conj (ψ s ^ 2 ^ n)

end CFSG.ClassicalInvolution.Asc77
