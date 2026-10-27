module

public import CFSG.LocalAnalysis.RankThreeUC.Asc1930

public section

namespace CFSG.LocalAnalysis.RankThreeUC

namespace SourceSetting

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G]

structure InUC (G : Type) [Group G] [Finite G] : Prop where
  standing : Standing G
  uc : rankThreeUC G

@[expose] def IsInMSigma (G : Type) [Group G] [Finite G] (M : Subgroup G) : Prop :=
  ∃ (p : ℕ) (P : Sylow p G), p ∈ rankThreeSigmaA G ∧ SigmaChoice G p ∧ IsWitness p P M

@[expose] def sigmaOf (G : Type) [Group G] [Finite G] (M : Subgroup G) : Set ℕ :=
  {p | p ∈ rankThreeSigmaA G ∧ ∃ P : Sylow p G, IsWitness p P M}

@[expose] def maxTwoLocalsContaining (X : Subgroup G) : Set (Subgroup G) :=
  {N | rankThreeIsMaxTwoLocal N ∧ X ≤ N}

@[expose] def maxSubgroupsContaining (Y : Subgroup G) : Set (Subgroup G) :=
  {N | IsCoatom N ∧ Y ≤ N}

@[expose] def invariantPPrimeSubgroups (M Y : Subgroup G) (p : ℕ) : Set (Subgroup G) :=
  {A | A ≤ M ∧ Y ≤ normalizer (A : Set G) ∧ Nat.Coprime p (Nat.card A)}

@[expose] def oPrimeResidual (p : ℕ) (Y : Subgroup G) : Subgroup G :=
  closure {x : G | x ∈ Y ∧ ∃ k : ℕ, orderOf x = p ^ k}

@[expose] def normalClosureUnder (X H : Subgroup G) : Subgroup G :=
  ⨆ h : H, X.map (MulAut.conj (h : G)).toMonoidHom

@[expose] def QuotientIsTwoGroup (p : ℕ) (Y : Subgroup G) : Prop :=
  ∀ y ∈ Y, ∃ k : ℕ, y ^ (2 ^ k) ∈ oPrimeResidual p Y

theorem IsInMSigma.exists {G : Type} [Group G] [Finite G] {M : Subgroup G}
    (h : IsInMSigma G M) :
    ∃ (p : ℕ) (P : Sylow p G), p ∈ rankThreeSigmaA G ∧ SigmaChoice G p ∧ IsWitness p P M := h

theorem sigmaOf_mem_iff {G : Type} [Group G] [Finite G] (M : Subgroup G) (p : ℕ) :
    p ∈ sigmaOf G M ↔ p ∈ rankThreeSigmaA G ∧ ∃ P : Sylow p G, IsWitness p P M :=
  Iff.rfl

end SourceSetting

end CFSG.LocalAnalysis.RankThreeUC
