module

public import CFSG.Open.PGLModelDefs
public import CFSG.Open.GeneratedCore
public import CFSG.Assembly.Defs
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Classification

public section

namespace CFSG.Assembly.RankThreeEven

open Matrix
open scoped MatrixGroups

noncomputable section

@[expose] noncomputable def localRank (p : ℕ) (G : Type*) [Group G] [Finite G] : ℕ :=
  CFSG.Open.twoLocalPrimeRank p G

@[expose] def oddStrata (k : ℕ) (X : Type*) [Group X] [Finite X] : Set ℕ :=
  {p | p.Prime ∧ p ≠ 2 ∧ p ∣ Nat.card X ∧ k ≤ localRank p X}

open Classical in
@[expose] noncomputable def sigmaA (G : Type*) [Group G] [Finite G] : Set ℕ :=
  let S₁ := {p | p.Prime ∧ p ≠ 2 ∧ p ∣ Nat.card G ∧ 3 < localRank p G}
  let S₂ := {p | p.Prime ∧ 5 < p ∧ p ∣ Nat.card G ∧ localRank p G = 3}
  let S₃ := {p | p.Prime ∧ 3 < p ∧ p ∣ Nat.card G ∧ localRank p G = 3}
  let S₄ := {p | p.Prime ∧ p ≠ 2 ∧ p ∣ Nat.card G ∧ localRank p G = 3}
  if S₁.Nonempty then S₁ else if S₂.Nonempty then S₂ else if S₃.Nonempty then S₃ else S₄

@[expose] noncomputable def aschCore {G : Type*} [Group G] [Finite G] (k p : ℕ) (P : Subgroup G) :
    Subgroup G :=
  CFSG.Open.rankThreeAschCore k p P

@[expose] def AschCoreLocal (G : Type*) [Group G] [Finite G] (k : ℕ) : Prop :=
  ∀ p ∈ sigmaA G, ∀ P : Sylow p G,
    ∃ H : Subgroup G, IsTwoLocal H ∧ aschCore k p (P : Subgroup G) ≤ H

export CFSG.PGLModel (projImage projSL projSU sympForm projSp minusQuadForm orthogonalMinus
  projOmegaMinus plusQuadForm orthogonalPlus projOmegaPlus IModel)

@[expose] def primePowerTwo : TauCeti.PrimePower :=
  ⟨2, 1, Nat.prime_two, Nat.one_pos⟩

@[expose] def f4TwoIndex : TauCeti.ValidLieTypeIndex :=
  ⟨.F4 primePowerTwo, by simp⟩

@[expose] def IIClassical (G : Type*) [Group G] : Prop :=
  Nonempty (G ≃* projSU 5 2 1) ∨ Nonempty (G ≃* projSU 6 2 1) ∨
    Nonempty (G ≃* projSL 6 (GaloisField 2 1)) ∨ Nonempty (G ≃* projSL 7 (GaloisField 2 1)) ∨
    Nonempty (G ≃* projSp 4 (GaloisField 2 1)) ∨
    Nonempty (G ≃* projOmegaPlus 4 (GaloisField 2 1)) ∨
    (∃ b c : GaloisField 2 1, (∀ s : GaloisField 2 1, s ^ 2 + b * s + c ≠ 0) ∧
      Nonempty (G ≃* projOmegaMinus 3 (GaloisField 2 1) b c)) ∨
    Nonempty (G ≃* projSL 4 (GaloisField 2 2)) ∨ Nonempty (G ≃* projSp 3 (GaloisField 2 2)) ∨
    Nonempty (G ≃* projSU 5 2 3)

@[expose] def IIModel (G : Type*) [Group G] : Prop :=
  Nonempty (G ≃* (TauCeti.CFSGIndex.sporadic .Co2).Group) ∨
    Nonempty (G ≃* (TauCeti.CFSGIndex.sporadic .Th).Group) ∨ IIClassical G ∨
    Nonempty (G ≃* (TauCeti.CFSGIndex.lie f4TwoIndex).Group)

end

end CFSG.Assembly.RankThreeEven
