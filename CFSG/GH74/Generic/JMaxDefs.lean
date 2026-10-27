module

public import CFSG.GH74.GLS.Classes

public section

namespace CFSG.GH74.Generic

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup

@[expose] def OfLieType (K : Type) [Group K] : Prop :=
  ∃ (t : StatedLieTag) (n p f : ℕ), LieModel (K ⧸ center K) t n p f

@[expose] def IsL3Odd (K : Type) [Group K] : Prop :=
  ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ (LieModel K .PSL 3 p f ∨ LieModel K .PSU 3 p f)

@[expose] def IsL3OddGt3 (K : Type) [Group K] : Prop :=
  ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 3 < p ^ f ∧ (LieModel K .PSL 3 p f ∨ LieModel K .PSU 3 p f)

@[expose] def InG2Depth (i : ℕ) (K : Type) [Group K] : Prop :=
  InG2 K ∧
    ((i = 1 ∧ ¬ OfLieType K ∧ ∃ n : ℕ, 12 ≤ n ∧ IsDoubleCoverOfAlt K n) ∨
      (i = 2 ∧ ¬ OfLieType K ∧ (NativeSporadic.IsSporadic K .McL ∨ NativeSporadic.IsSporadic K .Ly ∨
        NativeSporadic.IsSporadic K .ONan)) ∨
      (i = 3 ∧ ¬ OfLieType K ∧ ((∃ n : ℕ, 12 ≤ n ∧ Nonempty (K ≃* alternatingGroup (Fin n))) ∨
        NativeSporadic.IsSporadic K .HN)) ∨
      (i = 4 ∧ ¬ OfLieType K ∧ (NativeSporadic.IsSporadic K .J1 ∨ NativeSporadic.IsSporadic K .He ∨
        NativeSporadic.IsSporadic K .Co3)) ∨
      (i = 5 ∧ ¬ OfLieType K ∧ Nonempty (K ≃* alternatingGroup (Fin 11))) ∨
      (i = 6 ∧ OfLieType K ∧ ¬ IsL3Odd K) ∨
      (i = 7 ∧ IsL3OddGt3 K) ∨
      (i = 8 ∧ ¬ OfLieType K ∧ (Nonempty (K ≃* alternatingGroup (Fin 9)) ∨
        Nonempty (K ≃* alternatingGroup (Fin 10)))))

@[expose] noncomputable def d2 (K : Type) [Group K] : ℕ :=
  sInf {i : ℕ | InG2Depth i K}

@[expose] def lieRankSq : StatedLieTag → ℕ → ℕ
  | .PSL, n => (n - 1) ^ 2
  | .PSU, n => (n - 1) ^ 2
  | .PSp, n => n ^ 2
  | .POmegaOdd, n => n ^ 2
  | .POmegaPlus, n => n ^ 2
  | .POmegaMinus, n => n ^ 2
  | .G2, _ => 4
  | .F4, _ => 16
  | .E6, _ => 36
  | .E7, _ => 49
  | .E8, _ => 64
  | .twistedE6, _ => 36
  | .trialityD4, _ => 16
  | .twistedB2, _ => 4
  | .twistedG2, _ => 4
  | .twistedF4, _ => 16
  | .Tits, _ => 16

@[expose] def lieTypeRank : StatedLieTag → ℕ
  | .PSL => 0
  | .PSU => 0
  | .POmegaPlus => 1
  | .POmegaMinus => 1
  | .trialityD4 => 1
  | .E6 => 2
  | .E7 => 2
  | .E8 => 2
  | .twistedE6 => 2
  | .PSp => 3
  | .POmegaOdd => 3
  | .twistedB2 => 3
  | .F4 => 4
  | .twistedF4 => 4
  | .Tits => 4
  | .G2 => 5
  | .twistedG2 => 5

@[expose] def FValue (t : StatedLieTag) (n p f₀ : ℕ) : ℕ :=
  (p ^ f₀) ^ lieRankSq t n * 6 + lieTypeRank t

@[expose] def HasFValue (K : Type) [Group K] (v : ℕ) : Prop :=
  ∃ (t : StatedLieTag) (n p f₀ : ℕ), LieModel (K ⧸ center K) t n p f₀ ∧ v = FValue t n p f₀

@[expose] noncomputable def FRank (K : Type) [Group K] : ℕ :=
  sSup {v : ℕ | HasFValue K v}

@[expose] def G2Pair {G : Type} [Group G] (x : G) (K : Subgroup (CentralizerBar x)) : Prop :=
  orderOf x = 2 ∧ IsComponent K ∧ InG2 ↥K

@[expose] def IsJMax {G : Type} [Group G] (x : G) (K : Subgroup (CentralizerBar x)) : Prop :=
  G2Pair x K ∧ ∀ (y : G) (L : Subgroup (CentralizerBar y)), G2Pair y L →
    d2 ↥K ≤ d2 ↥L ∧ (d2 ↥L = d2 ↥K → FRank ↥L ≤ FRank ↥K)

end CFSG.GH74.Generic
