module

public import CFSG.GH74.Conclusion
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

structure Sec4Glob (G : Type) [Group G] [Finite G] : Prop where
  simple : IsSimpleGroup G
  kproper : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G
  not_catalog : ¬ CFSG.Blueprint.Catalog G
  dvd : 2 ^ 11 ∣ Nat.card G

@[expose] def CorAStatement : Prop :=
  ∀ (F : Type) [Group F] [Finite F], ¬ GH74.Gen4 F → ∀ S : Sylow 2 F,
    ∃ E : Subgroup F, E ≤ (S : Subgroup F) ∧ (E.subgroupOf (S : Subgroup F)).Normal ∧
      CFSG.Open.IsElemAbelian 2 E ∧ Nat.card E = 8

structure Sec4Inputs : Prop where
  gh74 : GH74.GH74Statement
  corA : CorAStatement

variable {G : Type} [Group G]

@[expose] def conjIn (K : Subgroup G) (x : G) : Set G := {u | ∃ k ∈ K, k * x * k⁻¹ = u}

@[expose] def ctxE (t x₁ x₂ : G) : Subgroup G := closure {t, x₁ ^ 2, (x₁ * x₂) ^ 2}

@[expose] def ctxX (t tau x₁ x₂ : G) : Subgroup G := closure {t, tau, x₁ ^ 2, (x₁ * x₂) ^ 2}

@[expose] def ctxM (t tau x₁ x₂ : G) : Subgroup G :=
  normalizer ((ctxX t tau x₁ x₂ : Subgroup G) : Set G)

@[expose] def ctxS1 (S 𝒮 : Subgroup G) : Subgroup G := normalizer (S : Set G) ⊓ 𝒮

@[expose] def IsE16In (S Y : Subgroup G) : Prop :=
  Y ≤ S ∧ CFSG.Open.IsElemAbelian 2 Y ∧ Nat.card Y = 16

end CFSG.OddStandard.SmallF3.HarrisU33
