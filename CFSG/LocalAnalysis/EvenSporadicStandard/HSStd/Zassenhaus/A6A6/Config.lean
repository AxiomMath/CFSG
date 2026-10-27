module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.Input
public import CFSG.Open.FusionDefs

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.A6A6

open Subgroup CFSG.Open CFSG.EvenSporadicStandard.M24Std

variable {V : Type} [Group V] {G : Type} [Group G]

@[expose] def c5 : alternatingGroup (Fin 6) :=
  ⟨Equiv.swap 0 4 * Equiv.swap 0 3 * Equiv.swap 0 2 * Equiv.swap 0 1,
    Equiv.Perm.mem_alternatingGroup.2 (by decide)⟩

structure Decomp (ρ : G →* MulAut V)
    (e : egaLayer (G ⧸ fusionOddCore G) ≃* alternatingGroup (Fin 6) × alternatingGroup (Fin 6)) where
  a : G
  b : G
  U₁ : Subgroup V
  U₂ : Subgroup V
  orderOf_a : orderOf a = 5
  orderOf_b : orderOf b = 5
  comm : a * b = b * a
  mk_a : (QuotientGroup.mk a : G ⧸ fusionOddCore G) = (e.symm (c5, 1) : G ⧸ fusionOddCore G)
  mk_b : (QuotientGroup.mk b : G ⧸ fusionOddCore G) = (e.symm (1, c5) : G ⧸ fusionOddCore G)
  fix_a : ∀ v : V, ρ a v = v ↔ v ∈ U₂
  fix_b : ∀ v : V, ρ b v = v ↔ v ∈ U₁
  card_U₁ : Nat.card U₁ = 16
  card_U₂ : Nat.card U₂ = 16
  inf_U : U₁ ⊓ U₂ = ⊥
  mem_U₁ : ∀ g : G, a * g = g * a → ∀ v ∈ U₁, ρ g v ∈ U₁
  mem_U₂ : ∀ g : G, b * g = g * b → ∀ v ∈ U₂, ρ g v ∈ U₂

structure Config (ρ : G →* MulAut V) where
  C : Subgroup G
  D : Subgroup G
  U₁ : Subgroup V
  U₂ : Subgroup V
  eC : C ≃* alternatingGroup (Fin 6)
  eD : D ≃* alternatingGroup (Fin 6)
  card_U₁ : Nat.card U₁ = 16
  card_U₂ : Nat.card U₂ = 16
  inf_U : U₁ ⊓ U₂ = ⊥
  C_mem : ∀ x ∈ C, ∀ v ∈ U₁, ρ x v ∈ U₁
  D_mem : ∀ x ∈ D, ∀ v ∈ U₂, ρ x v ∈ U₂
  C_fix : ∀ v : V, (∀ x ∈ C, ρ x v = v) ↔ v ∈ U₂
  D_fix : ∀ v : V, (∀ x ∈ D, ρ x v = v) ↔ v ∈ U₁
  comm : ∀ x ∈ C, ∀ y ∈ D, x * y = y * x
  inf_CD : C ⊓ D = ⊥
  inf_odd : (C ⊔ D) ⊓ fusionOddCore G = ⊥
  map_eq : (C ⊔ D).map (QuotientGroup.mk' (fusionOddCore G)) = egaLayer (G ⧸ fusionOddCore G)

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.A6A6
