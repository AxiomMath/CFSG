module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_21DS
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_20Facts
public import CFSG.Quasithin.Background.Basic

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin

@[expose] def OutFamily {G : Type} [Group G] (K H : Subgroup G) : Prop :=
  IsL2pType ↥K ∨ (Nonempty (↥K ≃* alternatingGroup (Fin 6)) ∧
    (Nonempty (↥(autOn H K) ≃* ↥A6Models.m10) ∨ Nonempty (↥(autOn H K) ≃* ↥A6Models.pgl29)))

structure OutSetting {G : Type} [Group G] [Finite G] (K H S : Subgroup G) : Prop where
  K_le_H : K ≤ H
  H_le_normalizer : H ≤ Subgroup.normalizer (K : Set G)
  simple : IsSimpleGroup ↥K
  sylow : IsSylowTwoOf S H
  join : H = K ⊔ S
  fam : OutFamily K H

@[expose] def OutShape : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K H S : Subgroup G), OutSetting K H S →
    Nat.card ↥S ≤ 2 * (Nat.card ↥(S ⊓ K) * Nat.card ↥(S ⊓ Subgroup.centralizer (K : Set G))) ∧
      ∃ R : Subgroup ↥(autOn S K), DS.DSData R

@[expose] def OutOneClass : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K H S : Subgroup G), OutSetting K H S →
    ∀ i j : G, i ∈ K → j ∈ K → i * i = 1 → j * j = 1 → i ≠ 1 → j ≠ 1 →
      ∃ k ∈ K, k * i * k⁻¹ = j

@[expose] def OutOuter : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K H S : Subgroup G), OutSetting K H S →
    ∀ u ∈ H, u * u = 1 → u ∉ K ⊔ (H ⊓ Subgroup.centralizer (K : Set G)) →
      ¬ Nonempty (↥(autOn H K) ≃* ↥A6Models.m10) ∧
        oddCoreIn (K ⊓ Subgroup.centralizer ({u} : Set G)) ≠ ⊥

end CFSG.QuasithinUnique
