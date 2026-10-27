module

public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialClauses
public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialLocal

public section

namespace CFSG.Semidihedral.FixedCoreNontrivial

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo

structure EqualParameterData (G : Type) [Group G] [Finite G] (t s₀ d d₁ : G) (J : Subgroup G)
    (p f : ℕ) (F : Type) [Field F] [Finite F] (κ : C t →* Equiv.Perm (Omega F))
    (F' : Type) [Field F'] [Finite F']
    (φ : torusH G t s₀ ⧸ CFSG.pPrimeCore 2 (torusH G t s₀) ≃*
      CFSG.GorensteinWalter.PGL2 F') : Prop where
  prime : p.Prime
  odd : Odd p
  one_le : 1 ≤ f
  q_gt : 9 < p ^ f
  card_F : Nat.card F = p ^ f
  card_F' : Nat.card F' = p ^ f
  clauses : TorusNormalizerClauses G t s₀ d (p ^ f) F' φ
  localData : LocalData t s₀ d₁ J ((N t).map (C t).subtype) (torusW G t s₀)
  sl2 : ∃ (F₀ : Type) (_ : Field F₀) (_ : Finite F₀), Nat.card F₀ = p ^ f ∧
    Nonempty (J ≃* Matrix.SpecialLinearGroup (Fin 2) F₀)
  card_C : Nat.card (C t) = 2 * Nat.card ((N t).map (C t).subtype) * p ^ f * ((p ^ f) ^ 2 - 1)
  B_ne_bot : (N t).map (C t).subtype ≠ ⊥
  confine : ∀ u ∈ (N t).map (C t).subtype, u ≠ 1 → Subgroup.centralizer {u} ≤ C t
  sylow_normalizer : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ Nat.card ((N t).map (C t).subtype) →
    ∀ P : Sylow ℓ ((N t).map (C t).subtype), ∀ Q : Subgroup G, Q ≤ C t → IsPGroup ℓ Q →
      (P : Subgroup ((N t).map (C t).subtype)).map ((N t).map (C t).subtype).subtype ≤ Q →
        Subgroup.normalizer (Q : Set G) ≤ C t
  not_cube : ¬ (p ^ f) ^ 3 ∣ Nat.card G
  ker_κ : κ.ker = NZ t
  range_κ : κ.range = coordinateD F
  layer_κ : (J.subgroupOf (C t)).map κ = coordinateG F
  conj_t : ∀ x : G, orderOf x = 2 → IsConj x t
  four_conj : ∀ T : Subgroup G, IsKleinFour T → ∃ g : G,
    T.map (MulAut.conj g).toMonoidHom = Subgroup.zpowers t ⊔ Subgroup.zpowers s₀
  three_cycle : ∃ τ : G, τ * t * τ⁻¹ = s₀ ∧ τ * s₀ * τ⁻¹ = t * s₀
  sylow_two : ∃ S : Sylow 2 G, Subgroup.zpowers t ⊔ Subgroup.zpowers s₀ ≤ (S : Subgroup G) ∧
    (S : Subgroup G) ≤ C t

end CFSG.Semidihedral.FixedCoreNontrivial
