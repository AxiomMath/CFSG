module

public import CFSG.GH74.GLS.Pattern

public section

namespace CFSG.GH74.GLS.LU

open Subgroup Blueprint Assembly.LowTwoRank

@[expose] def IsTwoCentralClassicalTypeCompat (G : Type) [Group G] (Gs : Type) [Group Gs] : Prop :=
  (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 3 < p ^ f ∧
    (LieModel Gs .PSp 2 p f ∨ LieModel Gs .PSL 4 p f ∨ LieModel Gs .PSU 4 p f)) ∧
  ∃ (S : Sylow 2 G) (z : G) (S' : Sylow 2 Gs) (z' : Gs),
    (center ↥(S : Subgroup G)).map (S : Subgroup G).subtype = zpowers z ∧
    (center ↥(S' : Subgroup Gs)).map (S' : Subgroup Gs).subtype = zpowers z' ∧
    (∃ ψ : ↥(layerTimesSylow z (S : Subgroup G)) ≃* ↥(layerTimesSylow z' (S' : Subgroup Gs)),
      (∀ x : ↥(layerTimesSylow z (S : Subgroup G)), (x : G) ∈ (S : Subgroup G) ↔
        (ψ x : Gs) ∈ (S' : Subgroup Gs)) ∧
      (∀ x y : ↥(layerTimesSylow z (S : Subgroup G)), (x : G) ∈ (S : Subgroup G) →
        (y : G) ∈ (S : Subgroup G) → orderOf (x : G) = 2 → orderOf (y : G) = 2 →
        (IsConj (x : G) (y : G) ↔ IsConj (ψ x : Gs) (ψ y : Gs)))) ∧
    ((∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ LieModel Gs .PSp 2 p f) →
      pPrimeCore 2 ↥(centralizer ({z} : Set G)) = ⊥) ∧
    ((∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ (LieModel Gs .PSL 4 p f ∨ LieModel Gs .PSU 4 p f)) →
      IsCyclic ↥(pPrimeCore 2 ↥(centralizer ({z} : Set G))) ∧
        Nat.card ↥(pPrimeCore 2 ↥(centralizer ({z} : Set G))) ∣
          Nat.card ↥(pPrimeCore 2 ↥(centralizer ({z'} : Set Gs))))

@[expose] def S_stage5_LU_compat : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProperSimple G →
    ∀ (Gs : Type) [Group Gs], (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 5 ≤ p ^ f ∧
        ((p ^ f % 8 ≠ 1 ∧ LieModel Gs .PSL 4 p f) ∨ (p ^ f % 8 ≠ 7 ∧ LieModel Gs .PSU 4 p f))) →
      IsTwoCentralClassicalTypeCompat G Gs → Nonempty (G ≃* Gs)

end CFSG.GH74.GLS.LU
