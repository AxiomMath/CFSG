module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.H13.A6Inputs13_3
public import CFSG.Quasithin.H13.A6S4Defs
public import CFSG.Quasithin.H13.StatementsL6

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

@[expose] def Lem1374OneDiag_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G) (S : Setting4 G T L V),
    ¬ LieModel G .PSp 3 2 1 → ¬ LieModel G .PSU 4 3 1 → ¬ IsHatA6 L →
    ∀ H : Subgroup G, H ∈ S.Hz → IsElemAbelian 2 (conjClosure S.V3 H) → ¬ H13.IsA6Block L →
    ∀ K : Subgroup G, K ∈ cComp H → H ≤ Subgroup.normalizer (K : Set G) →
      (Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)) ∨
        LieModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 3 2 1) →
      ¬ S.L1 ≤ K → ¬ (∀ k ∈ K, ∀ l ∈ S.L1, k * l * k⁻¹ * l⁻¹ ∈ pCoreOf 2 K) → False

@[expose] def Lem1374OneOdd_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G) (S : Setting4 G T L V),
    ¬ LieModel G .PSp 3 2 1 → ¬ LieModel G .PSU 4 3 1 → ¬ IsHatA6 L →
    ∀ H : Subgroup G, H ∈ S.Hz → IsElemAbelian 2 (conjClosure S.V3 H) → ¬ H13.IsA6Block L →
    ∀ (p : ℕ), p.Prime → p ≠ 2 →
    ∀ K : Subgroup G, K ≤ H → H ≤ Subgroup.normalizer (K : Set G) → oTwoRes K = K →
      (∀ k ∈ K, ∀ u ∈ conjClosure S.V3 H,
        k * u * k⁻¹ * u⁻¹ ∈ Subgroup.centralizer (pCoreOf 2 H : Set G)) →
      ¬ K ≤ Subgroup.centralizer ((conjClosure S.V3 H ⊓
        Subgroup.centralizer (pCoreOf 2 H : Set G) : Subgroup G) : Set G) →
      K ⊓ Subgroup.centralizer ((conjClosure S.V3 H ⊓
        Subgroup.centralizer (pCoreOf 2 H : Set G) : Subgroup G) : Set G) ≤ pCoreOf 2 K →
      ¬ K ≤ Subgroup.normalizer (L : Set G) → ¬ S.L1 ≤ K →
      (∀ k ∈ K, k ^ p ∈ pCoreOf 2 K) →
      (∀ k₁ ∈ K, ∀ k₂ ∈ K, k₁ * k₂ * k₁⁻¹ * k₂⁻¹ ∈ pCoreOf 2 K) →
      (∀ N : Subgroup G, pCoreOf 2 K ≤ N → N ≤ K → H ≤ Subgroup.normalizer (N : Set G) →
        N = pCoreOf 2 K ∨ N = K) →
      p = 3 ∧ Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 3

@[expose] def Lem1374OneFinal_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G) (S : Setting4 G T L V),
    ¬ LieModel G .PSp 3 2 1 → ¬ LieModel G .PSU 4 3 1 → ¬ IsHatA6 L →
    ∀ H : Subgroup G, H ∈ S.Hz → IsElemAbelian 2 (conjClosure S.V3 H) → ¬ H13.IsA6Block L →
    ∀ K : Subgroup G, K ≤ H → H ≤ Subgroup.normalizer (K : Set G) → oTwoRes K = K →
      (∀ k ∈ K, ∀ u ∈ conjClosure S.V3 H,
        k * u * k⁻¹ * u⁻¹ ∈ Subgroup.centralizer (pCoreOf 2 H : Set G)) →
      ¬ K ≤ Subgroup.centralizer ((conjClosure S.V3 H ⊓
        Subgroup.centralizer (pCoreOf 2 H : Set G) : Subgroup G) : Set G) →
      K ⊓ Subgroup.centralizer ((conjClosure S.V3 H ⊓
        Subgroup.centralizer (pCoreOf 2 H : Set G) : Subgroup G) : Set G) ≤ pCoreOf 2 K →
      ¬ K ≤ Subgroup.normalizer (L : Set G) → ¬ S.L1 ≤ K →
      (∀ k ∈ K, ∀ l ∈ S.L1, k * l * k⁻¹ * l⁻¹ ∈ pCoreOf 2 K) →
      (Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 3 ∨
        Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)) ∨
        LieModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 3 2 1) → False

end CFSG.Quasithin.H13.A6
