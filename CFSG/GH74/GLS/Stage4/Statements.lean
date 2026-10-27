module

public import CFSG.GH74.GLS.Stage4.Ree
public import CFSG.GH74.GLS.SP.GlueDefs

public section

namespace CFSG.GH74.GLS.Stage4

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.GH74.BNPair CFSG.GH74.GLS.SP

@[expose] def IsTwoCentralG2TypeG2 (G : Type) [Group G] (Gs : Type) [Group Gs] : Prop :=
  (∃ (S : Sylow 2 G) (S' : Sylow 2 Gs), Nonempty (↥(S : Subgroup G) ≃* ↥(S' : Subgroup Gs))) ∧
    ∃ z : G, IsCentralInvolution z ∧ (∀ u : G, orderOf u = 2 → IsConj z u) ∧
      pPrimeCore 2 ↥(centralizer ({z} : Set G)) = ⊥ ∧
      ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ LieModel Gs .G2 0 p f ∧
        HasSL2ProductOfIndexTwoCh6 (oPrimeResidual 2 ↥(centralizer ({z} : Set G))) (p ^ f)

theorem IsTwoCentralG2Type.g2 {G : Type} [Group G] [Finite G] {Gs : Type} [Group Gs]
    (hnonab : ∀ S : Sylow 2 G, ¬ IsMulCommutative (S : Subgroup G))
    (h : IsTwoCentralG2Type G Gs) : IsTwoCentralG2TypeG2 G Gs := by
  obtain ⟨-, hS, z, hz, hconj, hO, hbr⟩ := h
  refine ⟨hS, z, hz, hconj, hO, ?_⟩
  rcases hbr with ⟨-, K, hK, p, f, hp, h8, -, hL⟩ | h
  · exact (not_ree_branch hnonab hz hK h8 hL).elim
  · exact h

@[expose] def RootOrdersG2 {G : Type} [Group G] (root : ℤ → Subgroup G) (q : ℕ) : Prop :=
  ∀ i : ℤ, 1 ≤ i → i ≤ 6 → Nat.card ↥(root i) = q

@[expose] def RootOrdersD4 {G : Type} [Group G] (root : ℤ → Subgroup G) (q : ℕ) : Prop :=
  (∀ i : ℤ, 1 ≤ i → i ≤ 6 → Nat.card ↥(root i) = if i % 2 = 1 then q ^ 3 else q) ∨
    (∀ i : ℤ, 1 ≤ i → i ≤ 6 → Nat.card ↥(root i) = if i % 2 = 1 then q else q ^ 3)

@[expose] def Ch6LocalRGD2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Std G → pRank 2 G = 3 →
    ∀ (Gs : Type) [Group Gs], IsTwoCentralG2TypeG2 G Gs →
      ∃ (H : Subgroup G) (r₁ r₂ : G) (U : Subgroup G) (root : ℤ → Subgroup G)
        (R : RGD2 6 H r₁ r₂ U root), (H ⊔ U) ⊔ R.N = ⊤ ∧ ∃ q : ℕ, Odd q ∧
          ((5 ≤ q ∧ RootOrdersG2 root q) ∨ (3 ≤ q ∧ RootOrdersD4 root q))

@[expose] def Ch6LocalBN : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Std G → pRank 2 G = 3 →
    ∀ (Gs : Type) [Group Gs], IsTwoCentralG2TypeG2 G Gs →
      ∃ (D : RankTwoSystem G 6) (q : ℕ), Odd q ∧
        ((5 ≤ q ∧ RootOrdersG2 D.root q) ∨ (3 ≤ q ∧ RootOrdersD4 D.root q))

@[expose] def HexClassG2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (D : RankTwoSystem G 6) (q : ℕ),
    3 ≤ q → RootOrdersG2 D.root q → ∃ p f : ℕ, p.Prime ∧ 1 ≤ f ∧ p ^ f = q ∧ LieModel G .G2 0 p f

@[expose] def HexClassD4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (D : RankTwoSystem G 6) (q : ℕ),
    2 ≤ q → RootOrdersD4 D.root q →
      ∃ p f : ℕ, p.Prime ∧ 1 ≤ f ∧ p ^ f = q ∧ LieModel G .trialityD4 0 p f

@[expose] def HexagonClassification : Prop := HexClassG2 ∧ HexClassD4

end CFSG.GH74.GLS.Stage4
