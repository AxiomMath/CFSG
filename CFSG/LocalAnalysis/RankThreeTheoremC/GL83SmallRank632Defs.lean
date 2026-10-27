module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank627Defs
public import CFSG.LocalAnalysis.AGLEmbedding.CatalogComponent

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

@[expose] def NearCyclic (V : Type*) [Group V] : Prop :=
  ∃ C : Subgroup V, C ≤ center V ∧ IsCyclic C ∧ C.index ≤ 4

@[expose] def IsKleinOrQ8Central {G : Type*} [Group G] [Finite G] (H : Subgroup G) : Prop :=
  Nonempty (H ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) ∨
    ∃ n : ℕ, rankThreeIsQ8CentralCyclic H n

structure SimpleFactorData {Y : Type*} [Group Y] (N : Subgroup Y) {r : ℕ}
    (S : Fin r → Subgroup Y) : Prop where
  le : ∀ i, S i ≤ N
  simple : ∀ i, IsSimpleGroup (S i)
  nonabelian : ∀ i, ∃ a b : S i, a * b ≠ b * a
  normal : ∀ i, ((S i).subgroupOf N).Normal
  prod : ∃ e : ((i : Fin r) → S i) ≃* N, ∀ (i : Fin r) (x : (j : Fin r) → S j),
    (∀ j, j ≠ i → x j = 1) → (e x : Y) = x i

@[expose] def fixedSubgroup {Γ V : Type*} [Group Γ] [Group V] (ρ : Γ →* MulAut V) (y : Γ) :
    Subgroup V where
  carrier := {v | ρ y v = v}
  one_mem' := map_one (ρ y)
  mul_mem' := fun {a b} ha hb => by
    change ρ y (a * b) = a * b
    rw [map_mul, ha, hb]
  inv_mem' := fun {a} ha => by
    change ρ y a⁻¹ = a⁻¹
    rw [map_inv, ha]

@[expose] def SmallRankConstraintKFact3 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.AGLEmbedding.CatalogSimpleSections X →
    (∀ q : ℕ, q.Prime → 5 ≤ q → CFSG.Open.pRank q (⊤ : Subgroup X) ≤ 2) →
    (∀ N : Subgroup X, N.Normal → N.index ≠ 3) →
    ∀ S : Sylow 3 X,
      Nonempty ((S : Subgroup X) ≃* (Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3))) →
      (∃ x ∈ (S : Subgroup X), x ≠ 1 ∧ x ^ 3 = 1 ∧
        CFSG.Open.pRank 3 (Subgroup.centralizer ({x} : Set X)) ≤ 2) →
      HasPrimeConstraint (G := X) 3

structure SmallRank3Data {G : Type} [Group G] [Finite G] (P : Sylow 3 G) (M : Subgroup G)
    (x z g : G) (T : Subgroup G) : Prop where
  point : SmallRankPoint P M x
  central : SmallRankCentral P z
  sylowTwo : SmallRankSylowTwo P M T
  g_mem : g ∈ (P : Subgroup G)
  g_act : ∃ b : ℕ, ¬ 3 ∣ b ∧ g * x * g⁻¹ = x * z ^ b
  kleinOrQ8 : IsKleinOrQ8Central (T ⊓ centralizer ({x} : Set G))
  noncentral : ¬ (T ⊓ centralizer ({x} : Set G)) ≤ centralizer ({z} : Set G)
  near : NearCyclic ↥(T ⊓ centralizer ({x} : Set G))
  cyc : IsCyclic ↥(T ⊓ centralizer ((zpowers x ⊔ zpowers z : Subgroup G) : Set G))

end CFSG.LocalAnalysis.RankThreeTheoremC
