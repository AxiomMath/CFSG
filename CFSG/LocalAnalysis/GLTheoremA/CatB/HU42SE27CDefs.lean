module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.HU42SE27

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.U42Cat

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

@[expose] def U4Split {G : Type} [Group G] (s : G) (K₀ : Subgroup G) : Prop :=
  K₀ ≤ Subgroup.centralizer ({s} : Set G) ∧
    (∀ g ∈ Subgroup.centralizer ({s} : Set G), ∃ n : ℕ, ∃ k ∈ K₀, g = s ^ n * k) ∧
    s ∉ K₀ ∧ Subgroup.center ↥K₀ = ⊥ ∧ Nat.card ↥K₀ = 25920

@[expose] def NoU4Sect {G : Type} [Group G] (s : G) : Prop :=
  ∀ K : Subgroup G, K ≤ Subgroup.centralizer ({s} : Set G) → Group.IsPerfect ↥K → ¬ 5 ∣ Nat.card ↥K

@[expose] def CentSplitOn (G : Type) [Group G] : Prop :=
  ∀ s : G, orderOf s = 3 → NoU4Sect s ∨ ∃ K₀ : Subgroup G, U4Split s K₀

@[expose] def CentShapeOn (G : Type) [Group G] : Prop :=
  ∀ s : G, orderOf s = 3 → ∀ K : Subgroup G, K ≤ Subgroup.centralizer ({s} : Set G) →
    Group.IsPerfect ↥K → HasU4Quot K →
      s ∉ K ∧
        (∀ g ∈ Subgroup.centralizer ({s} : Set G), ∀ k ∈ K, g * k * g⁻¹ ∈ K) ∧
        (∀ g ∈ Subgroup.centralizer ({s} : Set G), ∃ n : ℕ, ∃ k ∈ K, g = s ^ n * k) ∧
        Subgroup.center ↥K = ⊥

end CFSG.LocalAnalysis.GLTheoremA.CatB.U42Cat

end
