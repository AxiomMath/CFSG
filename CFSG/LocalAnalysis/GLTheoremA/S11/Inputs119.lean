module

public import CFSG.LocalAnalysis.GLTheoremA.S11.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.S10

@[expose] def U64TypesAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (X K J : Subgroup G) (y : G) (lab : GLALabel), CFSG.Open.IsKGroup ↥X → GLAPComponent 5 X K →
    GLAPComponent 3 X K →
    GLAMarking (PQuot 5 K) (fun lab' _ _ _ _ _ => lab' = lab) →
    5 ∣ Nat.card (Subgroup.center (PQuot 5 K)) →
    y ∈ Subgroup.normalizer (K : Set G) → y ^ 3 = 1 →
    GLAPComponent 3 (K ⊓ Subgroup.centralizer ({y} : Set G)) J → LabelOf J ⟨.twA, 4, 2⟩ →
    lab = ⟨.twA, 4, 2⟩ ∨ lab = ⟨.twA, 4, 6⟩ ∨ ∃ r : ℕ, 1 < r ∧ lab = ⟨.twA, 5 * r - 1, 2⟩

@[expose] def U5RankAt : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (r : ℕ), 1 < r →
    GLAMarking K (fun lab _ _ _ _ _ => lab = ⟨.twA, 5 * r - 1, 2⟩) → 5 ≤ GLATwoLocalRank 5 K

@[expose] def U5OutAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (X K A : Subgroup G), GLAPComponent 5 X K → IsElemAbelian 5 A → A ≤ Subgroup.normalizer (K : Set G) →
    GLAMarking (PQuot 5 K) (fun lab _ _ _ _ _ => lab = ⟨.twA, 4, 2⟩ ∨ lab = ⟨.twA, 4, 6⟩) → InnDiagOn 5 A K

structure U6StructAt (G : Type) [Group G] [Finite G] : Prop where
  center : ∀ L : Subgroup G, LabelOf L ⟨.twA, 5, 2⟩ → Subgroup.center ↥L = ⊥
  rank : ∀ L : Subgroup G, LabelOf L ⟨.twA, 5, 2⟩ →
    ∃ F : Subgroup G, F ≤ L ∧ IsElemAbelian 5 F ∧ Nat.card F = 5 ^ 5
  mem : ∀ (L J : Subgroup G) (y : G), LabelOf L ⟨.twA, 5, 2⟩ → y ∈ L → orderOf y = 5 →
    GLALayer (L ⊓ Subgroup.centralizer ({y} : Set G)) = J → LabelOf J ⟨.twA, 4, 2⟩ → y ∈ J
  cent : ∀ (L J : Subgroup G) (y g : G), LabelOf L ⟨.twA, 5, 2⟩ → y ∈ L → orderOf y = 5 →
    GLALayer (L ⊓ Subgroup.centralizer ({y} : Set G)) = J → LabelOf J ⟨.twA, 4, 2⟩ →
    g ∈ Subgroup.normalizer (L : Set G) → g ∈ Subgroup.centralizer (J : Set G) →
    ∃ a ∈ Subgroup.zpowers y, ∀ l ∈ L, a⁻¹ * l * a = g⁻¹ * l * g

end CFSG.LocalAnalysis.GLTheoremA
