module

public import CFSG.LocalAnalysis.RankThreeTheoremC.TransitivityKFacts

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

structure PlaneData {X : Type} [Group X] [Finite X] (P D : Subgroup X) (z : X) : Prop where
  pgroup : IsPGroup 3 P
  plane : IsNonabelianPlane 3 P D
  normal : P ≤ normalizer (D : Set X)
  card : Nat.card D = 3 ^ 3
  zD : z ∈ D
  zo : orderOf z = 3
  zc : ∀ g ∈ P, z * g = g * z
  rank : CFSG.Open.pRank 3 P = 3

structure PlaneFacts {X : Type} [Group X] [Finite X] (P D : Subgroup X) (z : X) : Prop where
  comm_mem : ∀ a ∈ D, ∀ b ∈ D, a * b * a⁻¹ * b⁻¹ ∈ zpowers z
  center_le : ∀ d ∈ D, (∀ e ∈ D, d * e = e * d) → d ∈ zpowers z
  omega_cent : ∀ c ∈ P, (∀ d ∈ D, c * d = d * c) → c ^ 3 = 1 → c ∈ zpowers z
  cent_cyclic : IsCyclic ↥(P ⊓ centralizer (D : Set X))
  z_mem : ∀ N : Subgroup X, N ≤ P → P ≤ normalizer (N : Set X) → N ≠ ⊥ → z ∈ N
  inv_plane : ∃ B : Subgroup X, B ≤ D ∧ Nat.card B = 9 ∧ IsElemAbelian 3 B ∧ z ∈ B ∧
    P ≤ normalizer (B : Set X)
  inf_plane : ∀ R : Subgroup X, R ≤ P → P ≤ normalizer (R : Set X) → ¬ IsMulCommutative R →
    ∃ B : Subgroup X, B ≤ R ∧ B ≤ D ∧ Nat.card B = 9 ∧ IsElemAbelian 3 B ∧ z ∈ B ∧
      P ≤ normalizer (B : Set X)
  inner : ∀ x ∈ P, (∀ d ∈ D, x * d * x⁻¹ * d⁻¹ ∈ zpowers z) →
    ∃ δ ∈ D, ∀ d ∈ D, δ⁻¹ * x * d = d * (δ⁻¹ * x)
  eq_of_comm : ∀ B B' : Subgroup X, B ≤ D → B' ≤ D → Nat.card B = 9 → Nat.card B' = 9 →
    (∀ b ∈ B, ∀ b' ∈ B', b * b' = b' * b) → B = B'
  not_normal : ∃ D' : Subgroup X, D' ≤ P ∧ (∀ x ∈ D', x ^ 3 = 1) ∧ z ∈ D' ∧
    ¬ P ≤ normalizer (D' : Set X)

@[expose] def layerCenter (X : Type) [Group X] [Finite X] : Subgroup X :=
  (center (rankThreeLayer (⊤ : Subgroup X))).map (rankThreeLayer (⊤ : Subgroup X)).subtype

structure NGKData (X : Type) [Group X] [Finite X] (P : Sylow 3 X) (z : X) (D : Subgroup X) :
    Prop where
  cat : CFSG.AGLEmbedding.CatalogSimpleSections X
  rank3 : CFSG.twoLocalOddRank X ≤ 3
  core : primeComplementCore (G := X) 3 = ⊥
  prank : CFSG.Open.pRank 3 (P : Subgroup X) = 3
  ord : orderOf z = 3
  zc : z ∈ center X
  layer : z ∈ rankThreeLayer (⊤ : Subgroup X)
  plane : IsNonabelianPlane 3 (P : Subgroup X) D
  normal : (P : Subgroup X) ≤ normalizer (D : Set X)
  zD : z ∈ D
  card : Nat.card D = 3 ^ 3

namespace NGKData

variable {X : Type} [Group X] [Finite X] {P : Sylow 3 X} {z : X} {D : Subgroup X}

theorem zc' (h : NGKData X P z D) (g : X) : z * g = g * z :=
  (mem_center_iff.1 h.zc g).symm

theorem planeData (h : NGKData X P z D) : PlaneData (P : Subgroup X) D z where
  pgroup := P.isPGroup'
  plane := h.plane
  normal := h.normal
  card := h.card
  zD := h.zD
  zo := h.ord
  zc := fun g _ => h.zc' g
  rank := h.prank

end NGKData

end CFSG.LocalAnalysis.RankThreeTheoremC
