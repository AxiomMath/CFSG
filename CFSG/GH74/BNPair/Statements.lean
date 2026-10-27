module

public import CFSG.GH74.BNPair.Defs
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

public section

namespace CFSG.GH74.BNPair

universe u

open scoped Pointwise

section Prop302

variable {X : Type*} [Group X]

structure Proposition302 (B N : Subgroup X) [(cartan B N).Normal] (S : Finset (WeylGroup B N)) :
    Prop where
  iUnion_dc : (⋃ w : WeylGroup B N, dc B N w) = Set.univ
  pairwiseDisjoint_dc : Pairwise (Function.onFun Disjoint (dc B N))
  parabolic_subgroup : ∀ J : Finset (WeylGroup B N), J ⊆ S →
    ∃ P : Subgroup X, (P : Set X) = parabolicSet B N (J : Set (WeylGroup B N)) ∧ B ≤ P ∧
      Subgroup.normalizer (P : Set X) = P
  parabolic_le_iff : ∀ J K : Finset (WeylGroup B N), J ⊆ S → K ⊆ S →
    (parabolic B N (J : Set (WeylGroup B N)) ≤ parabolic B N (K : Set (WeylGroup B N)) ↔ J ⊆ K)
  exists_parabolic : ∀ P : Subgroup X, B ≤ P →
    ∃ J : Finset (WeylGroup B N), J ⊆ S ∧ P = parabolic B N (J : Set (WeylGroup B N))
  parabolic_empty : parabolic B N ((∅ : Finset (WeylGroup B N)) : Set (WeylGroup B N)) = B
  parabolic_univ : parabolic B N (S : Set (WeylGroup B N)) = ⊤
  refined : ∀ n m : N, (n : WeylGroup B N) ∈ S →
    wordLength (S : Set (WeylGroup B N)) ((n : WeylGroup B N) * (m : WeylGroup B N)) >
        wordLength (S : Set (WeylGroup B N)) (m : WeylGroup B N) →
      ({(n : X)} : Set X) * (B : Set X) * {(m : X)} ⊆
        dc B N ((n : WeylGroup B N) * (m : WeylGroup B N))

@[expose] def Prop30_2 : Prop :=
  ∀ (X : Type u) [Group X] (B N : Subgroup X) [(cartan B N).Normal] (S : Finset (WeylGroup B N)),
    IsTitsSystem B N S → Proposition302 B N S

end Prop302

section Building

@[expose] def Eq30_3 : Prop :=
  ∀ (X : Type u) [Group X] (n : ℕ) (D : RankTwoSystem X n), D.Xplus.Normal

@[expose] def Lemma30_5 : Prop :=
  ∀ (X : Type u) [Group X] (n : ℕ) (D : RankTwoSystem X n) (i j : ℤ), IsRoot n i → IsRoot n j →
    rootPos n j ≠ rootPos n i + (n : ZMod (2 * n)) →
      chainProd D.root (arc n i j) = chainProd D.root (arc n j i) ∧
        ∃ V : Subgroup X, (V : Set X) = chainProd D.root (arc n i j)

@[expose] def Eq30_5 : Prop :=
  ∀ (X : Type u) [Group X] (n : ℕ) (D : RankTwoSystem X n) (i : ℕ), i ≤ n →
    (∀ m : D.N, (m : D.Weyl) = altWord D.w₁ D.w₂ i →
      D.UwMinus m = chainProd D.root (intList 1 i) ∧
        D.UwPlus m = chainProd D.root (intList (i + 1) n)) ∧
    (∀ m : D.N, (m : D.Weyl) = altWord D.w₂ D.w₁ i →
      D.UwMinus m = chainProd D.root (intList (n - i + 1) n).reverse ∧
        D.UwPlus m = chainProd D.root (intList 1 (n - i)).reverse)

@[expose] def Lemma30_6 : Prop :=
  ∀ (X : Type u) [Group X] (n : ℕ) (D : RankTwoSystem X n),
    D.graph.Connected ∧
    (D.graphMinusTop.IsTree ∧
      ∀ (i j : ℕ), ∀ v ∈ D.sideOne i, ∀ v' ∈ D.sideTwo j, ∀ l : List D.Vertex,
        IsGLSPath D.graph l → l.head? = some v → l.getLast? = some v' →
          (∃ a b : D.Vertex, [a, b] <:+: l ∧ (a : Set X) ∩ (b : Set X) ⊆ dc D.B D.N D.w₀) ∨
            (([D.vertex₁, D.vertex₂] <:+: l ∨ [D.vertex₂, D.vertex₁] <:+: l) ∧
              l.length = i + j + 2)) ∧
    ((∀ a b a' b' : D.Vertex, D.graph.Adj a b → D.graph.Adj a' b' →
        ∃ g : X, (D.action g a = a' ∧ D.action g b = b') ∨ (D.action g a = b' ∧ D.action g b = a')) ∧
      (∀ v v' : D.Vertex, D.IsTypeOne v → D.IsTypeOne v' → ∃ g : X, D.action g v = v') ∧
      (∀ v v' : D.Vertex, D.IsTypeTwo v → D.IsTypeTwo v' → ∃ g : X, D.action g v = v')) ∧
    (∀ v : D.Vertex, 3 ≤ (D.graph.neighborSet v).encard)

@[expose] def Lemma30_7 : Prop :=
  ∀ (X : Type u) [Group X] (n : ℕ) (D : RankTwoSystem X n),
    (∀ v v' : D.Vertex, D.graph.dist v v' ≤ n) ∧
    (∀ v v' : D.Vertex, D.graph.dist v v' < n →
      ∃ l : List D.Vertex, IsGLSPath D.graph l ∧ l.head? = some v ∧ l.getLast? = some v' ∧
        l.length ≤ n ∧
        ∀ l' : List D.Vertex, IsGLSPath D.graph l' → l'.head? = some v → l'.getLast? = some v' →
          l'.length ≤ n → l' = l) ∧
    (∀ v v' : D.Vertex, D.graph.dist v v' = n → ∀ v₁ : D.Vertex, D.graph.Adj v v₁ →
      ∃! l : List D.Vertex, IsGLSPath D.graph l ∧ l.head? = some v ∧ l.getLast? = some v' ∧
        l.length = n + 1 ∧ l[1]? = some v₁) ∧
    (∀ v v' : D.Vertex, D.graph.dist v v' = n →
      ∃ f : D.Vertex → D.Vertex,
        Set.BijOn f (D.graph.neighborSet v) (D.graph.neighborSet v') ∧
          ∀ l : List D.Vertex, IsGLSPath D.graph l → l.head? = some v → l.getLast? = some v' →
            l.length = n + 1 → ∀ a b : D.Vertex, l[1]? = some a → l[n - 1]? = some b → f a = b) ∧
    (∀ v v' : D.Vertex, ∀ l : List D.Vertex, IsGLSPath D.graph l → l.head? = some v →
      l.getLast? = some v' → l.length = n + 1 → D.graph.dist v v' = n) ∧
    (∀ (a : D.Vertex) (p : D.graph.Walk a a), p.IsCycle → p.length = 2 * n →
      ∀ v : D.Vertex, ∃ u ∈ p.support, D.graph.dist v u = n)

@[expose] def Lemma30_8 : Prop :=
  ∀ (X : Type u) [Group X] (n : ℕ) (D : RankTwoSystem X n), ∀ j : ℕ, j ≤ n →
    ∀ l l' : List D.Vertex, IsGLSPath D.graph l → IsGLSPath D.graph l' → l.length = j + 1 →
      l'.length = j + 1 → (∀ a b : D.Vertex, l.head? = some a → l'.head? = some b →
        (D.IsTypeOne a ↔ D.IsTypeOne b)) → ∃ g : X, l.map (D.action g) = l'

@[expose] def Lemma30_9 : Prop :=
  ∀ (X : Type u) [Group X] (n : ℕ) (D : RankTwoSystem X n),
    ∃ π₁ π₂ : List D.Vertex,
      IsGLSPath D.graph π₁ ∧ IsGLSPath D.graph π₂ ∧ π₁.length = n + 1 ∧ π₂.length = n + 1 ∧
      (∃ a : D.Vertex, π₁.head? = some a ∧ D.IsTypeOne a) ∧
      (∃ a : D.Vertex, π₂.head? = some a ∧ D.IsTypeTwo a) ∧
      (∀ x ∈ D.root n, ∀ v ∈ interiorVertices π₂, ∀ w : D.Vertex, D.graph.Adj v w →
        D.action x w = w) ∧
      (∀ l l' : List D.Vertex, IsGLSPath D.graph l → IsGLSPath D.graph l' → l.length = n + 2 →
        l'.length = n + 2 → π₂ <+: l → π₂ <+: l' → ∃ x ∈ D.root n, l.map (D.action x) = l') ∧
      (∀ x ∈ D.root 1, ∀ v ∈ interiorVertices π₁, ∀ w : D.Vertex, D.graph.Adj v w →
        D.action x w = w) ∧
      (∀ l l' : List D.Vertex, IsGLSPath D.graph l → IsGLSPath D.graph l' → l.length = n + 2 →
        l'.length = n + 2 → π₁ <+: l → π₁ <+: l' → ∃ x ∈ D.root 1, l.map (D.action x) = l')

@[expose] def Lemma30_10 : Prop :=
  ∀ (X : Type u) [Group X] (n : ℕ) (D : RankTwoSystem X n), ∀ π π' : List D.Vertex,
    IsGLSPath D.graph π → IsGLSPath D.graph π' → π.length = n + 1 → π'.length = n + 2 →
      π <+: π' → ∀ g ∈ graphAut D.graph, (∀ v ∈ π', g v = v) →
        (∀ v ∈ interiorVertices π, ∀ w : D.Vertex, D.graph.Adj v w → g w = w) → g = 1

@[expose] def Theorem30_4 : Prop :=
  ∀ (X X' : Type u) [Group X] [Group X'] (n : ℕ) (D : RankTwoSystem X n) (D' : RankTwoSystem X' n)
    (φ : D.U ≃* D'.U),
    (∀ i : ℤ, 1 ≤ i → i ≤ n → ∀ x : D.U, (x : X) ∈ D.root i ↔ ((φ x : D'.U) : X') ∈ D'.root i) →
      Nonempty (D.Xplus ≃* D'.Xplus)

end Building

end CFSG.GH74.BNPair
