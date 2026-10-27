module

public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.Combinatorics.SimpleGraph.Metric

public noncomputable section

namespace CFSG.GH74.BNPair

open scoped Pointwise

section TitsSystem

variable {X : Type*} [Group X]

abbrev cartan (B N : Subgroup X) : Subgroup N :=
  (B ⊓ N).subgroupOf N

abbrev WeylGroup (B N : Subgroup X) : Type _ :=
  N ⧸ cartan B N

@[expose] def dc (B N : Subgroup X) (w : WeylGroup B N) : Set X :=
  {x | ∃ n : N, (n : WeylGroup B N) = w ∧ x ∈ (B : Set X) * {(n : X)} * (B : Set X)}

@[expose] def wordLength {W : Type*} [Monoid W] (J : Set W) (w : W) : ℕ :=
  sInf {k | ∃ l : List W, (∀ s ∈ l, s ∈ J) ∧ l.length = k ∧ l.prod = w}

@[expose] def altWord {W : Type*} [Monoid W] (a b : W) : ℕ → W
  | 0 => 1
  | i + 1 => altWord b a i * a

structure IsTitsSystem (B N : Subgroup X) [(cartan B N).Normal] (S : Finset (WeylGroup B N)) :
    Prop where
  gen : B ⊔ N = ⊤
  involution : ∀ s ∈ S, orderOf s = 2
  closure_eq : Subgroup.closure (S : Set (WeylGroup B N)) = ⊤
  mul_subset : ∀ n m : N, (n : WeylGroup B N) ∈ S →
    ({(n : X)} : Set X) * (B : Set X) * {(m : X)} ⊆
      dc B N ((n : WeylGroup B N) * (m : WeylGroup B N)) ∪ dc B N (m : WeylGroup B N)
  ne : ∀ n : N, (n : WeylGroup B N) ∈ S →
    ({(n : X)} : Set X) * (B : Set X) * {(n : X)} ≠ (B : Set X)

@[expose] def IsSplit (B N U : Subgroup X) : Prop :=
  Group.IsNilpotent U ∧ (B : Set X) = ((B ⊓ N : Subgroup X) : Set X) * (U : Set X)

@[expose] def IsSaturated (B N : Subgroup X) : Prop :=
  B ⊓ N = ⨅ n : N, B.map (MulAut.conj (n : X)⁻¹).toMonoidHom

@[expose] def bruhatSet (B N : Subgroup X) [(cartan B N).Normal] (V : Set (WeylGroup B N)) : Set X :=
  ⋃ w ∈ V, dc B N w

@[expose] def parabolicSet (B N : Subgroup X) [(cartan B N).Normal] (J : Set (WeylGroup B N)) : Set X :=
  bruhatSet B N ((Subgroup.closure J : Subgroup (WeylGroup B N)) : Set (WeylGroup B N))

@[expose] def parabolic (B N : Subgroup X) [(cartan B N).Normal] (J : Set (WeylGroup B N)) : Subgroup X :=
  Subgroup.closure (parabolicSet B N J)

end TitsSystem

section RankTwoBuilding

variable {X : Type*} [Group X] (B N : Subgroup X) [(cartan B N).Normal] (w₁ w₂ : WeylGroup B N)

@[expose] def rankTwoVertices : Set (Set X) :=
  {c | (∃ x : X, c = ((parabolic B N {w₁} : Subgroup X) : Set X) * {x}) ∨
    ∃ x : X, c = ((parabolic B N {w₂} : Subgroup X) : Set X) * {x}}

@[expose] def buildingGraph : SimpleGraph (rankTwoVertices B N w₁ w₂) where
  Adj v v' := v ≠ v' ∧ ((v : Set X) ∩ (v' : Set X)).Nonempty
  symm := ⟨fun _ _ h => ⟨h.1.symm, by simpa only [Set.inter_comm] using h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem mul_singleton_mem_rankTwoVertices {c : Set X} (hc : c ∈ rankTwoVertices B N w₁ w₂)
    (g : X) : c * {g} ∈ rankTwoVertices B N w₁ w₂ := by
  rcases hc with ⟨x, rfl⟩ | ⟨x, rfl⟩
  · exact Or.inl ⟨x * g, by rw [mul_assoc, Set.singleton_mul_singleton]⟩
  · exact Or.inr ⟨x * g, by rw [mul_assoc, Set.singleton_mul_singleton]⟩

@[expose] def rankTwoAction : X →* Equiv.Perm (rankTwoVertices B N w₁ w₂) where
  toFun g :=
    { toFun := fun v => ⟨(v : Set X) * {g⁻¹}, mul_singleton_mem_rankTwoVertices B N w₁ w₂ v.2 g⁻¹⟩
      invFun := fun v => ⟨(v : Set X) * {g}, mul_singleton_mem_rankTwoVertices B N w₁ w₂ v.2 g⟩
      left_inv := fun v => Subtype.ext (by
        change (v : Set X) * {g⁻¹} * {g} = v
        rw [mul_assoc, Set.singleton_mul_singleton, inv_mul_cancel, Set.singleton_one, mul_one])
      right_inv := fun v => Subtype.ext (by
        change (v : Set X) * {g} * {g⁻¹} = v
        rw [mul_assoc, Set.singleton_mul_singleton, mul_inv_cancel, Set.singleton_one, mul_one]) }
  map_one' := Equiv.ext fun v => Subtype.ext (by
    change (v : Set X) * {(1 : X)⁻¹} = v
    rw [inv_one, Set.singleton_one, mul_one])
  map_mul' g h := Equiv.ext fun v => Subtype.ext (by
    change (v : Set X) * {(g * h)⁻¹} = (v : Set X) * {h⁻¹} * {g⁻¹}
    rw [mul_assoc, Set.singleton_mul_singleton, mul_inv_rev])

@[expose] def FaithfulOnBuilding : Prop :=
  ∀ g : X, (∀ v ∈ rankTwoVertices B N w₁ w₂, v * {g} = v) → g = 1

end RankTwoBuilding

section RootGroups

variable {X : Type*} [Group X]

@[expose] def IsRoot (n : ℕ) (i : ℤ) : Prop :=
  i ≠ 0 ∧ i.natAbs ≤ n

@[expose] def intList (i j : ℤ) : List ℤ :=
  (List.range (j + 1 - i).toNat).map fun k : ℕ => i + (k : ℤ)

@[expose] def chainProd (A : ℤ → Subgroup X) (l : List ℤ) : Set X :=
  (l.map fun k => (A k : Set X)).prod

@[expose] def conjBy (m : X) (A : Subgroup X) : Subgroup X :=
  A.map (MulAut.conj m⁻¹).toMonoidHom

@[expose] def rootPos (n : ℕ) (i : ℤ) : ZMod (2 * n) :=
  if 0 < i then ((i - 1 : ℤ) : ZMod (2 * n)) else (((n : ℤ) + (-i - 1) : ℤ) : ZMod (2 * n))

@[expose] def posRoot (n : ℕ) (p : ZMod (2 * n)) : ℤ :=
  if p.val < n then (p.val : ℤ) + 1 else -((p.val : ℤ) - n + 1)

@[expose] def arc (n : ℕ) (i j : ℤ) : List ℤ :=
  if (rootPos n j - rootPos n i).val ≤ n then
    (List.range ((rootPos n j - rootPos n i).val + 1)).map fun t => posRoot n (rootPos n i + t)
  else
    (List.range ((2 * n - (rootPos n j - rootPos n i).val) + 1)).map fun t =>
      posRoot n (rootPos n i - t)

structure IsRootGroupSystem (B N : Subgroup X) [(cartan B N).Normal] (w₁ w₂ : WeylGroup B N)
    (U : Subgroup X) (n : ℕ) (root : ℤ → Subgroup X) : Prop where
  ne_bot : ∀ i, IsRoot n i → root i ≠ ⊥
  invariant : ∀ i, IsRoot n i → ∀ h ∈ B ⊓ N, ∀ x ∈ root i, h * x * h⁻¹ ∈ root i
  carrier_eq : (U : Set X) = chainProd root (intList 1 n)
  unique : ∀ f g : ℤ → X, (∀ k ∈ intList 1 n, f k ∈ root k) → (∀ k ∈ intList 1 n, g k ∈ root k) →
    ((intList 1 n).map f).prod = ((intList 1 n).map g).prod → ∀ k ∈ intList 1 n, f k = g k
  reverse_eq : ∀ i j : ℤ, 1 ≤ i → i ≤ j → j ≤ n →
    chainProd root (intList i j) = chainProd root (intList i j).reverse
  subgroup : ∀ i j : ℤ, 1 ≤ i → i ≤ j → j ≤ n →
    ∃ V : Subgroup X, (V : Set X) = chainProd root (intList i j) ∧ V ≤ U ∧
      (1 < i → ∀ x ∈ root (i - 1), ∀ v ∈ V, x * v * x⁻¹ ∈ V) ∧
      (j < n → ∀ x ∈ root (j + 1), ∀ v ∈ V, x * v * x⁻¹ ∈ V)
  action₁ : ∀ m : N, (m : WeylGroup B N) = w₁ →
    conjBy (m : X) (root 1) = root (-1) ∧ conjBy (m : X) (root (-1)) = root 1 ∧
      ∀ i : ℤ, 2 ≤ i → i ≤ n →
        conjBy (m : X) (root i) = root ((n : ℤ) + 2 - i) ∧
          conjBy (m : X) (root (-i)) = root (-((n : ℤ) + 2 - i))
  action₂ : ∀ m : N, (m : WeylGroup B N) = w₂ →
    conjBy (m : X) (root n) = root (-(n : ℤ)) ∧ conjBy (m : X) (root (-(n : ℤ))) = root n ∧
      ∀ i : ℤ, 1 ≤ i → i ≤ (n : ℤ) - 1 →
        conjBy (m : X) (root i) = root ((n : ℤ) - i) ∧
          conjBy (m : X) (root (-i)) = root (-((n : ℤ) - i))
  meet_one : ∀ x ∈ B, x ∈ chainProd root ((intList 1 n).map Neg.neg) → x = 1

end RootGroups

section RankTwoSystem

open Classical in
structure RankTwoSystem (X : Type*) [Group X] (n : ℕ) where
  B : Subgroup X
  N : Subgroup X
  [normal : (cartan B N).Normal]
  w₁ : WeylGroup B N
  w₂ : WeylGroup B N
  U : Subgroup X
  root : ℤ → Subgroup X
  isTits : IsTitsSystem B N {w₁, w₂}
  w₁_ne_w₂ : w₁ ≠ w₂
  isSplit : IsSplit B N U
  isSaturated : IsSaturated B N
  faithful : FaithfulOnBuilding B N w₁ w₂
  card_weyl : Nat.card (WeylGroup B N) = 2 * n
  three_le : 3 ≤ n
  roots : IsRootGroupSystem B N w₁ w₂ U n root

attribute [instance] RankTwoSystem.normal

namespace RankTwoSystem

variable {X : Type*} [Group X] {n : ℕ} (D : RankTwoSystem X n)

abbrev Weyl : Type _ :=
  WeylGroup D.B D.N

@[expose] def P₁ : Subgroup X :=
  parabolic D.B D.N {D.w₁}

@[expose] def P₂ : Subgroup X :=
  parabolic D.B D.N {D.w₂}

abbrev Vertex : Type _ :=
  ↥(rankTwoVertices D.B D.N D.w₁ D.w₂)

@[expose] def graph : SimpleGraph D.Vertex :=
  buildingGraph D.B D.N D.w₁ D.w₂

@[expose] def action : X →* Equiv.Perm D.Vertex :=
  rankTwoAction D.B D.N D.w₁ D.w₂

@[expose] def Xplus : Subgroup X :=
  Subgroup.closure (⋃ i ∈ {i : ℤ | IsRoot n i}, (D.root i : Set X))

@[expose] def IsTypeOne (v : D.Vertex) : Prop :=
  ∃ x : X, (v : Set X) = (D.P₁ : Set X) * {x}

@[expose] def IsTypeTwo (v : D.Vertex) : Prop :=
  ∃ x : X, (v : Set X) = (D.P₂ : Set X) * {x}

@[expose] def w₀ : D.Weyl :=
  altWord D.w₁ D.w₂ n

@[expose] def vertex₁ : D.Vertex :=
  ⟨(D.P₁ : Set X) * {1}, Or.inl ⟨1, rfl⟩⟩

@[expose] def vertex₂ : D.Vertex :=
  ⟨(D.P₂ : Set X) * {1}, Or.inr ⟨1, rfl⟩⟩

@[expose] def graphMinusTop : SimpleGraph D.Vertex where
  Adj v v' := D.graph.Adj v v' ∧ ¬ ((v : Set X) ∩ (v' : Set X) ⊆ dc D.B D.N D.w₀)
  symm := ⟨fun _ _ h => ⟨D.graph.symm.symm _ _ h.1, by simpa only [Set.inter_comm] using h.2⟩⟩
  loopless := ⟨fun _ h => D.graph.loopless.irrefl _ h.1⟩

@[expose] def sideOne (i : ℕ) : Set D.Vertex :=
  {v | D.graphMinusTop.dist v D.vertex₁ = i ∧
    D.graphMinusTop.dist v D.vertex₁ < D.graphMinusTop.dist v D.vertex₂}

@[expose] def sideTwo (i : ℕ) : Set D.Vertex :=
  {v | D.graphMinusTop.dist v D.vertex₂ = i ∧
    D.graphMinusTop.dist v D.vertex₂ < D.graphMinusTop.dist v D.vertex₁}

@[expose] def Uminus : Set X :=
  chainProd D.root ((intList 1 n).map Neg.neg)

@[expose] def UwMinus (m : D.N) : Set X :=
  {x | x ∈ D.U ∧ (m : X) * x * (m : X)⁻¹ ∈ D.Uminus}

@[expose] def UwPlus (m : D.N) : Set X :=
  {x | x ∈ D.U ∧ (m : X) * x * (m : X)⁻¹ ∈ D.U}

end RankTwoSystem

end RankTwoSystem

section GraphNotions

variable {V : Type*}

@[expose] def graphAut (G : SimpleGraph V) : Subgroup (Equiv.Perm V) where
  carrier := {σ | ∀ v w, G.Adj (σ v) (σ w) ↔ G.Adj v w}
  mul_mem' := fun {σ τ} hσ hτ v w => by
    simp only [Equiv.Perm.coe_mul, Function.comp_apply]
    rw [hσ, hτ]
  one_mem' := fun v w => by simp
  inv_mem' := fun {σ} hσ v w => by
    rw [← hσ]
    simp

@[expose] def IsGLSPath (G : SimpleGraph V) (l : List V) : Prop :=
  (∀ a b : V, [a, b] <:+: l → G.Adj a b) ∧ ∀ a b : V, [a, b, a] <:+: l → False

@[expose] def interiorVertices (l : List V) : List V :=
  l.tail.dropLast

@[expose] def pathFixer (G : SimpleGraph V) (l : List V) : Subgroup (Equiv.Perm V) :=
  graphAut G ⊓ ⨅ v ∈ interiorVertices l, ⨅ w ∈ G.neighborSet v,
    MulAction.stabilizer (Equiv.Perm V) w

@[expose] def pathFixerSpan (G : SimpleGraph V) (n : ℕ) : Subgroup (Equiv.Perm V) :=
  Subgroup.closure (⋃ l ∈ {l : List V | IsGLSPath G l ∧ l.length = n + 1},
    (pathFixer G l : Set (Equiv.Perm V)))

end GraphNotions

end CFSG.GH74.BNPair
