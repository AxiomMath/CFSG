module

public import CFSG.Quasithin.Background.A1cTransfer
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin

@[expose] def IsFermatOrMersenne (p : ℕ) : Prop :=
  p.Prime ∧ ((∃ k : ℕ, p = 2 ^ 2 ^ k + 1) ∨ (∃ k : ℕ, 2 ≤ k ∧ p = 2 ^ k - 1))

section Lie

variable {G : Type} [Group G]

@[expose] def IsBorelIn (B L : Subgroup G) : Prop :=
  ∃ P : Subgroup G, IsSylowTwoOf P L ∧ B = L ⊓ Subgroup.normalizer (P : Set G)

@[expose] def IsRankTwoEvenType (L : Subgroup G) : Prop :=
  (∃ n : ℕ, 1 ≤ n ∧ StatedClassicalModel ↥L .PSL 3 2 n) ∨
    (∃ n : ℕ, 2 ≤ n ∧ StatedClassicalModel ↥L .PSp 2 2 n) ∨
    Nonempty (↥L ≃* alternatingGroup (Fin 6)) ∨
    StatedClassicalModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 2 2

@[expose] def NontrivialOnDynkin (M S L : Subgroup G) : Prop :=
  ∀ X : Subgroup G, M ⊓ L ≤ X → X ≤ L →
    S ⊓ Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (X : Set G) →
      X = M ⊓ L ∨ X = L

@[expose] def IsFourSubgroup (F : Subgroup G) : Prop :=
  IsElemAbelian 2 F ∧ Nat.card F = 4

@[expose] def InducesAut (t : G) (L : Subgroup G) {X : Type*} [Group X] (φ : ↥L ≃* X)
    (σ : X ≃* X) : Prop :=
  t ∈ Subgroup.normalizer (L : Set G) ∧
    ∀ y y' : ↥L, (y' : G) = t⁻¹ * y * t → φ y' = σ (φ y)

end Lie

section UPairs

variable {G : Type*} [Group G]

@[expose] def IsUPair (M H U HU : Subgroup G) : Prop :=
  IsWitnessPair M U HU ∧ HU ≤ H

@[expose] def IsUStarPair (M H U HU : Subgroup G) : Prop :=
  IsUPair M H U HU ∧ ∀ V : Subgroup G, IsWitness M V → Nat.card V ≤ Nat.card U

end UPairs

namespace A6Models

@[expose] def perm10 (cs : List (List (Fin 10))) : Equiv.Perm (Fin 10) :=
  (cs.map List.formPerm).prod

@[expose] def tAdd : Equiv.Perm (Fin 10) := perm10 [[0, 1, 2], [3, 4, 5], [6, 7, 8]]

@[expose] def tSq : Equiv.Perm (Fin 10) := perm10 [[1, 6, 2, 3], [4, 7, 8, 5]]

@[expose] def tInv : Equiv.Perm (Fin 10) := perm10 [[0, 9], [1, 2], [4, 7], [5, 8]]

@[expose] def tMul : Equiv.Perm (Fin 10) := perm10 [[1, 4, 6, 7, 2, 8, 3, 5]]

@[expose] def tFrob : Equiv.Perm (Fin 10) := perm10 [[3, 6], [4, 7], [5, 8]]

@[expose] def tMulFrob : Equiv.Perm (Fin 10) := perm10 [[1, 4, 2, 8], [3, 7, 6, 5]]

@[expose] def psl29 : Subgroup (Equiv.Perm (Fin 10)) :=
  Subgroup.closure {tAdd, tSq, tInv}

@[expose] def pgl29 : Subgroup (Equiv.Perm (Fin 10)) :=
  Subgroup.closure {tAdd, tSq, tInv, tMul}

@[expose] def m10 : Subgroup (Equiv.Perm (Fin 10)) :=
  Subgroup.closure {tAdd, tSq, tInv, tMulFrob}

@[expose] def autA6 : Subgroup (Equiv.Perm (Fin 10)) :=
  Subgroup.closure {tAdd, tSq, tInv, tMul, tFrob}

end A6Models

end CFSG.QuasithinUnique
