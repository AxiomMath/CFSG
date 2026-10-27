module

public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.SupIndep

public section

namespace CFSG.LieType.Steinberg

open scoped commutatorElement

section RootSystem

variable {ι : Type*}

@[expose] def ht [Fintype ι] (v : ι → ℤ) : ℤ := ∑ j, v j

@[expose] def LinIndepPair (α β : ι → ℤ) : Prop :=
  ∀ a b : ℤ, a • α + b • β = 0 → a = 0 ∧ b = 0

@[expose] def IsNegMultiple (α β : ι → ℤ) : Prop :=
  ∃ c : ℝ, c < 0 ∧ ∀ j, (β j : ℝ) = c * α j

@[expose] def cone (Φ : Set (ι → ℤ)) (α β : ι → ℤ) : Set (ι → ℤ) :=
  {γ | γ ∈ Φ ∧ ∃ a b : ℕ, γ = a • α + b • β}

@[expose] def openCone (Φ : Set (ι → ℤ)) (α β : ι → ℤ) : Set (ι → ℤ) :=
  {γ | γ ∈ Φ ∧ ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ γ = a • α + b • β}

@[expose] def wordAct (s : ι → (ι → ℤ) →+ (ι → ℤ)) : List ι → (ι → ℤ) → (ι → ℤ)
  | [] => id
  | i :: w => fun v => s i (wordAct s w v)

variable [Fintype ι] [DecidableEq ι]

structure RootSystem (ι : Type*) [Fintype ι] [DecidableEq ι] where
  roots : Set (ι → ℤ)
  finite_roots : roots.Finite
  zero_notMem : (0 : ι → ℤ) ∉ roots
  neg_mem : ∀ γ ∈ roots, -γ ∈ roots
  sign : ∀ γ ∈ roots, (∀ j, 0 ≤ γ j) ∨ ∀ j, γ j ≤ 0
  single_mem : ∀ i, (Pi.single i 1 : ι → ℤ) ∈ roots
  proportional : ∀ γ ∈ roots, ∀ δ ∈ roots, ¬ LinIndepPair γ δ →
    γ = δ ∨ γ = -δ ∨ γ = 2 • δ ∨ γ = -(2 • δ) ∨ δ = 2 • γ ∨ δ = -(2 • γ)
  refl : ι → (ι → ℤ) →+ (ι → ℤ)
  refl_apply_of_ne : ∀ i v j, j ≠ i → refl i v j = v j
  refl_single : ∀ i, refl i (Pi.single i 1) = -Pi.single i 1
  refl_refl : ∀ i v, refl i (refl i v) = v
  refl_mem : ∀ i γ, γ ∈ roots → refl i γ ∈ roots
  exists_word : ∀ γ ∈ roots, (∀ δ ∈ roots, γ ≠ 2 • δ) →
    ∃ (w : List ι) (i : ι), γ = wordAct refl w (Pi.single i 1)
  sum_ne_two_smul : ∀ δ ∈ roots, ∀ δ' ∈ roots, ∀ ε ∈ roots, 0 < ht δ → ht δ = ht δ' → δ ≠ δ' →
    (∀ ζ ∈ roots, δ ≠ 2 • ζ) → (∀ ζ ∈ roots, δ' ≠ 2 • ζ) → δ + δ' ≠ 2 • ε

namespace RootSystem

variable (Φ : RootSystem ι)

@[expose] def pos : Set (ι → ℤ) := {γ | γ ∈ Φ.roots ∧ 0 < ht γ}

@[expose] def neg : Set (ι → ℤ) := {γ | γ ∈ Φ.roots ∧ ht γ < 0}

@[expose] def IsIndiv (γ : ι → ℤ) : Prop := ∀ δ ∈ Φ.roots, γ ≠ 2 • δ

end RootSystem

end RootSystem

section StGroup

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [Group K]
variable (Φ : RootSystem ι) (X : (ι → ℤ) → Subgroup K)

abbrev Symbol : Type _ := {p : (ι → ℤ) × K // p.1 ∈ Φ.roots ∧ p.2 ∈ X p.1}

abbrev FreeSt : Type _ := FreeGroup (Symbol Φ X)

@[expose] def piF : FreeSt Φ X →* K := FreeGroup.lift fun s => s.1.2

@[expose] def freeSub (Ψ : Set (ι → ℤ)) : Subgroup (FreeSt Φ X) :=
  Subgroup.closure (FreeGroup.of '' {s | s.1.1 ∈ Ψ})

@[expose] def rel1 : Set (FreeSt Φ X) :=
  {w | ∃ α ∈ Φ.roots, ∃ β ∈ Φ.roots, ¬ IsNegMultiple α β ∧
    w ∈ freeSub Φ X (cone Φ.roots α β) ∧ piF Φ X w = 1}

@[expose] def rel2 : Set (FreeSt Φ X) :=
  {w | ∃ i : ι, w ∈ freeSub Φ X {Pi.single i 1, -Pi.single i 1} ∧ piF Φ X w = 1}

@[expose] def relN : Subgroup (FreeSt Φ X) := Subgroup.normalClosure (rel1 Φ X ∪ rel2 Φ X)

instance relN_normal : (relN Φ X).Normal := Subgroup.normalClosure_normal

abbrev StGroup : Type _ := FreeSt Φ X ⧸ relN Φ X

theorem relN_le_ker : relN Φ X ≤ (piF Φ X).ker := by
  refine Subgroup.normalClosure_le_normal ?_
  rintro w (⟨-, -, -, -, -, -, hw⟩ | ⟨-, -, hw⟩) <;> exact hw

@[expose] noncomputable def stPi : StGroup Φ X →* K :=
  QuotientGroup.lift (relN Φ X) (piF Φ X) (relN_le_ker Φ X)

end StGroup

section RootGroupData

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

structure RootGroupData (Φ : RootSystem ι) (K : Type*) [Group K] where
  X : (ι → ℤ) → Subgroup K
  n : ι → K

namespace RootGroupData

variable {Φ : RootSystem ι} {K : Type*} [Group K] (D : RootGroupData Φ K)

@[expose] def rankOne (i : ι) : Subgroup K := D.X (Pi.single i 1) ⊔ D.X (-Pi.single i 1)

@[expose] def torus (i : ι) : Subgroup K :=
  D.rankOne i ⊓ Subgroup.normalizer (D.X (Pi.single i 1) : Set K) ⊓
    Subgroup.normalizer (D.X (-Pi.single i 1) : Set K)

@[expose] def posPart : Subgroup K := ⨆ γ ∈ Φ.pos, D.X γ

@[expose] def negPart : Subgroup K := ⨆ γ ∈ Φ.neg, D.X γ

@[expose] def torusPart : Subgroup K := ⨆ i, D.torus i

@[expose] def ProdInjective (L : List (ι → ℤ)) : Prop :=
  ∀ f g : (ι → ℤ) → K, (∀ γ ∈ L, f γ ∈ D.X γ) → (∀ γ ∈ L, g γ ∈ D.X γ) →
    (L.map f).prod = (L.map g).prod → ∀ γ ∈ L, f γ = g γ

structure IsSteinberg : Prop where
  ne_bot : ∀ γ ∈ Φ.roots, D.X γ ≠ ⊥
  two_smul_le : ∀ γ ∈ Φ.roots, 2 • γ ∈ Φ.roots → D.X (2 • γ) ≤ D.X γ
  commutator_mem : ∀ γ ∈ Φ.roots, ∀ δ ∈ Φ.roots, LinIndepPair γ δ →
    ∀ x ∈ D.X γ, ∀ y ∈ D.X δ, ⁅x, y⁆ ∈ ⨆ ε ∈ openCone Φ.roots γ δ, D.X ε
  exists_posList : ∃ L : List (ι → ℤ), L.Nodup ∧
    (∀ γ, γ ∈ L ↔ γ ∈ Φ.pos ∧ Φ.IsIndiv γ) ∧ L.Pairwise (fun γ δ => ht γ ≤ ht δ) ∧
    D.ProdInjective L
  exists_negList : ∃ L : List (ι → ℤ), L.Nodup ∧
    (∀ γ, γ ∈ L ↔ γ ∈ Φ.neg ∧ Φ.IsIndiv γ) ∧ L.Pairwise (fun γ δ => ht δ ≤ ht γ) ∧
    D.ProdInjective L
  posPart_inf_negPart : D.posPart ⊓ D.negPart = ⊥
  n_mem : ∀ i, D.n i ∈ D.rankOne i
  map_conj_n : ∀ i, ∀ γ ∈ Φ.roots,
    (D.X γ).map (MulAut.conj (D.n i)).toMonoidHom = D.X (Φ.refl i γ)
  torus_le_normalizer : ∀ i, ∀ γ ∈ Φ.roots, D.torus i ≤ Subgroup.normalizer (D.X γ : Set K)
  rankOne_bruhat : ∀ i, ∀ g ∈ D.rankOne i,
    (∃ h ∈ D.torus i, ∃ u ∈ D.X (Pi.single i 1), g = h * u) ∨
      ∃ u ∈ D.X (Pi.single i 1), ∃ h ∈ D.torus i, ∃ v ∈ D.X (Pi.single i 1),
        g = u * D.n i * h * v
  eq_one_of_mem_normalizer : ∀ i, ∀ u ∈ D.X (Pi.single i 1),
    u ∈ Subgroup.normalizer (D.X (-Pi.single i 1) : Set K) → u = 1
  torus_commute : ∀ i j, ∀ h ∈ D.torus i, ∀ h' ∈ D.torus j, Commute h h'
  torus_iSupIndep : iSupIndep D.torus
  torusPart_inf_posPart : D.torusPart ⊓ D.posPart = ⊥

end RootGroupData

end RootGroupData

end CFSG.LieType.Steinberg
