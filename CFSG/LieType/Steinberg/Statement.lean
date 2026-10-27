module

public import CFSG.LieType.Steinberg.Basic
public import Mathlib.GroupTheory.PresentedGroup

public section

namespace CFSG.LieType.Steinberg

open scoped commutatorElement

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

section PartA

variable {K : Type*} [Group K]

@[expose] def PresentationA (Φ : RootSystem ι) (X : (ι → ℤ) → Subgroup K) : Prop :=
  (⨆ γ ∈ Φ.roots, X γ = ⊤) ∧ Function.Bijective (stPi Φ X) ∧
    ∀ (G : Type*) [Group G] (φ : Symbol Φ X → G),
      (∀ w ∈ rel1 Φ X ∪ rel2 Φ X, FreeGroup.lift φ w = 1) →
        ∃! ψ : K →* G, ∀ s : Symbol Φ X, ψ s.1.2 = φ s

@[expose] def RedundantR2 (Φ : RootSystem ι) (X : (ι → ℤ) → Subgroup K) : Prop :=
  Function.Bijective (QuotientGroup.lift (Subgroup.normalClosure (rel1 Φ X)) (piF Φ X)
    (Subgroup.normalClosure_le_normal (by
      rintro w ⟨-, -, -, -, -, -, hw⟩
      exact hw)))

end PartA

section PartB

variable (Φ : RootSystem ι) (k : Type*) [Field k] {K : Type*} [Group K]

@[expose] def expPairs (α β : ι → ℤ) : Set (ℕ × ℕ) :=
  {p | 0 < p.1 ∧ 0 < p.2 ∧ p.1 • α + p.2 • β ∈ Φ.roots}

structure CommOrder where
  list : (ι → ℤ) → (ι → ℤ) → List (ℕ × ℕ)
  nodup : ∀ α β, (list α β).Nodup
  mem_iff : ∀ α ∈ Φ.roots, ∀ β ∈ Φ.roots, α + β ≠ 0 →
    ∀ p, p ∈ list α β ↔ p ∈ expPairs Φ α β

abbrev ChevGen : Type _ := {γ // γ ∈ Φ.roots} × k

variable {Φ k}

open _root_.Classical in
@[expose] noncomputable def chevOf (γ : ι → ℤ) (c : k) : FreeGroup (ChevGen Φ k) :=
  if h : γ ∈ Φ.roots then FreeGroup.of (⟨γ, h⟩, c) else 1

variable (Φ k)

@[expose] def relA : Set (FreeGroup (ChevGen Φ k)) :=
  {w | ∃ γ ∈ Φ.roots, ∃ c d : k,
    w = chevOf (Φ := Φ) γ c * chevOf (Φ := Φ) γ d * (chevOf (Φ := Φ) γ (c + d))⁻¹}

@[expose] def relB (O : CommOrder Φ) (C : (ι → ℤ) → (ι → ℤ) → ℕ × ℕ → ℤ) :
    Set (FreeGroup (ChevGen Φ k)) :=
  {w | ∃ α ∈ Φ.roots, ∃ β ∈ Φ.roots, α + β ≠ 0 ∧ ∃ c d : k,
    w = ⁅chevOf (Φ := Φ) α c, chevOf (Φ := Φ) β d⁆ *
      ((O.list α β).map fun p =>
        chevOf (Φ := Φ) (p.1 • α + p.2 • β) ((C α β p : k) * c ^ p.1 * d ^ p.2)).prod⁻¹}

abbrev ChevPresented (O : CommOrder Φ) (C : (ι → ℤ) → (ι → ℤ) → ℕ × ℕ → ℤ) : Type _ :=
  PresentedGroup (relA Φ k ∪ relB Φ k O C)

variable {Φ k}

@[expose] def CommutatorFormula (x : (ι → ℤ) → k → K) (O : CommOrder Φ)
    (C : (ι → ℤ) → (ι → ℤ) → ℕ × ℕ → ℤ) : Prop :=
  ∀ α ∈ Φ.roots, ∀ β ∈ Φ.roots, α + β ≠ 0 → ∀ c d : k,
    ⁅x α c, x β d⁆ =
      ((O.list α β).map fun p => x (p.1 • α + p.2 • β) ((C α β p : k) * c ^ p.1 * d ^ p.2)).prod

@[expose] def chevEval (x : (ι → ℤ) → k → K) (g : ChevGen Φ k) : K := x g.1.1 g.2

@[expose] def PresentationB (x : (ι → ℤ) → k → K) : Prop :=
  ∀ O : CommOrder Φ,
    (∃ C : (ι → ℤ) → (ι → ℤ) → ℕ × ℕ → ℤ,
      (∀ α ∈ Φ.roots, ∀ β ∈ Φ.roots, ∀ p ∈ expPairs Φ α β, (C α β p).natAbs ∈ ({1, 2, 3} : Set ℕ)) ∧
        CommutatorFormula x O C) ∧
    ∀ C : (ι → ℤ) → (ι → ℤ) → ℕ × ℕ → ℤ, CommutatorFormula x O C →
      ∃ h : ∀ r ∈ relA Φ k ∪ relB Φ k O C, FreeGroup.lift (chevEval x) r = 1,
        Function.Bijective (PresentedGroup.toGroup h)

@[expose] def IsParametrization (X : (ι → ℤ) → Subgroup K) (x : (ι → ℤ) → k → K) : Prop :=
  ∀ γ ∈ Φ.roots, (∀ g, g ∈ X γ ↔ ∃ c, x γ c = g) ∧ (∀ c d, x γ (c + d) = x γ c * x γ d) ∧
    Function.Injective (x γ)

end PartB

section Twisted

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

@[expose] def orbitSum (o : ι → κ) (v : ι → ℤ) : κ → ℤ :=
  fun c => ∑ j ∈ Finset.univ.filter (fun j => o j = c), v j

@[expose] def twistedRoots (Φ : Set (ι → ℤ)) (o : ι → κ) : Set (κ → ℤ) := orbitSum o '' Φ

@[expose] def twistedRootSubgroup {G : Type*} [Group G] (Φ : Set (ι → ℤ)) (o : ι → κ)
    (X : (ι → ℤ) → Subgroup G) (σ : G →* G) (β : κ → ℤ) : Subgroup G :=
  (⨆ α ∈ Φ, ⨆ (_ : ∃ c : ℕ, 0 < c ∧ orbitSum o α = c • β), X α) ⊓
    MonoidHom.eqLocus σ (MonoidHom.id G)

end Twisted

end CFSG.LieType.Steinberg
