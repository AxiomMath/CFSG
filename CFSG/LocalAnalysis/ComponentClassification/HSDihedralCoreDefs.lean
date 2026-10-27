module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.GroupTheory.ABGLocalTools.Basic

public noncomputable section

namespace CFSG.ComponentClassification.HSDihedral

open CFSG Subgroup CFSG.ABGLocalTools

variable {X : Type} [Group X] {A : Type} [Group A]

structure LocalDatum (X : Type) [Group X] (A : Type) [Group A] where
  t : X
  S : Subgroup X
  D : Subgroup X
  ψ : ↥S →* A
  orderOf_t : orderOf t = 2
  sylow : IsSylowOf 2 S (centralizer ({t} : Set X))
  D_le : D ≤ S
  conj_mem_D : ∀ s ∈ S, ∀ d ∈ D, s * d * s⁻¹ ∈ D
  eq_one_of_mem_D : ∀ d (hd : d ∈ D), ψ ⟨d, D_le hd⟩ = 1 → d = 1
  t_mem_ker : ∀ ht : t ∈ S, ψ ⟨t, ht⟩ = 1
  t_not_mem_D : t ∉ D
  isCyclic_ker : IsCyclic ↥ψ.ker
  dihedral : ∃ n : ℕ, 2 ≤ n ∧ Nonempty (↥D ≃* DihedralGroup n)

namespace LocalDatum

variable (Δ : LocalDatum X A)

abbrev R : Subgroup A := Δ.ψ.range

abbrev Dbar : Subgroup A := (Δ.D.subgroupOf Δ.S).map Δ.ψ

abbrev Q : Subgroup X := Δ.ψ.ker.map Δ.S.subtype

abbrev CaseOne : Prop :=
  ∀ c ∈ Δ.R, (∀ d ∈ Δ.Dbar, c * d = d * c) → c ∈ Δ.Dbar

abbrev CaseTwo (k : A) : Prop :=
  k ∈ Δ.R ∧ (∀ d ∈ Δ.Dbar, k * d = d * k) ∧ k ∉ Δ.Dbar ∧ k ^ 2 = 1 ∧ 8 ≤ Nat.card Δ.D ∧
    ∀ c ∈ Δ.R, (∀ d ∈ Δ.Dbar, c * d = d * c) → c ∈ Δ.Dbar ∨ c * k ∈ Δ.Dbar

end LocalDatum

structure AutFacts (Δ : LocalDatum X A) : Prop where
  gen3 : ∀ R' : Subgroup A, R' ≤ Δ.R →
    ∃ s : Finset A, s.card ≤ 3 ∧ closure (s : Set A) = R'
  dichotomy : Δ.CaseOne ∨ ∃ k, Δ.CaseTwo k
  index_one : Δ.CaseOne → ∀ r₁ ∈ Δ.R, ∀ r₂ ∈ Δ.R, r₁ ∉ Δ.Dbar → r₂ ∉ Δ.Dbar →
    r₁ * r₂⁻¹ ∈ Δ.Dbar
  klein_one : Δ.CaseOne → ∀ E : Subgroup A, E ≤ Δ.Dbar → Nat.card E = 4 →
    (∀ e ∈ E, e ^ 2 = 1) → ∀ c ∈ Δ.R, (∀ e ∈ E, c * e = e * c) → c ∈ Δ.Dbar
  inv_one : Δ.CaseOne → ∀ σ ∈ Δ.R, σ ∉ Δ.Dbar → σ ^ 2 = 1 →
    Nat.card ↥(Δ.Dbar ⊓ centralizer ({σ} : Set A)) ≤ 2
  two : ∀ k, Δ.CaseTwo k → ∃ Tbar : Subgroup A, Tbar ≤ Δ.R ∧ Δ.Dbar ≤ Tbar ∧
    (∀ r ∈ Δ.R, r ^ 2 = 1 → r ∈ Tbar ∨ r * k ∈ Δ.Dbar) ∧
    (∀ δ ∈ Tbar, δ ∉ Δ.Dbar → δ * k ≠ k * δ) ∧
    (Nat.card Δ.D = 8 → ∀ r ∈ Δ.R, r ∈ Tbar ∨ r * k ∈ Tbar) ∧
    (Tbar ≠ Δ.Dbar → ∃ m : ℕ, Nonempty (↥Tbar ≃* DihedralGroup m))

end CFSG.ComponentClassification.HSDihedral
