module

public import CFSG.LocalAnalysis.ABGTheoremB.Basic
public import CFSG.GroupTheory.ABGLocalTools.Constraint
public import CFSG.GroupTheory.ABGQGroups.Defs

public noncomputable section

namespace CFSG.ABGTheoremB

open CFSG.QuasiDihedralFusion CFSG.ABGLocalTools CFSG.ABGQGroups
open scoped Pointwise

universe u

structure Setting (G : Type u) [Group G] where
  x : G
  x₂ : G
  S : Sylow 2 G
  height : ℕ
  p : ℕ
  f : ℕ
  L₀ : Subgroup G

@[expose] def WorkingHypothesisI (G : Type u) [Group G] : Prop :=
  ∀ H : Subgroup G, H ≠ ⊤ → IsQDGroup H → ∀ y ∈ H, orderOf y = 2 →
    ∀ T₁ : Subgroup G, T₁ ≤ H → IsKleinFour T₁ → y ∈ T₁ →
      ⁅T₁, oddCoreIn (H ⊓ Subgroup.centralizer ({y} : Set G))⁆ ≤ oddCoreIn H

namespace Setting

variable {G : Type u} [Group G] (σ : Setting G)

@[expose] def q : ℕ := σ.p ^ σ.f

@[expose] def N : Subgroup G := Subgroup.centralizer ({σ.x} : Set G)

@[expose] def ON : Subgroup G := oddCoreIn σ.N

@[expose] def T : Subgroup G := Subgroup.closure ({σ.x, σ.x₂} : Set G)

@[expose] def D : Subgroup G := (σ.S : Subgroup G) ⊓ Subgroup.normalizer (σ.T : Set G)

@[expose] def C : Subgroup G := Subgroup.centralizer (σ.T : Set G)

@[expose] def E : Subgroup G := oddCoreIn (Subgroup.centralizer ((σ.S : Subgroup G) : Set G))

@[expose] def L : Subgroup G := σ.L₀ ⊔ (σ.S : Subgroup G)

@[expose] def M : Subgroup G := Subgroup.normalizer (σ.C : Set G)

structure IsValid [Finite G] : Prop where
  simple : IsSimpleGroup G
  nonabelian : ∃ a b : G, a * b ≠ b * a
  sylow : HasQDOrWreathedSylowOfHeight G σ.height
  x_order : orderOf σ.x = 2
  x_mem_center : σ.x ∈ centerOf (σ.S : Subgroup G)
  center_involution : ∀ z ∈ centerOf (σ.S : Subgroup G), orderOf z = 2 → z = σ.x
  x₂_order : orderOf σ.x₂ = 2
  x₂_mem : σ.x₂ ∈ (σ.S : Subgroup G)
  commute : σ.x * σ.x₂ = σ.x₂ * σ.x
  x_ne_x₂ : σ.x ≠ σ.x₂
  T_normal : σ.height ≠ 1 → (σ.S : Subgroup G) ≤ Subgroup.normalizer (σ.T : Set G)
  p_prime : σ.p.Prime
  p_ne_two : σ.p ≠ 2
  one_le_f : 1 ≤ σ.f
  five_lt_q : 5 < σ.q
  L₀_le_N : σ.L₀ ≤ σ.N
  ON_le_L₀ : σ.ON ≤ σ.L₀
  N_le_normalizer_L₀ : σ.N ≤ Subgroup.normalizer (σ.L₀ : Set G)
  L₀_quotient : ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = σ.q ∧
    ∃ ψ : σ.L₀ →* Matrix.SpecialLinearGroup (Fin 2) F, Function.Surjective ψ ∧
      ψ.ker = σ.ON.subgroupOf σ.L₀

@[expose] def WorkingHypothesisII : Prop :=
  ∀ H : Subgroup G, H ≠ ⊤ → HasQDCharPower H σ.q → oddCoreIn H = ⊥

@[expose] def Stationary (r : ℕ) : Prop :=
  ∃ R : Subgroup G, IsSylowOf r R σ.ON ∧
    IsSylowOf r R (oddCoreIn (Subgroup.normalizer (R : Set G)))

@[expose] def Centralized (r : ℕ) : Prop :=
  ∃ R : Subgroup G, IsSylowOf r R σ.ON ∧ σ.T ≤ Subgroup.normalizer (R : Set G) ∧
    σ.T ≤ Subgroup.centralizer (R : Set G)

@[expose] def Inverted (r : ℕ) : Prop :=
  ∃ R : Subgroup G, IsSylowOf r R σ.ON ∧ σ.T ≤ Subgroup.normalizer (R : Set G) ∧
    ∀ y ∈ R, σ.x₂ * y * σ.x₂⁻¹ = y⁻¹

@[expose] def Ordinary (r : ℕ) : Prop :=
  σ.Stationary r ∧ (σ.Centralized r ∨ σ.Inverted r)

@[expose] def Exceptional (r : ℕ) : Prop := ¬ σ.Ordinary r

@[expose] def Constrained (r : ℕ) : Prop :=
  PConstrainedWithin r σ.N (CFSG.solvableRadical σ.N)

@[expose] def TotallyInverted (r : ℕ) : Prop :=
  ¬ r ∣ Nat.card (σ.C ⊓ σ.L : Subgroup G)

@[expose] def familyL (r : ℕ) : Set (Subgroup G) :=
  {H | IsPLocal r H ∧ (σ.L₀ : Set G) ⊆ (H : Set G) * (σ.ON : Set G) ∧ σ.D ≤ H ∧
    ∃ R : Subgroup G, IsSylowOf r R σ.ON ∧ R ≤ H}

@[expose] def TheoremBStar : Prop :=
  ∀ r : ℕ, r.Prime → r ∣ Nat.card σ.ON → σ.Ordinary r

end Setting

end CFSG.ABGTheoremB
