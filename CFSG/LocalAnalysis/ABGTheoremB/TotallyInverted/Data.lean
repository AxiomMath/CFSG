module

public import CFSG.LocalAnalysis.ABGTheoremB.Setting

public noncomputable section

namespace CFSG.ABGTheoremB

open CFSG.QuasiDihedralFusion CFSG.ABGLocalTools CFSG.ABGQGroups
open scoped Pointwise Classical

namespace Setting

variable {G : Type} [Group G] (σ : Setting G)

@[expose] def x₃ : G := σ.x * σ.x₂

@[expose] def xs (i : Fin 3) : G := ![σ.x, σ.x₂, σ.x₃] i

@[expose] def Ns (i : Fin 3) : Subgroup G := Subgroup.centralizer ({σ.xs i} : Set G)

@[expose] def DeltaEpsMinus : Prop :=
  (σ.height = 1 ∧ σ.q % 4 = 3) ∨ (σ.height ≠ 1 ∧ σ.q % 4 = 1)

@[expose] def F₀ : Subgroup G := σ.D ⊓ Subgroup.centralizer (σ.T : Set G)

@[expose] def Ps (r : ℕ) (i : Fin 3) : Subgroup G := pCoreIn r (σ.Ns i)

end Setting

namespace TotallyInverted

variable {G : Type} [Group G]

@[expose] def conjSub (g : G) (X : Subgroup G) : Subgroup G :=
  X.map (MulAut.conj g).toMonoidHom

structure Data [Finite G] (σ : Setting G) (r : ℕ) where
  prime : r.Prime
  ne_two : r ≠ 2
  dvd : r ∣ Nat.card σ.ON
  exceptional : σ.Exceptional r
  totallyInverted : σ.TotallyInverted r
  a : G
  a_mem : a ∈ σ.M
  a_three : ∃ k : ℕ, a ^ 3 ^ k = 1
  a_cycle : ∀ i : Fin 3, a * σ.xs i * a⁻¹ = σ.xs (i + 1)
  d : G
  d_mem : d ∈ σ.D
  d_x : d * σ.x * d⁻¹ = σ.x
  d_x₂ : d * σ.x₂ * d⁻¹ = σ.x₃
  M_eq : σ.M = σ.C ⊔ Subgroup.closure ({d, a} : Set G)
  F₀_sylow : IsSylowOf 2 σ.F₀ σ.C
  F₀_abelian : ∀ g ∈ σ.F₀, ∀ h ∈ σ.F₀, g * h = h * g
  F₀_omega : ∀ g ∈ σ.F₀, g ^ 2 = 1 → g ∈ σ.T
  L_normal : σ.N ≤ Subgroup.normalizer (σ.L : Set G)
  T_le_L : σ.T ≤ σ.L
  J : Subgroup G
  J_le : J ≤ σ.L₀
  L₀_eq : σ.L₀ = J ⊔ σ.ON
  J_centralizes : J ≤ Subgroup.centralizer (σ.ON : Set G)
  J_normal : σ.N ≤ Subgroup.normalizer (J : Set G)
  J_inf : J ⊓ σ.ON = ⊥ ∨ (σ.q = 9 ∧ σ.height = 1 ∧ Nat.card (J ⊓ σ.ON : Subgroup G) = 3)
  J_sl2 : J ⊓ σ.ON = ⊥ → ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = σ.q ∧
    Nonempty (J ≃* Matrix.SpecialLinearGroup (Fin 2) F)
  W : Subgroup G
  W_eq : W = oddCoreIn (σ.C ⊓ J)
  W_cyclic : IsCyclic W
  W_coprime : ¬ r ∣ Nat.card W
  Op_C : pCoreIn r σ.C = ⊥
  P_conj : ∀ i : Fin 3, conjSub a (σ.Ps r i) = σ.Ps r (i + 1)
  P_abelian : ∀ i : Fin 3, ∀ g ∈ σ.Ps r i, ∀ h ∈ σ.Ps r i, g * h = h * g
  P_centralized : ∀ i : Fin 3, σ.Ps r i ≤ Subgroup.centralizer ({σ.xs i} : Set G)
  P_inverted : ∀ i j : Fin 3, j ≠ i → ∀ u ∈ σ.Ps r i, σ.xs j * u * (σ.xs j)⁻¹ = u⁻¹
  P_sylow : IsSylowOf r (σ.Ps r 0) σ.ON
  Q : Fin 3 → Subgroup G
  Qs : Fin 3 → Subgroup G
  Q_trivial : ¬ (σ.DeltaEpsMinus ∧ r ∣ σ.q) → ∀ i, Q i = ⊥ ∧ Qs i = ⊥
  Q_le : ∀ i, Q i ≤ conjSub (a ^ (i : ℕ)) J ∧ Qs i ≤ conjSub (a ^ (i : ℕ)) J
  Q_pgroup : ∀ i, IsPGroup r (Q i) ∧ IsPGroup r (Qs i)
  Q_C : ∀ i, σ.C ≤ Subgroup.normalizer (Q i : Set G) ∧ σ.C ≤ Subgroup.normalizer (Qs i : Set G)
  Q_conj : ∀ i, conjSub a (Q i) = Q (i + 1) ∧ conjSub a (Qs i) = Qs (i + 1)
  Q_cases : σ.DeltaEpsMinus ∧ r ∣ σ.q → ∀ i : Fin 3,
    Q i ≠ Qs i ∧ Nat.card (Q i) = σ.q ∧ Nat.card (Qs i) = σ.q ∧
    conjSub (a ^ (i : ℕ)) J = Q i ⊔ Qs i ∧
    (∃ z ∈ conjSub (a ^ (i : ℕ)) σ.D, conjSub z (Q i) = Qs i) ∧
    (∀ X : Subgroup G, X ≤ conjSub (a ^ (i : ℕ)) J → IsPGroup r X →
      σ.C ≤ Subgroup.normalizer (X : Set G) → X ≤ Q i ∨ X ≤ Qs i) ∧
    (∀ X : Subgroup G, X ≤ Q i → σ.C ≤ Subgroup.normalizer (X : Set G) → X = ⊥ ∨ X = Q i) ∧
    (∀ X : Subgroup G, X ≤ Qs i → σ.C ≤ Subgroup.normalizer (X : Set G) → X = ⊥ ∨ X = Qs i) ∧
    Q i ≤ Subgroup.centralizer (σ.Ps r i : Set G) ∧
    Qs i ≤ Subgroup.centralizer (σ.Ps r i : Set G)
  P : Subgroup G
  P_sylowC : IsSylowOf r P σ.C
  P_D : σ.D ≤ Subgroup.normalizer (P : Set G)
  P_L : P ⊓ σ.L = ⊥
  lemma71 : ∀ i : Fin 3, maximals (signalizers (σ.Ns i) σ.C r) =
    if σ.DeltaEpsMinus ∧ r ∣ σ.q then {σ.Ps r i ⊔ Q i, σ.Ps r i ⊔ Qs i} else {σ.Ps r i}
  lemma72 : ∀ (i : Fin 3) (R : Subgroup G), IsSylowOf r R σ.C →
    {U | U ∈ maximals (signalizersPerm (σ.Ns i) σ.T σ.C r) ∧ R ≤ U} =
      if σ.DeltaEpsMinus ∧ r ∣ σ.q then
        {R ⊔ Q i ⊔ σ.Ps r i, R ⊔ Qs i ⊔ σ.Ps r i} else {R ⊔ σ.Ps r i}

end TotallyInverted

end CFSG.ABGTheoremB
