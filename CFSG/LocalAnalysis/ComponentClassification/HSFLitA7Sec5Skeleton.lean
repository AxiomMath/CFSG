module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Skeleton

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

inductive Sec5Case
  | E
  | H

namespace A7Base

variable {X : Type} [Group X] [Finite X] (S : A7Base X)

structure Sec5 (F : S.Frame) (T₁ : Subgroup X) where
  T₂ : Subgroup X
  R : Subgroup X
  Q : Subgroup X
  w : X
  g : X
  d : X
  w₁ : X
  w₂ : X
  case : Sec5Case
  orbit : ∀ e ∈ F.E₁, (∃ n ∈ normalizer (F.E₁ : Set X), n * S.t * n⁻¹ = e) ↔
    e = S.t ∨ e = S.t * S.z ∨ e = S.t * F.yF ∨ e = S.t * S.z * F.yF
  automizer : Nonempty (normalizer (F.E₁ : Set X) ⧸
    (centralizer (F.E₁ : Set X)).subgroupOf (normalizer (F.E₁ : Set X)) ≃* Equiv.Perm (Fin 4))
  zy_normal : ∀ n ∈ normalizer (F.E₁ : Set X),
    n * S.z * n⁻¹ ∈ closure {S.z, F.yF} ∧ n * F.yF * n⁻¹ ∈ closure {S.z, F.yF}
  k_fixed : ∀ n ∈ normalizer (F.E₁ : Set X), n * F.kF * n⁻¹ = F.kF
  normalizer_eq : normalizer (F.E₁ : Set X) = centralizer (F.E₁ : Set X) ⊔ R ⊔ zpowers d
  g_mem : g ∈ T₁
  g_E : F.E₁.map (MulAut.conj g).toMonoidHom = F.E₂
  g_t : g * S.t * g⁻¹ = S.t * F.kF
  g_k : g * F.kF * g⁻¹ = S.z * F.kF
  g_sq_mem : g ^ 2 ∈ T₂
  g_sq_not_mem : g ^ 2 ∉ S.data.T
  T₁_eq : T₁ = T₂ ⊔ zpowers g
  center_T₁ : CenterEq T₁ (zpowers S.z)
  not_sylow : ∃ P : Subgroup X, IsPGroup 2 P ∧ T₁ < P
  T₂_eq : T₂ = T₁ ⊓ normalizer (F.E₁ : Set X)
  T₂_eq_sup : T₂ = S.data.T ⊔ zpowers w
  card_T₂ : Nat.card T₂ = 64
  w_sq : w ^ 2 = 1
  w_t : w * S.t * w⁻¹ = S.t * S.z
  w_x : w * F.xF = F.xF * w
  w_y : w * F.yF = F.yF * w
  w_k : w * F.kF = F.kF * w
  isPGroup_R : IsPGroup 2 R
  R_le : R ≤ normalizer (F.E₁ : Set X)
  R_maximal : ∀ P : Subgroup X, IsPGroup 2 P → R ≤ P → P ≤ normalizer (F.E₁ : Set X) → P = R
  T₂_le : T₂ ≤ R
  R_eq : R = T₂ ⊔ zpowers w₂
  card_R : Nat.card R = 128
  R_inf_centralizer : R ⊓ centralizer (F.E₁ : Set X) = F.E₁
  le_E : ∀ P : Subgroup X, IsPGroup 2 P → P ≤ centralizer (F.E₁ : Set X) → P ≤ F.E₁
  Q_eq : Q = R ⊓ oddTwoCoreIn (normalizer (F.E₁ : Set X))
  Q_eq_sup : Q = F.E₁ ⊔ zpowers w₁ ⊔ zpowers w₂
  w₁_eq : (case = .E ∧ w₁ = w) ∨ (case = .H ∧ w₁ = w * S.t)
  w₂_t : w₂ * S.t * w₂⁻¹ = S.t * F.yF
  w₂_z : w₂ * S.z = S.z * w₂
  w₂_y : w₂ * F.yF = F.yF * w₂
  w₂_k : w₂ * F.kF = F.kF * w₂
  w₂_w₁ : w₂ * w₁ = w₁ * w₂
  sq_cases : (case = .E ∧ w₁ ^ 2 = 1 ∧ w₂ ^ 2 = 1) ∨
    (case = .H ∧ w₁ ^ 2 = S.z ∧ w₂ ^ 2 = F.yF)
  u_w₂ : F.xF * F.yF * w₂ * (F.xF * F.yF)⁻¹ = (w₂ * w₁)⁻¹
  d_mem : d ∈ normalizer (F.E₁ : Set X) ⊓ normalizer (Q : Set X) ⊓ centralizer ({S.t} : Set X)
  isPGroup_d : IsPGroup 3 (zpowers d)
  d_z : d * S.z * d⁻¹ = F.yF
  d_y : d * F.yF * d⁻¹ = S.z * F.yF
  d_k : d * F.kF * d⁻¹ = F.kF
  d_w₁ : d * w₁ * d⁻¹ = w₂
  d_w₂ : d * w₂ * d⁻¹ = (w₂ * w₁)⁻¹
  u_d : F.xF * F.yF * d * (F.xF * F.yF)⁻¹ * d ∈ centralizer (Q : Set X)

variable {S}

@[expose] noncomputable def Sec5.Q₀ {F : S.Frame} {T₁ : Subgroup X} (D : S.Sec5 F T₁) :
    Subgroup X :=
  closure {S.z, F.yF, D.w₁, D.w₂}

end A7Base

@[expose] def FritzA7Section5Data : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (S : A7Base X) (F : S.Frame) (T₁ : Subgroup X),
    S.Sec4 F T₁ → F.Normal → (∃ g ∈ T₁, F.E₁.map (MulAut.conj g).toMonoidHom = F.E₂) →
      Nonempty (S.Sec5 F T₁)

@[expose] def FritzA7Section5E : Prop :=
  HaradaInput →
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    ¬ SectRank4 X → ∀ (S : A7Base X) (F : S.Frame) (T₁ : Subgroup X), S.Sec4 F T₁ →
      F.Normal → ∀ D : S.Sec5 F T₁, D.case = .E → False

@[expose] def FritzA7Section5H : Prop :=
  HaradaInput →
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    ¬ SectRank4 X → ∀ (S : A7Base X) (F : S.Frame) (T₁ : Subgroup X), S.Sec4 F T₁ →
      F.Normal → ∀ D : S.Sec5 F T₁, D.case = .H → False

theorem fritzA7Section5_of_parts (hD : FritzA7Section5Data) (hE : FritzA7Section5E)
    (hH : FritzA7Section5H) : FritzA7Section5 := by
  intro hHar X _ _ _ hX hsr S F T₁ h4 hF hg
  obtain ⟨D⟩ := hD X S F T₁ h4 hF hg
  cases hc : D.case
  · exact hE hHar X hX hsr S F T₁ h4 hF D hc
  · exact hH hHar X hX hsr S F T₁ h4 hF D hc

end CFSG.ComponentClassification.HSFLit
