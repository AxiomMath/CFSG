module

public import CFSG.GH74.Uniqueness.Section12Basic

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

section Facts

variable {X : Type} [Group X] [Finite X]

structure Facts14 (Z : Set X) (M : Subgroup X) (t : X) (n r : ℕ)
    (L K J Mo P U T S2 : Subgroup X) : Prop where
  n_odd : Odd n
  three_le : 3 ≤ n
  r_prime : r.Prime
  r_ne_two : r ≠ 2
  invariant : IsInvariantInvolutionSet Z
  t_not_mem : t ∉ M
  zM : ∀ x ∈ M, x ∈ Z ↔ x ∈ Mo ∧ x ≠ 1
  Mo_le_M : Mo ≤ M
  Mo_normal : ∀ g ∈ M, ∀ x ∈ Mo, g * x * g⁻¹ ∈ Mo
  normalizer_Mo_le : normalizer (Mo : Set X) ≤ M
  centralizer_Mo_le : centralizer (Mo : Set X) ≤ M
  card_M : Nat.card M = 2 ^ (3 * n) * (2 ^ (2 * n) - 2 ^ n + 1) * Nat.card (dGrp M t)
  r_not_dvd_D : ¬ r ∣ Nat.card (dGrp M t)
  K_eq : K = dGrp M t ⊓ L
  K_card : Nat.card K = 2 ^ n - 1
  K_comm : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a
  K_trans : ∀ a ∈ Mo, a ≠ 1 → ∀ b ∈ Mo, b ≠ 1 → ∃ k ∈ K, k * a * k⁻¹ = b
  K_fpf_P : ∀ k ∈ K, k ≠ 1 → ∀ x ∈ P, k * x = x * k → x = 1
  cent_K_M : ∀ x ∈ K, x ≠ 1 → centralizer ({x} : Set X) ⊓ M ≤ dGrp M t
  cent_K_C0 : ∀ x ∈ K, x ≠ 1 → centralizer ({x} : Set X) ⊓ centralizer (Mo : Set X) = J
  conj_D : ∀ g : X, K ≤ conjugate (dGrp M t) g → conjugate (dGrp M t) g = dGrp M t
  D_norm_L : dGrp M t ≤ normalizer (L : Set X)
  D_norm_P : dGrp M t ≤ normalizer (P : Set X)
  cent_D_K : ∀ d ∈ dGrp M t, (∀ k ∈ K, d * k = k * d) → ∃ k ∈ K, ∃ j ∈ J, d = k * j
  card_D : ∃ d : ℕ, Nat.card (dGrp M t) = (2 ^ n - 1) * Nat.card J * d ∧ d ∣ n ∧ Odd d
  J_eq : J = centralizer (L : Set X)
  J_le_D : J ≤ dGrp M t
  L_inf_J : L ⊓ J = ⊥
  NY_le : ∀ Y : Subgroup X, Y ≤ J → Y ≠ ⊥ → normalizer (Y : Set X) ≤ normalizer (L : Set X)
  conj_J_NL : ∀ v ∈ J, v ≠ 1 → ∀ w ∈ J, w ≠ 1 → ∀ g : X, g * v * g⁻¹ = w →
    g ∈ normalizer (L : Set X)
  NL_eq : ∀ g ∈ normalizer (L : Set X), ∃ l ∈ L, ∃ d ∈ dGrp M t, g = l * d
  NL_P : ∀ l ∈ L, l ∈ normalizer (P : Set X) → ∃ p ∈ P, ∃ k ∈ K, l = p * k
  coprime_J : ¬ Nat.Coprime (Nat.card J) (2 ^ n - 1)
  card_J_14 : n = 3 → 7 ∣ Nat.card J → Nat.card U = 2 → Nat.card J = 14
  big_U : 2 < Nat.card U → ∀ j ∈ J, ∀ u ∈ U, j * u * j⁻¹ ∈ U
  card_U_le : Nat.card U ≤ 2 ^ n
  Mo_le_P : Mo ≤ P
  P_le_L : P ≤ L
  P_le_M : P ≤ M
  card_Mo : Nat.card Mo = 2 ^ n
  card_P : Nat.card P = 2 ^ (2 * n)
  Mo_sq : ∀ x ∈ Mo, x * x = 1
  Mo_central : ∀ x ∈ P, ∀ m ∈ Mo, x * m = m * x
  center_P : ∀ x ∈ P, (∀ y ∈ P, x * y = y * x) → x ∈ Mo
  comm_P : ⁅P, P⁆ = Mo
  P_sq : ∀ x ∈ P, x * x ∈ Mo
  P_sq_ne : ∀ x ∈ P, x ∉ Mo → x * x ≠ 1
  P_sq_inj : ∀ x ∈ P, ∀ y ∈ P, x * x = y * y → x⁻¹ * y ∈ Mo
  U_le_J : U ≤ J
  U_ne_bot : U ≠ ⊥
  U_sylow_J : ABGLocalTools.IsSylowOf 2 U J
  U_sylow_D : ABGLocalTools.IsSylowOf 2 U (dGrp M t)
  U_sq : ∀ u ∈ U, u * u = 1
  cent_U_J : ∀ u ∈ U, u ≠ 1 → centralizer ({u} : Set X) ⊓ J = U
  T_eq : T = P ⊔ U
  comm_T : ⁅T, T⁆ = Mo
  T_sylow : ABGLocalTools.IsSylowOf 2 T (normalizer (L : Set X))
  cent_Mo_NL : centralizer (Mo : Set X) ⊓ normalizer (L : Set X) = P ⊔ J
  cent_Mo_u : ∀ u ∈ U, u ≠ 1 → centralizer (Mo : Set X) ⊓ centralizer ({u} : Set X) = T
  two_part : 2 ^ (Nat.card X).factorization 2 = 2 ^ n * Nat.card T
  M_eq : ∀ g ∈ M, ∃ c ∈ centralizer (Mo : Set X), ∃ d ∈ dGrp M t, g = c * d
  two_C0 : ∀ g ∈ M, IsPGroup 2 (zpowers g) → g ∈ centralizer (Mo : Set X)
  S2_sylow : ABGLocalTools.IsSylowOf 2 S2 (normalizer (T : Set X))
  T_le_S2 : T ≤ S2
  not_norm_sylow : ∀ R : Subgroup X, ABGLocalTools.IsSylowOf r R M → ¬ K ≤ normalizer (R : Set X)
  conj_U : ∀ a : X, orderOf a = 2 → a ∉ Z → ∃ g : X, g * a * g⁻¹ ∈ U

structure Concl146 (M : Subgroup X) (t : X) (n : ℕ) (K Mo U T S2 : Subgroup X) : Prop where
  sylow2 : ∀ W : Subgroup X, IsPGroup 2 W → Nat.card W ≤ Nat.card S2
  card_S2 : Nat.card S2 = 2 ^ n * Nat.card T
  S2_le_M : S2 ≤ M
  S2_le_C0 : S2 ≤ centralizer (Mo : Set X)
  normal : normalizer (T : Set X) ≤ normalizer (S2 : Set X)
  center : ∀ x ∈ S2, (∀ y ∈ S2, x * y = y * x) → x ∈ Mo
  quot_center : ∀ s ∈ S2, ∀ w ∈ Mo ⊔ U, s * w * s⁻¹ * w⁻¹ ∈ Mo
  cent_S2_u : ∀ u ∈ U, u ≠ 1 → centralizer ({u} : Set X) ⊓ S2 = T
  trans_u : ∀ u ∈ U, u ≠ 1 → ∀ m ∈ Mo, ∃ s ∈ S2, s * u * s⁻¹ = m * u
  cent_out : ∀ x ∈ S2, x ∉ T → ∀ w ∈ Mo ⊔ U, x * w = w * x → w ∈ Mo
  normalizer_T : ∀ g ∈ normalizer (T : Set X), ∃ s ∈ S2, ∃ d ∈ dGrp M t,
    d ∈ normalizer (U : Set X) ∧ g = s * d
  K_trans_S2 : ∀ a ∈ S2, a ∉ T → ∀ b ∈ S2, b ∉ T → ∃ k ∈ K, (k * a * k⁻¹)⁻¹ * b ∈ T
  K_norm_S2 : K ≤ normalizer (S2 : Set X)
  sq_mem_T : ∀ x ∈ S2, x * x ∈ T
  T_lt_S2 : T < S2

structure Concl147 (n : ℕ) (K J Mo U T S2 : Subgroup X) : Prop where
  complement : ∀ y ∈ J, (orderOf y).Prime → orderOf y ∣ 2 ^ n - 1 →
    y ∈ normalizer (U : Set X) →
    ∃ A : Subgroup X, A ≤ S2 ∧ A ⊓ T = ⊥ ∧ Nat.card A = 2 ^ n ∧ (∀ a ∈ A, a * a = 1) ∧
      K ≤ normalizer (A : Set X)
  elem : (∃ a ∈ S2, a ∉ T ∧ a * a = 1) →
    ∀ x ∈ S2, ∀ y ∈ S2, x * y * x⁻¹ * y⁻¹ ∈ Mo ∧ x * x ∈ Mo

end Facts

section Abstract

@[expose] def FrobRankStmt : Prop :=
  ∀ {G V : Type} [Group G] [Finite G] [Group V] [Finite V], (∀ v : V, v * v = 1) →
    ∀ (ρ : G →* MulAut V) (A B : Subgroup G), (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) →
    Odd (Nat.card A) → B ≤ normalizer (A : Set G) →
    (∀ b ∈ B, b ≠ 1 → ∀ a ∈ A, b * a = a * b → a = 1) →
    (∃ a ∈ A, ∃ v : V, ρ a v ≠ v) → 2 ^ Nat.card B ≤ Nat.card V

@[expose] def Frob149Stmt : Prop :=
  ∀ {G V : Type} [Group G] [Finite G] [Group V] [Finite V] (ρ : G →* MulAut V) (K : Subgroup G)
    (u : V) (n : ℕ), Odd (Nat.card G) → (∀ v : V, v * v = 1) → Function.Injective ρ → 3 ≤ n →
    Nat.card V = 2 ^ (2 * n + 1) → Nat.card K = 2 ^ n - 1 → u ≠ 1 → (∀ k ∈ K, ρ k u = u) →
    (∀ y ∈ K, (orderOf y).Prime → ∀ v : V, ρ y v = v → v = 1 ∨ v = u) →
    (∀ y ∈ K, (orderOf y).Prime → centralizer ({y} : Set G) ≤ normalizer (K : Set G)) →
    centralizer (K : Set G) ≤ K →
    (n = 3 → ∀ p a : ℕ, p.Prime → 0 < a → p ^ a ∣ Nat.card G → p ^ a % 7 ≠ 1) →
    ∀ g : G, ρ g u = u

@[expose] def Weak149Stmt : Prop :=
  ∀ {X : Type} [Group X] [Finite X] (M V S K : Subgroup X) (u : X) (n : ℕ),
    V ≤ M → (∀ g ∈ M, ∀ v ∈ V, g * v * g⁻¹ ∈ V) → V ≤ S → ABGLocalTools.IsSylowOf 2 S M →
    (∀ x ∈ S, ∀ y ∈ S, x * y * x⁻¹ * y⁻¹ ∈ V ∧ x * x ∈ V) →
    3 ≤ n → Nat.card S = 2 ^ (2 * n + 1) * Nat.card V → u ∈ S → u ∉ V →
    K ≤ M → K ≤ normalizer (S : Set X) → Nat.card K = 2 ^ n - 1 → (∀ k ∈ K, k * u = u * k) →
    (∀ g ∈ M, g ∈ normalizer (S : Set X) → (∀ s ∈ S, g * s * g⁻¹ * s⁻¹ ∈ V) → g ∈ S) →
    (∀ y ∈ K, (orderOf y).Prime → ∀ s ∈ S, s * y * s⁻¹ * y⁻¹ ∈ V → s ∈ V ∨ s * u⁻¹ ∈ V) →
    (∀ y ∈ K, (orderOf y).Prime → ∀ g ∈ M, g ∈ normalizer (S : Set X) →
      g * y * g⁻¹ * y⁻¹ ∈ S → ∃ s ∈ S, s * g ∈ normalizer (K : Set X)) →
    (∀ g ∈ M, g ∈ normalizer (S : Set X) → (∀ k ∈ K, g * k * g⁻¹ * k⁻¹ ∈ S) →
      ∃ k ∈ K, ∃ s ∈ S, g = k * s) →
    (n = 3 → ∀ p a : ℕ, p.Prime → p ≠ 2 → 0 < a → p ^ a ∣ Nat.card M → p ^ a % 7 ≠ 1) →
    ∀ g ∈ M, g * u * g⁻¹ ∈ S → g * u * g⁻¹ * u⁻¹ ∈ V

@[expose] def ZStar14Stmt : Prop :=
  ∀ {X : Type} [Group X] [Finite X] (M V S : Subgroup X) (u : X) (r : ℕ),
    V ≤ M → (∀ g ∈ M, ∀ v ∈ V, g * v * g⁻¹ ∈ V) → IsPGroup 2 V →
    ABGLocalTools.IsSylowOf 2 S M → V ≤ S → u ∈ S → u ∉ V → u * u ∈ V →
    (∀ s ∈ S, s * u * s⁻¹ * u⁻¹ ∈ V) →
    (∀ g ∈ M, g * u * g⁻¹ ∈ S → g * u * g⁻¹ * u⁻¹ ∈ V) →
    (∀ g ∈ M, g * u * g⁻¹ * u⁻¹ ∈ V → g ∈ normalizer (S : Set X)) →
    (∀ w ∈ M, Odd (orderOf w) → w ∈ normalizer (S : Set X) →
      (∀ s ∈ S, w * s * w⁻¹ * s⁻¹ ∈ V) → w = 1) →
    r.Prime → r ≠ 2 → (∀ g ∈ M, g * u * g⁻¹ * u⁻¹ ∈ V → ¬ r ∣ orderOf g) →
    ∃ R : Subgroup X, ABGLocalTools.IsSylowOf r R M ∧
      ∀ g ∈ M, ∀ x ∈ R ⊔ V, g * x * g⁻¹ ∈ R ⊔ V

end Abstract

end CFSG.GH74.Uniqueness
