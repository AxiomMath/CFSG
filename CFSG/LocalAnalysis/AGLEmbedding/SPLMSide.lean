module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoEscapeAux
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallDefs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def IsSPLBlockType (p : ℕ) {Y : Type} [Group Y] (L : Subgroup Y) : Prop :=
  IsClassicalTwoOrG2 (↥L ⧸ Subgroup.center ↥L) ∨
    (∃ n : ℕ, Nonempty (↥L ⧸ Subgroup.center ↥L ≃* alternatingGroup (Fin n))) ∨
    ∃ S : Sylow p ↥L, IsCyclic ↥(S : Subgroup ↥L)

@[expose] def KFactSPLBlockTorus : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L : Subgroup Y) (p r : ℕ), CFSG.IsComponent L →
    p.Prime → p ≠ 2 → r.Prime → r ∣ p ^ 2 + 1 → ¬ r ∣ p ^ 2 - 1 → IsSPLBlockType p L →
    IsCatalogGroup (↥L ⧸ Subgroup.center ↥L) →
    ∀ (u c : Y) (T X : Subgroup Y),
      u ∈ Subgroup.normalizer (L : Set Y) → u ^ p = 1 →
      u ∉ Subgroup.centralizer (L : Set Y) →
      Group.IsSolvable ↥(L ⊓ Subgroup.centralizer ({u} : Set Y)) →
      T ≤ Subgroup.normalizer (L : Set Y) → T ≤ Subgroup.centralizer ({u} : Set Y) → X ≤ T →
      T ⊓ Subgroup.centralizer (L : Set Y) = X →
      (∀ a ∈ T, ∀ b ∈ T, a * b * a⁻¹ * b⁻¹ ∈ X) → (∀ a ∈ T, a ^ p ∈ X) →
      X.relIndex T = p ^ 4 →
      c ∈ Subgroup.normalizer (L : Set Y) → c ∈ Subgroup.centralizer ({u} : Set Y) →
      (∃ k : ℕ, c ^ r ^ k = 1) → (∀ t ∈ T, c * t * c⁻¹ ∈ T) →
      (∀ V : Subgroup Y, X ≤ V → V ≤ T → (∀ t ∈ T, ∀ v ∈ V, t * v * t⁻¹ ∈ V) →
        (∀ v ∈ V, c * v * c⁻¹ ∈ V) → V = X ∨ V = T) → False

structure SPLMSideConfig (p : ℕ) (Y : Type) [Group Y] [Finite Y] (u c : Y) (r : ℕ)
    (T X O : Subgroup Y) : Prop where
  prime : p.Prime
  ne_two : p ≠ 2
  u_pow : u ^ p = 1
  u_norm : ∀ Λ : Subgroup Y, CFSG.IsComponent Λ → u ∈ Subgroup.normalizer (Λ : Set Y)
  u_noncent : ∀ Λ : Subgroup Y, CFSG.IsComponent Λ → u ∉ Subgroup.centralizer (Λ : Set Y)
  solv : Group.IsSolvable ↥(Subgroup.centralizer ({u} : Set Y))
  T_le : T ≤ Subgroup.centralizer ({u} : Set Y)
  X_le : X ≤ T
  T_p : IsPGroup p T
  O_coprime : p.Coprime (Nat.card O)
  TO_norm : ∀ g ∈ Subgroup.centralizer ({u} : Set Y), ∀ t ∈ T,
    ∃ t' ∈ T, ∃ o ∈ O, g * t * g⁻¹ = t' * o
  T_X : ∀ t ∈ T, ∀ x ∈ X, t * x = x * t
  T_O : ∀ t ∈ T, ∀ o ∈ O, t * o = o * t
  TT : ∀ a ∈ T, ∀ b ∈ T, a * b * a⁻¹ * b⁻¹ ∈ X
  Tp : ∀ a ∈ T, a ^ p ∈ X
  index : X.relIndex T = p ^ 4
  E_le : ∀ t ∈ T, (∀ Λ : Subgroup Y, CFSG.IsComponent Λ → ∀ a ∈ Λ, t * a = a * t) → t ∈ X
  c_mem : c ∈ Subgroup.centralizer ({u} : Set Y)
  c_T : ∀ t ∈ T, c * t * c⁻¹ ∈ T
  c_X : ∀ x ∈ X, c * x = x * c
  c_pow : ∃ k : ℕ, c ^ r ^ k = 1
  r_prime : r.Prime
  r_dvd : r ∣ p ^ 2 + 1
  r_ndvd : ¬ r ∣ p ^ 2 - 1
  irr : ∀ V : Subgroup Y, X ≤ V → V ≤ T → (∀ t ∈ T, ∀ v ∈ V, t * v * t⁻¹ ∈ V) →
    (∀ v ∈ V, c * v * c⁻¹ ∈ V) → V = X ∨ V = T
  X_elem : CFSG.Open.IsElemAbelian p X
  X_card : Nat.card X = p ^ 2
  X_E : ∀ Λ : Subgroup Y, CFSG.IsComponent Λ → ∀ x ∈ X, ∀ a ∈ Λ, x * a = a * x
  Z_X : ∀ Λ : Subgroup Y, CFSG.IsComponent Λ → ∀ φ ∈ Λ, (∀ a ∈ Λ, a * φ = φ * a) →
    (∃ k : ℕ, φ ^ p ^ k = 1) → φ ∈ X
  rank : ∀ A : Subgroup Y, A ≤ Subgroup.centralizer ({u} : Set Y) →
    CFSG.Open.IsElemAbelian p A → Nat.card A < p ^ 6
  CT_odd : ∀ j ∈ Subgroup.centralizer ({u} : Set Y), (∀ t ∈ T, j * t = t * j) → j ^ 2 = 1 →
    j = 1
  catalog : ∀ Λ : Subgroup Y, CFSG.IsComponent Λ → IsCatalogGroup (↥Λ ⧸ Subgroup.center ↥Λ)
  types : ∀ Λ : Subgroup Y, CFSG.IsComponent Λ → p ∣ (Subgroup.center Λ).index →
    IsSPLBlockType p Λ

theorem five_le_of_dvd_sq_add_one {p r : ℕ} (hp2 : p ≠ 2) (hpp : p.Prime) (hr : r.Prime)
    (hd : r ∣ p ^ 2 + 1) (hnd : ¬ r ∣ p ^ 2 - 1) : 5 ≤ r := by
  have hr2 := hr.two_le
  have hodd : p % 2 = 1 := by
    rcases hpp.eq_two_or_odd with h | h
    · exact absurd h hp2
    · exact h
  by_contra hlt
  push Not at hlt
  interval_cases r
  ·
    apply hnd
    have : p ^ 2 % 2 = 1 := by rw [Nat.pow_mod, hodd]
    omega
  ·
    have h3 : (p ^ 2 + 1) % 3 = 0 := Nat.dvd_iff_mod_eq_zero.mp hd
    have h4 : (p ^ 2 + 1) % 3 = ((p % 3) ^ 2 % 3 + 1) % 3 := by
      rw [Nat.add_mod, Nat.pow_mod]
    obtain h5 | h5 | h5 : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 := by omega
    all_goals rw [h5] at h4; norm_num at h4; omega
  · exact absurd hr (by decide)

@[expose] def D1SPLMSideBridge : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)), D1OneSmallData p P M H R Rbar K →
    D1UniqueOver H R (nclIn H (d1LiftX p H R K)) → ∀ z : G, D1SmallCZElt p H R K z →
    (IsSmallLinTwo p K ∨ (p = 3 ∧ IsAltTwoP 3 K)) → D1CzSP p z → D1CzOutside p z →
    d1MapPCore p M H ⊓ K ≠ ⊥ →
    d1MapPCore p M H ⊓ Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) = ⊥ →
    (p = 3 ∨ ¬ D1SmallIa p H K) →
    (∀ (P' : Sylow p G) (Pbar : Sylow p (D1CzQuot p z)) (KC : Subgroup (D1CzQuot p z)),
      D1ReducedCentralizer p P' M z Pbar KC → R ≤ (P' : Subgroup G) → (P' : Subgroup G) ≤ M →
      Nat.card ((Pbar : Subgroup (D1CzQuot p z)) ⊓ KC : Subgroup _) = p ^ 6 ∧
      ((d1LiftX p H R K).subgroupOf (Subgroup.centralizer ({z} : Set G))).map
          (QuotientGroup.mk' (primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p)) =
        centerOf ((Pbar : Subgroup (D1CzQuot p z)) ⊓ KC)) →
    ∃ (u c : ↥M ⧸ CFSG.pCore 2 ↥M) (r : ℕ) (T X O : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)),
      SPLMSideConfig p (↥M ⧸ CFSG.pCore 2 ↥M) u c r T X O

end CFSG.AGLEmbedding
