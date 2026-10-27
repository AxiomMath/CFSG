module

public import CFSG.LocalAnalysis.AGLEmbedding.SPLMSide

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Defs

variable {G : Type} [Group G] [Finite G]

structure D1SPLPairData (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)) (z : G) : Prop where
  data : D1OneSmallData p P M H R Rbar K
  uniq : D1UniqueOver H R (nclIn H (d1LiftX p H R K))
  czElt : D1SmallCZElt p H R K z
  family : IsSmallLinTwo p K ∨ (p = 3 ∧ IsAltTwoP 3 K)
  sp : D1CzSP p z
  outside : D1CzOutside p z
  posK : d1MapPCore p M H ⊓ K ≠ ⊥
  posC : d1MapPCore p M H ⊓
    Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) = ⊥
  ib : p = 3 ∨ ¬ D1SmallIa p H K
  pair : ∀ (P' : Sylow p G) (Pbar : Sylow p (D1CzQuot p z)) (KC : Subgroup (D1CzQuot p z)),
    D1ReducedCentralizer p P' M z Pbar KC → R ≤ (P' : Subgroup G) → (P' : Subgroup G) ≤ M →
    Nat.card ((Pbar : Subgroup (D1CzQuot p z)) ⊓ KC : Subgroup _) = p ^ 6 ∧
    ((d1LiftX p H R K).subgroupOf (Subgroup.centralizer ({z} : Set G))).map
        (QuotientGroup.mk' (primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p)) =
      centerOf ((Pbar : Subgroup (D1CzQuot p z)) ⊓ KC)

@[expose] def splBar {M : Subgroup G} {g : G} (hg : g ∈ M) : ↥M ⧸ CFSG.pCore 2 ↥M :=
  QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨g, hg⟩

@[expose] def splXt0 (p : ℕ) (M : Subgroup G) (z : G) : Subgroup (D1CzQuot p z) :=
  ((Subgroup.centralizer ({z} : Set G) ⊓ M).subgroupOf
      (Subgroup.centralizer ({z} : Set G))).map
    (QuotientGroup.mk' (primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p))

end Defs

section Facts

variable {G : Type} [Group G] [Finite G]

structure SPLCtildeFacts (p : ℕ) (M : Subgroup G) (z : G) (Pbar : Sylow p (D1CzQuot p z))
    (KC : Subgroup (D1CzQuot p z)) : Prop where
  norm : ∀ x ∈ splXt0 p M z, ∀ t ∈ (Pbar : Subgroup (D1CzQuot p z)) ⊓ KC,
    x * t * x⁻¹ ∈ (Pbar : Subgroup (D1CzQuot p z)) ⊓ KC
  cent_p : ∀ x ∈ splXt0 p M z, (∀ t ∈ (Pbar : Subgroup (D1CzQuot p z)) ⊓ KC, x * t = t * x) →
    ∃ k : ℕ, x ^ p ^ k = 1
  solv : Group.IsSolvable ↥(splXt0 p M z)
  rank : ∀ A : Subgroup (D1CzQuot p z), A ≤ splXt0 p M z → IsElemAbelian p A →
    Nat.card A ≤ p ^ 5
  exp : ∀ t ∈ (Pbar : Subgroup (D1CzQuot p z)) ⊓ KC, t ^ p = 1
  comm : ∀ a ∈ (Pbar : Subgroup (D1CzQuot p z)) ⊓ KC,
    ∀ b ∈ (Pbar : Subgroup (D1CzQuot p z)) ⊓ KC,
      a * b * a⁻¹ * b⁻¹ ∈ centerOf ((Pbar : Subgroup (D1CzQuot p z)) ⊓ KC)
  nonab : ∃ a ∈ (Pbar : Subgroup (D1CzQuot p z)) ⊓ KC,
    ∃ b ∈ (Pbar : Subgroup (D1CzQuot p z)) ⊓ KC, a * b ≠ b * a
  simple : ∀ N : Subgroup (D1CzQuot p z), N ≤ KC → (∀ k ∈ KC, ∀ n ∈ N, k * n * k⁻¹ ∈ N) →
    N ≠ ⊥ → N = KC
  ppd : ∃ r : ℕ, r.Prime ∧ r ∣ p ^ 2 + 1 ∧ ¬ r ∣ p ^ 2 - 1 ∧ ∃ c ∈ splXt0 p M z, c ^ r = 1 ∧
    (∀ t ∈ (Pbar : Subgroup (D1CzQuot p z)) ⊓ KC,
      c * t * c⁻¹ ∈ (Pbar : Subgroup (D1CzQuot p z)) ⊓ KC) ∧
    (∀ x ∈ centerOf ((Pbar : Subgroup (D1CzQuot p z)) ⊓ KC), c * x = x * c) ∧
    ∀ V : Subgroup (D1CzQuot p z), centerOf ((Pbar : Subgroup (D1CzQuot p z)) ⊓ KC) ≤ V →
      V ≤ (Pbar : Subgroup (D1CzQuot p z)) ⊓ KC → (∀ v ∈ V, c * v * c⁻¹ ∈ V) →
      V = centerOf ((Pbar : Subgroup (D1CzQuot p z)) ⊓ KC) ∨
        V = (Pbar : Subgroup (D1CzQuot p z)) ⊓ KC

structure SPLCentralizerFacts (p : ℕ) (M : Subgroup G) {z : G} (hzM : z ∈ M) : Prop where
  core_le : GLBPrimeCore p (Subgroup.centralizer ({z} : Set G)) ≤ M
  core_odd : Odd (Nat.card (GLBPrimeCore p (Subgroup.centralizer ({z} : Set G))))
  twoCore_inf : pCoreOf 2 M ⊓ Subgroup.centralizer ({z} : Set G) = ⊥
  lift : ∀ g ∈ Subgroup.centralizer ({splBar hzM} : Set (↥M ⧸ CFSG.pCore 2 ↥M)),
    ∃ m : M, (m : G) ∈ Subgroup.centralizer ({z} : Set G) ∧
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) m = g
  normal_le : ∀ N : Subgroup G, N ≤ Subgroup.centralizer ({z} : Set G) ⊓ M →
    (∀ g ∈ Subgroup.centralizer ({z} : Set G) ⊓ M, ∀ n ∈ N, g * n * g⁻¹ ∈ N) →
    p.Coprime (Nat.card N) → N ≤ GLBPrimeCore p (Subgroup.centralizer ({z} : Set G))
  rank : ∀ A : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M),
    A ≤ Subgroup.centralizer ({splBar hzM} : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
    IsElemAbelian p A → Nat.card A < p ^ 6
  u_norm : ∀ Λ : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), CFSG.IsComponent Λ →
    splBar hzM ∈ Subgroup.normalizer (Λ : Set (↥M ⧸ CFSG.pCore 2 ↥M))
  u_noncent : ∀ Λ : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), CFSG.IsComponent Λ →
    splBar hzM ∉ Subgroup.centralizer (Λ : Set (↥M ⧸ CFSG.pCore 2 ↥M))
  solv : Group.IsSolvable
    ↥(Subgroup.centralizer ({splBar hzM} : Set (↥M ⧸ CFSG.pCore 2 ↥M)))

structure SPLTorusFacts (p : ℕ) (M : Subgroup G) {z : G} (hzM : z ∈ M) (X₀ T₀ : Subgroup G)
    {c₀ : G} (hc₀ : c₀ ∈ M) (r : ℕ) : Prop where
  T_le : barM M T₀ ≤ Subgroup.centralizer ({splBar hzM} : Set (↥M ⧸ CFSG.pCore 2 ↥M))
  X_le : barM M X₀ ≤ barM M T₀
  T_p : IsPGroup p (barM M T₀)
  TO_norm : ∀ g ∈ Subgroup.centralizer ({splBar hzM} : Set (↥M ⧸ CFSG.pCore 2 ↥M)),
    ∀ t ∈ barM M T₀, ∃ t' ∈ barM M T₀,
      ∃ o ∈ barM M (GLBPrimeCore p (Subgroup.centralizer ({z} : Set G))), g * t * g⁻¹ = t' * o
  T_X : ∀ t ∈ barM M T₀, ∀ x ∈ barM M X₀, t * x = x * t
  T_O : ∀ t ∈ barM M T₀, ∀ o ∈ barM M (GLBPrimeCore p (Subgroup.centralizer ({z} : Set G))),
    t * o = o * t
  TT : ∀ a ∈ barM M T₀, ∀ b ∈ barM M T₀, a * b * a⁻¹ * b⁻¹ ∈ barM M X₀
  Tp : ∀ a ∈ barM M T₀, a ^ p ∈ barM M X₀
  index : (barM M X₀).relIndex (barM M T₀) = p ^ 4
  nonab : ∃ a ∈ barM M T₀, ∃ b ∈ barM M T₀, a * b ≠ b * a
  c_mem : splBar hc₀ ∈ Subgroup.centralizer ({splBar hzM} : Set (↥M ⧸ CFSG.pCore 2 ↥M))
  c_T : ∀ t ∈ barM M T₀, splBar hc₀ * t * (splBar hc₀)⁻¹ ∈ barM M T₀
  c_X : ∀ x ∈ barM M X₀, splBar hc₀ * x = x * splBar hc₀
  r_prime : r.Prime
  r_dvd : r ∣ p ^ 2 + 1
  r_ndvd : ¬ r ∣ p ^ 2 - 1
  irr : ∀ V : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), barM M X₀ ≤ V → V ≤ barM M T₀ →
    (∀ t ∈ barM M T₀, ∀ v ∈ V, t * v * t⁻¹ ∈ V) →
    (∀ v ∈ V, splBar hc₀ * v * (splBar hc₀)⁻¹ ∈ V) → V = barM M X₀ ∨ V = barM M T₀
  CT_odd : ∀ j ∈ Subgroup.centralizer ({splBar hzM} : Set (↥M ⧸ CFSG.pCore 2 ↥M)),
    (∀ t ∈ barM M T₀, j * t = t * j) → j ^ 2 = 1 → j = 1

structure SPLBlockFacts (p : ℕ) (M X₀ : Subgroup G) : Prop where
  pcore : CFSG.pCore p (↥M ⧸ CFSG.pCore 2 ↥M) = barM M X₀
  X_elem : IsElemAbelian p (barM M X₀)
  X_card : Nat.card (barM M X₀) = p ^ 2
  X_E : ∀ Λ : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), CFSG.IsComponent Λ →
    ∀ x ∈ barM M X₀, ∀ a ∈ Λ, x * a = a * x
  Z_X : ∀ Λ : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), CFSG.IsComponent Λ → ∀ φ ∈ Λ,
    (∀ a ∈ Λ, a * φ = φ * a) → (∃ k : ℕ, φ ^ p ^ k = 1) → φ ∈ barM M X₀
  catalog : ∀ Λ : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), CFSG.IsComponent Λ →
    IsCatalogGroup (↥Λ ⧸ Subgroup.center ↥Λ)
  types : ∀ Λ : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), CFSG.IsComponent Λ →
    p ∣ (Subgroup.center Λ).index → IsSPLBlockType p Λ

end Facts

@[expose] def D1SPLPieceCtilde : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)) (z : G),
    D1SPLPairData p P M H R Rbar K z →
    ∀ (P' : Sylow p G) (Pbar : Sylow p (D1CzQuot p z)) (KC : Subgroup (D1CzQuot p z)),
      D1ReducedCentralizer p P' M z Pbar KC → R ≤ (P' : Subgroup G) →
      (P' : Subgroup G) ≤ M → SPLCtildeFacts p M z Pbar KC

@[expose] def D1SPLPieceCentralizer : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)) (z : G),
    D1SPLPairData p P M H R Rbar K z → ∀ hzM : z ∈ M,
    ∀ (P' : Sylow p G) (Pbar : Sylow p (D1CzQuot p z)) (KC : Subgroup (D1CzQuot p z)),
      D1ReducedCentralizer p P' M z Pbar KC → R ≤ (P' : Subgroup G) →
      (P' : Subgroup G) ≤ M → SPLCtildeFacts p M z Pbar KC → SPLCentralizerFacts p M hzM

@[expose] def D1SPLPieceTorus : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)) (z : G),
    D1SPLPairData p P M H R Rbar K z → ∀ hzM : z ∈ M,
    ∀ (P' : Sylow p G) (Pbar : Sylow p (D1CzQuot p z)) (KC : Subgroup (D1CzQuot p z)),
      D1ReducedCentralizer p P' M z Pbar KC → R ≤ (P' : Subgroup G) →
      (P' : Subgroup G) ≤ M → SPLCtildeFacts p M z Pbar KC → SPLCentralizerFacts p M hzM →
      SPLBlockFacts p M (d1LiftX p H R K) →
      ∃ (T₀ : Subgroup G) (c₀ : G) (hc₀ : c₀ ∈ M) (r : ℕ),
        SPLTorusFacts p M hzM (d1LiftX p H R K) T₀ hc₀ r ∧ ∃ k : ℕ, splBar hc₀ ^ r ^ k = 1

@[expose] def D1SPLPieceZK : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)) (z : G),
    D1SPLPairData p P M H R Rbar K z → ∀ hzM : z ∈ M,
    ∀ s : ℕ, s.Prime → s ≠ 2 → s ≠ p →
      CFSG.pCore s (↥M ⧸ CFSG.pCore 2 ↥M) ≤
        Subgroup.centralizer ({splBar hzM} : Set (↥M ⧸ CFSG.pCore 2 ↥M))

@[expose] def D1SPLPieceLemmaT : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)) (z : G),
    D1SPLPairData p P M H R Rbar K z → ∀ hzM : z ∈ M,
    SPLCentralizerFacts p M hzM → SPLBlockFacts p M (d1LiftX p H R K) →
    (∀ s : ℕ, s.Prime → s ≠ 2 → s ≠ p →
      CFSG.pCore s (↥M ⧸ CFSG.pCore 2 ↥M) ≤
        Subgroup.centralizer ({splBar hzM} : Set (↥M ⧸ CFSG.pCore 2 ↥M))) →
    ∀ (T₀ : Subgroup G) (c₀ : G) (hc₀ : c₀ ∈ M) (r : ℕ),
      SPLTorusFacts p M hzM (d1LiftX p H R K) T₀ hc₀ r →
      ∀ t ∈ barM M T₀, (∀ Λ : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), CFSG.IsComponent Λ →
        ∀ a ∈ Λ, t * a = a * t) → t ∈ barM M (d1LiftX p H R K)

@[expose] def D1SPLPieceBlocks : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)) (z : G),
    D1SPLPairData p P M H R Rbar K z → SPLBlockFacts p M (d1LiftX p H R K)

end CFSG.AGLEmbedding
