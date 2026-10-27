module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setting
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesExtraComponents
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.PerfectResiduals

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin

structure UnconstrainedSetting (G : Type) [Group G] [Finite G] (T M : Subgroup G) : Prop where
  setting : UniqueSetting G T M
  notBender : ¬ fusionIsBenderGroup G
  notSmall : ¬ UniqueSmallModel G
  escaping : ∃ D : Subgroup G, IsEscaping M D
  noCharTwo : ∀ H : Subgroup G, IsGamma0 M H → ¬ CharTwo H

structure Tuple25 {G : Type} [Group G] [Finite G] (T M H S : Subgroup G) (z : G) : Prop where
  gamma0 : IsGamma0 M H
  sylow_inf : IsSylowTwoOf S (H ⊓ M)
  sylow : IsSylowTwoOf S H
  center_le : centerOf T ≤ S
  lt : S < T
  z_mem : z ∈ centerOf T
  z_ne_one : z ≠ 1
  z_sq : z ^ 2 = 1

structure Notation25 {G : Type} [Group G] [Finite G] {T M : Subgroup G}
    (hs : UnconstrainedSetting G T M) where
  H : Subgroup G
  S : Subgroup G
  K : Subgroup G
  z : G
  x : G
  tuple : Tuple25 T M H S z
  gammaU : IsGammaU M H
  isComp : IsComponentIn K H
  nonBender : ¬ fusionIsBenderGroup ↥K
  join : H = K ⊔ S
  x_mem : x ∈ T ⊓ Subgroup.normalizer (S : Set G)
  x_not_mem : x ∉ S
  x_sq : x ^ 2 ∈ S

namespace Notation25

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {hs : UnconstrainedSetting G T M}
  (N : Notation25 hs)

@[expose] def K0 : Subgroup G := conjJoin N.S N.K

@[expose] def SK : Subgroup G := N.S ⊓ N.K

@[expose] def SK0 : Subgroup G := N.S ⊓ N.K0

@[expose] def SC : Subgroup G := N.S ⊓ Subgroup.centralizer (N.K0 : Set G)

end Notation25

section Lists

variable {G : Type} [Group G]

@[expose] def ComponentList (M S : Subgroup G) (z : G) (L : Subgroup G) : Prop :=
  z ∈ Subgroup.normalizer (L : Set G) ∧ Ch1.InducesInner z L ∧ ⁅L, Subgroup.zpowers z⁆ = L ∧
    ¬ L ≤ M ∧
    ((fusionIsBenderGroup ↥L ∧ IsBorelIn (M ⊓ L) L) ∨
      (IsRankTwoEvenType L ∧ NontrivialOnDynkin M S L ∧ IsBorelIn (M ⊓ L) L) ∨
      ((StatedClassicalModel ↥L .PSL 3 3 1 ∨
          Nonempty (↥L ≃* CFSG.Blueprint.NativeSporadic.Carrier .M11)) ∧
        ∃ zL : G, IsProjectionOn z zL L ∧
          M ⊓ L = L ⊓ Subgroup.centralizer ({zL} : Set G)) ∨
      ((∃ p : ℕ, IsFermatOrMersenne p ∧ 7 < p ∧ StatedClassicalModel ↥L .PSL 2 p 1) ∧
        M ⊓ L = S ⊓ L))

end Lists

@[expose] def Lemma252 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H S : Subgroup G) (z : G),
    UnconstrainedSetting G T M → Tuple25 T M H S z →
      ∀ L : Subgroup G, IsComponentIn L H → ComponentList M S z L

@[expose] def Lemma253Bender : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H S : Subgroup G) (z : G),
    UnconstrainedSetting G T M → Tuple25 T M H S z →
      ∀ (k : ℕ) (B : Fin k → Subgroup G), (∀ i, B i ≤ H ∧ IsPGroup 2 (B i)) →
        H = ⨅ i, Subgroup.normalizer (B i : Set G) →
        ∀ U HU : Subgroup G, IsUPair M H U HU →
          ∀ L : Subgroup G, IsComponentIn L H → fusionIsBenderGroup ↥L →
            (∀ Q₁ : Subgroup G, Q₁ ≤ H → IsPGroup 2 Q₁ →
              HU ≤ Subgroup.normalizer (Q₁ : Set G) → Q₁ ≤ pCoreOf 2 HU) →
            IsSylowTwoOf (pCoreOf 2 HU ⊓ L) L

@[expose] def Lemma253Component : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H S : Subgroup G) (z : G),
    UnconstrainedSetting G T M → Tuple25 T M H S z →
      ∀ (k : ℕ) (B : Fin k → Subgroup G), (∀ i, B i ≤ H ∧ IsPGroup 2 (B i)) →
        H = ⨅ i, Subgroup.normalizer (B i : Set G) →
        ∃ K : Subgroup G, IsComponentIn K H ∧ ¬ fusionIsBenderGroup ↥K ∧
          IsComponentIn K (K ⊔ S) ∧
          (IsGammaU M H → IsGammaU M (K ⊔ S)) ∧ (IsGamma2 M H → IsGamma2 M (K ⊔ S))

section Stages254

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {hs : UnconstrainedSetting G T M}

structure Facts254 (N : Notation25 hs) : Prop where
  shape : N.K0 = N.K ∨
    ∃ s ∈ N.S, CFSG.conjugate N.K s ≠ N.K ∧ N.K0 = N.K ⊔ CFSG.conjugate N.K s ∧
      ⁅N.K, CFSG.conjugate N.K s⁆ = ⊥
  SC_eq : N.SC = pCoreOf 2 N.H
  SC_sylow : IsSylowTwoOf N.SC (N.H ⊓ Subgroup.centralizer (N.K0 : Set G))
  SC_ne_bot : N.SC ≠ ⊥
  z_mem : N.z ∈ N.K0 ⊔ N.SC
  z_not_mem : N.z ∉ N.SC

@[expose] def Notation254 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G) (hs : UnconstrainedSetting G T M)
    (N : Notation25 hs), ComponentList M N.S N.z N.K → Facts254 N

@[expose] def Concl255 (N : Notation25 hs) : Prop :=
  N.SC ⊓ CFSG.conjugate N.SC N.x = ⊥ ∧ CFSG.conjugate N.SC N.x ≤ N.S ∧
    ∀ a ∈ N.SC, ∀ b ∈ CFSG.conjugate N.SC N.x, a * b = b * a

@[expose] def Concl256 (N : Notation25 hs) : Prop :=
  ∀ E : Subgroup G, E ≠ ⊥ → E ≤ N.SC → N.S ≤ Subgroup.normalizer (E : Set G) →
    IsGammaU M (Subgroup.normalizer (E : Set G)) ∧
      IsSylowTwoOf N.S (Subgroup.normalizer (E : Set G)) ∧
      (IsComponentIn N.K (Subgroup.normalizer (E : Set G)) ∨
        (N.K0 = N.K ∧ Nonempty (↥N.K ≃* alternatingGroup (Fin 6)) ∧
          Nonempty (↥(autOn N.H N.K) ≃* ↥A6Models.m10) ∧
          ∃ KE : Subgroup G,
            KE = ⨆ g : ↥(Subgroup.normalizer (E : Set G)), CFSG.conjugate N.K (g : G) ∧
              IsComponentIn KE (Subgroup.normalizer (E : Set G)) ∧
              Nonempty (↥KE ≃* CFSG.Blueprint.NativeSporadic.Carrier .M11)))

@[expose] def Concl257 (N : Notation25 hs) : Prop :=
  ∀ n : ℕ, (StatedClassicalModel (↥N.K ⧸ CFSG.pCore 2 ↥N.K) .PSL 3 2 n ∨
    StatedClassicalModel (↥N.K ⧸ CFSG.pCore 2 ↥N.K) .PSp 2 2 n) → n = 1

structure Facts258 (N : Notation25 hs) : Prop where
  out_two : ∀ φ : MulAut ↥N.K, ∃ k : ℕ, φ ^ 2 ^ k ∈ (MulAut.conj : ↥N.K →* MulAut ↥N.K).range
  simple : IsSimpleGroup ↥N.K
  K0_inf_SC : N.K0 ⊓ N.SC = ⊥
  SK_shape : (∃ n : ℕ, 4 ≤ n ∧ Nonempty (↥N.SK ≃* DihedralGroup n)) ∨
    Nonempty (↥N.SK ≃* SemidihedralGroup 4)
  center_decomp : centerOf N.S = (centerOf N.S ⊓ N.SK0) ⊔ (centerOf N.S ⊓ N.SC)
  zK_exists : ∃ zK : G, zK ∈ N.K0 ∧ zK⁻¹ * N.z ∈ N.SC ∧
    centerOf N.S ⊓ N.SK0 = Subgroup.zpowers zK ∧ Nat.card (Subgroup.zpowers zK) = 2
  four_normalizer : ∀ F : Subgroup G, F ≤ N.K → IsFourSubgroup F →
    Nonempty (↥(N.K ⊓ Subgroup.normalizer (F : Set G)) ≃* Equiv.Perm (Fin 4))
  four_centralizer : ∀ F : Subgroup G, F ≤ N.SK → IsFourSubgroup F →
    ∀ φ ∈ autOn N.H N.K, (∀ f : ↥N.K, (f : G) ∈ F → (φ f : G) = f) → φ ∈ autOn N.S N.K

end Stages254

section Levels

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {hs : UnconstrainedSetting G T M}

structure Lv254 (N : Notation25 hs) : Prop where
  list252 : ComponentList M N.S N.z N.K
  facts254 : Facts254 N

structure Lv255 (N : Notation25 hs) : Prop extends Lv254 N where
  concl255 : Concl255 N

structure Lv256 (N : Notation25 hs) : Prop extends Lv255 N where
  concl256 : Concl256 N

structure Lv257 (N : Notation25 hs) : Prop extends Lv256 N where
  concl257 : Concl257 N

structure Lv258 (N : Notation25 hs) : Prop extends Lv257 N where
  facts258 : Facts258 N

end Levels

@[expose] def Lemma255 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G) (hs : UnconstrainedSetting G T M)
    (N : Notation25 hs), Concl255 N

@[expose] def Lemma256 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G) (hs : UnconstrainedSetting G T M)
    (N : Notation25 hs), Lv255 N → Concl256 N

@[expose] def Lemma257 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G) (hs : UnconstrainedSetting G T M)
    (N : Notation25 hs), Lv256 N → Concl257 N

@[expose] def Lemma258 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G) (hs : UnconstrainedSetting G T M)
    (N : Notation25 hs), Lv257 N → Facts258 N

section Stages2510

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {hs : UnconstrainedSetting G T M}

@[expose] def Concl2510 (N : Notation25 hs) : Prop :=
  (∀ U HU : Subgroup G, IsUPair M N.H U HU →
    CharTwo (Subgroup.normalizer (pCoreOf 2 HU : Set G))) ∧
  (∀ U HU : Subgroup G, IsUStarPair M N.H U HU →
    IsSylowTwoOf U (Subgroup.normalizer (pCoreOf 2 HU : Set G)) ∧ IsSylowTwoOf U HU ∧
      (U ≤ N.S → N.z ∈ centerOf N.S ∧ centerOf N.S ≤ centerOf U))

structure Facts2511 (N : Notation25 hs) (t zK : G) : Prop where
  zK_mem : zK ∈ N.K0
  zK_proj : zK⁻¹ * N.z ∈ N.SC
  t_mem : t ∈ N.SC
  t_ne_one : t ≠ 1
  t_sq : t ^ 2 = 1
  centerT : centerOf T = Subgroup.zpowers N.z
  z_order : orderOf N.z = 2
  centerS_z : centerOf N.S = Subgroup.closure {t, N.z}
  centerS_x : centerOf N.S = Subgroup.closure {t, N.x⁻¹ * t * N.x}
  centerS_zK : centerOf N.S = Subgroup.closure {t, zK}
  centerS_E4 : IsFourSubgroup (centerOf N.S)
  H_le : N.H ≤ Subgroup.centralizer ({t} : Set G)
  gammaU : IsGammaU M (Subgroup.centralizer ({t} : Set G))
  sylow : IsSylowTwoOf N.S (Subgroup.centralizer ({t} : Set G))
  not_conj : ∀ g : G, g⁻¹ * N.z * g ≠ t

@[expose] def Concl2512 (N : Notation25 hs) : Prop :=
  N.H ≤ Subgroup.normalizer (N.K : Set G) →
    (∀ U HU : Subgroup G, IsUStarPair M N.H U HU → U ≤ N.S →
      (∃ E : Subgroup G, E ≤ N.SK ∧ IsFourSubgroup E ∧
        HU = N.H ⊓ Subgroup.normalizer (E : Set G) ∧
        U = N.S ⊓ Subgroup.normalizer (E : Set G) ∧
        Nonempty (↥(pResidualOf 2 HU) ≃* alternatingGroup (Fin 4)) ∧
        E = pCoreOf 2 (pResidualOf 2 HU) ∧ E = N.K ⊓ Subgroup.centralizer (E : Set G)) ∧
      (∀ Q : Subgroup G, IsPGroup 2 Q → N.z ∈ Q → Q ≤ HU →
        HU ≤ Subgroup.normalizer (Q : Set G) →
        IsGamma M (Subgroup.normalizer (Q : Set G)) ∧
          IsSylowTwoOf U (Subgroup.normalizer (Q : Set G)))) ∧
    (∀ E : Subgroup G, E ≤ N.SK → IsFourSubgroup E →
      IsSylowTwoOf (N.S ⊓ Subgroup.normalizer (E : Set G))
        (N.H ⊓ Subgroup.normalizer (E : Set G))) ∧
    (∀ E E' : Subgroup G, E ≤ N.SK → IsFourSubgroup E → E' ≤ N.SK → IsFourSubgroup E' →
      N.S ⊓ Subgroup.normalizer (E : Set G) = N.S ⊓ Subgroup.normalizer (E' : Set G) →
      N.H ⊓ Subgroup.normalizer (E : Set G) = N.H ⊓ Subgroup.normalizer (E' : Set G) → E = E')

@[expose] def Concl2513 (N : Notation25 hs) (t zK : G) : Prop :=
  (Nat.card ↥(T ⊓ Subgroup.normalizer (N.S : Set G)) = 2 * Nat.card N.S ∧
    ∀ y ∈ T ⊓ Subgroup.normalizer (N.S : Set G), y ∉ N.S → y⁻¹ * t * y = t * N.z) ∧
  (N.x⁻¹ * zK * N.x = zK → N.z = zK ∧ N.x⁻¹ * t * N.x = t * zK) ∧
  ((∃ g : G, g⁻¹ * t * g = t * zK) → N.z = zK ∧ N.x⁻¹ * t * N.x = t * zK)

end Stages2510

section Levels2510

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {hs : UnconstrainedSetting G T M}

structure Lv2510 (N : Notation25 hs) : Prop extends Lv258 N where
  concl2510 : Concl2510 N

structure Lv2511 (N : Notation25 hs) (t zK : G) : Prop extends Lv2510 N where
  facts2511 : Facts2511 N t zK

structure Lv2512 (N : Notation25 hs) (t zK : G) : Prop extends Lv2511 N t zK where
  concl2512 : Concl2512 N

structure Lv2513 (N : Notation25 hs) (t zK : G) : Prop extends Lv2512 N t zK where
  concl2513 : Concl2513 N t zK

end Levels2510

@[expose] def Lemma2510 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G) (hs : UnconstrainedSetting G T M)
    (N : Notation25 hs), Concl2510 N

@[expose] def Lemma2511 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G) (hs : UnconstrainedSetting G T M)
    (N : Notation25 hs), Lv2510 N → ∃ t zK : G, Facts2511 N t zK

@[expose] def Lemma2512 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G) (hs : UnconstrainedSetting G T M)
    (N : Notation25 hs) (t zK : G), Lv2511 N t zK → Concl2512 N

@[expose] def Lemma2513 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G) (hs : UnconstrainedSetting G T M)
    (N : Notation25 hs) (t zK : G), Lv2512 N t zK → Concl2513 N t zK

section Stages2515

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {hs : UnconstrainedSetting G T M}

@[expose] def Concl2515 (N : Notation25 hs) : Prop :=
  ¬ Nonempty (↥N.K ≃* CFSG.Blueprint.NativeSporadic.Carrier .M11) ∧
    ¬ StatedClassicalModel ↥N.K .PSL 3 3 1

@[expose] def Concl2516 (N : Notation25 hs) : Prop :=
  (∃ p : ℕ, IsFermatOrMersenne p ∧ 7 < p ∧ StatedClassicalModel ↥N.K .PSL 2 p 1) ∨
    (StatedClassicalModel ↥N.K .PSL 3 2 1 ∧ autOn N.H N.K = ⊤) ∨
    (Nonempty (↥N.K ≃* alternatingGroup (Fin 6)) ∧
      (Nonempty (↥(autOn N.H N.K) ≃* ↥A6Models.m10) ∨
        Nonempty (↥(autOn N.H N.K) ≃* ↥A6Models.pgl29) ∨
        Nonempty (↥(autOn N.H N.K) ≃* ↥A6Models.autA6)))

@[expose] def Concl2518 (N : Notation25 hs) (t : G) : Prop :=
  IsComponentIn N.K (Subgroup.centralizer ({t} : Set G)) ∧
    Subgroup.centralizer ({t} : Set G) =
      N.K0 ⊔ N.S ⊔ (Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer (N.K0 : Set G)) ∧
    (Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer (N.K0 : Set G)) ⊔ N.S ≤ M ∧
    CharTwo (Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer (N.K0 : Set G)) ∧
    oddCoreIn (Subgroup.centralizer ({t} : Set G)) = ⊥

@[expose] def Concl2519 (N : Notation25 hs) (t : G) : Prop :=
  ∀ i : G, i ∈ N.S ⊓ Subgroup.centralizer (N.K : Set G) → i ≠ 1 → i ^ 2 = 1 →
    ¬ IsComponentIn N.K (Subgroup.centralizer ({i} : Set G)) →
    N.K0 = N.K ∧
    N.S ⊓ Subgroup.centralizer ({i} : Set G) ⊓ (N.S ⊓ Subgroup.centralizer (N.K : Set G)) =
      Subgroup.closure {t, i} ∧
    ∃ Ki : Subgroup G, IsComponentIn Ki (Subgroup.centralizer ({i} : Set G)) ∧
      ((Ki ≠ CFSG.conjugate Ki t ∧
          N.K = CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf
            ((Ki ⊔ CFSG.conjugate Ki t) ⊓ Subgroup.centralizer ({t} : Set G)) ∧
          ∃ p : ℕ, IsFermatOrMersenne p ∧ 7 ≤ p ∧ StatedClassicalModel ↥N.K .PSL 2 p 1 ∧
            StatedClassicalModel ↥Ki .PSL 2 p 1) ∨
        (N.K = CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf
            (Ki ⊓ Subgroup.centralizer ({t} : Set G)) ∧
          ((StatedClassicalModel ↥N.K .PSL 3 2 1 ∧
              StatedClassicalModel (↥Ki ⧸ Subgroup.center ↥Ki) .PSL 3 2 2 ∧
              Nat.card (Subgroup.center ↥Ki) ≤ 2 ∧ InducesOuter t Ki) ∨
            (StatedClassicalModel ↥N.K .PSL 3 2 1 ∧
              Nonempty (↥Ki ≃* CFSG.Blueprint.NativeSporadic.Carrier .J2) ∧
              InducesOuter t Ki) ∨
            (Nonempty (↥N.K ≃* alternatingGroup (Fin 6)) ∧
              (StatedClassicalModel ↥Ki .PSp 2 2 2 ∨ StatedClassicalModel ↥Ki .PSL 5 2 1 ∨
                Nonempty (↥Ki ≃* CFSG.Blueprint.NativeSporadic.Carrier .HS) ∨
                Nonempty (↥Ki ≃* alternatingGroup (Fin 8))))))) ∧
      ((N.z ∈ N.K ∧ ∃ g : G, g⁻¹ * t * g = t * N.z) ∨
        (Nonempty (↥Ki ≃* alternatingGroup (Fin 8)) ∧
          ∃ (φ : ↥Ki ≃* alternatingGroup (Fin 8)) (a b : Fin 8), a ≠ b ∧
            InducesAut t Ki φ (MulAut.conjNormal (Equiv.swap a b))))

@[expose] def Concl2520 (N : Notation25 hs) : Prop :=
  N.K0 = N.K

end Stages2515

section Levels2515

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {hs : UnconstrainedSetting G T M}

structure Lv2515 (N : Notation25 hs) (t zK : G) : Prop extends Lv2513 N t zK where
  concl2515 : Concl2515 N

structure Lv2516 (N : Notation25 hs) (t zK : G) : Prop extends Lv2515 N t zK where
  concl2516 : Concl2516 N

structure Lv2518 (N : Notation25 hs) (t zK : G) : Prop extends Lv2516 N t zK where
  concl2518 : Concl2518 N t

structure Lv2519 (N : Notation25 hs) (t zK : G) : Prop extends Lv2518 N t zK where
  concl2519 : Concl2519 N t

structure Lv2520 (N : Notation25 hs) (t zK : G) : Prop extends Lv2519 N t zK where
  concl2520 : Concl2520 N

end Levels2515

@[expose] def Lemma2515 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G) (hs : UnconstrainedSetting G T M)
    (N : Notation25 hs) (t zK : G), Lv2513 N t zK → Concl2515 N

@[expose] def Lemma2516 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G) (hs : UnconstrainedSetting G T M)
    (N : Notation25 hs) (t zK : G), Lv2515 N t zK → Concl2516 N

@[expose] def Lemma2518 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G) (hs : UnconstrainedSetting G T M)
    (N : Notation25 hs) (t zK : G), Lv2516 N t zK → Concl2518 N t

@[expose] def Lemma2519 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G) (hs : UnconstrainedSetting G T M)
    (N : Notation25 hs) (t zK : G), Lv2518 N t zK → Concl2519 N t

@[expose] def Lemma2520 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G) (hs : UnconstrainedSetting G T M)
    (N : Notation25 hs) (t zK : G), Lv2519 N t zK → Concl2520 N

section Stages2521

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {hs : UnconstrainedSetting G T M}

@[expose] def Concl2521 (N : Notation25 hs) : Prop :=
  Nonempty (↥N.K ≃* alternatingGroup (Fin 6)) ∧
    ∃ (φ : ↥N.K ≃* ↥A6Models.psl29) (ψ : ↥(autOn N.H N.K) ≃* ↥A6Models.autA6),
      ∀ (k : ↥N.K) (hk : conjAct N.K ⟨(k : G), Subgroup.le_normalizer k.2⟩ ∈ autOn N.H N.K),
        (ψ ⟨conjAct N.K ⟨(k : G), Subgroup.le_normalizer k.2⟩, hk⟩ : Equiv.Perm (Fin 10)) =
          (φ k : Equiv.Perm (Fin 10))

theorem Concl2521.nonempty_K {N : Notation25 hs} (h : Concl2521 N) :
    Nonempty (↥N.K ≃* alternatingGroup (Fin 6)) := h.1

theorem Concl2521.nonempty_autOn {N : Notation25 hs} (h : Concl2521 N) :
    Nonempty (↥(autOn N.H N.K) ≃* ↥A6Models.autA6) := by
  obtain ⟨-, -, ψ, -⟩ := h
  exact ⟨ψ⟩

@[expose] def Concl2522 (N : Notation25 hs) (t : G) : Prop :=
  (∀ g : G, g⁻¹ * N.z * g ∈ N.S →
    ⁅N.K, Subgroup.zpowers (g⁻¹ * N.z * g)⁆ = N.K ∧
      ∃ (φ : ↥N.K ≃* alternatingGroup (Fin 6)) (σ : Equiv.Perm (Fin 6)),
        InducesAut (g⁻¹ * N.z * g) N.K φ (MulAut.conjNormal σ)) ∧
    N.H = Subgroup.centralizer ({t} : Set G) ∧
    N.H ⊓ Subgroup.centralizer ({N.z} : Set G) = N.S

@[expose] def Concl2523 (N : Notation25 hs) : Prop :=
  ∃ E₁ E₂ : Subgroup G, E₁ ≤ N.SK ∧ E₂ ≤ N.SK ∧ IsFourSubgroup E₁ ∧ IsFourSubgroup E₂ ∧
    E₁ ≠ E₂ ∧ (∀ E : Subgroup G, E ≤ N.SK → IsFourSubgroup E → E = E₁ ∨ E = E₂) ∧
    (∀ U HU : Subgroup G, IsUStarPair M N.H U HU → U ≤ N.S →
      (U = N.S ⊓ Subgroup.normalizer (E₁ : Set G) ∧ HU = N.H ⊓ Subgroup.normalizer (E₁ : Set G)) ∨
      (U = N.S ⊓ Subgroup.normalizer (E₂ : Set G) ∧ HU = N.H ⊓ Subgroup.normalizer (E₂ : Set G))) ∧
    (∀ E ∈ ({E₁, E₂} : Set (Subgroup G)),
      IsUStarPair M N.H (N.S ⊓ Subgroup.normalizer (E : Set G))
          (N.H ⊓ Subgroup.normalizer (E : Set G)) ∧
        IsSylowTwoOf (N.S ⊓ Subgroup.normalizer (E : Set G))
          (N.H ⊓ Subgroup.normalizer (E : Set G)))

@[expose] def Concl2524 (N : Notation25 hs) : Prop :=
  frattini ↥N.SC ≠ ⊥

@[expose] def Concl2525 (N : Notation25 hs) (t zK : G) : Prop :=
  N.x⁻¹ * t * N.x = zK ∧ N.z = t * zK

@[expose] def Concl2526 (N : Notation25 hs) : Prop :=
  CFSG.Open.pRank 2 N.SC = 1

@[expose] def Concl2527 (N : Notation25 hs) : Prop :=
  Nonempty (↥N.SC ≃* Multiplicative (ZMod 4)) ∨ Nonempty (↥N.SC ≃* Multiplicative (ZMod 8)) ∨
    Nonempty (↥N.SC ≃* QuaternionGroup 2)

end Stages2521

section Levels2521

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {hs : UnconstrainedSetting G T M}

structure Lv2521 (N : Notation25 hs) (t zK : G) : Prop extends Lv2520 N t zK where
  concl2521 : Concl2521 N

structure Lv2522 (N : Notation25 hs) (t zK : G) : Prop extends Lv2521 N t zK where
  concl2522 : Concl2522 N t

structure Lv2523 (N : Notation25 hs) (t zK : G) : Prop extends Lv2522 N t zK where
  concl2523 : Concl2523 N

structure Lv2524 (N : Notation25 hs) (t zK : G) : Prop extends Lv2523 N t zK where
  concl2524 : Concl2524 N

structure Lv2525 (N : Notation25 hs) (t zK : G) : Prop extends Lv2524 N t zK where
  concl2525 : Concl2525 N t zK

structure Lv2526 (N : Notation25 hs) (t zK : G) : Prop extends Lv2525 N t zK where
  concl2526 : Concl2526 N

structure Lv2527 (N : Notation25 hs) (t zK : G) : Prop extends Lv2526 N t zK where
  concl2527 : Concl2527 N

end Levels2521

@[expose] def Lemma2521 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G) (hs : UnconstrainedSetting G T M)
    (N : Notation25 hs) (t zK : G), Lv2520 N t zK → Concl2521 N

@[expose] def Lemma2522 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G) (hs : UnconstrainedSetting G T M)
    (N : Notation25 hs) (t zK : G), Lv2521 N t zK → Concl2522 N t

@[expose] def Lemma2523 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G) (hs : UnconstrainedSetting G T M)
    (N : Notation25 hs) (t zK : G), Lv2522 N t zK → Concl2523 N

@[expose] def Lemma2524 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G) (hs : UnconstrainedSetting G T M)
    (N : Notation25 hs) (t zK : G), Lv2523 N t zK → Concl2524 N

@[expose] def Lemma2525 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G) (hs : UnconstrainedSetting G T M)
    (N : Notation25 hs) (t zK : G), Lv2524 N t zK → Concl2525 N t zK

@[expose] def Lemma2526 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G) (hs : UnconstrainedSetting G T M)
    (N : Notation25 hs) (t zK : G), Lv2525 N t zK → Concl2526 N

@[expose] def Lemma2527 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G) (hs : UnconstrainedSetting G T M)
    (N : Notation25 hs) (t zK : G), Lv2526 N t zK → Concl2527 N

@[expose] def Lemma25Final : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G) (hs : UnconstrainedSetting G T M)
    (N : Notation25 hs) (t zK : G), Lv2527 N t zK → False

end CFSG.QuasithinUnique
