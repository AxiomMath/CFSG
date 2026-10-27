module

public import CFSG.GH74.GLS.Stage12.Interface
public import CFSG.GH74.GLS.IVK.Defs

public section

namespace CFSG.GH74.GLS.Stage2.Local

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12
open scoped commutatorElement

section Notation

variable {G : Type} [Group G]

abbrev Cen (z : G) : Subgroup G := centralizer ({z} : Set G)

@[expose] def OddCore (z : G) : Subgroup G := pPrimeCoreOf 2 (Cen z)

@[expose] def toBar (z : G) : ↥(Cen z) →* CentralizerBar z := QuotientGroup.mk' (pPrimeCore 2 ↥(Cen z))

@[expose] def barOf (z : G) (X : Subgroup G) : Subgroup (CentralizerBar z) :=
  (X.subgroupOf (Cen z)).map (toBar z)

@[expose] def InnerE (z : G) : Subgroup (CentralizerBar z) :=
  layer (CentralizerBar z) ⊔ centralizer (layer (CentralizerBar z) : Set (CentralizerBar z))

@[expose] def PerfInner (z : G) : Prop :=
  ∀ Q : Subgroup (CentralizerBar z), Group.IsPerfect ↥Q → Q ≤ InnerE z

@[expose] def LC (z : G) : Subgroup G :=
  (oPrimePResidual 2 ↥(Cen z) ⊓ (InnerE z).comap (toBar z)).map (Cen z).subtype

@[expose] def WC (z : G) : Subgroup G :=
  ((pPrimePCore 2 ↥(oResidual 2 ↥(Cen z))).map (oResidual 2 ↥(Cen z)).subtype).map
    (Cen z).subtype

@[expose] def RC (S : Subgroup G) (z : G) : Subgroup G := S ⊓ LC z

@[expose] def LBar (z : G) : Subgroup (CentralizerBar z) := barOf z (LC z)

@[expose] def WBar (z : G) : Subgroup (CentralizerBar z) := barOf z (WC z)

@[expose] def SBar (S : Subgroup G) (z : G) : Subgroup (CentralizerBar z) := barOf z S

@[expose] def S1 (S : Subgroup G) (z : G) : Subgroup G :=
  S ⊓ (⨅ K ∈ {K : Subgroup (CentralizerBar z) | IsComponent K ∧ K ≤ LBar z},
    (normalizer (K : Set (CentralizerBar z))).comap (toBar z)).map (Cen z).subtype

@[expose] def Dz (S : Subgroup G) (z : G) : Subgroup G :=
  pPrimeCoreOf 2 (Cen z ⊓ centralizer ((S1 S z : Subgroup G) : Set G))

@[expose] noncomputable def AutOrd (A V : Subgroup G) : ℕ :=
  (centralizer (V : Set G) ⊓ A).relIndex (normalizer (V : Set G) ⊓ A)

@[expose] def Swaps (z t : G) (L₁ L₂ : Subgroup (CentralizerBar z)) : Prop :=
  ∃ ht : t ∈ Cen z,
    conjugate L₁ (toBar z ⟨t, ht⟩) = L₂ ∧ conjugate L₂ (toBar z ⟨t, ht⟩) = L₁

@[expose] def CL (z t : G) : Subgroup (CentralizerBar z) :=
  LBar z ⊓ centralizer ((barOf z (zpowers t) : Subgroup (CentralizerBar z)) : Set (CentralizerBar z))

@[expose] def Ixz (z x : G) : Subgroup G := pLayerOf 2 (centralizer ({x, z} : Set G))

@[expose] def Jx (x : G) : Subgroup G := pLayerOf 2 (centralizer ({x} : Set G))

end Notation

section Preds

variable {X : Type} [Group X]

@[expose] def IsCentralProd (A B Y : Subgroup X) : Prop :=
  A ⊔ B = Y ∧ (∀ a ∈ A, ∀ b ∈ B, a * b = b * a) ∧ Nat.card ↥(A ⊓ B) = 2

@[expose] def InducedPGL2 (L T : Subgroup X) (r : ℕ) : Prop :=
  ∃ _ : ((centralizer (L : Set X)).subgroupOf (L ⊔ T)).Normal,
    IVK.IsPGL2 (↥(L ⊔ T) ⧸ (centralizer (L : Set X)).subgroupOf (L ⊔ T)) (fun q => q = r)

@[expose] def PGLOver (L T : Subgroup X) (r : ℕ) : Prop :=
  ∃ _ : (((center ↥L).map L.subtype).subgroupOf (L ⊔ T)).Normal,
    IVK.IsPGL2 (↥(L ⊔ T) ⧸ ((center ↥L).map L.subtype).subgroupOf (L ⊔ T)) (fun q => q = r)

@[expose] def IsDihedral (Y : Type) [Group Y] : Prop := ∃ m : ℕ, IVK.IsDihedralOrder Y m

@[expose] def NormIso (A : Subgroup X) (Y : Type) [Group Y] : Prop :=
  ∃ _ : ((centralizer (A : Set X)).subgroupOf (normalizer (A : Set X))).Normal,
    Nonempty ((↥(normalizer (A : Set X)) ⧸
      (centralizer (A : Set X)).subgroupOf (normalizer (A : Set X))) ≃* Y)

end Preds

section Preds2

variable {G : Type} [Group G]

@[expose] def PGLModO (K T : Subgroup G) (q : ℕ) : Prop :=
  ∃ _ : ((pPrimeCoreOf 2 K).subgroupOf (K ⊔ T)).Normal,
    IVK.IsPGL2 (↥(K ⊔ T) ⧸ (pPrimeCoreOf 2 K).subgroupOf (K ⊔ T)) (fun r => r = q)

@[expose] def IsNonCentralInvolution (x : G) : Prop := orderOf x = 2 ∧ ¬ IsCentralInvolution x

end Preds2

section Preds3

variable {G : Type} [Group G]

@[expose] def O2Of (X : Subgroup G) : Subgroup G := (oResidual 2 ↥X).map X.subtype

@[expose] def O22Of (X : Subgroup G) : Subgroup G := (pPrimePCore 2 ↥X).map X.subtype

@[expose] def O2coreOf (X : Subgroup G) : Subgroup G := (pCore 2 ↥X).map X.subtype

abbrev HBar (H : Subgroup G) : Type := ↥H ⧸ pPrimeCore 2 ↥H

@[expose] def barIn (H X : Subgroup G) : Subgroup (HBar H) :=
  (X.subgroupOf H).map (QuotientGroup.mk' (pPrimeCore 2 ↥H))

@[expose] def HasNormal2Compl (X : Subgroup G) : Prop :=
  ∃ N : Subgroup G, N ≤ X ∧ (N.subgroupOf X).Normal ∧ Odd (Nat.card ↥N) ∧
    ∃ a : ℕ, (N.subgroupOf X).index = 2 ^ a

@[expose] def QuotIso (X N : Subgroup G) (Y : Type) [Group Y] : Prop :=
  ∃ _ : (N.subgroupOf X).Normal, Nonempty ((↥X ⧸ N.subgroupOf X) ≃* Y)

@[expose] def SwapsComps (z t : G) : Prop :=
  ∃ L₁ L₂ : Subgroup (CentralizerBar z), L₁ ≠ L₂ ∧
    {K : Subgroup (CentralizerBar z) | IsComponent K} = {L₁, L₂} ∧ Swaps z t L₁ L₂

end Preds3

structure Stage1Base (G : Type) [Group G] [Finite G] (z : G) (S : Subgroup G) : Prop where
  zcen : ∀ w ∈ S, (∀ s ∈ S, s * w = w * s) → orderOf w = 2 → w = z
  inv_out : RC S z ≠ S → ∃ s ∈ S, s ∉ RC S z ∧ orderOf s = 2
  four_le : ∀ U : Subgroup G, U ≤ S → IVK.IsFourSubgroup U →
    (∀ s ∈ S, ∀ u ∈ U, s * u * s⁻¹ ∈ U) → U ≤ LC z

@[expose] def G2Shape {G : Type} [Group G] (z : G) (S : Subgroup G) (r₁ r₂ : ℕ)
    (L₁ L₂ : Subgroup (CentralizerBar z)) : Prop :=
  Odd r₁ ∧ Odd r₂ ∧ 3 < r₁ ∧
    IsCentralProd L₁ L₂ (LBar z) ∧ HasSL2Model ↥L₁ (fun q => q = r₁) ∧
    HasSL2Model ↥L₂ (fun q => q = r₂) ∧
    (∃ (n : ℕ) (A B : Subgroup G), IsCentralProd A B (RC S z) ∧ IVK.IsQuaternionTwoGroup ↥A n ∧
      IVK.IsQuaternionTwoGroup ↥B n) ∧
    (r₂ = 3 → Nonempty (↥(WBar z) ≃* QuaternionGroup 2) ∧
      generalizedFitting (CentralizerBar z) = oPrimeResidualOf 2 (LBar z)) ∧
    (3 < r₂ → WBar z = barOf z (zpowers z) ∧ generalizedFitting (CentralizerBar z) = LBar z) ∧
    (RC S z).relIndex S = 2 ∧ InducedPGL2 L₁ (SBar S z) r₁ ∧ InducedPGL2 L₂ (SBar S z) r₂

structure Stage1G2 (G : Type) [Group G] [Finite G] (z : G) (S : Subgroup G) : Prop where
  base : Stage1Base G z S
  one_class : ∀ u v : G, orderOf u = 2 → orderOf v = 2 → IsConj u v
  shape : ∃ (r₁ r₂ : ℕ) (L₁ L₂ : Subgroup (CentralizerBar z)), G2Shape z S r₁ r₂ L₁ L₂
  perf : PerfInner z

structure Stage1M12 (G : Type) [Group G] [Finite G] (z : G) (S : Subgroup G) : Prop where
  base : Stage1Base G z S
  W_shape : ∃ A B : Subgroup (CentralizerBar z), IsCentralProd A B (WBar z) ∧
    Nonempty (↥A ≃* QuaternionGroup 2) ∧ Nonempty (↥B ≃* QuaternionGroup 2) ∧ A.Normal
  L_shape : ∃ A : Subgroup (CentralizerBar z), Nonempty (↥A ≃* Multiplicative (ZMod 3)) ∧
    LBar z = oResidual 2 (CentralizerBar z) ∧ oResidual 2 (CentralizerBar z) = WBar z ⊔ A ∧
    generalizedFitting (CentralizerBar z) = WBar z ∧ ⁅WBar z, A⁆ = WBar z ∧
    (∀ w ∈ WBar z, (∀ a ∈ A, a * w = w * a) → w ∈ barOf z (zpowers z))
  quot : ∃ _ : (WBar z).Normal, Nonempty ((CentralizerBar z ⧸ WBar z) ≃* Equiv.Perm (Fin 3))
  two_classes : ∃ x : G, orderOf x = 2 ∧ ¬ IsConj z x ∧
    ∀ u : G, orderOf u = 2 → IsConj z u ∨ IsConj x u
  four_group : ∃ U : Subgroup G, U ≤ S ∧ IVK.IsFourSubgroup U ∧ (∀ s ∈ S, ∀ u ∈ U, s * u * s⁻¹ ∈ U) ∧
    z ∈ U ∧ U ≤ WC z ∧
    (∀ U' : Subgroup G, U' ≤ S → IVK.IsFourSubgroup U' → (∀ s ∈ S, ∀ u ∈ U', s * u * s⁻¹ ∈ U') →
      U' = U) ∧ AutOrd (⊤ : Subgroup G) U = 6
  fuse_out : ∃ t ∈ S, t ∉ WC z ∧ orderOf t = 2 ∧ IsConj z t
  card_zW : Nat.card {u : G // u ∈ S ∧ u ∈ WC z ∧ orderOf u = 2 ∧ IsConj z u} = 7

structure Stage1Pair (G : Type) [Group G] [Finite G] (z : G) (S : Subgroup G) (q : ℕ)
    (L₁ L₂ : Subgroup (CentralizerBar z)) : Prop where
  base : Stage1Base G z S
  odd : Odd q
  gt3 : 3 < q
  ne : L₁ ≠ L₂
  prod : IsCentralProd L₁ L₂ (LBar z)
  sl₁ : HasSL2Model ↥L₁ (fun r => r = q)
  sl₂ : HasSL2Model ↥L₂ (fun r => r = q)
  comps : {K : Subgroup (CentralizerBar z) | IsComponent K} = {L₁, L₂}
  fitting : generalizedFitting (CentralizerBar z) = LBar z
  swap : ∃ s ∈ S, Swaps z s L₁ L₂

structure TwoClassData (G : Type) [Group G] [Finite G] (z : G) (S : Subgroup G)
    (L₁ L₂ : Subgroup (CentralizerBar z)) (q : ℕ) (x : G) : Prop where
  x_mem : x ∈ S
  x_inv : orderOf x = 2
  x_nonCentral : ¬ IsCentralInvolution x
  classes : ∀ u : G, orderOf u = 2 → IsConj z u ∨ IsConj x u
  x_normal : ∀ s ∈ S, ∀ w ∈ zpowers z ⊔ zpowers x, s * w * s⁻¹ ∈ zpowers z ⊔ zpowers x
  coset : ∀ g ∈ LC z ⊔ S, ∃ l ∈ LC z, IsConj z (g * l)
  invol_L : ∀ u ∈ LC z, orderOf u = 2 → u ≠ z →
    IsConj x u ∧ ∀ v ∈ LC z, orderOf v = 2 → v ≠ z → IVK.ConjUnder (LC z) u v
  swap_exists : ∃ t ∈ S, IsConj z t ∧ Swaps z t L₁ L₂
  swap_conseq : ∀ t ∈ S, IsConj z t → Swaps z t L₁ L₂ →
    IsConj x (t * z) ∧ IVK.IsL2 ↥(layer ↥(CL z t)) (fun r => r = q) ∧
    (S ⊓ centralizer ({t} : Set G) = S ⊓ normalizer ((zpowers z ⊔ zpowers t : Subgroup G) : Set G) ∧
      ∃ D : Subgroup G, IsInternalDirectProduct (zpowers z ⊔ zpowers t) D
        (S ⊓ centralizer ({t} : Set G)) ∧ IsDihedral ↥D) ∧
    ∃ V : Subgroup G, V ≤ LC z ∧ IVK.IsFourSubgroup V ∧
      (AutOrd (Cen z) V = 3 ∨ AutOrd (Cen z) V = 6) ∧ ∀ v ∈ V, t * v = v * t

@[expose] def GoodInvolution {G : Type} [Group G] (z : G) (S : Subgroup G)
    (L₁ L₂ : Subgroup (CentralizerBar z)) (q : ℕ) (y : G) : Prop :=
  y ∈ S ∧ orderOf y = 2 ∧ PGLOver L₁ (barOf z (zpowers y)) q ∧ PGLOver L₂ (barOf z (zpowers y)) q

structure Stage1PSp4 (G : Type) [Group G] [Finite G] (z : G) (S : Subgroup G) (q : ℕ)
    (L₁ L₂ : Subgroup (CentralizerBar z)) : Prop where
  pair : Stage1Pair G z S q L₁ L₂
  index : (RC S z).relIndex S = 2
  two : ∃ x : G, TwoClassData G z S L₁ L₂ q x

structure Stage1L4 (G : Type) [Group G] [Finite G] (z : G) (S : Subgroup G) (ε : Bool) (q : ℕ)
    (L₁ L₂ : Subgroup (CentralizerBar z)) : Prop where
  pair : Stage1Pair G z S q L₁ L₂
  mod8 : q % 8 ≠ (if ε then 1 else 7)
  index_le : (RC S z).relIndex S ≤ 4
  pgl : InducedPGL2 L₁ (SBar (S1 S z) z) q ∧ InducedPGL2 L₂ (SBar (S1 S z) z) q
  fusion : (q % 4 = (if ε then 1 else 3) ∧ ∀ u v : G, orderOf u = 2 → orderOf v = 2 → IsConj u v) ∨
    (q % 4 = (if ε then 3 else 1) ∧ ∃ x : G, TwoClassData G z S L₁ L₂ q x ∧
      (∃ y : G, GoodInvolution z S L₁ L₂ q y ∧ y ∈ centralizer ({x} : Set G)) ∧
      ∀ y : G, GoodInvolution z S L₁ L₂ q y → IsConj z y)
  noDiag : (∀ u v : G, orderOf u = 2 → orderOf v = 2 → IsConj u v) →
    ∀ y ∈ S1 S z, y * y = 1 → y ∈ RC S z

structure Stage1Sporadic (G : Type) [Group G] [Finite G] (z : G) (S : Subgroup G) (n : ℕ) : Prop where
  base : Stage1Base G z S
  one_class : ∀ u v : G, orderOf u = 2 → orderOf v = 2 → IsConj u v
  cover : IsDoubleCoverOfAlt (CentralizerBar z) n
  eq_L : LBar z = ⊤

inductive Stage1Data (G : Type) [Group G] [Finite G] (z : G) (S : Subgroup G) : Kind → Prop
  | g2 (h : Stage1G2 G z S) : Stage1Data G z S Kind.g2
  | m12 (h : Stage1M12 G z S) : Stage1Data G z S Kind.m12
  | psp4 (h : ∃ (q : ℕ) (L₁ L₂ : Subgroup (CentralizerBar z)), Stage1PSp4 G z S q L₁ L₂) :
      Stage1Data G z S Kind.psp4
  | l4 (ε : Bool)
      (h : ∃ (q : ℕ) (L₁ L₂ : Subgroup (CentralizerBar z)), Stage1L4 G z S ε q L₁ L₂) :
      Stage1Data G z S (Kind.l4 ε)
  | mcl (h : ∃ n : ℕ, (n = 8 ∨ n = 9) ∧ Stage1Sporadic G z S n) : Stage1Data G z S Kind.mcl
  | ly (h : ∃ n : ℕ, (n = 10 ∨ n = 11) ∧ Stage1Sporadic G z S n) : Stage1Data G z S Kind.ly

@[expose] def M12NonCentral {G : Type} [Group G] (x : G) : Prop :=
  ∃ (K : Subgroup G) (y : G) (q : ℕ), IsPCompIn 2 (centralizer ({x} : Set G)) K ∧
    IVK.IsL2 (↥K ⧸ pPrimeCore 2 ↥K) (fun r => r = q) ∧ (q % 8 = 3 ∨ q % 8 = 5) ∧
    y ∈ centralizer ({x} : Set G) ∧ orderOf y = 2 ∧ PGLModO K (zpowers y) q ∧
    zpowers x ⊓ (K ⊔ zpowers y) = ⊥ ∧
    oPrimeResidualOf 2 (centralizer ({x} : Set G)) ⊔ pPrimeCoreOf 2 (centralizer ({x} : Set G)) =
      pPrimeCoreOf 2 (centralizer ({x} : Set G)) ⊔ zpowers x ⊔ (K ⊔ zpowers y) ∧
    ∀ u ∈ centralizer ({x} : Set G), orderOf u = 2 → u ∉ K → IsConj x u

@[expose] def L4TwoClassField {G : Type} [Group G] [Finite G] (z : G) (S : Subgroup G)
    (L₁ L₂ : Subgroup (CentralizerBar z)) (q : ℕ) (x₀ : G) : Prop :=
  ∃ t ∈ S, IsConj z t ∧ Swaps z t L₁ L₂ ∧
    ∃ w ∈ S, orderOf w = 2 ∧ t * w = w * t ∧ w ∉ RC S z ⊔ zpowers t ∧
      GoodInvolution z S L₁ L₂ q w ∧
      IsConj z w ∧ IsConj z (t * w) ∧ IsConj x₀ (t * w * z) ∧
      ∀ y ∈ S, y * y = 1 → y ≠ 1 → (∃ r ∈ RC S z, y = r * w) → IsConj z y

structure Stage1Detail (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G) : Prop where
  no_fAut : ∀ s ∈ S, ∀ K : Subgroup G, IsPCompIn 2 (Cen z) K → pRank 2 ↥K = 1 → InducesFAut s K →
    s ∈ centralizerSection K (pPrimeCoreOf 2 K)
  m12 : k = Kind.m12 → ∀ x : G, orderOf x = 2 → ¬ IsConj z x → M12NonCentral x
  l4_two : ∀ (ε : Bool) (q : ℕ) (L₁ L₂ : Subgroup (CentralizerBar z)) (x₀ : G), k = Kind.l4 ε →
    Stage1L4 G z S ε q L₁ L₂ → TwoClassData G z S L₁ L₂ q x₀ → q % 4 = (if ε then 3 else 1) →
      L4TwoClassField z S L₁ L₂ q x₀

structure Stage2Ctx0 (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G) : Prop where
  std : Std0 G
  central : IsCentralInvolution z
  sylow : CFSG.ABGLocalTools.IsSylowOf 2 S (centralizer ({z} : Set G))
  data : Stage1Data G z S k
  detail : Stage1Detail G z k S
  rank_three : (k = Kind.g2 ∨ k = Kind.m12) → pRank 2 G = 3

structure Stage2Ctx (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G) : Prop where
  std : Std G
  central : IsCentralInvolution z
  sylow : CFSG.ABGLocalTools.IsSylowOf 2 S (centralizer ({z} : Set G))
  data : Stage1Data G z S k
  detail : Stage1Detail G z k S
  rank_three : (k = Kind.g2 ∨ k = Kind.m12) → pRank 2 G = 3

end CFSG.GH74.GLS.Stage2.Local
