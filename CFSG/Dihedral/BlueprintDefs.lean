module

public import CFSG.Assembly.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2Subgroups

public section

namespace CFSG.DihedralBlueprint

open Assembly GorensteinWalter

noncomputable section

variable {G : Type} [Group G] [Finite G]

@[expose] def IsSylowIn (p : ℕ) (P H : Subgroup G) : Prop :=
  P ≤ H ∧ IsPGroup p P ∧
    ∀ Q : Subgroup G, Q ≤ H → IsPGroup p Q → P ≤ Q → Q = P

@[expose] def NormalizedBy (P S : Subgroup G) : Prop := S ≤ Subgroup.normalizer (P : Set G)

@[expose] def oddCoreOf (H : Subgroup G) : Subgroup G := (Assembly.oddCore H).map H.subtype

@[expose] def primeSupport (H : Subgroup G) : Set ℕ := {p | p.Prime ∧ p ∣ Nat.card H}

@[expose] def HasNormalTwoComplement (H : Subgroup G) : Prop :=
  ∃ K : Subgroup G, K ≤ H ∧ (K.subgroupOf H).Normal ∧ Odd (Nat.card K) ∧
    ∃ a : ℕ, (K.subgroupOf H).index = 2 ^ a

@[expose] def HasNormalIndexTwo (H : Subgroup G) : Prop :=
  ∃ K : Subgroup G, K ≤ H ∧ (K.subgroupOf H).Normal ∧ (K.subgroupOf H).index = 2

@[expose] def sigma (j : Fin 4) (R : Subgroup G) : Set ℕ :=
  {p | p ∈ primeSupport R ∧ ∃ P : Subgroup G, IsSylowIn p P R ∧
    let N := Subgroup.normalizer (P : Set G)
    let K := oddCoreOf N
    match j.val with
    | 0 => IsSylowIn p P K ∧ HasNormalTwoComplement N
    | 1 => IsSylowIn p P K ∧ ¬ HasNormalTwoComplement N
    | 2 => IsCyclic P ∧ ¬ IsSylowIn p P K
    | _ => ¬ IsCyclic P ∧ ¬ IsSylowIn p P K}

structure CoordinateWitness (X : Type) [Group X] where
  K : Type
  [field : Field K]
  [finite : Finite K]
  odd : Odd (Nat.card K)
  rho : X →* PGammaL2 K
  injective : Function.Injective rho
  containsPSL : pGammaL2PSLRange K ≤ rho.range

attribute [instance] CoordinateWitness.field CoordinateWitness.finite

def HasCoordinates (H : Subgroup G) : Prop :=
  Nonempty (CoordinateWitness (H ⧸ Assembly.oddCore H))

def HasPGLCoordinates (H : Subgroup G) : Prop :=
  ∃ w : CoordinateWitness (H ⧸ Assembly.oddCore H), pGammaL2PGLRange w.K ≤ w.rho.range

@[expose] def HasAlternatingQuotient (H : Subgroup G) : Prop :=
  Nonempty ((H ⧸ Assembly.oddCore H) ≃* alternatingGroup (Fin 7))

@[expose] def HasSylowTwoQuotient (H : Subgroup G) : Prop :=
  ∃ T : Sylow 2 H, Nonempty ((H ⧸ Assembly.oddCore H) ≃* (T : Subgroup H))

@[expose] def GWQuotient (H : Subgroup G) : Prop :=
  HasCoordinates H ∨ HasAlternatingQuotient H ∨ HasSylowTwoQuotient H

def IsFourGroup (V : Subgroup G) : Prop := Nat.card V = 4 ∧ ∀ v ∈ V, v ^ 2 = 1

def Cycles (H V : Subgroup G) : Prop :=
  ∃ x ∈ H, x ∈ Subgroup.normalizer (V : Set G) ∧
    ∀ v ∈ V, v ≠ 1 → x * v * x⁻¹ ≠ v

def FullAutomorphismImage (H V : Subgroup G) : Prop :=
  ∀ a : MulAut V, ∃ x ∈ H, ∀ v : V, (a v : G) = x * (v : G) * x⁻¹

@[expose] def IsMaxNormalized (p : ℕ) (S P : Subgroup G) : Prop :=
  IsPGroup p P ∧ NormalizedBy P S ∧
    ∀ Q : Subgroup G, IsPGroup p Q → NormalizedBy Q S → P ≤ Q → Q = P

@[expose] def actionCommutator {H P : Type} [Group H] [Group P] (rho : H →* MulAut P)
    (u : P) (x : H) : P := u⁻¹ * rho x⁻¹ u

def IsStableAction (p : ℕ) {H P : Type} [Group H] [Group P] (rho : H →* MulAut P) : Prop :=
  ∀ x : H, (∀ u : P, actionCommutator rho (actionCommutator rho u x) x = 1) →
    x ∈ (Assembly.pCore p rho.range).comap rho.rangeRestrict

structure OriginalData (G : Type) [Group G] [Finite G] where
  n : ℕ
  three_le : 3 ≤ n
  S : Sylow 2 G
  r : G
  s : G
  order_r : orderOf r = 2 ^ (n - 1)
  order_s : orderOf s = 2
  dihedral : s * r * s = r⁻¹
  generators : Subgroup.closure ({r, s} : Set G) = (S : Subgroup G)
  order_S : Nat.card (S : Subgroup G) = 2 ^ n
  R : Subgroup G
  C : Subgroup G
  centralizer : C = Subgroup.centralizer ({r ^ (2 ^ (n - 2))} : Set G)
  decomposition : C = R ⊔ (S : Subgroup G)
  R_le : R ≤ C
  R_normal : (R.subgroupOf C).Normal
  R_odd : Odd (Nat.card R)
  disjoint : R ⊓ (S : Subgroup G) = ⊥
  proper_quotients : ∀ H : Subgroup G, H ≠ ⊤ → GWQuotient H
  index_two : ∀ H : Subgroup G, H ≠ ⊤ → C ≤ H → HasNormalIndexTwo H
  stable : ∀ (H : Subgroup G) (p : ℕ), p.Prime → Odd p →
    ∀ (P : Type) [Group P] [Finite P], IsPGroup p P →
      ∀ rho : H →* MulAut P, IsStableAction p rho
  local_constraint : ∀ p ∈ primeSupport R, ∀ P : Subgroup G, IsSylowIn p P R →
    let N := Subgroup.normalizer (P : Set G)
    let K := oddCoreOf N
    N ≠ ⊤ ∧ P ≤ K ∧
      ∀ T : Subgroup G, IsSylowIn 2 T (C ⊓ N) →
        ∃ Q : Subgroup G, IsSylowIn p Q K ∧ P ≤ Q ∧ NormalizedBy Q T

namespace OriginalData

variable (d : OriginalData G)

@[expose] def t : G := d.r ^ (2 ^ (d.n - 2))
def V (i : Fin 2) : Subgroup G := Subgroup.closure ({d.t, d.s * d.r ^ i.val} : Set G)
def E (i : Fin 2) : Subgroup G := d.R ⊓ Subgroup.centralizer (d.V i : Set G)
@[expose] def commonE : Subgroup G := d.R ⊓ Subgroup.centralizer (d.S : Set G)
@[expose] def N : Subgroup G := Subgroup.normalizer (d.R : Set G)
def HP (_d : OriginalData G) (P : Subgroup G) : Subgroup G :=
  Subgroup.normalizer (((Subgroup.center P).map P.subtype : Subgroup G) : Set G)
def JP (P : Subgroup G) : Subgroup G := oddCoreOf (d.HP P)
@[expose] def invertedSubgroup (H : Subgroup G) (v : G) : Subgroup G :=
  Subgroup.closure {u : G | u ∈ d.R ⊓ H ∧ v⁻¹ * u * v = u⁻¹}

@[expose] def Stationarity : Prop :=
  sigma 2 d.R = ∅ ∧ sigma 3 d.R = ∅ ∧
  primeSupport d.R = sigma 0 d.R ∪ sigma 1 d.R ∧ Disjoint (sigma 0 d.R) (sigma 1 d.R) ∧
  (∀ p ∈ primeSupport d.R, ∀ P : Subgroup G, IsSylowIn p P d.R →
    ∀ T : Subgroup G, IsSylowIn 2 T (d.C ⊓ Subgroup.normalizer (P : Set G)) →
    ∀ Q : Subgroup G, IsSylowIn p Q (oddCoreOf (Subgroup.normalizer (P : Set G))) →
      P ≤ Q → NormalizedBy Q T →
      IsSylowIn p P (oddCoreOf (Subgroup.normalizer (P : Set G))) ∧
      P = (Assembly.pCore p (oddCoreOf (Subgroup.normalizer (P : Set G)))).map
        (oddCoreOf (Subgroup.normalizer (P : Set G))).subtype ∧ Q = P) ∧
  (∀ (V H : Subgroup G), IsFourGroup V → V ≤ (d.S : Subgroup G) →
    V ≤ H → H ≠ ⊤ → Cycles H V →
    oddCoreOf H ≤ d.R ⊓ Subgroup.centralizer (V : Set G) ⊓ H ∧
    ∀ v ∈ V, v ≠ 1 → v ≠ d.t → IsCyclic (d.invertedSubgroup H v)) ∧
  (∀ H : Subgroup G, H ≠ ⊤ → (d.S : Subgroup G) ≤ H →
    (∀ i j : Fin 2, i ≠ j → Cycles H (d.V i) → ¬ Cycles H (d.V j) →
      d.E j ⊓ H = d.commonE ⊓ H ∧ HasPGLCoordinates H ∧ HasNormalIndexTwo H) ∧
    (Cycles H (d.V 0) → Cycles H (d.V 1) →
      oddCoreOf H ≤ Subgroup.centralizer (d.S : Set G) ∧
      (HasCoordinates H ∨ HasAlternatingQuotient H) ∧ ¬ HasNormalIndexTwo H)) ∧
  (∀ H : Subgroup G, H ≠ ⊤ → d.C ≤ H →
    (Cycles H (d.V 0) ∨ Cycles H (d.V 1)) →
    ¬ (Cycles H (d.V 0) ∧ Cycles H (d.V 1)))

@[expose] def CanonicalNormalizers : Prop :=
  (∀ p ∈ primeSupport d.R, ∀ P : Subgroup G, IsSylowIn p P d.R →
    NormalizedBy P (d.S : Subgroup G) →
    IsMaxNormalized p (d.S : Subgroup G) P ∧
    (∀ D : Subgroup G, IsMaxNormalized p (d.S : Subgroup G) D → P ≤ D → D = P) ∧
    d.HP P ≠ ⊤ ∧ (d.S : Subgroup G) ≤ d.HP P ∧
    Subgroup.normalizer (P : Set G) ≤ d.HP P ∧
    IsSylowIn p (P ⊓ d.JP P) (d.JP P) ∧ GWQuotient (d.HP P) ∧
    (p ∈ sigma 0 d.R → IsSylowIn p P ⊤ ∧ ¬ HasAlternatingQuotient (d.HP P) ∧
      (HasCoordinates (d.HP P) ∨ HasSylowTwoQuotient (d.HP P))) ∧
    (p ∈ sigma 1 d.R →
      (∃ V : Subgroup G, IsFourGroup V ∧ V ≤ (d.S : Subgroup G) ∧
        P ≤ Subgroup.centralizer (V : Set G)) ∧
      (∀ V : Subgroup G, IsFourGroup V → V ≤ (d.S : Subgroup G) →
        P ≤ Subgroup.centralizer (V : Set G) →
        FullAutomorphismImage (Subgroup.normalizer (P : Set G) ⊓
          Subgroup.normalizer (V : Set G)) V ∧ Cycles (d.HP P) V ∧
          d.JP P ≤ d.R ⊓ Subgroup.centralizer (V : Set G) ⊓ d.HP P) ∧
      ¬ HasSylowTwoQuotient (d.HP P) ∧
      (HasCoordinates (d.HP P) ∨ HasAlternatingQuotient (d.HP P)) ∧
      (4 ≤ d.n → HasCoordinates (d.HP P))) ∧
    (HasAlternatingQuotient (d.HP P) → p ∈ sigma 1 d.R ∧ d.n = 3 ∧
      d.JP P ≤ d.commonE ∧ ¬ d.C ≤ d.HP P ∧
      ((d.HP P ⊓ d.C).subgroupOf (d.HP P)).index = 105 ∧ d.C.index ≥ 105) ∧
    (P ≤ Subgroup.centralizer (d.S : Set G) →
      Cycles (d.HP P) (d.V 0) ∧ Cycles (d.HP P) (d.V 1) ∧
      d.JP P ≤ d.commonE ∧ ¬ HasNormalIndexTwo (d.HP P) ∧
      ¬ d.C ≤ d.HP P ∧ ¬ (P.subgroupOf d.R).Normal)) ∧
  (∀ p ∈ sigma 1 d.R, ∀ q ∈ sigma 1 d.R, ∀ P Q : Subgroup G,
    IsSylowIn p P d.R → IsSylowIn q Q d.R →
    NormalizedBy P (d.S : Subgroup G) → NormalizedBy Q (d.S : Subgroup G) →
    P ≤ Subgroup.centralizer (d.V 0 : Set G) →
    Q ≤ Subgroup.centralizer (d.V 1 : Set G) → d.JP P ⊓ d.JP Q ≤ d.commonE)

@[expose] def MaximalOddKernel : Prop :=
  (∀ W : Subgroup G, Odd (Nat.card W) → NormalizedBy W (d.S : Subgroup G) →
    primeSupport W ⊆ primeSupport d.R ∧ (d.R ≤ W → W = d.R)) ∧
  oddCoreOf d.N = d.R ∧ d.C ≤ d.N ∧ (d.R ≠ ⊥ → d.N ≠ ⊤) ∧
  (∀ H : Subgroup G, H ≠ ⊤ → d.C ≤ H →
    (H ≤ d.N ↔ d.R ≤ oddCoreOf H) ∧
    (H ≤ d.N → oddCoreOf H = d.R ∧
      (IsPGroup 2 (H ⧸ Assembly.oddCore H) ↔ H = d.C))) ∧
  (∀ H : Subgroup G, H ≠ ⊤ → d.C < H →
    HasCoordinates H ∧ ¬ HasAlternatingQuotient H ∧ ¬ HasSylowTwoQuotient H) ∧
  (d.R ≠ ⊥ → d.N = d.C ∨ HasCoordinates d.N)

@[expose] def PureProjectiveNormalizer : Prop :=
  d.N ≠ ⊤ ∧ oddCoreOf d.N = d.R ∧
  d.N ⊓ Subgroup.centralizer ({d.t} : Set G) = d.C ∧
  (∀ w : CoordinateWitness (d.N ⧸ Assembly.oddCore d.N),
    w.rho.range = pGammaL2PGLRange w.K ∧
    ∀ epsilon : ℤ, (epsilon = 1 ∨ epsilon = -1) →
      (Nat.card w.K : ℤ) % 4 = epsilon % 4 →
      (Nat.card w.K : ℤ) - epsilon = (2 : ℤ) ^ (d.n - 1) ∧
      (d.C.subgroupOf d.N).index =
        ((Nat.card w.K : ℤ) * ((Nat.card w.K : ℤ) + epsilon) / 2).toNat ∧
      d.C.index = d.N.index * (d.C.subgroupOf d.N).index ∧
      (d.C.subgroupOf d.N).index ∣ d.C.index) ∧
  ∃ i : Fin 2, Cycles d.N (d.V i) ∧
    (∀ j : Fin 2, j ≠ i → ¬ Cycles d.N (d.V j) ∧ d.E j = d.commonE) ∧
    d.E i = d.R ∧
    Subgroup.closure ({d.r ^ 2, d.s * d.r ^ i.val} : Set G) ≤
      Subgroup.centralizer (d.R : Set G) ∧
    primeSupport d.R = sigma 1 d.R ∧
    ∀ p ∈ primeSupport d.R, ∀ P : Subgroup G, IsSylowIn p P d.R →
      NormalizedBy P (d.S : Subgroup G) →
      P ≤ Subgroup.centralizer (d.V i : Set G) ∧ d.HP P ≠ ⊤ ∧
      Cycles (Subgroup.normalizer (P : Set G)) (d.V i) ∧ d.JP P ≤ d.R

@[expose] def CosetBounds : Prop :=
  ∀ (w : CoordinateWitness (d.N ⧸ Assembly.oddCore d.N)) (epsilon : ℤ),
    (epsilon = 1 ∨ epsilon = -1) → (Nat.card w.K : ℤ) % 4 = epsilon % 4 →
    ∀ i j : Fin 2, i ≠ j → Cycles d.N (d.V i) →
    let q := Nat.card w.K
    let a := ((q : ℤ) + epsilon).toNat / 2
    let h := (d.commonE.subgroupOf d.R).index
    let m := h / a
    let u := d.s * d.r ^ j.val
    orderOf u = 2 ∧ d.R ⊓ Subgroup.centralizer ({u} : Set G) = d.commonE ∧
    Nat.card (d.N ⊓ Subgroup.centralizer ({u} : Set G) : Subgroup G) = 4 * a * Nat.card d.commonE ∧
    0 < a ∧ Odd a ∧ a ∣ h ∧ 0 < m ∧ Odd m ∧
    (∀ p : ℕ, p.Prime → p ∣ a → p ∈ sigma 1 d.R) ∧
    (1 < a → d.commonE < d.R) ∧
    (∀ x ∈ d.N, orderOf x = 2 →
      ∃ y ∈ d.N, y * x * y⁻¹ = d.t ∨ y * x * y⁻¹ = u) ∧
    (¬ ∃ y ∈ d.N, y * d.t * y⁻¹ = u) ∧
    Set.ncard {x : G ⧸ d.N | d.t • x = x} = 1 + 2 ^ (d.n - 2) * m ∧
    3 + 2 ^ (d.n - 2) * m ≤ d.N.index ∧
    q * a * (3 + 2 ^ (d.n - 2) * m) ≤ d.C.index

@[expose] def ConditionalOrder : Prop :=
  ∀ k l : Fin 2, k ≠ l → ∀ R0 : Subgroup G, R0 ≤ d.R →
    (R0.subgroupOf d.R).Normal → NormalizedBy R0 (d.S : Subgroup G) →
    ⁅d.R, d.R⁆ ≤ R0 → ⁅d.R, d.V k⁆ ≤ R0 → ⁅d.R, (d.S : Subgroup G)⁆ ⊔ R0 ≠ d.R →
    NormalizedBy (d.E k ⊓ R0) (Subgroup.normalizer (d.V k : Set G)) →
    d.E l = d.commonE → (d.commonE.subgroupOf (d.E k)).index = 3 →
    Nat.card G = 2520 * Nat.card d.commonE * ((d.E k).subgroupOf d.R).index ^ 3 ∧
    Nat.card d.C = 24 * Nat.card d.commonE * ((d.E k).subgroupOf d.R).index ∧
    d.C.index = 105 * ((d.E k).subgroupOf d.R).index ^ 2

@[expose] def CharacterKernelConclusion : Prop :=
  (∃ i : Fin 2, Cycles d.N (d.V i) ∧
    Subgroup.centralizer (d.V i : Set G) = d.R ⊔ d.V i ∧
    d.R ⊓ d.V i = ⊥ ∧ Subgroup.normalizer (d.V i : Set G) ≤ d.N) ∧
  ⁅d.R, d.R⁆ ⊔ ⁅d.R, (d.S : Subgroup G)⁆ = ⁅d.R, d.N⁆ ∧
  ((⁅d.R, d.R⁆ ⊔ ⁅d.R, (d.S : Subgroup G)⁆).subgroupOf d.N).Normal ∧
  ⁅d.R, d.R⁆ ⊔ ⁅d.R, (d.S : Subgroup G)⁆ = d.R ∧
  (∀ mu : d.R →* ℂˣ,
    (∀ s ∈ (d.S : Subgroup G), ∀ r r' : d.R,
      (r' : G) = s⁻¹ * (r : G) * s → mu r' = mu r) → mu = 1) ∧
  (∃ (z : G) (i j : Fin 2), i ≠ j ∧ Cycles d.N (d.V i) ∧ orderOf z = 3 ∧
    (d.s * d.r ^ j.val)⁻¹ * z * (d.s * d.r ^ j.val) = z⁻¹ ∧
    d.R = d.commonE ⊔ Subgroup.zpowers z ∧ d.commonE ⊓ Subgroup.zpowers z = ⊥ ∧
    d.commonE ≤ Subgroup.centralizer (Subgroup.zpowers z : Set G) ∧
    ⁅d.R, d.R⁆ ⊔ ⁅d.R, (d.S : Subgroup G)⁆ =
      ⁅d.commonE, d.commonE⁆ ⊔ Subgroup.zpowers z) ∧
  ⁅d.commonE, d.commonE⁆ = d.commonE

end OriginalData
end
end CFSG.DihedralBlueprint
