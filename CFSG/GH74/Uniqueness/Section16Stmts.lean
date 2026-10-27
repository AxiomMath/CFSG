module

public import CFSG.GH74.Uniqueness.Bender.Frame311
public import CFSG.GH74.Uniqueness.Section12Basic
public import CFSG.GH74.Uniqueness.Section5Basic

public section

namespace CFSG.GH74.Uniqueness

open Subgroup
open scoped Pointwise

variable {X : Type} [Group X] [Finite X]

@[expose] def omegaOneSub (H : Subgroup X) : Subgroup X :=
  Subgroup.closure {x : X | x ∈ H ∧ x * x = 1}

@[expose] noncomputable def oTwoIn (H : Subgroup X) : Subgroup X := (pCore 2 ↥H).map H.subtype

@[expose] def centerIn (H : Subgroup X) : Subgroup X := H ⊓ centralizer (H : Set X)

structure Ctx16 {X : Type} [Group X] [Finite X] (Z : Set X) (M : Subgroup X) where
  t : X
  z : X
  ht : t ∈ Z
  htM : t ∉ M
  hz : z ∈ Z
  hzM : z ∈ M
  hD : Even (Nat.card ↥(M ⊓ conjugate M t))

structure Conf16 {X : Type} [Group X] [Finite X] (Z : Set X) (M : Subgroup X) extends Ctx16 Z M where
  u : X
  hu : u ∈ M ⊓ conjugate M t
  hu2 : orderOf u = 2
  hmax : ∀ v ∈ M ⊓ conjugate M t, orderOf v = 2 →
    (Z ∩ ((centralizer ({v} : Set X) ⊓ M : Subgroup X) : Set X)).ncard ≤
      (Z ∩ ((centralizer ({u} : Set X) ⊓ M : Subgroup X) : Set X)).ncard
  P : Subgroup X
  T1 : Subgroup X
  hP : ABGLocalTools.IsSylowOf 2 P (zHull Z (centralizer ({u} : Set X)) ⊓ M)
  hT1 : ABGLocalTools.IsSylowOf 2 T1 (centralizer ({u} : Set X) ⊓ M)
  hPT1 : P ≤ T1
  ht_B : t ∈ centralizer ({u} : Set X)
  hz_T1 : z ∈ T1 ∧ ∀ y ∈ T1, y * z = z * y

namespace Conf16

variable {Z : Set X} {M : Subgroup X}

abbrev D (c : Conf16 Z M) : Subgroup X := M ⊓ conjugate M c.t

abbrev B (c : Conf16 Z M) : Subgroup X := centralizer ({c.u} : Set X)

abbrev B0 (c : Conf16 Z M) : Subgroup X := cenHull Z c.u

abbrev J (c : Conf16 Z M) : Subgroup X := centralizer (cenHull Z c.u : Set X)

abbrev Q (c : Conf16 Z M) : Subgroup X := omegaOneSub c.P

abbrev T (c : Conf16 Z M) : Subgroup X := c.T1 ⊓ (cenHull Z c.u ⊔ (c.B ⊓ c.J))

@[expose] def Bzero (c : Conf16 Z M) : Subgroup X :=
  Subgroup.closure ((zHull Z (c.B ⊓ M) : Set X) ∪ {c.t})

end Conf16

section Stmts

variable (Z : Set X) (M : Subgroup X)

@[expose] def Lemma161Stmt : Prop :=
  ∀ (c : Ctx16 Z M) (W : Subgroup X), Nat.card W = 4 → (∀ w ∈ W, w * w = 1) →
    W ≤ normalizer (kGrp M c.t : Set X) → W ≤ centralizer ({c.t} : Set X) →
    kGrp M c.t = ⨆ w ∈ (W : Set X) \ {1},
      ⁅zpowers c.t, centralizer ({w} : Set X) ⊓ kGrp M c.t⁆

@[expose] def fZero (Z : Set X) (M F : Subgroup X) (t : X) : Subgroup X :=
  Subgroup.closure ((zHull Z (M ⊓ F) : Set X) ∪ {t})

@[expose] def Lemma162Stmt : Prop :=
  ∀ (c : Ctx16 Z M) (F : Subgroup X), F ≠ ⊤ → c.z ∈ F → c.t ∈ F →
    (∃ y ∈ Z, y ∈ F ∧ y ∈ M ∧ y ≠ c.z) → zHull Z F = F →
    ∃ m : ℕ, 2 ≤ m ∧
      ((fZero Z M F c.t = F ∧ (Bender.BenderType ↥F m 1 1 ∨ Bender.BenderType ↥F m 2 1)) ∨
      (Bender.BenderType ↥(fZero Z M F c.t) m 1 1 ∧ (∃ e, BenderSub Z M F m 3 e) ∧
        ⁅zpowers c.t, (M ⊓ conjugate M c.t) ⊓ F⁆ ≤ fZero Z M F c.t ∧
        ∀ v : MulAut ↥F, v * v = 1 → (∀ x : ↥F, (x : X) = c.z ∨ (x : X) = c.t → v x = x) →
          ∀ x : ↥F, (x : X) ∈ fZero Z M F c.t → v x = x))

@[expose] def Lemma163Stmt : Prop :=
  ∀ c : Conf16 Z M,
    (∃ n i e : ℕ, BenderSub Z M (cenHull Z c.u) n i e) ∧
    ((c.B : Set X) = (c.B0 : Set X) * ((c.B ⊓ c.D : Subgroup X) : Set X)) ∧
    ABGLocalTools.IsSylowOf 2 c.T1 c.B ∧
    ∀ u' ∈ M, orderOf u' = 2 → Group.IsSolvable ↥(cenHull Z u') → centralizer ({u'} : Set X) ≤ M

@[expose] def Lemma164Stmt : Prop :=
  ∀ (c : Conf16 Z M) (n i e : ℕ), BenderSub Z M (cenHull Z c.u) n i e →
    (c.u ∈ centralizer (c.Bzero : Set X) ∧
      ∀ y ∈ c.B ⊓ centralizer (c.Bzero : Set X), orderOf y = 2 → y = c.u) ∧
    (closure ({c.u, c.z} : Set X) ≤ omegaOneSub (centerIn c.T1) ∧
      omegaOneSub (centerIn c.T1) ≤ c.Q ⊔ zpowers c.u ∧
      c.Q ⊔ zpowers c.u = omegaOneSub c.T) ∧
    ((∃ S : Subgroup X, ABGLocalTools.IsSylowOf 2 S c.D ∧ c.u ∈ S ∧ ∀ y ∈ S, y * c.u = c.u * y) →
      IsConj c.u (c.u * c.z) → 2 ^ n * Nat.card c.P ∣ (omega M).ncard - 1)

@[expose] def Prop165Stmt : Prop :=
  ∀ c : Conf16 Z M, Open.pRank 2 c.D = 1

@[expose] def Cor166Stmt : Prop :=
  ∀ c : Conf16 Z M,
    c.Q ⊔ zpowers c.u = omegaOneSub c.T1 ∧
    ABGLocalTools.IsSylowOf 2 (zpowers c.u) c.J ∧
    (IsConj c.u (c.u * c.z) ∧ ∀ y : X, orderOf y = 2 → IsConj c.z y ∨ IsConj c.u y) ∧
    (∀ W : Subgroup X, Nat.card W = 4 → (∀ w ∈ W, w * w = 1) → ∃ w ∈ W, w ∈ Z) ∧
    ∀ Y : Subgroup X, zHull Z Y = ⊥ →
      (∃ N : Subgroup X, N ≤ Y ∧ (N.subgroupOf Y).Normal ∧ Odd (Nat.card N) ∧
        ∃ k : ℕ, Nat.card Y = Nat.card N * 2 ^ k) ∧
      ∀ S : Sylow 2 ↥Y, IsCyclic (S : Subgroup ↥Y)

@[expose] def Lemma167Stmt : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ Y : Subgroup X, IsPGroup p Y → 3 ≤ (omegaFix M (Y : Set X)).ncard →
    zHull Z (normalizer (Y : Set X)) ≤ centralizer (Y : Set X)

@[expose] def Lemma171Stmt : Prop :=
  ∀ (c : Conf16 Z M) (n i e : ℕ), BenderSub Z M (cenHull Z c.u) n i e →
    (omega M).ncard ≥ (2 ^ n) ^ i + 1 ∧
    ((omega M).ncard - ((2 ^ n) ^ i + 1)) * Nat.card ↥(c.D ⊓ centralizer ({c.t * c.u} : Set X)) =
      (2 ^ n) ^ i * ((2 ^ n) ^ i + 1) * Nat.card ↥(c.D ⊓ centralizer ({c.u} : Set X))

@[expose] def Lemma172Stmt : Prop :=
  ∀ (c : Conf16 Z M) (n i e : ℕ), BenderSub Z M (cenHull Z c.u) n i e →
    (c.D ⊓ centralizer ({c.t, c.u} : Set X)).relIndex (c.D ⊓ centralizer ({c.u} : Set X)) =
        2 ^ n - 1 ∧
    (c.D ⊓ centralizer ({c.t, c.u} : Set X)).relIndex
        (c.D ⊓ centralizer ({c.t * c.u} : Set X)) ≡ 1 [MOD 2 ^ n] ∧
    (c.D ⊓ centralizer ({c.t, c.u} : Set X)).relIndex
        (c.D ⊓ centralizer ({c.t * c.u} : Set X)) ≠ 1 ∧
    Odd (Nat.card ↥(c.D ⊓ cenHull Z (c.t * c.u))) ∧
    omegaFix M ((c.D ⊓ cenHull Z (c.t * c.u) : Subgroup X) : Set X) = {M, conjugate M c.t} ∧
    ∀ Y : Subgroup X, Y ≤ c.D ⊓ cenHull Z (c.t * c.u) → ⁅zpowers c.t, Y⁆ ≠ ⊥ →
      ⁅zpowers c.t, Y⁆ ≤ Y →
      omegaFix M (Y : Set X) = {M, conjugate M c.t} ∧
        normalizer (Y : Set X) ⊓ cenHull Z (c.t * c.u) ≤
          (c.D ⊓ cenHull Z (c.t * c.u)) ⊔ zpowers c.t

@[expose] def Lemma173Stmt : Prop :=
  ∀ (c : Conf16 Z M) (n e : ℕ), ¬ BenderSub Z M (cenHull Z c.u) n 2 e

@[expose] def Lemma174Stmt : Prop :=
  ∀ (c : Conf16 Z M) (n e : ℕ), ¬ BenderSub Z M (cenHull Z c.u) n 3 e

@[expose] def Lemma175Stmt : Prop :=
  ∀ (c : Conf16 Z M) (n e : ℕ), BenderSub Z M (cenHull Z c.u) n 1 e →
    (omega M).ncard = (2 ^ n) ^ 2 + 1

@[expose] def Prop176Stmt : Prop :=
  ∀ (c : Conf16 Z M) (n e : ℕ), BenderSub Z M (cenHull Z c.u) n 1 e →
    oTwoIn M ⊔ c.D = M ∧ oTwoIn M ⊓ c.D = ⊥

@[expose] def Lemma311BenderStmt : Prop :=
  ∀ {K : Type} [Group K] [Finite K] {n e : ℕ}, Bender.BenderType K n 3 e →
    ∀ (C : Subgroup K), Odd (Nat.card C) → ∀ t : K, t * t = 1 → t ≠ 1 →
      (∀ c ∈ C, t * c * t⁻¹ ∈ C) → (∀ Q : Sylow 2 K, ¬ C ≤ Bender.borel (Q : Subgroup K)) →
        ∃ F F₀ : Subgroup K, Bender.Frame311 (2 ^ n) (Nat.gcd 3 (2 ^ n + 1)) F F₀ t ∧
          C ⊔ zpowers t ≤ F₀

end Stmts

end CFSG.GH74.Uniqueness
