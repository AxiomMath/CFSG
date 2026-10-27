module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case2Basic
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case2K0
public import CFSG.Open.GLADefs
public import CFSG.Blueprint.Catalog
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3 (u3S u3T u3K0 U3LineWC CentSeries)

@[expose] def KFactI6103Five : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsQuasisimple K → IsCatalogGroup (K ⧸ Subgroup.center K) →
    5 ∣ Nat.card (Subgroup.center K) → ∀ Q : Sylow 5 K,
      4 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup K) ∨
        ¬ IsMulCommutative (Subgroup.closure {g : K | g ∈ (Q : Subgroup K) ∧ g ^ 5 = 1})

@[expose] def KFactI122Five : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K : Subgroup X), K.Normal → IsSimpleGroup K →
    (∃ a b : K, a * b ≠ b * a) → IsCatalogGroup K → Subgroup.centralizer (K : Set X) = ⊥ →
    ∀ (Q : Sylow 5 X) (A B : Subgroup X) (y : X), Nat.card (Q : Subgroup X) = 5 ^ 5 →
      A ≤ (Q : Subgroup X) → B ≤ (Q : Subgroup X) → IsCyclic A → IsCyclic B →
      Nat.card A = 5 ^ 2 → Nat.card B = 5 ^ 2 → A ⊓ B = ⊥ → (∀ a ∈ A, ∀ b ∈ B, a * b = b * a) →
      y ∈ (Q : Subgroup X) → orderOf y = 5 → y ∉ A ⊔ B → (A ⊔ B) ⊔ Subgroup.zpowers y = (Q : Subgroup X) →
      y ∈ Subgroup.normalizer (A : Set X) → y ∈ Subgroup.normalizer (B : Set X) →
      (∀ z ∈ (Q : Subgroup X), (∀ q ∈ (Q : Subgroup X), q * z = z * q) ↔ (z ∈ A ⊔ B ∧ z ^ 5 = 1)) →
      ∃ N : Subgroup X, N.Normal ∧ (∃ k : ℕ, N.index = 5 ^ k) ∧ N ≠ ⊤

@[expose] def KFactI713Out : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K →
    (∃ a b : K, a * b ≠ b * a) → IsCatalogGroup K → CFSG.Open.pRank p (⊤ : Subgroup K) ≤ 1 →
      ((∀ S : Sylow p K, Nat.card (S : Subgroup K) = p) →
        ¬ p ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer K)) ∧
      (∃ N : Subgroup (CFSG.ComponentClassification.OuterAutomorphisms.Outer K), N.Normal ∧
        ¬ p ∣ Nat.card N ∧ ∃ k : ℕ, N.index = p ^ k)

@[expose] def KFactFieldGeneration5 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L : Subgroup Y), L.Normal → IsSimpleGroup L →
    (∃ a b : L, a * b ≠ b * a) → IsCatalogGroup L → Subgroup.centralizer (L : Set Y) = ⊥ →
    ¬ CFSG.RankThree.PartOne.Census3.IsoLie ↥L (.suzuki 2) →
    (∃ (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n ℓ f : ℕ), ℓ ≠ 5 ∧
      CFSG.Blueprint.LieModel ↥L t n ℓ f) →
    (∀ S : Sylow 5 ↥L, IsCyclic (S : Subgroup ↥L)) →
    ∀ (B : Subgroup Y) (x : Y), IsElemAbelian 5 B → Nat.card B = 5 ^ 2 → x ∈ B → x ∈ L → x ≠ 1 →
      (∀ b ∈ B, b ∈ L → b ∈ Subgroup.zpowers x) →
      L ≤ ⨆ b ∈ {b : Y | b ∈ B ∧ b ∉ L}, Subgroup.centralizer ({b} : Set Y)

@[expose] def KFactNonabF5 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CFSG.AGLEmbedding.CatalogSimpleSections Y →
    primeComplementCore (G := Y) 5 = ⊥ →
    ∀ (F Γ B R₀ : Subgroup Y) (x : Y), CFSG.ABGLocalTools.IsSylowOf 5 F ⊤ → ¬ IsMulCommutative F →
      Nat.card F = 125 → (∀ f ∈ F, f ^ 25 = 1) →
      (∀ z ∈ F, (∀ f ∈ F, f * z = z * f) ↔ z ∈ Subgroup.zpowers x) →
      (∀ b, b ∈ B ↔ (b ∈ F ∧ b ^ 5 = 1)) → IsElemAbelian 5 B → Nat.card B = 5 ^ 2 → F ≤ Γ →
      (∀ b ∈ B, b ∉ Subgroup.zpowers x → Subgroup.centralizer ({b} : Set Y) ≤ Γ) →
      R₀ ≠ ⊥ → IsPGroup 2 R₀ → B ≤ Subgroup.normalizer (R₀ : Set Y) →
      GLALayer (⊤ : Subgroup Y) ⊔ pCoreOf 5 (⊤ : Subgroup Y) ≤ Γ

section Abstract

variable {X : Type*} [Group X]

@[expose] def sz32Q0 (a c : X) : Subgroup X := Subgroup.zpowers a ⊔ Subgroup.zpowers c

@[expose] def sz32Z (a c : X) : Subgroup X := Subgroup.zpowers (a ^ 5) ⊔ Subgroup.zpowers (c ^ 5)

@[expose] def sz32Om (a c y : X) : Subgroup X := sz32Z a c ⊔ Subgroup.zpowers y

structure Sz32QPres (Q : Subgroup X) (a c y x : X) : Prop where
  a_mem : a ∈ Q
  c_mem : c ∈ Q
  y_mem : y ∈ Q
  gen : Q = Subgroup.zpowers a ⊔ Subgroup.zpowers c ⊔ Subgroup.zpowers y
  ord_a : orderOf a = 25
  ord_c : ∃ m : ℕ, 1 ≤ m ∧ orderOf c = 5 ^ m
  ac : a * c = c * a
  inf : Subgroup.zpowers a ⊓ Subgroup.zpowers c = ⊥
  y5 : y ^ 5 = 1
  y_not : y ∉ Subgroup.zpowers a ⊔ Subgroup.zpowers c
  ya : ∃ n : ℤ, y * a * y⁻¹ = a ^ n ∧ n % 5 = 1 ∧ n % 25 ≠ 1
  yc : ∃ ν : ℤ, y * c * y⁻¹ = c ^ ν ∧ ν % 5 = 1
  x_mem : x ∈ Subgroup.zpowers c
  x_ord : orderOf x = 5

structure Sz32QFacts (Q : Subgroup X) (a c y x : X) : Prop where
  ord_c : orderOf c = 25
  x_eq : Subgroup.zpowers x = Subgroup.zpowers (c ^ 5)
  yc_ne : y * c * y⁻¹ ≠ c
  card : Nat.card Q = 5 ^ 5
  Q0_card : Nat.card (sz32Q0 a c) = 5 ^ 4
  Q0_comm : IsMulCommutative (sz32Q0 a c)
  Q0_unique : ∀ B : Subgroup X, B ≤ Q → IsMulCommutative B → 5 ^ 4 ≤ Nat.card B → B = sz32Q0 a c
  center : ∀ z ∈ Q, (∀ q ∈ Q, q * z = z * q) ↔ z ∈ sz32Z a c
  Z_card : Nat.card (sz32Z a c) = 5 ^ 2
  Z_elem : IsElemAbelian 5 (sz32Z a c)
  comm_eq : ⁅Q, Q⁆ = sz32Z a c
  pow5 : ∀ v ∈ Q, v ^ 5 ∈ sz32Z a c
  pow5_surj : ∀ z ∈ sz32Z a c, ∃ v ∈ Q, v ^ 5 = z
  exp : ∀ v ∈ Q, v ^ 25 = 1
  Om_le : sz32Om a c y ≤ Q
  Om_card : Nat.card (sz32Om a c y) = 5 ^ 3
  Om_elem : IsElemAbelian 5 (sz32Om a c y)
  Om_all : ∀ v ∈ Q, v ^ 5 = 1 → v ∈ sz32Om a c y
  cent_le : ∀ u ∈ sz32Om a c y, u ∉ sz32Z a c → ∀ q ∈ Q, q * u = u * q → q ∈ sz32Om a c y
  shear : ∀ u ∈ sz32Om a c y, u ∉ sz32Z a c → ∀ z ∈ sz32Z a c, ∃ q ∈ Q, q * u * q⁻¹ = u * z

structure Sz32PlaneAbs (Z Om : Subgroup X) (x : X) (U : Subgroup X) : Prop where
  elem : IsElemAbelian 5 U
  card : Nat.card U = 5 ^ 2
  le_Om : U ≤ Om
  mem : x ∈ U
  inf_Z : U ⊓ Z = Subgroup.zpowers x

structure Sz32Case2Data {Y : Type} [Group Y] [Finite Y] (Pb : Subgroup Y) (a c y : Y) : Prop where
  core : primeComplementCore (G := Y) 5 = ⊥
  catalog : CFSG.AGLEmbedding.CatalogSimpleSections Y
  rank : CFSG.Open.pRank 5 (⊤ : Subgroup Y) ≤ 3
  sylow : ∃ S : Sylow 5 Y, (S : Subgroup Y) = Pb
  pres : Sz32QPres Pb a c y (c ^ 5)
  facts : Sz32QFacts Pb a c y (c ^ 5)
  swap : ∃ g ∈ Subgroup.normalizer (Pb : Set Y),
    (Subgroup.zpowers (c ^ 5)).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers (a ^ 5)
  wc : ∀ g : Y, (sz32Z a c).map (MulAut.conj g).toMonoidHom ≤ Pb →
    (sz32Z a c).map (MulAut.conj g).toMonoidHom = sz32Z a c
  irr : ∀ L : Subgroup Y, L ≤ sz32Z a c →
    Subgroup.normalizer (sz32Z a c : Set Y) ≤ Subgroup.normalizer (L : Set Y) → L = ⊥ ∨ L = sz32Z a c
  perf : ∀ N : Subgroup Y, N.Normal → (∃ k : ℕ, N.index = 5 ^ k) → N = ⊤
  series : ∃ N : Subgroup Y, CentSeries 5 (Subgroup.centralizer ({c ^ 5} : Set Y)) Pb N

end Abstract

section GLevel

variable {G : Type} [Group G] [Finite G] {P : Sylow 5 G} {M : Subgroup G} {x : G} {J : Subgroup G}

structure Sz32QDecomp (P : Sylow 5 G) (x : G) (J : Subgroup G) (a c y : G) : Prop where
  pres : Sz32QPres (u3S P x) a c y x
  a_J : a ∈ J
  T_eq : Subgroup.zpowers a = u3T P x J
  c_K0 : c ∈ u3K0 5 x J
  QC : ∀ q ∈ u3S P x, q ∈ u3K0 5 x J → q ∈ Subgroup.zpowers c

structure Sz32Lines (P : Sylow 5 G) (x e : G) : Prop where
  le_cent : (P : Subgroup G) ≤ Subgroup.centralizer ({x} : Set G)
  lines : ∀ g : G, (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom ≤ (P : Subgroup G) →
    (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers x ∨
      (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers e
  swap : ∃ g ∈ Subgroup.normalizer ((P : Subgroup G) : Set G),
    (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers e

structure Sz32Struct (P : Sylow 5 G) (x : G) (J : Subgroup G) (a c y : G) : Prop where
  decomp : Sz32QDecomp P x J a c y
  le_cent : (P : Subgroup G) ≤ Subgroup.centralizer ({x} : Set G)
  facts : Sz32QFacts (P : Subgroup G) a c y x

structure Sz32ZFacts (P : Sylow 5 G) (M : Subgroup G) (x e : G) : Prop where
  NZ_le : Subgroup.normalizer ((Subgroup.zpowers e ⊔ Subgroup.zpowers x : Subgroup G) : Set G) ≤ M
  Z_wc : ∀ h : G, (Subgroup.zpowers e ⊔ Subgroup.zpowers x).map (MulAut.conj h).toMonoidHom ≤ (P : Subgroup G) →
    (Subgroup.zpowers e ⊔ Subgroup.zpowers x).map (MulAut.conj h).toMonoidHom =
      Subgroup.zpowers e ⊔ Subgroup.zpowers x
  Z_irr : ∀ L : Subgroup G, L ≤ Subgroup.zpowers e ⊔ Subgroup.zpowers x →
    Subgroup.normalizer ((Subgroup.zpowers e ⊔ Subgroup.zpowers x : Subgroup G) : Set G) ≤
      Subgroup.normalizer (L : Set G) → L = ⊥ ∨ L = Subgroup.zpowers e ⊔ Subgroup.zpowers x

structure Sz32Plane (P : Sylow 5 G) (x a c y : G) (U : Subgroup G) : Prop where
  abs : Sz32PlaneAbs (sz32Z a c) (sz32Om a c y) x U
  le_P : U ≤ (P : Subgroup G)
  wc : ∀ g : G, (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom ≤ U →
    (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers x

theorem u3S_eq_of_le_cent {p : ℕ} {P : Sylow p G} {x : G}
    (h : (P : Subgroup G) ≤ Subgroup.centralizer ({x} : Set G)) : u3S P x = (P : Subgroup G) :=
  inf_eq_left.2 h

theorem Sz32Struct.pres_P {P : Sylow 5 G} {x : G} {J : Subgroup G} {a c y : G}
    (h : Sz32Struct P x J a c y) : Sz32QPres (P : Subgroup G) a c y x := by
  have := h.decomp.pres
  rwa [u3S_eq_of_le_cent h.le_cent] at this

end GLevel

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
