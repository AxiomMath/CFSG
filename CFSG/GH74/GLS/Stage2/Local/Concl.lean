module

public import CFSG.GH74.GLS.Stage2.Local.Defs
public import CFSG.GH74.GLS.IVK.Defs2
public import CFSG.GH74.GLS.Bg.TwoGroups.Models
public import CFSG.GH74.GLS.Bg.Statements

public section

namespace CFSG.GH74.GLS.Stage2.Local

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12
open scoped commutatorElement Matrix MatrixGroups

section Vocab

variable {G : Type} [Group G]

@[expose] def IsClassicalKind (k : Kind) : Prop := k = Kind.psp4 ∨ ∃ ε : Bool, k = Kind.l4 ε

@[expose] def G2Three (z : G) (S : Subgroup G) : Prop :=
  ∃ (r₁ : ℕ) (L₁ L₂ : Subgroup (CentralizerBar z)), G2Shape z S r₁ 3 L₁ L₂

@[expose] def G2Big (z : G) (S : Subgroup G) : Prop :=
  ∃ (r₁ r₂ : ℕ) (L₁ L₂ : Subgroup (CentralizerBar z)), 3 < r₂ ∧ G2Shape z S r₁ r₂ L₁ L₂

@[expose] def IsQuat (Y : Type) [Group Y] : Prop := ∃ n : ℕ, IVK.IsQuaternionTwoGroup Y n

@[expose] def IsL34Two (Y : Type) [Group Y] : Prop :=
  Nonempty (Y ≃* CFSG.GH74.GLS.Bg.TwoGroups.SylSL3_4)

@[expose] def SO5 (K : Type) [Field K] : Subgroup (GL (Fin 2 ⊕ Fin 2 ⊕ Unit) K) :=
  Subgroup.closure {A : GL (Fin 2 ⊕ Fin 2 ⊕ Unit) K | ∀ v,
    StatedQuadOdd 2 K ((A : Matrix (Fin 2 ⊕ Fin 2 ⊕ Unit) (Fin 2 ⊕ Fin 2 ⊕ Unit) K) *ᵥ v) =
      StatedQuadOdd 2 K v} ⊓ (Matrix.GeneralLinearGroup.det).ker

@[expose] def IsSO5 (X : Type) [Group X] (q : ℕ) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = q ∧ Nonempty (X ≃* ↥(SO5 F))

@[expose] def HasTwoInvolutionClasses (Y : Type) [Group Y] : Prop :=
  ∃ x y : Y, orderOf x = 2 ∧ orderOf y = 2 ∧ ¬ IsConj x y

end Vocab

section P21

variable {G : Type} [Group G]

@[expose] def Prop21g (z : G) (S : Subgroup G) : Prop :=
  (∀ c ∈ Cen z, ∃ o ∈ OddCore z, ∃ l ∈ LC z, ∃ s ∈ S, ∃ d ∈ Dz S z, c = o * l * s * d) ∧
    Dz S z = pPrimeCoreOf 2 (centralizer ((S1 S z : Subgroup G) : Set G))

@[expose] def Prop21h (z : G) : Prop :=
  ∃ V : Subgroup G, V ≤ LC z ∧ IVK.IsFourSubgroup V ∧
    (AutOrd (Cen z) V = 3 ∨ AutOrd (Cen z) V = 6)

@[expose] def Prop22a (z : G) (S : Subgroup G) : Prop :=
  (∀ u v : G, orderOf u = 2 → orderOf v = 2 → IsConj u v) → ¬ IsMulCommutative ↥S →
    ∀ U : Subgroup G, U ≤ S → IVK.IsFourSubgroup U → (∀ s ∈ S, ∀ u ∈ U, s * u * s⁻¹ ∈ U) →
      z ∈ U ∧ AutOrd (⊤ : Subgroup G) U = 6

@[expose] def Prop22x [Finite G] (z : G) (S : Subgroup G) : Prop :=
  ∀ (q : ℕ) (L₁ L₂ : Subgroup (CentralizerBar z)), Stage1Pair G z S q L₁ L₂ →
    ∀ t ∈ S, IsConj z t → Swaps z t L₁ L₂ → z ∈ ⁅LC z, zpowers t⁆

end P21

section L23

variable {G : Type} [Group G]

@[expose] def Lemma23e (z : G) (k : Kind) (S : Subgroup G) : Prop :=
  ∀ U : Subgroup G, U ≤ S → IVK.IsFourSubgroup U → (∀ s ∈ S, ∀ u ∈ U, s * u * s⁻¹ ∈ U) →
    U ≤ LC z ⊓ ⁅Cen z, U⁆ ∧
    (k ≠ Kind.m12 → (k = Kind.g2 → G2Big z S) → LC z ≤ ⁅Cen z, U⁆ ⊔ OddCore z)

@[expose] def Lemma23 (z : G) (k : Kind) (S : Subgroup G) : Prop :=
  ((RC S z).relIndex S ≤ 4 ∧ ((RC S z).relIndex S = 4 → ∃ ε : Bool, k = Kind.l4 ε)) ∧
  (RC S z = S → k = Kind.mcl ∨ k = Kind.ly) ∧
  (RC S z ≠ S → ∃ s ∈ S, s ∉ RC S z ∧ orderOf s = 2) ∧
  2 ≤ pRank 2 ↥(⁅Cen z, Cen z⁆ : Subgroup G) ∧
  Lemma23e z k S

@[expose] def Lemma26 (z : G) (S : Subgroup G) : Prop :=
  pLayerOf 2 (Cen z) ⊔ (S ⊓ WC z) ≤
    ⨆ (t : G) (_ : t ∈ S) (_ : IsConj z t), O2Of ⁅Cen z, zpowers t⁆

end L23

section P27

variable {G : Type} [Group G] [Finite G]

@[expose] def Prop27Hyp (z x : G) (T : Subgroup G) : Prop :=
  x ∈ Cen z ∧ IsNonCentralInvolution x ∧
    (Ixz z x ≠ ⊥ ∨ ∀ x' ∈ Cen z, IsNonCentralInvolution x' → Ixz z x' = ⊥) ∧
    CFSG.ABGLocalTools.IsSylowOf 2 T (centralizer ({x} : Set G)) ∧ z ∈ T

@[expose] def Prop27Concl (z : G) (k : Kind) (S : Subgroup G) (x : G) (T : Subgroup G) : Prop :=
  (k = Kind.m12 → ∃ q : ℕ, (q % 8 = 3 ∨ q % 8 = 5) ∧
      IVK.IsL2 (↥(Jx x) ⧸ pPrimeCore 2 ↥(Jx x)) (fun r => r = q) ∧
      CFSG.ABGLocalTools.IsSylowOf 2 (zpowers x) (CxK x (Jx x)) ∧
      (∃ _ : ((CxK x (Jx x)).subgroupOf (centralizer ({x} : Set G))).Normal,
        IVK.IsPGL2 ↥(oPrimeResidual 2 (↥(centralizer ({x} : Set G)) ⧸
          (CxK x (Jx x)).subgroupOf (centralizer ({x} : Set G)))) (fun r => r = q)) ∧
      ∀ u : G, (u ∈ Jx x ∧ orderOf u = 2) ↔
        (orderOf u = 2 ∧ IsConj z u ∧ u ∈ centralizer ({x} : Set G))) ∧
  (IsClassicalKind k → Ixz z x ≠ ⊥) ∧
  (k = Kind.psp4 → ∀ (q : ℕ) (L₁ L₂ : Subgroup (CentralizerBar z)), Stage1PSp4 G z S q L₁ L₂ →
      IVK.IsL2 (↥(Jx x) ⧸ pPrimeCore 2 ↥(Jx x)) (fun r => r = q) ∧
        IsDihedral ↥(T ⊓ CxK x (Ixz z x))) ∧
  (∀ ε : Bool, k = Kind.l4 ε → ∀ (q : ℕ) (L₁ L₂ : Subgroup (CentralizerBar z)),
      Stage1L4 G z S ε q L₁ L₂ →
      (IVK.IsL2 (↥(Jx x) ⧸ pPrimeCore 2 ↥(Jx x)) (fun r => r = q ^ 2) ∨
        (q = 5 ∧ Nonempty ((↥(Jx x) ⧸ pPrimeCore 2 ↥(Jx x)) ≃* alternatingGroup (Fin 7))))) ∧
  (IsClassicalKind k → (∀ u ∈ Jx x, orderOf u = 2 → IsConj x u) ∧
      (∀ j ∈ Jx x, orderOf j = 2 → IsConj z (x * j))) ∧
  (IsClassicalKind k → HasNormal2Compl (CxK x (Ixz z x)) ∧
      (IsCyclic ↥(T ⊓ CxK x (Ixz z x)) ∨ IsDihedral ↥(T ⊓ CxK x (Ixz z x)))) ∧
  oPrimeResidualOf 2 (centralizer ({x} : Set G)) ⊔ pPrimeCoreOf 2 (centralizer ({x} : Set G)) =
    pPrimeCoreOf 2 (centralizer ({x} : Set G)) ⊔ Jx x ⊔ T ∧
  (∃ T₁ : Subgroup G, T₁ ≤ T ∧ (T ⊓ Jx x) ⊔ T₁ = T ∧ T₁ ⊓ Jx x = ⊥ ∧ x ∈ T₁ ∧
      (IsClassicalKind k → z ∈ T₁) ∧ IsDihedral ↥T₁) ∧
  (∀ P : Sylow 2 ↥(O2Of (centralizer ({x} : Set G))), IsDihedral ↥P)

end P27

section L29

variable {G : Type} [Group G]

@[expose] def Lemma29b (U : Subgroup G) : Prop :=
  ∃ (Q Xg : Subgroup G) (v : G),
    CFSG.ABGLocalTools.IsSylowOf 2 Q (O22Of (centralizer (U : Set G))) ∧ v * v = 1 ∧
    (∃ x : G, Xg = zpowers x ∧ IsPGroup 3 ↥Xg ∧
      x ∈ normalizer (Q : Set G) ⊓ centralizer (U : Set G) ∧
      x ^ 3 ∈ pPrimeCoreOf 2 (centralizer (U : Set G))) ∧
    (∀ c ∈ centralizer (U : Set G), ∃ o ∈ pPrimeCoreOf 2 (centralizer (U : Set G)), ∃ q ∈ Q,
      ∃ a ∈ Xg, ∃ b ∈ zpowers v, c = o * q * a * b) ∧
    ⁅Q, Xg⁆ = Q ∧ IsL34Two ↥Q ∧ Q ⊓ centralizer (Xg : Set G) = U ∧
    CFSG.ABGLocalTools.IsSylowOf 2 U (centralizer (Q : Set G)) ∧
    (QuotIso (centralizer (U : Set G)) (O22Of (centralizer (U : Set G))) (Multiplicative (ZMod 3)) ∨
      QuotIso (centralizer (U : Set G)) (O22Of (centralizer (U : Set G))) (Equiv.Perm (Fin 3)))

@[expose] def Lemma29 (z : G) (k : Kind) : Prop :=
  ∀ U : Subgroup G, IVK.IsFourSubgroup U →
    (HasNormal2Compl (centralizer (U : Set G)) ∨
      (IsClassicalKind k ∧ (∀ P : Sylow 2 ↥(O2Of (centralizer (U : Set G))), IsDihedral ↥P) ∧
        ((∀ u ∈ U, ¬ IsConj z u) ∨
          ∃ t g : G, SwapsComps z t ∧ conjugate (zpowers z ⊔ zpowers t) g = U)) ∨
      ((k = Kind.mcl ∨ k = Kind.ly) ∧ Lemma29b U)) ∧
    ∀ X : Subgroup G, X ≤ centralizer (U : Set G) → ¬ Group.IsSolvable ↥X →
      (IVK.IsL2 (↥(pLayerOf 2 X) ⧸ pPrimeCore 2 ↥(pLayerOf 2 X)) Odd ∨
        Nonempty ((↥(pLayerOf 2 X) ⧸ pPrimeCore 2 ↥(pLayerOf 2 X)) ≃* alternatingGroup (Fin 7)))

end L29

section Sec3

variable {G : Type} [Group G]

abbrev Hat (K : Subgroup G) : Type := ↥K ⧸ pPrimeCore 2 ↥K

@[expose] def Lemma31Hyp (k : Kind) (H J R : Subgroup G) : Prop :=
  (IsPCompIn 2 H J ∨
    (J ≤ H ∧ (J.subgroupOf H).Normal ∧ HasSL2Model (Hat J) (fun q => q = 3))) ∧
  (Group.IsSolvable ↥J → k ≠ Kind.mcl ∧ k ≠ Kind.ly) ∧
  CFSG.ABGLocalTools.IsSylowOf 2 R (H ⊓ centralizerSection J (pPrimeCoreOf 2 J)) ∧ R ≠ ⊥

@[expose] def Lemma31Concl (z : G) (H J R : Subgroup G) : Prop :=
  (IsCyclic ↥R ∨ IsQuat ↥R ∨ IsDihedral ↥R) ∧
  (IsDihedral ↥R → (Nonempty (Hat J ≃* alternatingGroup (Fin 7)) ∨ IVK.IsL2 (Hat J) Odd)) ∧
  (¬ Group.IsSolvable ↥J → ¬ IsMulCommutative ↥R → ∀ s : G,
    (center ↥R).map R.subtype = zpowers s → IsCentralInvolution s → s ∈ J) ∧
  (J ≤ pLayerOf 2 H → J ≠ pLayerOf 2 H →
    generalizedFitting (HBar H) = barIn H (pLayerOf 2 H) ∧
    ((∃ K₁ K₂ : Subgroup (HBar H), IsCentralProd K₁ K₂ (barIn H (pLayerOf 2 H)) ∧
        HasSL2Model ↥K₁ Odd ∧ HasSL2Model ↥K₂ Odd) ∨
      (∃ K₁ K₂ : Subgroup (HBar H), IsInternalDirectProduct K₁ K₂ (barIn H (pLayerOf 2 H)) ∧
        (IVK.IsL2 ↥K₁ Odd ∨ Nonempty (↥K₁ ≃* alternatingGroup (Fin 7))) ∧
        (IVK.IsL2 ↥K₂ Odd ∨ Nonempty (↥K₂ ≃* alternatingGroup (Fin 7)))))) ∧
  (∀ m : ℕ, 7 ≤ m → m ≤ 11 → IsDoubleCoverOfAlt (Hat J) m →
    ∃ n : ℕ, m ≤ n ∧ 8 ≤ n ∧ n ≤ 11 ∧ IsDoubleCoverOfAlt (CentralizerBar z) n) ∧
  ((NativeSporadic.IsSporadic (Hat J) .M11 ∨
      ∃ p f : ℕ, p.Prime ∧ 1 ≤ f ∧ (Odd (p ^ f) ∨ p ^ f = 4) ∧
        (LieModel (Hat J) .PSL 3 p f ∨ LieModel (Hat J) .PSU 3 p f)) →
    NativeSporadic.IsSporadic (Hat J) .M11 ∧ IsDoubleCoverOfAlt (CentralizerBar z) 11) ∧
  (¬ IsCyclic ↥R → (Nonempty ((Hat J ⧸ center (Hat J)) ≃* alternatingGroup (Fin 7)) ∨
    IVK.IsL2 (Hat J ⧸ center (Hat J)) Odd))

@[expose] def CompList (J : Type) [Group J] : Prop :=
  (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧
    (HasSL2Model J (fun q => q = p ^ f) ∨ LieModel J .PSL 2 p f ∨ LieModel J .PSL 3 p f ∨
      LieModel J .PSU 3 p f ∨ LieModel J .twistedG2 0 p f ∨ LieModel J .G2 0 p f ∨
      LieModel J .trialityD4 0 p f ∨ LieModel J .PSp 2 p f ∨
      (p ^ f % 8 ≠ 1 ∧ LieModel J .PSL 4 p f) ∨ (p ^ f % 8 ≠ 7 ∧ LieModel J .PSU 4 p f))) ∨
  (LieModel J .PSL 2 2 3 ∨ LieModel J .PSL 2 2 4 ∨ LieModel J .twistedB2 0 2 3 ∨
    LieModel J .PSU 3 2 2 ∨ LieModel J .PSL 3 2 2 ∨
    (IsL34Quotient J ∧ Nonempty (↥(center J) ≃* Multiplicative (ZMod 4)))) ∨
  (∃ n : ℕ, 7 ≤ n ∧ n ≤ 11 ∧
    (Nonempty (J ≃* alternatingGroup (Fin n)) ∨ IsDoubleCoverOfAlt J n)) ∨
  (NativeSporadic.IsSporadic J .M11 ∨ NativeSporadic.IsSporadic J .M12 ∨
    NativeSporadic.IsSporadic J .M22 ∨ NativeSporadic.IsSporadic J .M23 ∨
    NativeSporadic.IsSporadic J .J1 ∨ NativeSporadic.IsSporadic J .J3 ∨
    NativeSporadic.IsSporadic J .McL ∨ NativeSporadic.IsSporadic J .Ly ∨
    NativeSporadic.IsSporadic J .ONan)

@[expose] def Prop32Concl (H : Subgroup G) : Prop :=
  ∀ J : Subgroup (HBar H), IsComponent J → IsCyclic ↥(center ↥J) ∧ CompList ↥J

end Sec3

section Sec3b

variable {G : Type} [Group G] [Finite G]

@[expose] def Prop34Concl (z : G) (k : Kind) (S : Subgroup G) (H : Subgroup G) : Prop :=
  (∀ h ∈ H, ∃ c ∈ Cen z, ∃ o ∈ pPrimeCoreOf 2 H, h = c * o) ∨
    IsDihedral ↥S ∨
    (∃ (ε : Bool) (q : ℕ) (L₁ L₂ : Subgroup (CentralizerBar z)),
      k = Kind.l4 ε ∧ Stage1L4 G z S ε q L₁ L₂ ∧ q % 4 = (if ε then 3 else 1) ∧ 3 < q ∧
      IVK.IsPSp4 ↥(generalizedFitting (HBar H)) q ∧ IsCoatom (barIn H (Cen z)) ∧
      barIn H (LC z) ≤ generalizedFitting (HBar H) ∧ ¬ barIn H S ≤ generalizedFitting (HBar H) ∧
      O2Of H ≠ H ∧ CFSG.GH74.GLS.Bg.Fm (barIn H (Cen z)) = barIn H (zpowers z))

@[expose] def Lemma35Hyp (H J R : Subgroup G) : Prop :=
  IsPCompIn 2 H J ∧ CFSG.ABGLocalTools.IsSylowOf 2 R (H ⊓ centralizerSection J (pPrimeCoreOf 2 J))

@[expose] def Lemma35Concl (z : G) (k : Kind) (S : Subgroup G) (H J R : Subgroup G) : Prop :=
  O2coreOf H ≤ R ∧ (2 ≤ pRank 2 ↥J → IsCyclic ↥R) ∧
    (pRank 2 ↥J = 1 → (∀ h ∈ H, ∃ o ∈ pPrimeCoreOf 2 H, ∃ c ∈ Cen z, h = o * c) ∧ z ∈ R ⊓ J ∧
      ((J ≠ pLayerOf 2 H ∧ ((k = Kind.g2 ∧ G2Big z S) ∨ IsClassicalKind k) ∧ IsQuat ↥R) ∨
        (J = pLayerOf 2 H ∧ k = Kind.g2 ∧ G2Three z S ∧ IsQuat ↥R)))

end Sec3b

structure Stage2Local (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G) : Prop where
  data : Stage1Data G z S k
  prop21g : Prop21g z S
  prop21h : Prop21h z
  prop22a : Prop22a z S
  prop22x : Prop22x z S
  lemma23 : Lemma23 z k S
  lemma26 : Lemma26 z S
  prop27 : ∀ (x : G) (T : Subgroup G), Prop27Hyp z x T → Prop27Concl z k S x T
  lemma29 : Lemma29 z k
  lemma31 : ∀ H J R : Subgroup G, H ≠ ⊤ → Lemma31Hyp k H J R → Lemma31Concl z H J R
  prop32 : ∀ H : Subgroup G, H ≠ ⊤ → Prop32Concl H
  prop34 : ∀ H : Subgroup G, Cen z ≤ H → H ≠ ⊤ → Prop34Concl z k S H
  lemma35 : ∀ H J R : Subgroup G, Cen z ≤ H → H ≠ ⊤ → Lemma35Hyp H J R → Lemma35Concl z k S H J R

end CFSG.GH74.GLS.Stage2.Local
