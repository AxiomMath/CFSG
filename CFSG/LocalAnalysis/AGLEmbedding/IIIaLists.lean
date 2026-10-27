module

public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCatalog
public import CFSG.LocalAnalysis.AGLEmbedding.KlingenRoute

public section

namespace CFSG.AGLEmbedding

open CFSG.Open

@[expose] def IsSpFourIndex (p : ℕ) (d : TauCeti.ValidLieTypeIndex) : Prop :=
  ∃ q : TauCeti.PrimePower, (q.p = p ∧ q.exponent = 1 ∧ d.1 = .B 2 q) ∨
    (p = 3 ∧ q.p = 2 ∧ q.exponent = 1 ∧ d.1 = .twistedA 3 q)

@[expose] def IsUnitaryIndex (p : ℕ) (d : TauCeti.ValidLieTypeIndex) : Prop :=
  ∃ q : TauCeti.PrimePower, q.p = p ∧ d.1 = .twistedA 2 q

@[expose] def IsReeGTwoIndex (p : ℕ) (d : TauCeti.ValidLieTypeIndex) : Prop :=
  p = 3 ∧ ∃ m, d.1 = .reeG2 m

@[expose] def IsP1ChevTwoIndex (p : ℕ) (d : TauCeti.ValidLieTypeIndex) : Prop :=
  (p = 3 ∧ ∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 1 ∧
    (d.1 = .B 3 q ∨ d.1 = .B 4 q ∨ d.1 = .twistedA 4 q ∨ d.1 = .twistedA 5 q ∨ d.1 = .D 4 q ∨
      d.1 = .F4 q ∨ d.1 = .E6 q ∨ d.1 = .trialityD4 q)) ∨
  (p = 3 ∧ ∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 3 ∧
    (d.1 = .B 2 q ∨ d.1 = .G2 q ∨ d.1 = .trialityD4 q ∨ d.1 = .twistedA 2 q)) ∨
  (p = 5 ∧ d.1 = .reeF4 2)

@[expose] def P1ThreeLieList (p : ℕ) (d : TauCeti.ValidLieTypeIndex) : Prop :=
  (∃ n, IsLinTwoIndex p n d) ∨ IsUnitaryIndex p d ∨ IsReeGTwoIndex p d ∨ IsSpFourIndex p d ∨
    IsP1ChevTwoIndex p d

@[expose] def KFactP1ThreeLie : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (Y : Type) [Group Y] [Finite Y] (Rb : Sylow p Y) (Y₀ : Subgroup Y),
    ReducedNongeneration p Y Rb Y₀ → CatalogSimpleSections Y →
    ∀ K : Subgroup Y, IsComponentOf K ⊤ → (∀ L : Subgroup Y, IsComponentOf L ⊤ → L = K) →
      ¬ IsCyclic ((Rb : Subgroup Y) ⊓ K : Subgroup Y) →
      (∀ c ∈ (Rb : Subgroup Y) ⊓ Subgroup.centralizer (K : Set Y), orderOf c = p →
        c ∈ (Subgroup.center K).map K.subtype) →
      ∀ d : TauCeti.ValidLieTypeIndex,
        Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group) → P1ThreeLieList p d

@[expose] def KFactKlingenSpFour : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (Y : Type) [Group Y] [Finite Y] (Rb : Sylow p Y) (Y₀ : Subgroup Y),
    ReducedNongeneration p Y Rb Y₀ → CatalogSimpleSections Y →
    ∀ K : Subgroup Y, IsComponentOf K ⊤ → (∀ L : Subgroup Y, IsComponentOf L ⊤ → L = K) →
      ¬ IsCyclic ((Rb : Subgroup Y) ⊓ K : Subgroup Y) →
      (∀ c ∈ (Rb : Subgroup Y) ⊓ Subgroup.centralizer (K : Set Y), orderOf c = p →
        c ∈ (Subgroup.center K).map K.subtype) →
      ∀ d : TauCeti.ValidLieTypeIndex, IsSpFourIndex p d →
        Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group) →
        HasKlingenData p Rb Y₀

@[expose] def P1ThreeSporList (p : ℕ) (s : TauCeti.SporadicName) : Prop :=
  (p = 3 ∧ (s = .J3 ∨ s = .McL ∨ s = .Suz ∨ s = .ONan ∨ s = .Co1 ∨ s = .Co2 ∨ s = .Co3 ∨
    s = .Fi22 ∨ s = .Fi23 ∨ s = .Fi24Prime ∨ s = .HN ∨ s = .Ly ∨ s = .Th ∨ s = .B ∨ s = .M ∨
    s = .M22)) ∨
  (p = 5 ∧ (s = .Co1 ∨ s = .Ly ∨ s = .HN ∨ s = .B ∨ s = .M)) ∨
  (p = 7 ∧ (s = .Fi24Prime ∨ s = .M)) ∨ (p = 13 ∧ s = .M)

@[expose] def KFactP1ThreeAlt : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (Y : Type) [Group Y] [Finite Y] (Rb : Sylow p Y) (Y₀ : Subgroup Y),
    ReducedNongeneration p Y Rb Y₀ → CatalogSimpleSections Y →
    ∀ K : Subgroup Y, IsComponentOf K ⊤ → (∀ L : Subgroup Y, IsComponentOf L ⊤ → L = K) →
      ¬ IsCyclic ((Rb : Subgroup Y) ⊓ K : Subgroup Y) →
      (∀ c ∈ (Rb : Subgroup Y) ⊓ Subgroup.centralizer (K : Set Y), orderOf c = p →
        c ∈ (Subgroup.center K).map K.subtype) →
      ∀ m : ℕ, 5 ≤ m → Nonempty (K ⧸ Subgroup.center K ≃* alternatingGroup (Fin m)) → m = 3 * p

@[expose] def KFactP1ThreeSpor : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (Y : Type) [Group Y] [Finite Y] (Rb : Sylow p Y) (Y₀ : Subgroup Y),
    ReducedNongeneration p Y Rb Y₀ → CatalogSimpleSections Y →
    ∀ K : Subgroup Y, IsComponentOf K ⊤ → (∀ L : Subgroup Y, IsComponentOf L ⊤ → L = K) →
      ¬ IsCyclic ((Rb : Subgroup Y) ⊓ K : Subgroup Y) →
      (∀ c ∈ (Rb : Subgroup Y) ⊓ Subgroup.centralizer (K : Set Y), orderOf c = p →
        c ∈ (Subgroup.center K).map K.subtype) →
      ∀ s : TauCeti.SporadicName,
        Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.sporadic s).Group) →
        P1ThreeSporList p s

@[expose] def JStarElimData (L : Type) [Group L] [Finite L] (p n : ℕ) [Fact p.Prime] : Prop :=
  ∃ A J : Subgroup (MulAut L), (MulAut.conj : L →* MulAut L).range ≤ A ∧ J ≤ A ∧
    (∀ S : Subgroup (MulAut L), S ≤ A → IsPGroup p S → Nat.card S ∣ p ^ n * n) ∧
    ∃ φ : J →* PSL2GF p n, Function.Surjective φ ∧ p.Coprime (Nat.card φ.ker)

@[expose] def KFactJStarElimLie : Prop :=
  ∀ (p n : ℕ) [Fact p.Prime], p ≠ 2 → 3 ≤ n → ∀ (L : Type) [Group L] [Finite L],
    IsSimpleGroup L → ∀ d : TauCeti.ValidLieTypeIndex, P1ThreeLieList p d →
      (¬ ∃ m, IsLinTwoIndex p m d) → Nonempty (L ≃* (TauCeti.CFSGIndex.lie d).Group) →
      ¬ JStarElimData L p n

@[expose] def KFactJStarElimAlt : Prop :=
  ∀ (p n : ℕ) [Fact p.Prime], p ≠ 2 → 3 ≤ n → ∀ (L : Type) [Group L] [Finite L],
    Nonempty (L ≃* alternatingGroup (Fin (3 * p))) → ¬ JStarElimData L p n

@[expose] def KFactJStarElimSpor : Prop :=
  ∀ (p n : ℕ) [Fact p.Prime], p ≠ 2 → 3 ≤ n → ∀ (L : Type) [Group L] [Finite L],
    ∀ s : TauCeti.SporadicName, P1ThreeSporList p s →
      Nonempty (L ≃* (TauCeti.CFSGIndex.sporadic s).Group) → ¬ JStarElimData L p n

end CFSG.AGLEmbedding
