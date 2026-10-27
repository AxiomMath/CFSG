
module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239ListedBasic
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesExtraComponents

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239

open CFSG.Open CFSG.Quasithin CFSG.Blueprint

@[expose] def IsBadLieChar2 (X : Type) [Group X] : Prop :=
  (∃ f : ℕ, (2 ≤ f ∧ ChevalleyExceptionalModel X .G2 2 f) ∨
    (1 ≤ f ∧ ChevalleyExceptionalModel X .trialityD4 2 f) ∨
    (Odd f ∧ 3 ≤ f ∧ ReeTitsModel X .twistedF4 2 f)) ∨
  ReeTitsModel X .Tits 2 1 ∨ StatedClassicalModel X .PSL 5 2 1 ∨ StatedClassicalModel X .PSU 3 3 1

@[expose] def IsBadSporadicName (s : TauCeti.SporadicName) : Prop :=
  s = .M12 ∨ s = .M24 ∨ s = .J2 ∨ s = .J4 ∨ s = .HS ∨ s = .He ∨ s = .Ru

@[expose] def IsBadSporadicQuot {G : Type} [Group G] (L : Subgroup G) : Prop :=
  ∃ s : TauCeti.SporadicName, IsBadSporadicName s ∧
    Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ≃* NativeSporadic.Carrier s)

@[expose] def IsG24Quot {G : Type} [Group G] (L : Subgroup G) : Prop :=
  ChevalleyExceptionalModel (↥L ⧸ CFSG.pCore 2 ↥L) .G2 2 2

@[expose] def IsM22M23Quot {G : Type} [Group G] (L : Subgroup G) : Prop :=
  Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ≃* NativeSporadic.Carrier .M22) ∨
    Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ≃* NativeSporadic.Carrier .M23)

@[expose] def IsNormalListedType {G : Type} [Group G] (L : Subgroup G) : Prop :=
  IsBadLieChar2 ↥L ∨ IsG24Quot L ∨ IsBadSporadicQuot L ∨ IsM22M23Quot L ∨
    StatedClassicalModel ↥L .PSL 4 2 1 ∨ CentralQuotientAlt L 7 ∨ StatedClassicalModel ↥L .PSL 3 3 1

@[expose] def IsParabolicPairType {G : Type} [Group G] (L R : Subgroup G) : Prop :=
  IsBadLieChar2 ↥L ∨ IsG24Quot L ∨ IsBadSporadicQuot L ∨
    (StatedClassicalModel ↥L .PSL 4 2 1 ∧ ¬ ∃ s ∈ R, InducesOuter s L)

@[expose] def L239NotRankOne : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), CFSG.IsQuasisimple ↥L →
    IsNormalListedType L → ¬ A38Types (↥L ⧸ CFSG.pCore 2 ↥L)

@[expose] def L239ParabolicPairs : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L R : Subgroup G), CFSG.IsQuasisimple ↥L →
    IsParabolicPairType L R → IsPGroup 2 R → R ≤ Subgroup.normalizer (L : Set G) →
    IsSylowTwoOf (R ⊓ L) L →
    ∃ K₁ K₂ : Subgroup G, K₁ ≤ L ∧ K₂ ≤ L ∧ K₁ ≠ L ∧ K₂ ≠ L ∧ K₁ ⊔ K₂ = L ∧
      R ≤ Subgroup.normalizer (K₁ : Set G) ∧ R ≤ Subgroup.normalizer (K₂ : Set G) ∧
      CharTwo K₁ ∧ CharTwo K₂ ∧ ¬ HasChi0Block K₁ ∧ ¬ HasChi0Block K₂

@[expose] def L239L42Overgroups : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L R : Subgroup G) (t : G),
    StatedClassicalModel ↥L .PSL 4 2 1 → IsPGroup 2 R → R ≤ Subgroup.normalizer (L : Set G) →
    IsSylowTwoOf (R ⊓ L) L → (∃ s ∈ R, InducesOuter s L) → t ∈ L → t ≠ 1 →
    t ∈ Subgroup.centralizer ((R ⊓ L : Subgroup G) : Set G) →
    ∀ X : Subgroup G, X ≤ L → R ≤ Subgroup.normalizer (X : Set G) →
      L ⊓ Subgroup.centralizer ({t} : Set G) ≤ X → X ≠ L →
        X = L ⊓ Subgroup.centralizer ({t} : Set G)

@[expose] def L239A7Overgroups : Prop :=
  ∀ σ : Equiv.Perm (Fin 7), σ.cycleType = {2, 2, 2} →
    ∀ Y : Subgroup (alternatingGroup (Fin 7)),
      (Subgroup.centralizer ({σ} : Set (Equiv.Perm (Fin 7)))).comap
        (alternatingGroup (Fin 7)).subtype ≤ Y → Y ≠ ⊤ → CharTwo Y →
      Y = (Subgroup.centralizer ({σ} : Set (Equiv.Perm (Fin 7)))).comap
        (alternatingGroup (Fin 7)).subtype

@[expose] def L239L33Overgroups : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (t : G),
    StatedClassicalModel ↥L .PSL 3 3 1 → t ∈ L → t ^ 2 = 1 → t ≠ 1 →
    ∀ Y : Subgroup G, Y ≤ L → L ⊓ Subgroup.centralizer ({t} : Set G) ≤ Y → Y ≠ L → CharTwo Y →
      Y = L ⊓ Subgroup.centralizer ({t} : Set G)

@[expose] def L239M11Overgroups : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (t : G),
    Nonempty (↥L ≃* NativeSporadic.Carrier .M11) → t ∈ L → t ^ 2 = 1 → t ≠ 1 →
    ∀ Y : Subgroup G, Y ≤ L → L ⊓ Subgroup.centralizer ({t} : Set G) ≤ Y → Y ≠ L →
      Y = L ⊓ Subgroup.centralizer ({t} : Set G)

@[expose] def L239M22Parabolic : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L R : Subgroup G),
    Nonempty (↥L ≃* NativeSporadic.Carrier .M22) → IsPGroup 2 R →
    R ≤ Subgroup.normalizer (L : Set G) → IsSylowTwoOf (R ⊓ L) L →
    ∃ K : Subgroup G, K ≤ L ∧ R ≤ Subgroup.normalizer (K : Set G) ∧ CharTwo K ∧
      ¬ HasChi0Block K ∧ IsAltOverElemAbelian K 4 6 ∧ ∀ Y : Subgroup G, K ≤ Y → Y ≤ L → Y = K ∨ Y = L

@[expose] def L239M23Parabolic : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L R : Subgroup G),
    Nonempty (↥L ≃* NativeSporadic.Carrier .M23) → IsPGroup 2 R →
    R ≤ Subgroup.normalizer (L : Set G) → IsSylowTwoOf (R ⊓ L) L →
    ∃ K : Subgroup G, K ≤ L ∧ R ≤ Subgroup.normalizer (K : Set G) ∧ CharTwo K ∧
      ¬ HasChi0Block K ∧ IsAltOverElemAbelian K 4 7 ∧ ∀ Y : Subgroup G, K ≤ Y → Y ≤ L → Y = K ∨ Y = L

@[expose] def L239Sylow2PSL2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L P : Subgroup G) (p : ℕ), Ch1.IsFermatOrMersennePrime p →
    7 < p → StatedClassicalModel ↥L .PSL 2 p 1 → IsSylowTwoOf P L →
    ∀ Y : Subgroup G, P ≤ Y → Y ≤ L → Y = P ∨ Y = L

@[expose] def L239Covers : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), CFSG.IsQuasisimple ↥L →
    (Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ≃* NativeSporadic.Carrier .M11) ∨
      Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ≃* NativeSporadic.Carrier .M23)) →
    Subgroup.center ↥L = ⊥

@[expose] def L239M22NoCover : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), UniqueSetting G T M →
    ∀ (H S T' : Subgroup G) (z : G), IsGamma0 M H → IsSylowTwoOf S (H ⊓ M) →
      IsSylowTwoOf T' M → S ≤ T' → z ∈ T' ⊓ Subgroup.centralizer (T' : Set G) → z ≠ 1 →
      z ^ 2 = 1 → ∀ L : Subgroup G, IsComponentIn L H →
        Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ≃* NativeSporadic.Carrier .M22) →
          Subgroup.center ↥L = ⊥

end CFSG.QuasithinUnique.Vol2Native.L239
