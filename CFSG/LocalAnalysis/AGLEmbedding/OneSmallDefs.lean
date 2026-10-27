module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDefs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def IsSmallLinTwo (p : ℕ) (K : Type) [Group K] : Prop :=
  ∃ d : TauCeti.ValidLieTypeIndex, IsLinTwoIndex p 2 d ∧
    Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group)

@[expose] def IsSmallUnitary (p : ℕ) (K : Type) [Group K] : Prop :=
  ∃ d : TauCeti.ValidLieTypeIndex,
    (∃ q : TauCeti.PrimePower, q.p = p ∧ q.exponent = 1 ∧ d.1 = .twistedA 2 q) ∧
    Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group)

@[expose] def IsAltTwoP (p : ℕ) (K : Type) [Group K] : Prop :=
  Nonempty (K ≃* alternatingGroup (Fin (2 * p)))

@[expose] def IsLinThreeFour (K : Type) [Group K] : Prop :=
  ∃ d : TauCeti.ValidLieTypeIndex,
    (∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 2 ∧ d.1 = .A 2 q) ∧
    Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group)

@[expose] def IsFi22 (K : Type) [Group K] : Prop :=
  Nonempty (K ≃* (TauCeti.CFSGIndex.sporadic .Fi22).Group)

@[expose] def IsSPLFamily (p : ℕ) (K : Type) [Group K] : Prop :=
  IsSmallLinTwo p K ∨ IsSmallUnitary p K ∨ (p = 3 ∧ IsAltTwoP 3 K)

section Data

variable {G : Type} [Group G] [Finite G]

structure D1OneSmallData (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)) : Prop where
  cfg : D1ComponentConfig p P M H R Rbar
  comp : IsComponentOf K ⊤
  center : Subgroup.center K = ⊥
  noncyclic : ¬ IsCyclic ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
    Subgroup (H ⧸ primeComplementCore (G := H) p))
  z : ∃ z ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)), z ∉ K ∧ orderOf z = p ∧
    z ∈ Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p))
  small : Open.pRank p (⊤ : Subgroup (MulAut K)) ≤ 2

@[expose] def D1OneSmallClass (p : ℕ) (P : Sylow p G) (M R X H : Subgroup G) : Prop :=
  ∃ (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)),
    D1OneSmallData p P M H R Rbar K ∧ d1LiftX p H R K = X

end Data

@[expose] def D1OneSmallUnique : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)), D1OneSmallData p P M H R Rbar K →
    D1UniqueOver H R (nclIn H (d1LiftX p H R K)) → False

section Pos

variable {G : Type} [Group G] [Finite G]

@[expose] def D1SmallPosZ (p : ℕ) (M H : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)) : Prop :=
  d1MapPCore p M H ⊓ ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K) =
      centerOf ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K) ∧
    centerOf ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K) ≠
      (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K

@[expose] def D1SmallIa (p : ℕ) (H : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)) : Prop :=
  ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ → L = K

@[expose] def D1SmallOpenPos (p : ℕ) (M H : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)) : Prop :=
  (d1MapPCore p M H ⊓ K = ⊥ → d1MapPCore p M H = ⊥) ∧
  (d1MapPCore p M H ⊓ K ≠ ⊥ →
    d1MapPCore p M H ⊓ Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) ≠ ⊥ →
    D1SmallPosZ p M H Rbar K) ∧
  (d1MapPCore p M H ⊓ K ≠ ⊥ →
    d1MapPCore p M H ⊓ Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) = ⊥ →
    D1SmallIa p H K → 5 ≤ p → (IsSmallLinTwo p K ∨ IsSmallUnitary p K) →
    D1SmallPosZ p M H Rbar K)

@[expose] def D1SmallOpenPosIf (p : ℕ) (M H : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)) : Prop :=
  ¬ (p = 5 ∧ IsFi22 K) → D1SmallOpenPos p M H Rbar K

@[expose] def D1SmallCZElt (p : ℕ) (H R : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)) (z : G) : Prop :=
  z ∈ R ∧ orderOf z = p ∧ ∃ hzH : z ∈ H,
    QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨z, hzH⟩ ∈
      Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p))

abbrev D1CzQuot (p : ℕ) (z : G) : Type :=
  Subgroup.centralizer ({z} : Set G) ⧸
    primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p

@[expose] def d1CzElt (p : ℕ) (z : G) : D1CzQuot p z :=
  QuotientGroup.mk' _ ⟨z, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩

@[expose] def D1CzSP (p : ℕ) (z : G) : Prop :=
  4 ≤ Open.pRank p (Subgroup.centralizer ({z} : Set G))

@[expose] def D1CzB0 (p : ℕ) (R : Subgroup G) (z : G) : Prop :=
  ∃ Q : Sylow p (Subgroup.centralizer ({z} : Set G)),
    (Q : Subgroup (Subgroup.centralizer ({z} : Set G))).map
      (Subgroup.centralizer ({z} : Set G)).subtype = R

@[expose] def D1CzEven (p : ℕ) (z : G) : Prop :=
  2 ∣ Nat.card (GLBPrimeCore p (Subgroup.centralizer ({z} : Set G)))

@[expose] def D1CzIso (p : ℕ) (z : G) (K : Type) [Group K] : Prop :=
  ∀ KC : Subgroup (D1CzQuot p z), IsComponentOf KC ⊤ → Nonempty (KC ≃* K)

@[expose] def D1CzOutside (p : ℕ) (z : G) : Prop :=
  ∀ KC : Subgroup (D1CzQuot p z), IsComponentOf KC ⊤ → d1CzElt p z ∉ KC

@[expose] def D1CzJ3 (p : ℕ) (z : G) : Prop :=
  ∃ KC : Subgroup (D1CzQuot p z), IsComponentOf KC ⊤ ∧ d1CzElt p z ∈ KC ∧
    Nonempty (KC ⧸ Subgroup.center KC ≃* (TauCeti.CFSGIndex.sporadic .J3).Group)

@[expose] def D1CzOuterP (p : ℕ) (z : G) : Prop :=
  ∃ KC : Subgroup (D1CzQuot p z), IsComponentOf KC ⊤ ∧ ∃ x : D1CzQuot p z,
    (∃ k : ℕ, x ^ p ^ k = 1) ∧ x ∉ KC ⊔ Subgroup.centralizer (KC : Set (D1CzQuot p z))

@[expose] def D1SmallExotic (p : ℕ) (H R : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)) (z : G) : Prop :=
  ∃ g ∈ Subgroup.normalizer (R : Set G), g * z * g⁻¹ ∈ d1LiftX p H R K

@[expose] def D1SmallOuterR (p : ℕ) (H : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)) : Prop :=
  ¬ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ≤
    K ⊔ Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p))

@[expose] def D1SmallU2Fails (p : ℕ) (M H : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)) : Prop :=
  ∃ w ∈ Subgroup.normalizer (K : Set (H ⧸ primeComplementCore (G := H) p)),
    w ∈ Subgroup.centralizer ((d1X0 p M H ⊓ K : Subgroup _) :
      Set (H ⧸ primeComplementCore (G := H) p)) ∧
    w ∉ Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p))

@[expose] def D1SmallLa (p : ℕ) (M H : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)) : Prop :=
  p = 3 → IsLinThreeFour K → ¬ D1SmallOuterR p H Rbar K ∧ ¬ D1SmallU2Fails p M H K

end Pos

end CFSG.AGLEmbedding
