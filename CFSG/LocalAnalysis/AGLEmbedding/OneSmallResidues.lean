module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallDefs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def StmtSmallGuest : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)), D1OneSmallData p P M H R Rbar K →
    (IsAltTwoP p K ∧ 7 ≤ p ∧ (11 ≤ p ∨ 3 ∈ GLBBetaFour G)) ∨
      (p = 5 ∧ IsFi22 K ∧ 3 ∈ GLBBetaFour G) → False

@[expose] def StmtSmallPosA : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)), D1OneSmallData p P M H R Rbar K →
    D1UniqueOver H R (nclIn H (d1LiftX p H R K)) → D1SmallLa p M H Rbar K →
    ¬ (p = 5 ∧ IsFi22 K) → d1MapPCore p M H ⊓ K ≠ ⊥ →
    d1MapPCore p M H ⊓ Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) ≠ ⊥ →
    ¬ D1SmallPosZ p M H Rbar K → False

@[expose] def StmtSmallPoszSP : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)), D1OneSmallData p P M H R Rbar K →
    D1SmallLa p M H Rbar K → ¬ (p = 5 ∧ IsFi22 K) → d1MapPCore p M H ≠ ⊥ →
    d1MapPCore p M H ⊓ K = ⊥ → ∀ z : G, D1SmallCZElt p H R K z → D1CzSP p z

@[expose] def StmtSmallPoszOut : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)), D1OneSmallData p P M H R Rbar K →
    D1SmallLa p M H Rbar K → ¬ (p = 5 ∧ IsFi22 K) → d1MapPCore p M H ≠ ⊥ →
    d1MapPCore p M H ⊓ K = ⊥ → ∀ z : G, D1SmallCZElt p H R K z → D1CzOutside p z → False

@[expose] def StmtSmallPosT : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)), D1OneSmallData p P M H R Rbar K →
    D1UniqueOver H R (nclIn H (d1LiftX p H R K)) → ¬ (p = 5 ∧ IsFi22 K) →
    d1MapPCore p M H ⊓ K ≠ ⊥ →
    d1MapPCore p M H ⊓ Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) = ⊥ →
    D1SmallIa p H K → 5 ≤ p → (IsSmallLinTwo p K ∨ IsSmallUnitary p K) →
    ¬ D1SmallPosZ p M H Rbar K → False

@[expose] def StmtSmallSPIn : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)), D1OneSmallData p P M H R Rbar K →
    D1UniqueOver H R (nclIn H (d1LiftX p H R K)) → ∀ z : G, D1SmallCZElt p H R K z →
    D1SmallLa p M H Rbar K → 5 ≤ p → D1CzSP p z → ¬ D1CzOutside p z → False

@[expose] def StmtSmallSPOut : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)), D1OneSmallData p P M H R Rbar K →
    D1UniqueOver H R (nclIn H (d1LiftX p H R K)) → ∀ z : G, D1SmallCZElt p H R K z →
    D1SmallLa p M H Rbar K → D1CzSP p z → D1CzOutside p z → ¬ IsSPLFamily p K → False

@[expose] def StmtSmallSPInThree : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)), D1OneSmallData p P M H R Rbar K →
    D1UniqueOver H R (nclIn H (d1LiftX p H R K)) → ∀ z : G, D1SmallCZElt p H R K z →
    D1SmallLa p M H Rbar K → p = 3 → D1CzSP p z → ¬ D1CzOutside p z →
    ¬ (IsAltTwoP 3 K ∧ D1CzJ3 p z) → False

@[expose] def StmtSmallBOne : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)), D1OneSmallData p P M H R Rbar K →
    D1UniqueOver H R (nclIn H (d1LiftX p H R K)) → ∀ z : G, D1SmallCZElt p H R K z →
    ¬ D1CzSP p z → ¬ D1CzB0 p R z → D1CzIso p z K → D1SmallLa p M H Rbar K →
    (p = 3 → IsLinThreeFour K → ¬ D1CzOuterP p z) → False

@[expose] def StmtSmallBZeroOdd : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)), D1OneSmallData p P M H R Rbar K →
    D1UniqueOver H R (nclIn H (d1LiftX p H R K)) → ∀ z : G, D1SmallCZElt p H R K z →
    D1CzB0 p R z → ¬ D1CzEven p z → D1CzIso p z K →
    ¬ (p = 3 ∧ IsAltTwoP 3 K ∧ D1SmallExotic p H R K z) → ¬ (p = 3 ∧ IsSmallUnitary 3 K) →
    ¬ (p = 5 ∧ IsFi22 K) → D1SmallLa p M H Rbar K → False

@[expose] def StmtSmallGEV : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)), D1OneSmallData p P M H R Rbar K →
    D1UniqueOver H R (nclIn H (d1LiftX p H R K)) → ∀ z : G, D1SmallCZElt p H R K z →
    D1SmallIa p H K → D1CzB0 p R z → D1CzEven p z → D1CzIso p z K →
    ¬ (p = 3 ∧ IsAltTwoP 3 K) → ¬ (p = 3 ∧ IsSmallUnitary 3 K) →
    ¬ (p = 3 ∧ IsLinThreeFour K) → ¬ (p = 5 ∧ IsFi22 K) → False

@[expose] def D1SmallIbEV : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)), D1OneSmallData p P M H R Rbar K →
    D1UniqueOver H R (nclIn H (d1LiftX p H R K)) → ∀ z : G, D1SmallCZElt p H R K z →
    ¬ D1SmallIa p H K → D1CzB0 p R z → D1CzEven p z → D1CzIso p z K →
    ¬ (p = 3 ∧ IsAltTwoP 3 K) → ¬ (p = 3 ∧ IsSmallUnitary 3 K) →
    ¬ (p = 3 ∧ IsLinThreeFour K) → ¬ (p = 5 ∧ IsFi22 K) →
    ¬ (IsAltTwoP p K ∧ 7 ≤ p ∧ (11 ≤ p ∨ 3 ∈ GLBBetaFour G)) →
    D1SmallOpenPos p M H Rbar K → False

@[expose] def D1SmallSPL : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)), D1OneSmallData p P M H R Rbar K →
    D1UniqueOver H R (nclIn H (d1LiftX p H R K)) → ∀ z : G, D1SmallCZElt p H R K z →
    IsSPLFamily p K → D1CzSP p z → D1CzOutside p z → D1SmallOpenPosIf p M H Rbar K → False

@[expose] def D1SmallKC : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)), D1OneSmallData p P M H R Rbar K →
    D1UniqueOver H R (nclIn H (d1LiftX p H R K)) → ∀ z : G, D1SmallCZElt p H R K z →
    ¬ D1CzSP p z → ¬ D1CzIso p z K → D1SmallOpenPosIf p M H Rbar K → False

@[expose] def D1SmallA6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)), D1OneSmallData p P M H R Rbar K →
    D1UniqueOver H R (nclIn H (d1LiftX p H R K)) → ∀ z : G, D1SmallCZElt p H R K z →
    p = 3 → IsAltTwoP 3 K →
    (D1CzB0 p R z ∧ D1CzIso p z K ∧ (D1SmallExotic p H R K z ∨ D1CzEven p z) ∧
        D1SmallOpenPosIf p M H Rbar K) ∨ (D1CzSP p z ∧ D1CzJ3 p z) → False

@[expose] def D1SmallU33 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)), D1OneSmallData p P M H R Rbar K →
    D1UniqueOver H R (nclIn H (d1LiftX p H R K)) → ∀ z : G, D1SmallCZElt p H R K z →
    p = 3 → IsSmallUnitary 3 K → D1CzB0 p R z → D1CzIso p z K →
    D1SmallOpenPosIf p M H Rbar K → False

@[expose] def D1SmallL34 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)), D1OneSmallData p P M H R Rbar K →
    D1UniqueOver H R (nclIn H (d1LiftX p H R K)) → ∀ z : G, D1SmallCZElt p H R K z →
    p = 3 → IsLinThreeFour K →
    D1SmallOuterR p H Rbar K ∨ D1SmallU2Fails p M H K ∨
      (D1SmallOpenPos p M H Rbar K ∧ ¬ D1CzSP p z ∧ D1CzIso p z K ∧
        ((D1CzB0 p R z ∧ D1CzEven p z) ∨ (¬ D1CzB0 p R z ∧ D1CzOuterP p z))) → False

@[expose] def D1SmallFi22 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)), D1OneSmallData p P M H R Rbar K →
    D1UniqueOver H R (nclIn H (d1LiftX p H R K)) → ∀ z : G, D1SmallCZElt p H R K z →
    p = 5 → IsFi22 K → 3 ∉ GLBBetaFour G → D1CzB0 p R z → D1CzIso p z K → False

end CFSG.AGLEmbedding
