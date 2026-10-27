module

public import CFSG.GH74.GLS.C3.Layer1.Th2Defs

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG.ABGLocalTools

@[expose] def B_thm2_v2ss : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G →
    (∃ (x y : G) (K : Subgroup G), IsV2Triple x y K) →
      ∃ (x y : G) (K : Subgroup G), IsV2StarStar x y K

@[expose] def B_thm2_p73 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ∀ (x y : G) (K T S : Subgroup G),
    Th2Std x y K T S →
      ∃ ρ : Th2Row, ρ.holds x y K T S ∧ (ρ.BT x K T S).Nonempty ∧
        ∀ B ∈ ρ.BT x K T S, IsE ρ.level.minRank T B ∧ ρ.level.IsBal B

@[expose] def B_thm2_p72c : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ∀ (x y : G) (K T S : Subgroup G),
    Th2Std x y K T S → ¬ IsTerminalPair 2 x K → ∀ ρ : Th2Row, ρ.holds x y K T S →
      (∀ B ∈ ρ.BT x K T S, ρ.level.IsBal B) →
        ∃ B ∈ ρ.BT x K T S, ρ.level.theta B ≠ ⊥ ∧ pRank 2 ↥(B ⊓ (T ⊓ K)) = pRank 2 ↥(T ⊓ K)

@[expose] def B_thm2_caseI : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ∀ (x y : G) (K T S : Subgroup G),
    Th2Std x y K T S → IsTerminalPair 2 x K →
      IsStandardSubgroup K ∧ IsSylowOf 2 (T ⊓ CxK x K) (centralizer (K : Set G))

@[expose] def B_thm2_caseI_M : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ∀ (x y : G) (K T S M : Subgroup G),
    Th2M1 x y K T S M → M = normalizer (K : Set G)

@[expose] def B_thm2_l82 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ∀ (x y : G) (K T S M : Subgroup G) (ρ : Th2Row)
    (B : Subgroup G), Th2M2 x y K T S M ρ B →
      (ρ ≠ .r4b → ρ ≠ .r4c → gammaK 2 (ρ.Tstar x K T S) ρ.level.r ≤ M) ∧
      gammaK 2 (ρ.Tstar x K T S) ρ.level.n ≤ M ∧
      (∀ A : Subgroup G, IsE ρ.level.n (ρ.Tstar x K T S) A → gammaK 2 A ρ.level.r ≤ M) ∧
      gammaK 2 B ρ.level.r ≤ M

@[expose] def B_thm2_l83 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ∀ (x y : G) (K T S M : Subgroup G) (ρ : Th2Row)
    (B : Subgroup G), Th2M2 x y K T S M ρ B → K ≤ M

@[expose] def B_thm2_l84 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ∀ (x y : G) (K T S M : Subgroup G),
    Th2Choice x y K T S M → K ≤ M →
      IsSylowOf 2 (T ⊓ CxK x K) (CMbar M K) ∧ (¬ IsTerminalPair 2 x K → T ≤ M)

@[expose] def B_thm2_p85 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ∀ (x y : G) (K T S M : Subgroup G),
    Th2Choice x y K T S M → K ≤ M → IsSylowOf 2 (T ⊓ CxK x K) (CMbar M K) →
      ∀ L : Subgroup G, IsMinSubnormalIn K M L →
        IsPCompIn 2 M L ∧ L = pPrimeCoreOf 2 L ⊔ K

@[expose] def B_thm2_p812 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ∀ (x y : G) (K T S M : Subgroup G),
    Th2Choice x y K T S M → K ≤ M → IsSylowOf 2 (T ⊓ CxK x K) (CMbar M K) →
      ∀ L : Subgroup G, IsMinSubnormalIn K M L → IsPCompIn 2 M L → L = pPrimeCoreOf 2 L ⊔ K →
        gammaK 2 (T ⊓ CxK x K) 1 ≤ M ∧ 2 ≤ pRank 2 ↥(T ⊓ CxK x K)

@[expose] def B_thm2_PU3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ∀ (x y : G) (K T S M : Subgroup G),
    Th2Choice x y K T S M → K ≤ M → IsSylowOf 2 (T ⊓ CxK x K) (CMbar M K) →
      ∀ L : Subgroup G, IsMinSubnormalIn K M L → IsPCompIn 2 M L → L = pPrimeCoreOf 2 L ⊔ K →
        gammaK 2 (T ⊓ CxK x K) 1 ≤ M → 2 ≤ pRank 2 ↥(T ⊓ CxK x K) →
          ∀ m ∈ M, ∀ l ∈ L, m * l * m⁻¹ ∈ L

@[expose] def B_thm2_cent5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ∀ (x y : G) (K T S : Subgroup G),
    Th2Std x y K T S → ∀ u ∈ T ⊓ CxK x K, (∀ t ∈ T, u * t = t * u) → orderOf u = 2 →
      IsSylowOf 2 T (centralizer ({u} : Set G))

@[expose] def B_thm2_tstar : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ∀ (x y : G) (K T S M : Subgroup G) (ρ : Th2Row)
    (B : Subgroup G), Th2M2 x y K T S M ρ B → Nat.card ↥(T ⊓ CxK x K) = 4 →
      (Nonempty (kBar K ≃* alternatingGroup (Fin 5)) ∨ Nonempty (kBar K ≃* alternatingGroup (Fin 7))) →
        T < S → ρ.level.n ≤ pRank 2 ↥(ρ.Tstar x K T S) ∧
          ∀ a ∈ S, a ∈ normalizer (T : Set G) → a ∈ normalizer (ρ.Tstar x K T S : Set G)

end CFSG.GH74.GLS
