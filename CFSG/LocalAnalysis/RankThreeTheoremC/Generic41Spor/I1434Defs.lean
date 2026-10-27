module

public import CFSG.Blueprint.Catalog
public import CFSG.Open.GLADefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.PrimeComplementCore

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedLieTag StatedLieAdmissible)
open CFSG.Blueprint (LieModel)
open CFSG.RankThreeCoreUniqueness.Helpers (primeComplementCore)

namespace I1434

structure FiveLayerData {K : Type} [Group K] (C J₁ J₂ : Subgroup K) : Prop where
  ne : J₁ ≠ J₂
  comp₁ : CFSG.Open.GLAPComponent 5 C J₁
  comp₂ : CFSG.Open.GLAPComponent 5 C J₂
  layer : CFSG.Open.GLAPLayer 5 C = J₁ ⊔ J₂
  quot₁ : Nonempty (↥J₁ ⧸ primeComplementCore (G := ↥J₁) 5 ≃* alternatingGroup (Fin 5))
  quot₂ : Nonempty (↥J₂ ⧸ primeComplementCore (G := ↥J₂) 5 ≃* alternatingGroup (Fin 5))

structure Data (K : Type) [Group K] [Finite K] (Q : Sylow 5 K) (x : K) (J₁ J₂ : Subgroup K) :
    Prop where
  rank : CFSG.Open.pRank 5 (Q : Subgroup K) = 3
  abelian : IsMulCommutative (Q : Subgroup K)
  mem : x ∈ (Q : Subgroup K)
  ne_one : x ≠ 1
  pow_five : x ^ 5 = 1
  five : FiveLayerData (Subgroup.centralizer ({x} : Set K)) J₁ J₂

end I1434

@[expose] def I1434AltCase : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (n : ℕ), 5 ≤ n → Nonempty (K ≃* alternatingGroup (Fin n)) →
    ∀ (Q : Sylow 5 K) (x : K) (J₁ J₂ : Subgroup K), I1434.Data K Q x J₁ J₂ → False

@[expose] def I1434SporCase : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Blueprint.NativeSporadic.SporadicRep K →
    ∀ (Q : Sylow 5 K) (x : K) (J₁ J₂ : Subgroup K), I1434.Data K Q x J₁ J₂ → False

@[expose] def I1434DefCase : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (t : StatedLieTag) (n f : ℕ), StatedLieAdmissible t n 5 f →
    LieModel K t n 5 f →
    ∀ (Q : Sylow 5 K) (x : K) (J₁ J₂ : Subgroup K), I1434.Data K Q x J₁ J₂ → False

@[expose] def I1434ExcCase : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (t : StatedLieTag) (ℓ f : ℕ),
    (t = .G2 ∨ t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .twistedE6 ∨ t = .trialityD4 ∨
      t = .twistedB2 ∨ t = .twistedG2 ∨ t = .twistedF4 ∨ t = .Tits) →
    LieModel K t 0 ℓ f → ℓ ≠ 5 →
    ∀ Q : Sylow 5 K, IsMulCommutative (Q : Subgroup K) → CFSG.Open.pRank 5 (Q : Subgroup K) ≠ 3

@[expose] def I1434ClassicalCase : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (t : StatedLieTag) (n ℓ f : ℕ),
    StatedClassicalModel K t n ℓ f → ℓ ≠ 5 → IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    ∀ (Q : Sylow 5 K) (x : K) (J₁ J₂ : Subgroup K), I1434.Data K Q x J₁ J₂ →
      (Set.ncard {A : Subgroup K | ∃ g : K, A = (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom ∧
          A ≤ (Q : Subgroup K)} = 1 ∨
        Set.ncard {A : Subgroup K | ∃ g : K, A = (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom ∧
          A ≤ (Q : Subgroup K)} = 3) →
      Nonempty (K ≃* CFSG.Assembly.RankThreeEven.projSU 4 2 2)

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
