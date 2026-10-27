module

public import CFSG.Open.GLADefs
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Config

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open Subgroup
open CFSG.RankThreeCoreUniqueness.Helpers (primeComplementCore)
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3 (u3S u3T u3ZT u3U0 U3LineWC)

variable {G : Type} [Group G] [Finite G]

@[expose] def conjLines (x : G) (P : Subgroup G) : Set (Subgroup G) :=
  {A | ∃ g : G, A = (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom ∧ A ≤ P}

@[expose] def IsFiveCycleLine {Q : Type} [Group Q] (J T : Subgroup G) (ψ : ↥J →* Q) (A : Subgroup G) : Prop :=
  A ≤ T ∧ Nat.card A = 5 ∧ ∃ (a : G) (ha : a ∈ J), a ∈ A ∧ ψ ⟨a, ha⟩ ≠ 1 ∧
    Nat.card (Subgroup.centralizer ({ψ ⟨a, ha⟩} : Set Q)) = 300

@[expose] def A10PlaneShape {Q : Type} [Group Q] (J T : Subgroup G) (ψ : ↥J →* Q) (U : Subgroup G) : Prop :=
  ∃ (d : G) (hd : d ∈ J), d ∈ U ⊓ T ∧ ψ ⟨d, hd⟩ ≠ 1 ∧
    Nat.card (Subgroup.centralizer ({ψ ⟨d, hd⟩} : Set Q)) = 25

@[expose] def A10StageB {Q : Type} [Group Q] (P : Sylow 5 G) (x : G) (J : Subgroup G) (ψ : ↥J →* Q) : Prop :=
  (P : Subgroup G) ≤ Subgroup.centralizer ({x} : Set G) ∧
    (conjLines x (P : Subgroup G) = {Subgroup.zpowers x} ∨
      ∃ A₁ A₂ : Subgroup G, A₁ ≠ A₂ ∧ IsFiveCycleLine J (u3T P x J) ψ A₁ ∧
        IsFiveCycleLine J (u3T P x J) ψ A₂ ∧
        conjLines x (P : Subgroup G) = {Subgroup.zpowers x, A₁, A₂})

@[expose] def KFactI1434 : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) → IsCatalogGroup K →
    ∀ Q : Sylow 5 K, CFSG.Open.pRank 5 (Q : Subgroup K) = 3 → IsMulCommutative (Q : Subgroup K) →
    ∀ x ∈ (Q : Subgroup K), x ≠ 1 → x ^ 5 = 1 →
    ∀ J₁ J₂ : Subgroup K, J₁ ≠ J₂ → GLAPComponent 5 (Subgroup.centralizer ({x} : Set K)) J₁ →
      GLAPComponent 5 (Subgroup.centralizer ({x} : Set K)) J₂ →
      GLAPLayer 5 (Subgroup.centralizer ({x} : Set K)) = J₁ ⊔ J₂ →
      Nonempty (↥J₁ ⧸ primeComplementCore (G := ↥J₁) 5 ≃* alternatingGroup (Fin 5)) →
      Nonempty (↥J₂ ⧸ primeComplementCore (G := ↥J₂) 5 ≃* alternatingGroup (Fin 5)) →
      (Set.ncard {A : Subgroup K | ∃ g : K, A = (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom ∧
          A ≤ (Q : Subgroup K)} = 1 ∨
        Set.ncard {A : Subgroup K | ∃ g : K, A = (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom ∧
          A ≤ (Q : Subgroup K)} = 3) →
      Nonempty (K ≃* CFSG.Assembly.RankThreeEven.projSU 4 2 2)

@[expose] def KFactU44Data : Prop :=
  ∀ (K : Type) [Group K] [Finite K], Nonempty (K ≃* CFSG.Assembly.RankThreeEven.projSU 4 2 2) →
    ∀ Q : Sylow 5 K, ∀ x ∈ (Q : Subgroup K), x ≠ 1 → x ^ 5 = 1 →
    ∀ J₁ J₂ : Subgroup K, J₁ ≠ J₂ → GLAPComponent 5 (Subgroup.centralizer ({x} : Set K)) J₁ →
      GLAPComponent 5 (Subgroup.centralizer ({x} : Set K)) J₂ →
      GLAPLayer 5 (Subgroup.centralizer ({x} : Set K)) = J₁ ⊔ J₂ →
      Nonempty (↥J₁ ⧸ primeComplementCore (G := ↥J₁) 5 ≃* alternatingGroup (Fin 5)) →
      Nonempty (↥J₂ ⧸ primeComplementCore (G := ↥J₂) 5 ≃* alternatingGroup (Fin 5)) →
      Set.ncard {A : Subgroup K | ∃ g : K, A = (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom ∧
          A ≤ (Q : Subgroup K)} = 3 ∧
        ∀ J : Subgroup K, (J = J₁ ∨ J = J₂) → ∀ a ∈ (Q : Subgroup K) ⊓ J, a ≠ 1 →
          ∀ φ : MulAut K, φ x ∉ Subgroup.zpowers a

@[expose] def A10Scalars (K : Type) [Group K] [Finite K] : Prop :=
  ∀ S : Sylow 5 K, ∃ n ∈ normalizer ((S : Subgroup K) : Set K), ∀ s ∈ (S : Subgroup K), n * s * n⁻¹ = s * s

@[expose] def A10Gamma (K : Type) [Group K] (S : Subgroup K) : Subgroup K :=
  Subgroup.closure {g : K | ∃ B : Subgroup K, B ≤ S ∧ B ≠ ⊥ ∧ g ∈ normalizer (B : Set K)}

@[expose] def A10GammaMax (K : Type) [Group K] [Finite K] : Prop :=
  ∀ S : Sylow 5 K, ∀ H : Subgroup K, A10Gamma K (S : Subgroup K) ≤ H →
    H = A10Gamma K (S : Subgroup K) ∨ H = ⊤

structure A10Ext : Prop where
  scalars : ∀ (K : Type) [Group K] [Finite K], IsA10Type 5 K → A10Scalars K
  gammaMax : ∀ (K : Type) [Group K] [Finite K], IsA10Type 5 K → A10GammaMax K

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
