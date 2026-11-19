module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieUniqueJDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.PrimeComplementCore

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding Subgroup

@[expose] def fiveRes {G : Type} [Group G] (H : Subgroup G) : Subgroup G :=
  Subgroup.closure {g : G | g ∈ H ∧ ∃ k : ℕ, g ^ 5 ^ k = 1}

@[expose] def a10Pre {G Q : Type} [Group G] [Group Q] (J : Subgroup G) (ψ : ↥J →* Q) (Λ : Subgroup Q) :
    Subgroup G :=
  (Λ.comap ψ).map J.subtype

@[expose] def a10E {G Q : Type} [Group G] [Group Q] (J : Subgroup G) (ψ : ↥J →* Q) (Λ : Subgroup Q) :
    Subgroup G :=
  fiveRes (a10Pre J ψ Λ)

abbrev A10Y {G : Type} [Group G] (M : Subgroup G) : Type :=
  ↥M ⧸ primeComplementCore (G := ↥M) 5

abbrev a10π {G : Type} [Group G] (M : Subgroup G) : ↥M →* A10Y M :=
  QuotientGroup.mk' (primeComplementCore (G := ↥M) 5)

@[expose] def a10Img {G : Type} [Group G] (M H : Subgroup G) : Subgroup (A10Y M) :=
  (H.subgroupOf M).map (a10π M)

structure A10EBase {G : Type} [Group G] (W O E₁ E₂ : Subgroup G) : Prop where
  E₁_le : E₁ ≤ W
  E₂_le : E₂ ≤ W
  O_le : O ≤ W
  O_norm : ∀ w ∈ W, ∀ o ∈ O, w * o * w⁻¹ ∈ O
  O_cop : ¬ 5 ∣ Nat.card O
  E_norm : ∀ w ∈ W, ∀ e ∈ E₁ ⊔ E₂, w * e * w⁻¹ ∈ E₁ ⊔ E₂
  E₁_norm : ∀ e ∈ E₂, ∀ a ∈ E₁, e * a * e⁻¹ ∈ E₁
  E₂_norm : ∀ e ∈ E₁, ∀ a ∈ E₂, e * a * e⁻¹ ∈ E₂
  E₁_gen : Subgroup.closure {g : G | g ∈ E₁ ∧ ∃ k : ℕ, g ^ 5 ^ k = 1} = E₁
  E₂_gen : Subgroup.closure {g : G | g ∈ E₂ ∧ ∃ k : ℕ, g ^ 5 ^ k = 1} = E₂
  E₁_A5 : ∃ f : ↥E₁ →* alternatingGroup (Fin 5), Function.Surjective f ∧ f.ker = O.subgroupOf E₁
  E₂_A5 : ∃ f : ↥E₂ →* alternatingGroup (Fin 5), Function.Surjective f ∧ f.ker = O.subgroupOf E₂
  comm : ∀ a ∈ E₁, ∀ b ∈ E₂, a * b * a⁻¹ * b⁻¹ ∈ O

structure A10KData {G : Type} [Group G] (W N D : Subgroup G) : Prop where
  N_le : N ≤ W
  D_le : D ≤ W
  N_norm : ∀ w ∈ W, ∀ n ∈ N, w * n * w⁻¹ ∈ N
  N_cop : ¬ 5 ∣ Nat.card N
  D_cyc : IsCyclic ↥D

structure A10EData {G : Type} [Group G] (W O N D E₁ E₂ : Subgroup G) : Prop where
  base : A10EBase W O E₁ E₂
  kd : A10KData W N D
  five : ∀ w ∈ W, (∃ k : ℕ, w ^ 5 ^ k = 1) → w ∈ (E₁ ⊔ E₂) ⊔ (N ⊔ D)

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
