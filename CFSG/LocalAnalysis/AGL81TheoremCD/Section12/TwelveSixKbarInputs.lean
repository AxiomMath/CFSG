module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixIData

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open Subgroup CFSG.LocalAnalysis.RankThreeUC.AGL81C

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {Q H : Subgroup G} {d : ℕ}
  {L₁ L₂ L₃ : Subgroup G} {n₁ n₂ n₃ : ℕ}

abbrev kbarQuot (p : ℕ) (M H : Subgroup G) : Type :=
  modTwoCore (kSub p M H) ⧸ center (modTwoCore (kSub p M H))

@[expose] def TwelveSixKbarHyp (G : Type) [Group G] [Finite G] (M : Subgroup G) (p : ℕ)
    (Q H : Subgroup G) (d : ℕ) (L₁ L₂ L₃ : Subgroup G) (n₁ n₂ n₃ : ℕ) : Prop :=
  TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃ ∧
    Nonempty (TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃) ∧
    CFSG.ABGLocalTools.IsSylowOf p Q H ∧ ¬ pLayerIn p H ≤ M ∧ xSub p M H ≤ M ∧
    H = kSub p M H ⊔ (H ⊓ M) ∧ ((kSub p M H).subgroupOf H).Normal

@[expose] def TwelveSixKbarSingle : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M : Subgroup G) (p : ℕ) (Q H : Subgroup G) (d : ℕ)
    (L₁ L₂ L₃ : Subgroup G) (n₁ n₂ n₃ : ℕ),
    TwelveSixKbarHyp G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃ →
      IsTwoPrimeComponentIn (kSub p M H) H

@[expose] def TwelveSixKbarList : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M : Subgroup G) (p : ℕ) (Q H : Subgroup G) (d : ℕ)
    (L₁ L₂ L₃ : Subgroup G) (n₁ n₂ n₃ : ℕ),
    TwelveSixKbarHyp G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃ →
      IsTwoPrimeComponentIn (kSub p M H) H →
        (p = 3 ∧ (CFSG.Blueprint.LieModel (kbarQuot p M H) .PSL 2 3 3 ∨
            CFSG.Blueprint.LieModel (kbarQuot p M H) .PSp 2 3 1 ∨
            CFSG.Blueprint.LieModel (kbarQuot p M H) .PSp 3 2 1 ∨
            Nonempty (kbarQuot p M H ≃* alternatingGroup (Fin 9)) ∨
            Nonempty (kbarQuot p M H ≃* alternatingGroup (Fin 10)) ∨
            Nonempty (kbarQuot p M H ≃* alternatingGroup (Fin 11)))) ∨
        (p = 5 ∧ Nonempty (kbarQuot p M H ≃* alternatingGroup (Fin 10)))

@[expose] def TwelveSixKbarExclusion : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M : Subgroup G) (p : ℕ) (Q H : Subgroup G) (d : ℕ)
    (L₁ L₂ L₃ : Subgroup G) (n₁ n₂ n₃ : ℕ),
    TwelveSixKbarHyp G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃ →
      IsTwoPrimeComponentIn (kSub p M H) H →
        ¬ (CFSG.Blueprint.LieModel (kbarQuot p M H) .PSp 3 2 1 ∨
          Nonempty (kbarQuot p M H ≃* alternatingGroup (Fin 10)) ∨
          Nonempty (kbarQuot p M H ≃* alternatingGroup (Fin 11)))

@[expose] def KFactL227AutE27 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Blueprint.LieModel Y .PSL 2 3 3 →
    ∀ E : Subgroup (MulAut Y), IsElemAbelian 3 E → Nat.card E = 27 →
      ∀ a v₁ v₂ : MulAut Y, a ∈ normalizer (E : Set (MulAut Y)) → v₁ ∈ E → v₂ ∈ E →
        v₁ ≠ 1 → v₂ ≠ 1 → a * v₁ * a⁻¹ = v₁⁻¹ → a * v₂ * a⁻¹ = v₂ → False

@[expose] def KFactKbarThompsonNormalizer : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y],
    (CFSG.Blueprint.LieModel Y .PSp 2 3 1 ∨
        Nonempty (Y ≃* alternatingGroup (Fin 9))) →
    ∀ P B V : Subgroup Y, CFSG.ABGLocalTools.IsSylowOf 3 P ⊤ → B ≠ ⊤ →
      normalizer (P : Set Y) ≤ B → V ≤ B → IsElemAbelian 3 V → Nat.card V = 27 →
      4 ∣ (B ⊓ centralizer (V : Set Y)).relIndex (B ⊓ normalizer (V : Set Y)) →
      B = normalizer (thompsonSubgroup P : Set Y)

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12

end
