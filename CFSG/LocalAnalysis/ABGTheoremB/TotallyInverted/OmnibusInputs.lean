module

public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.OmnibusTools
public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.Statements

public section

namespace CFSG.ABGTheoremB.TotallyInverted

open CFSG.QuasiDihedralFusion CFSG.ABGLocalTools
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

namespace Omnibus

@[expose] def liftedSignalizers (σ : Setting G) (H : Subgroup G) (r : ℕ) : Set (Subgroup G) :=
  {X | oddCoreIn H ≤ X ∧ X ≤ H ∧ (∀ g ∈ X, ∃ k : ℕ, g ^ r ^ k ∈ oddCoreIn H) ∧
    σ.T ≤ Subgroup.normalizer (X : Set G) ∧ (X : Set G) * (σ.C : Set G) = (σ.C : Set G) * X}

end Omnibus

open Omnibus

@[expose] def ABG_II_4_11_Input {σ : Setting G} {r : ℕ} (Δ : Data σ r) : Prop :=
  ∀ (i : Fin 3) (Z : Subgroup G), Z ≤ σ.Ns i → Odd (Nat.card Z) →
    σ.C ≤ Subgroup.normalizer (Z : Set G) →
    ∃ P : Subgroup G, σ.C ≤ Subgroup.normalizer (P : Set G) ∧
      (Z : Set G) ⊆ (σ.C : Set G) * (P : Set G) ∧
      ∃ Y ∈ ({σ.Ps r i, R Δ i, Rs Δ i} : Set (Subgroup G)),
        ∀ g ∈ P, (∃ k : ℕ, g ^ r ^ k = 1) → g ∈ Y

@[expose] def ABG_II_3_1_Input (G : Type) [Group G] [Finite G] : Prop :=
  ∀ K : Subgroup G, IsQGroup K → ∀ S₁ : Subgroup G, IsSylowOf 2 S₁ K →
    K ≤ oddCoreIn K ⊔ (K ⊓ Subgroup.centralizer (centerOf S₁ : Set G))

@[expose] def ABG_II_5_7_Input (σ : Setting G) : Prop :=
  σ.height = 1 → ∀ K : Subgroup G, IsDGroup K → ∀ T₁ : Subgroup G, T₁ ≤ K → IsKleinFour T₁ →
    ∀ Y : Subgroup G, Y ≤ K → Odd (Nat.card Y) → T₁ ≤ Subgroup.normalizer (Y : Set G) →
      ∃ t ∈ T₁, t ≠ 1 ∧ ∀ y ∈ Y, y * t * y⁻¹ * t⁻¹ ∈ oddCoreIn K

@[expose] def ABG_V_8_7_Q_Input (σ : Setting G) (r : ℕ) : Prop :=
  ∀ H : Subgroup G, σ.C ≤ H → oddCoreIn H ≠ ⊥ → IsQGroup H →
    ∀ X ∈ maximals (liftedSignalizers σ H r), ∀ X' ∈ maximals (liftedSignalizers σ H r),
      ∃ m ∈ H ⊓ Subgroup.normalizer (σ.T : Set G), conjSub m X' = X

@[expose] def ABG_V_8_7_D_Input (σ : Setting G) (r : ℕ) : Prop :=
  σ.height = 1 → ∀ H : Subgroup G, σ.C ≤ H → oddCoreIn H ≠ ⊥ → IsDGroup H →
    ∀ X ∈ maximals (liftedSignalizers σ H r), ∀ X' ∈ maximals (liftedSignalizers σ H r),
      ∃ m ∈ H ⊓ Subgroup.normalizer (σ.T : Set G), conjSub m X' = X

structure OmnibusInputs {σ : Setting G} {r : ℕ} (Δ : Data σ r) : Prop where
  nStructure : ABG_II_4_11_Input Δ
  qCentralizer : ABG_II_3_1_Input G
  dCentralizer : ABG_II_5_7_Input σ
  qConjugacy : ABG_V_8_7_Q_Input σ r
  dConjugacy : ABG_V_8_7_D_Input σ r

end CFSG.ABGTheoremB.TotallyInverted
