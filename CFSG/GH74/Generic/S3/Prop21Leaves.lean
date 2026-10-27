module

public import CFSG.GH74.Generic.S3.Lem22

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.Blueprint CFSG.ABGLocalTools CFSG.Assembly.LowTwoRank Subgroup
open scoped MatrixGroups

structure Config22 (G : Type) [Group G] [Finite G] (t : StatedLieTag) (p f : ℕ) (v w : G)
    (Iv Iw Ivw P V : Subgroup G) (v₁ : G) : Prop where
  conf : Conf2A G t p f v w Iv Iw Ivw P
  setup : Count23Setup V w
  hv : v ∈ Vsharp V
  hv₁ : v₁ ∈ Vsharp V
  hne : v ≠ v₁
  hVIw : V ≤ Iw
  hVIvw : V ≤ Ivw
  conj : ∀ x ∈ Wset V w, ∃ n : G, NormV V n ∧ NormV V n⁻¹ ∧ n * w * n⁻¹ = x

@[expose] def B_S3_lemma22_v1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], GlobalHyp G →
    ∀ (t : StatedLieTag) (p f : ℕ) (v w : G) (Iv Iw Ivw P : Subgroup G),
      Conf2A G t p f v w Iv Iw Ivw P →
      ∃ v₁ : G, v₁ ∈ P ∧ v₁ ∈ Iw ∧ v₁ ∈ Ivw ∧ v₁ * v₁ = 1 ∧ v₁ ≠ 1 ∧ v₁ ≠ v

@[expose] def B_L3_fourgroup : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : StatedLieTag) (p f : ℕ), (t = .PSL ∨ t = .PSU) → p.Prime →
    p ≠ 2 → 5 ≤ p ^ f → ∀ L : Subgroup G, IsQuasisimple ↥L → Odd (Nat.card ↥(center ↥L)) →
      LieModel (↥L ⧸ center ↥L) t 3 p f →
      ∀ a b : G, a ∈ L → b ∈ L → a * a = 1 → b * b = 1 → a * b = b * a → a ≠ 1 → b ≠ 1 → a ≠ b →
        ∃ g ∈ L, g * a * g⁻¹ = a * b ∧ g * b * g⁻¹ = a

@[expose] def B_S3_layers : Prop :=
  ∀ (G : Type) [Group G] [Finite G], GlobalHyp G →
    ∀ (t : StatedLieTag) (p f : ℕ) (v w : G) (Iv Iw Ivw P V : Subgroup G) (v₁ : G),
      Config22 G t p f v w Iv Iw Ivw P V v₁ →
      ∀ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f →
        (∀ w₁ ∈ Wset V w, ∀ e ∈ Vsharp V, ∃! J : Subgroup G, IsSL2Comp F w₁ e J) ∧
        (∀ w₁ ∈ Wset V w, ∀ e ∈ Vsharp V, ∀ J : Subgroup G, IsSL2Comp F w₁ e J →
          ∀ e' ∈ Vsharp V, e' ≠ e → ∃ j ∈ J, j * e' ≠ e' * j) ∧
        (∀ w₁ ∈ Wset V w, ∀ e ∈ Vsharp V, ∀ J : Subgroup G, IsSL2Comp F w₁ e J → IsCompC J e)

@[expose] def B_S3_sl3pair_lin : Prop :=
  ∀ (G : Type) [Group G] [Finite G], GlobalHyp G →
    ∀ (p f : ℕ) (v w : G) (Iv Iw Ivw P V : Subgroup G) (v₁ : G),
      Config22 G .PSL p f v w Iv Iw Ivw P V v₁ →
      ∀ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f →
        ∀ J₀ J₁ J₂ : Subgroup G, IsSL2Comp F w v J₀ → IsSL2Comp F w v₁ J₁ →
          IsSL2Comp F (w * v₁) v J₂ →
          J₀ ⊔ J₁ = Iw ∧
          (∃ α : SL(3, F) →* G, α.ker ≤ Subgroup.center SL(3, F) ∧ α.range = J₀ ⊔ J₁) ∧
          (∃ α : SL(3, F) →* G, α.ker ≤ Subgroup.center SL(3, F) ∧ α.range = J₁ ⊔ J₂)

@[expose] def B_S3_sl3pair_uni : Prop :=
  ∀ (G : Type) [Group G] [Finite G], GlobalHyp G →
    ∀ (p f : ℕ) (v w : G) (Iv Iw Ivw P V : Subgroup G) (v₁ : G),
      Config22 G .PSU p f v w Iv Iw Ivw P V v₁ →
      ∀ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f →
        ∀ J₀ J₁ J₂ : Subgroup G, IsSL2Comp F w v J₀ → IsSL2Comp F w v₁ J₁ →
          IsSL2Comp F (w * v₁) v J₂ →
          J₀ ⊔ J₁ = Iw ∧
          ∃ (F₂ : Type) (_ : Field F₂) (_ : Finite F₂), Nat.card F₂ = (p ^ f) ^ 2 ∧
            (∃ α : ↥(StatedSU 3 (p ^ f) F₂) →* G,
              α.ker ≤ Subgroup.center ↥(StatedSU 3 (p ^ f) F₂) ∧ α.range = J₀ ⊔ J₁) ∧
            (∃ α : ↥(StatedSU 3 (p ^ f) F₂) →* G,
              α.ker ≤ Subgroup.center ↥(StatedSU 3 (p ^ f) F₂) ∧ α.range = J₁ ⊔ J₂)

@[expose] def B_S3_lemma24_25 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], GlobalHyp G →
    ∀ (t : StatedLieTag) (p f : ℕ) (v w : G) (Iv Iw Ivw P V : Subgroup G) (v₁ : G),
      Config22 G t p f v w Iv Iw Ivw P V v₁ →
      ∀ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f →
        ∀ J₀ J₁ J₂ : Subgroup G, IsSL2Comp F w v J₀ → IsSL2Comp F w v₁ J₁ →
          IsSL2Comp F (w * v₁) v J₂ → J₀ = Iv → J₀ ≠ J₂ → (∀ a ∈ J₀, ∀ b ∈ J₂, a * b = b * a) →
          Odd (Nat.card ↥(centralizer (Iw : Set G) ⊓ centralizer (Ivw : Set G))) →
          ∃ X₁ : Subgroup G, IsCompC X₁ v ∧ X₁ ≠ Iv ∧ (∀ J : Subgroup G, IsCompC J v → J = Iv ∨ J = X₁) ∧
            Nonempty (SL(2, F) ≃* X₁) ∧ (∀ x ∈ X₁, w * x * w⁻¹ ∈ X₁) ∧
            (((t = .PSL ∧ p ^ f % 4 = 3) ∨ (t = .PSU ∧ p ^ f % 4 = 1)) →
              ¬ ∃ x₀ ∈ X₁, ∀ y ∈ X₁, w * y * w⁻¹ = x₀ * y * x₀⁻¹)

@[expose] def B_SL2_outAbelian : Prop :=
  ∀ (F : Type) (_ : Field F) (_ : Finite F), Odd (Nat.card F) →
    ∀ (A : Type) (_ : Group A), Nonempty (SL(2, F) ≃* A) →
      commutator (MulAut A) ≤ (MulAut.conj : A →* MulAut A).range

@[expose] def B_S3_lemma26_transfer : Prop :=
  ∀ (G : Type) [Group G] [Finite G], GlobalHyp G →
    ∀ (t : StatedLieTag) (p f : ℕ) (v w : G) (Iv Iw Ivw P : Subgroup G),
      Conf2A G t p f v w Iv Iw Ivw P →
      ∃ hw : w ∈ centralizer ({v} : Set G),
        (⟨w, hw⟩ : ↥(centralizer ({v} : Set G))) ∈ commutator ↥(centralizer ({v} : Set G))

end CFSG.GH74.Generic.S3
