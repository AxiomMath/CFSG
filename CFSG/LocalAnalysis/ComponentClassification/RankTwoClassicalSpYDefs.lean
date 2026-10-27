module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalSp44Defs
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalStep76

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.RankTwoStandard
open CFSG.ComponentClassification.AschbacherTightEmbedding

@[expose] def SymplecticOddCentralizerO2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (D : ClassicalModel A),
    D.family = .symplectic → CFSG.Open.IsQuasisimple ↥A → Odd (Nat.card (center A)) →
      4 ≤ D.q → ∀ z ∈ A, Odd (orderOf z) → NoNormalTwo (A ⊓ centralizer ({z} : Set G))

section Stages

variable {G : Type} [Group G] {A : Subgroup G}

structure LeviOddElt (A W L : Subgroup G) (z : G) : Prop where
  mem : z ∈ W
  odd : Odd (orderOf z)
  ne_one : z ≠ 1
  layer : AS76b.layerCentralizer A (zpowers z) = L
  noInv : NoInvolutoryCentralizing A (zpowers z ⊔ L)

structure Levi75Y (D : ClassicalModel A) (T Y W L : Subgroup G) : Prop where
  Y_ne_bot : Y ≠ ⊥
  Y_le : Y ≤ A
  T_le : T ≤ centralizer (Y : Set G)
  L_le : L ≤ A ⊓ centralizer (Y : Set G)
  levi : D.LeviType L
  quasisimple : CFSG.Open.IsQuasisimple ↥L
  oddCenter : Odd (Nat.card (center ↥L))
  standard : standardComponentIsStandard (L.subgroupOf (centralizer (Y : Set G)))
  not_normal : ¬ (L.subgroupOf (centralizer (Y : Set G))).Normal
  L_eq : L = AS76b.layerCentralizer A Y
  diag : D.IsLinearFiveFour → ∃ y ∈ A ⊓ centralizer (Y : Set G), (∃ k : ℕ, y ^ 3 ^ k = 1) ∧
    ¬ ∃ l ∈ L, ∀ x ∈ L, y * x * y⁻¹ * (l * x * l⁻¹)⁻¹ ∈ (center ↥L).map L.subtype
  noInv : NoInvolutoryCentralizing A (Y ⊔ L)
  outerFree : D.IsLTwoFour → ∀ σ : MulAut ↥A, σ * σ = 1 → (∀ y : ↥A, (y : G) ∈ Y → σ y = y) →
    ∃ l ∈ L, ∀ z : ↥A, (z : G) ∈ L → ((σ z : ↥A) : G) = l * z * l⁻¹
  sym : D.IsLTwoFour → D.family ≠ .symplectic → ∃ (D' : Subgroup G) (s x : G), Y = D' ⊔ W ∧
    s ∈ A ∧ rightConjugate W s = L ∧ rightConjugate L s = W ∧ rightConjugate D' s = D' ∧
    x ∈ L ∧ orderOf x = 5 ∧ AS76b.layerCentralizer A (D' ⊔ zpowers x) = W ∧
    NoInvolutoryCentralizing A (D' ⊔ zpowers x ⊔ W)
  spFour : D.IsLTwoFour → D.family = .symplectic → ∃ y s y₃ : G, Y = zpowers y ∧
    Sp44 A W L y s y₃

theorem Levi75.toLevi75Y {D : ClassicalModel A} {T Y W L : Subgroup G} (hl : Levi75 D T Y W L)
    (hfam : D.family ≠ .symplectic) : Levi75Y D T Y W L :=
  ⟨hl.Y_ne_bot, hl.Y_le, hl.T_le, hl.L_le, hl.levi, hl.quasisimple, hl.oddCenter, hl.standard,
    hl.not_normal, hl.L_eq, hl.diag, hl.noInv, hl.outerFree, fun hD _ => hl.sym hD,
    fun _ h => absurd h hfam⟩

end Stages

@[expose] def SymplecticYChoice : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (D : ClassicalModel A),
    D.family = .symplectic → CFSG.Open.IsQuasisimple ↥A → Odd (Nat.card (center A)) →
      4 ≤ D.q → ∀ p : G, D.IsPrimary p → ∃ (W : Subgroup G) (y : G),
        LeviChoice D p W W ∧ LeviOddElt A W (AS76b.layerCentralizer A W) y ∧
        (D.IsLTwoFour → orderOf y = 5 ∧
          (∀ σ : MulAut ↥A, σ * σ = 1 → (∀ x : ↥A, (x : G) ∈ zpowers y → σ x = x) →
            ∃ l ∈ AS76b.layerCentralizer A W, ∀ z : ↥A, (z : G) ∈ AS76b.layerCentralizer A W →
              ((σ z : ↥A) : G) = l * z * l⁻¹) ∧
          NoThreeCentralizing A (zpowers y ⊔ AS76b.layerCentralizer A W) ∧
          ∃ y₃ : G, LeviOddElt A W (AS76b.layerCentralizer A W) y₃ ∧ orderOf y₃ = 3)

@[expose] def Step75Y : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (D : ClassicalModel A) (R T : Subgroup G)
    (g : G), AS76b.Hyp31 A → RankTwoClassicalEvenType (rankTwoQuot A) → Choice74 D R T g →
      ∃ Y W L : Subgroup G, Levi75Y D T Y W L

@[expose] def Step76Y : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (D : ClassicalModel A)
    (R T Y W L : Subgroup G) (g : G), RankTwoHyp G A → AS76b.Hyp31 A →
    RankTwoClassicalEvenType (rankTwoQuot A) → Choice74 D R T g → Levi75Y D T Y W L →
    (∀ (G' : Type) [Group G'] [Finite G'] (A' : Subgroup G'), Nat.card G' < Nat.card G →
      RankTwoHyp G' A' → standardComponentOddCore G' = ⊥ →
        ¬ RankTwoClassicalEvenType (rankTwoQuot A')) → False

end CFSG.ComponentClassification.RankTwoClassical
