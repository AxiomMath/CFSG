module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.EmptyFaithful.S152Stmts

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique
open scoped Pointwise

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

@[expose] def StageTheorem15115_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T Mc M : Subgroup G), quasithinQTFE14Cat G T Mc →
    IsMf T Mc M → IsCE1513 T M →
    ¬ (Case1517Four T M (V154 T Mc M) (mBar0 T Mc M) ∨
      (∃ p : ℕ, (p = 3 ∨ p = 5) ∧ Case1517Six T M (V154 T Mc M) (mBar0 T Mc M) p) ∨
      Case1517Seven T M (V154 T Mc M) (mBar0 T Mc M))

@[expose] def StageLemma15201_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T Mc M : Subgroup G), Setting152 T Mc M →
    Lemma15201Concl T Mc M

@[expose] def StageLemma15203_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T Mc M : Subgroup G), Setting152 T Mc M →
    Lemma15203Concl T Mc M

@[expose] def StageLemma15204_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T Mc M : Subgroup G), Setting152 T Mc M →
    ∀ H : Subgroup G, IsHStar T M H →
      ¬ Nonempty (OTwoQuot H ≃* Equiv.Perm (Fin 5) ≀ᵣ Multiplicative (ZMod 2))

@[expose] def StageLemma15205_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T Mc M : Subgroup G), Setting152 T Mc M →
    ∀ M₁ : Subgroup G, InM T M₁ ↔ (M₁ = M ∨ M₁ = Mc)

@[expose] def StageLemma15206_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T Mc M : Subgroup G), Setting152 T Mc M →
    ∃ Y₁ : Subgroup G, IsY1 T Mc M Y₁

@[expose] def StageLemma15207_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T Mc M : Subgroup G), Setting152 T Mc M →
    ∀ Y₁ : Subgroup G, IsY1 T Mc M Y₁ → Lemma15207Concl T Mc M Y₁

@[expose] def StageLemma15208_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T Mc M : Subgroup G), Setting152 T Mc M →
    ∀ H : Subgroup G, IsHStar T M H →
      Nonempty (OTwoQuot H ≃* Equiv.Perm (Fin 3) ≀ᵣ Multiplicative (ZMod 2))

@[expose] def StageNotation15209_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T Mc M : Subgroup G), Setting152 T Mc M →
    ∀ H : Subgroup G, IsHStar T M H → Notation15209Concl T Mc M H

@[expose] def StageLemma15210_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T Mc M : Subgroup G), Setting152 T Mc M →
    ∀ D : Subgroup (MulAut (V154 T Mc M)), D ∈ QsetOn T (V154 T Mc M) →
      D ≤ mBar0 T Mc M ∧ Nat.card D = 2 ∧
      Nat.card (⁅V154 T Mc M, preOn T (V154 T Mc M) D⁆ : Subgroup G) = 4 ∧
      T ≤ Subgroup.normalizer ((⁅V154 T Mc M, preOn T (V154 T Mc M) D⁆ : Subgroup G) : Set G)

@[expose] def StageLemma15211_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T Mc M : Subgroup G), Setting152 T Mc M →
    ∀ H : Subgroup G, IsHStar T M H → ∀ B ∈ sigmaPrime T H (V154 T Mc M),
      Lemma15211Concl T Mc M H B

@[expose] def StageLemma15213_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T Mc M : Subgroup G), Setting152 T Mc M →
    ∀ H : Subgroup G, IsHStar T M H → Lemma15213Concl T Mc M H

@[expose] def StageLemma15214_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T Mc M : Subgroup G), Setting152 T Mc M →
    ∀ B₀ : Subgroup (MulAut (V154 T Mc M)), IsB0 T Mc M B₀ → Lemma15214Concl T Mc M B₀

@[expose] def StageTheorem15215_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T Mc M : Subgroup G), Setting152 T Mc M →
    ∀ B₀ : Subgroup (MulAut (V154 T Mc M)), IsB0 T Mc M B₀ →
      IsUniqueM (Mc ⊓ Subgroup.centralizer (zSOf T Mc M B₀ : Set G)) Mc

@[expose] def StageLemma15216_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T Mc M : Subgroup G), Setting152 T Mc M →
    ∀ H : Subgroup G, IsHStar T M H → ∀ B₀ : Subgroup (MulAut (V154 T Mc M)), IsB0 T Mc M B₀ →
      ∀ I : Subgroup G, Hyp15215 T Mc M B₀ I → Lemma15216Concl T Mc M H B₀ I

@[expose] def StageLemma15217_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T Mc M : Subgroup G), Setting152 T Mc M →
    ∀ B₀ : Subgroup (MulAut (V154 T Mc M)), IsB0 T Mc M B₀ →
      ∀ I : Subgroup G, Hyp15215 T Mc M B₀ I →
        (Nonempty (↥(autOn M (V154 T Mc M)) ≃* ↥(CFSG.Open.Sz 0)) ∨
          IsOmegaFourPlusOn M (V154 T Mc M)) ∧
        Nat.card (quasithinOmegaOneCenter T) = 2 ∧ (sOf152 T Mc M B₀).relIndex T = 2

@[expose] def StageLemma15218_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T Mc M : Subgroup G), Setting152 T Mc M →
    ∀ H : Subgroup G, IsHStar T M H → ∀ B₀ : Subgroup (MulAut (V154 T Mc M)), IsB0 T Mc M B₀ →
      ∀ I : Subgroup G, Hyp15215 T Mc M B₀ I → Lemma15218Concl T Mc M H B₀ I

@[expose] def StageLemma15220_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T Mc M : Subgroup G), Setting152 T Mc M →
    ∀ H : Subgroup G, IsHStar T M H → ∀ B₀ : Subgroup (MulAut (V154 T Mc M)), IsB0 T Mc M B₀ →
      ∀ I : Subgroup G, Hyp15215 T Mc M B₀ I → Lemma15220Concl T Mc M B₀ I

@[expose] def StageLemma15223_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T Mc M : Subgroup G), Setting152 T Mc M →
    ∀ H : Subgroup G, IsHStar T M H → ∀ B₀ : Subgroup (MulAut (V154 T Mc M)), IsB0 T Mc M B₀ →
      ∀ I : Subgroup G, Hyp15215.Min T Mc M B₀ I → ¬ CharTwo I

@[expose] def StageLemma15224_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T Mc M : Subgroup G), Setting152 T Mc M →
    ∀ H : Subgroup G, IsHStar T M H → ∀ B₀ : Subgroup (MulAut (V154 T Mc M)), IsB0 T Mc M B₀ →
      ∀ I : Subgroup G, Hyp15215.Min T Mc M B₀ I → ∀ L : Subgroup G, IsComponentIn L I →
        ¬ L ≤ Mc → ¬ Lemma115LieCharTwo (↥L ⧸ Subgroup.center ↥L)

@[expose] def StageLemma15225_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T Mc M : Subgroup G), Setting152 T Mc M →
    Lemma15225Concl T Mc M

@[expose] def StageLemma15226_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T Mc M : Subgroup G), Setting152 T Mc M →
    Lemma15226Concl T Mc M ∧ ∀ H : Subgroup G, IsHStar T M H →
      E3.wClos (V154 T Mc M) 0 (pCoreOf 2 H) ≤
        H ⊓ Subgroup.centralizer (conjClosure (V154 T Mc M) H : Set G)

@[expose] def StageLemma15228_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T Mc M : Subgroup G), Setting152 T Mc M →
    ∀ H : Subgroup G, IsHStar T M H → ∀ B₀ : Subgroup (MulAut (V154 T Mc M)), IsB0 T Mc M B₀ →
      ⁅conjClosure (V154 T Mc M) H, lambdaOf (pCoreOf 2 H)⁆ ≤ zSOf T Mc M B₀

end CFSG.Quasithin
