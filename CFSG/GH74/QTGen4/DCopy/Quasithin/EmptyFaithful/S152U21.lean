module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.EmptyFaithful.S152Stmts

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

@[expose] def Input15209Irr_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T Mc M : Subgroup G), Setting152 T Mc M →
    ∀ H : Subgroup G, IsHStar T M H →
      IsIrredOnSection T (oTwoUpper H) (pCoreOf 2 (oTwoUpper H))

@[expose] def Input15112J_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T Mc M : Subgroup G), Setting152 T Mc M →
    ∀ H : Subgroup G, IsHStar T M H → ∀ H₁ H₂ : Subgroup G, IsHPair H (V154 T Mc M) H₁ H₂ →
      IsSylowTwoOf (thompsonJ T ⊔ pCoreOf 2 H) (H₁ ⊔ H₂) ∧
        (thompsonJ T ⊔ pCoreOf 2 H).relIndex T = 2

@[expose] def Input1210Kc_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T Mc M : Subgroup G), Setting152 T Mc M →
    ∀ B₀ : Subgroup (MulAut (V154 T Mc M)), IsB0 T Mc M B₀ → ∀ H : Subgroup G, IsHStar T M H →
      conjClosure (oTwoUpper H) Mc ≠ oTwoUpper H →
        pCoreOf 2 (conjClosure (oTwoUpper H) Mc ⊔ T) ≤ sOf152 T Mc M B₀ →
          conjClosure (oTwoUpper H) Mc ≤ Subgroup.centralizer (zSOf T Mc M B₀ : Set G)

@[expose] def Input15221Three_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T Mc M : Subgroup G), Setting152 T Mc M →
    ∀ H : Subgroup G, IsHStar T M H → ∀ H₁ H₂ : Subgroup G, IsHPair H (V154 T Mc M) H₁ H₂ →
      ∀ B₀ : Subgroup (MulAut (V154 T Mc M)), IsB0 T Mc M B₀ →
        ∀ I : Subgroup G, Hyp15215 T Mc M B₀ I →
          IsLnTwo 4 (OTwoQuot (conjClosure (oTwoUpper H) Mc)) → Concl15218ii T Mc M H B₀ I →
          (∃ Y₁ : Subgroup G, Y₁ = oTwoUpper Y₁ ∧ Y₁ ≤ M ⊓ I ∧
              sOf152 T Mc M B₀ ≤ Subgroup.normalizer (Y₁ : Set G) ∧
              Nonempty (OTwoQuot (Y₁ ⊔ sOf152 T Mc M B₀) ≃* Equiv.Perm (Fin 3)) ∧
              ¬ Y₁ ≤ Mc ⊓ I) →
          IsIrredOnSection (sOf152 T Mc M B₀) (oTwoUpper H) (pCoreOf 2 (oTwoUpper H))

end CFSG.Quasithin
