module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.Background.A3Structure316
public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.Background.ThreePrimeGroup
public import CFSG.Quasithin.EmptyFaithful.S152Defs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

@[expose] def Input15222ThreeCanon_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T Mc M : Subgroup G), Setting152 T Mc M →
    ∀ H : Subgroup G, IsHStar T M H → ∀ H₁ H₂ : Subgroup G, IsHPair H (V154 T Mc M) H₁ H₂ →
      ∀ B₀ : Subgroup (MulAut (V154 T Mc M)), IsB0 T Mc M B₀ →
        ∀ I : Subgroup G, Hyp15215 T Mc M B₀ I → Concl15218ii T Mc M H B₀ I → CharTwo I →
          IsThreePrimeGroup (M ⊓ Subgroup.centralizer (V154 T Mc M : Set G)) →
          ¬ IsIrredOnSection (sOf152 T Mc M B₀) (oTwoUpper H) (pCoreOf 2 (oTwoUpper H)) →
          ∀ Y₁ : Subgroup G, Y₁ = oPrimeResidualOf 3 (M ⊓ I) → Y₁ = oTwoUpper Y₁ →
            Y₁ ≤ M ⊓ I → sOf152 T Mc M B₀ ≤ Subgroup.normalizer (Y₁ : Set G) →
            Nonempty (OTwoQuot (Y₁ ⊔ sOf152 T Mc M B₀) ≃* Equiv.Perm (Fin 3)) →
            ∃ t ∈ T, t ∉ sOf152 T Mc M B₀ ∧ ⁅Y₁, conjSub t Y₁⁆ ≤ Y₁ ⊓ conjSub t Y₁ ∧
              autOn (Y₁ ⊔ conjSub t Y₁) (V154 T Mc M) = oTwoUpper (mBar0 T Mc M)

@[expose] def StageLemma15222Canon_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T Mc M : Subgroup G), Setting152 T Mc M →
    ∀ H : Subgroup G, IsHStar T M H → ∀ H₁ H₂ : Subgroup G, IsHPair H (V154 T Mc M) H₁ H₂ →
      ∀ B₀ : Subgroup (MulAut (V154 T Mc M)), IsB0 T Mc M B₀ →
        ∀ I : Subgroup G, Hyp15215 T Mc M B₀ I → Concl15218ii T Mc M H B₀ I → CharTwo I →
          IsThreePrimeGroup (M ⊓ Subgroup.centralizer (V154 T Mc M : Set G)) →
          ¬ IsIrredOnSection (sOf152 T Mc M B₀) (oTwoUpper H) (pCoreOf 2 (oTwoUpper H)) →
          ∀ Y₁ : Subgroup G, Y₁ = oPrimeResidualOf 3 (M ⊓ I) → Y₁ = oTwoUpper Y₁ →
            Y₁ ≤ M ⊓ I → sOf152 T Mc M B₀ ≤ Subgroup.normalizer (Y₁ : Set G) →
            Nonempty (OTwoQuot (Y₁ ⊔ sOf152 T Mc M B₀) ≃* Equiv.Perm (Fin 3)) →
            ¬ ⁅Y₁, oTwoUpper H₂⁆ ≤ Y₁ ⊓ oTwoUpper H₂

end CFSG.Quasithin
