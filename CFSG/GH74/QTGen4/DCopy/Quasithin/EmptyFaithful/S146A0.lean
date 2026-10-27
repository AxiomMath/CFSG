module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.EmptyFaithful.S146A0

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

@[expose] def Stage14614_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M : Subgroup G), Setting146 G T M →
    ∀ (H PQ : Subgroup G) (p : ℕ), IsRedCE T M H PQ p → PMaximal T M p →
      (conjClosure (oTwoUpper H) (mcOf T) = oTwoUpper H ∧
          (p = 3 → ∀ r : ℕ, r.Prime → r ∣ Nat.card (mcOf T) → r = 2 ∨ r = 3)) ∨
      (p = 3 ∧ conjClosure (oTwoUpper H) (mcOf T) ∈ cComp (mcOf T) ∧
          ∃ n : ℕ, (n = 4 ∨ n = 5) ∧
            Nonempty (OTwoQuot (mcOf T) ≃* MulAut (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)))) ∨
      (p = 3 ∧ ∃ (K₁ : Subgroup G) (s : G), K₁ ∈ cComp (mcOf T) ∧ s ∈ T ∧
          s ∉ Subgroup.normalizer (K₁ : Set G) ∧
          conjClosure (oTwoUpper H) (mcOf T) = K₁ ⊔ conjSub s K₁ ∧
          (Nonempty (OTwoQuot (mcOf T) ≃* (Equiv.Perm (Fin 5) ≀ᵣ Multiplicative (ZMod 2))) ∨
            Nonempty (OTwoQuot (mcOf T) ≃*
              (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) ≀ᵣ Multiplicative (ZMod 2))))) ∨
      (p = 5 ∧ ∃ (K₁ : Subgroup G) (s : G), K₁ ∈ cComp (mcOf T) ∧ s ∈ T ∧
          s ∉ Subgroup.normalizer (K₁ : Set G) ∧
          conjClosure (oTwoUpper H) (mcOf T) = K₁ ⊔ conjSub s K₁ ∧
          mcOf T = conjClosure (oTwoUpper H) (mcOf T) ⊔ T ∧
          (imageOTwoQuot (mcOf T) (conjClosure (oTwoUpper H) (mcOf T))).index ∣ 32 ∧
          Nonempty (OTwoQuot K₁ ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 4)))

@[expose] def Stage14615_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M : Subgroup G), Setting146 G T M →
    ∀ (H PQ : Subgroup G) (p : ℕ), IsRedCE T M H PQ p → PMaximal T M p → p = 3

@[expose] def Stage14616_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M : Subgroup G), Setting146 G T M →
    ∀ (H PQ : Subgroup G) (p : ℕ), IsRedCE T M H PQ p → PMaximal T M p →
      ∀ (H₀ H₁ H₂ : Subgroup G) (t : G), IsDec12 T M H p H₀ H₁ H₂ t →
        (T ⊓ Subgroup.normalizer (H₁ : Set G)).relIndex T = 2 ∧
          Subgroup.normalizer ((T ⊓ Subgroup.normalizer (H₁ : Set G) : Subgroup G) : Set G) ⊓ mcOf T = T

@[expose] def Stage14617_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M : Subgroup G), Setting146 G T M →
    ∀ (H PQ : Subgroup G) (p : ℕ), IsRedCE T M H PQ p → PMaximal T M p →
      IsOFourPlusOn T M H ∧
        ∀ (H₀ H₁ H₂ : Subgroup G) (t : G), IsDec12 T M H p H₀ H₁ H₂ t →
          (∀ (γ γ' : F8.Geom T (yOfL22 T M) H) (g : ↥(((yOfL22 T M) ⊔ T) ⊔ H)),
              F8Setup T (VZ T M) (yOfL22 T M) H γ γ' g →
              ¬ F8.A₁ (quasithinOmegaOneCenter T) (g : G) ≤ uHi T M H H₁) ∧
          (∀ u : G, u ∈ uK T M H → (u ∈ uHi T M H H₁ ∨ u ∈ uHi T M H H₂) →
              u ∉ quasithinOmegaOneCenter T →
              T ⊓ Subgroup.normalizer (H₁ : Set G) ≤ tZero T u → IsInvU T M H u) ∧
          (∀ u : G, u ∈ uK T M H → (u ∈ uHi T M H H₁ ∨ u ∈ uHi T M H H₂) →
              u ∉ quasithinOmegaOneCenter T →
              T ⊓ Subgroup.normalizer (H₁ : Set G) ≤ tZero T u →
              IsI T M u (Subgroup.centralizer ({u} : Set G))) ∧
          Nat.card (conjClosure (VZ T M) (oTwoUpper H₂)) = 2 ^ 4

end CFSG.Quasithin
