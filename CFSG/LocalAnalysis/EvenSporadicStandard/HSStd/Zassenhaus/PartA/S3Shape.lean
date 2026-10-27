module

public import CFSG.LocalAnalysis.SectionRank.NativeKGroup
public import CFSG.Open.FusionDefs

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup CFSG.Open

structure DShape (D : Type) [Group D] [Finite D] (t : D) (K : Subgroup D) : Prop where
  t_sq : t * t = 1
  t_ne : t ≠ 1
  cent : centralizer ({t} : Set D) = zpowers t ⊔ K
  disj : Disjoint (zpowers t) K
  K_S5 : Nonempty (↥K ≃* Equiv.Perm (Fin 5))
  zstar : fusionZStar D = ⊥

structure CaseAData (D : Type) [Group D] (t : D) where
  Y₁ : Subgroup D
  Y₂ : Subgroup D
  e₁ : ↥Y₁ ≃* alternatingGroup (Fin 5)
  comm : ∀ a ∈ Y₁, ∀ b ∈ Y₂, a * b = b * a
  perm : ∀ d : D, ((∀ a ∈ Y₁, d * a * d⁻¹ ∈ Y₁) ∧ (∀ b ∈ Y₂, d * b * d⁻¹ ∈ Y₂)) ∨
    ((∀ a ∈ Y₁, d * a * d⁻¹ ∈ Y₂) ∧ (∀ b ∈ Y₂, d * b * d⁻¹ ∈ Y₁))
  swap₁ : ∀ a ∈ Y₁, t * a * t⁻¹ ∈ Y₂
  swap₂ : ∀ b ∈ Y₂, t * b * t⁻¹ ∈ Y₁
  faithful : ∀ d : D, (∀ a ∈ Y₁, d * a = a * d) → (∀ b ∈ Y₂, d * b = b * d) → d = 1

@[expose] def HarrisContra : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.SectionRank.IsKGroupCat X → fusionOddCore X = ⊥ →
    ∀ s : X, orderOf s = 2 →
    Nonempty (↥(centralizer ({s} : Set X)) ≃*
      Multiplicative (ZMod 2) × MulAut (alternatingGroup (Fin 6))) →
    ∀ y : X, orderOf y = 3 → ¬ 7 ∣ Nat.card ↥(centralizer ({y} : Set X))

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
