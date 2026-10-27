module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7Basic
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog8Sp4

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

@[expose] def Prop29Concl (H : Type) [Group H] (ι : H) (J₁ S₁ : Subgroup H) : Prop :=
  ∃ t ∈ generalizedFitting H, t ∈ normalizer (S₁ : Set H) ∧ t ∉ S₁ ∧ t * t ∈ S₁ ∧
    (S₁ ⊓ J₁) ⊓ conjugate (S₁ ⊓ J₁) t = ⊥ ∧
    (∀ d ∈ S₁ ⊓ J₁, ∀ e ∈ conjugate (S₁ ⊓ J₁) t, d * e = e * d) ∧
    (S₁ ⊓ J₁) ⊔ conjugate (S₁ ⊓ J₁) t = S₁ ⊓ generalizedFitting H ∧
    (conjugate (S₁ ⊓ J₁) t ⊓ coreActionKernel J₁).relIndex (conjugate (S₁ ⊓ J₁) t) = 2 ∧
    ι ∈ conjugate (S₁ ⊓ J₁) t ⊓ coreActionKernel J₁ ∧
    (∀ e ∈ conjugate (S₁ ⊓ J₁) t, ι * e = e * ι) ∧
    (¬ Nonempty (↥(generalizedFitting H) ≃* alternatingGroup (Fin 10)) →
      IsCyclic ↥(conjugate (S₁ ⊓ J₁) t ⊓ coreActionKernel J₁)) ∧
    ∀ d ∈ conjugate (S₁ ⊓ J₁) t, d ∉ coreActionKernel J₁ → ∀ j ∈ J₁, ∃ w ∈ J₁,
      (d * w * d⁻¹)⁻¹ * (j * w * j⁻¹) ∉ oddCoreIn J₁

@[expose] def CF82Prop29A10 : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (p f : ℕ), p.Prime → p ≠ 2 → 1 ≤ f →
    centralizer (generalizedFitting H : Set H) = ⊥ →
    Nonempty (↥(generalizedFitting H) ≃* alternatingGroup (Fin 10)) →
    ∀ ι : H, orderOf ι = 2 →
    ∀ J₁ : Subgroup H, J₁ ≤ centralizer ({ι} : Set H) →
      IsPComponent 2 (J₁.subgroupOf (centralizer ({ι} : Set H))) →
      IsSec8JType (↥J₁ ⧸ pPrimeCore 2 ↥J₁) p f →
    ∀ S₁ : Subgroup H, Seven.IsSylowIn S₁ (centralizer ({ι} : Set H)) →
      Prop29Concl H ι J₁ S₁

end CFSG.ComponentClassification.GSThmB
