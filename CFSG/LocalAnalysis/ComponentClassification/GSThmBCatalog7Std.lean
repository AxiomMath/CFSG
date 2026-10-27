module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7Basic
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBHyp

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup

@[expose] def CFSp4RecognitionStd : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (h : Hyp59 H),
    (∀ M : Subgroup H, IsComponent M → GSRestricted (↥M ⧸ center ↥M)) →
    Nat.card h.B = 2 → conjugate h.K h.a = h.K → 8 ≤ Nat.card h.toHyp52.P →
    ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → 5 ≤ p ^ f →
      Blueprint.LieModel (h.J ⧸ pPrimeCore 2 h.J) .PSL 2 p f →
      Blueprint.LieModel (h.K ⧸ pPrimeCore 2 h.K) .PSL 2 p (2 * f) →
      Blueprint.LieModel ↥(generalizedFitting H) .PSp 2 p f

@[expose] def CFSp4TwoCentral : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (p f : ℕ), p.Prime → p ≠ 2 → 1 ≤ f → 5 ≤ p ^ f →
    IsSimpleGroup ↥(generalizedFitting H) →
    Blueprint.LieModel ↥(generalizedFitting H) .PSp 2 p f →
    ∀ a : H, orderOf a = 2 → ∀ J : Subgroup H, J ≤ generalizedFitting H →
      J ≤ centralizer ({a} : Set H) → IsPComponent 2 (J.subgroupOf (centralizer ({a} : Set H))) →
      Blueprint.LieModel (↥J ⧸ pPrimeCore 2 ↥J) .PSL 2 p f →
      ∀ R : Subgroup H, IsPGroup 2 R →
        R ≤ centralizer ({a} : Set H) ⊓ UnbalancedLayer.coreActionKernel J →
        Seven.IsSylowIn (R ⊓ generalizedFitting H) (generalizedFitting H ⊓
          centralizer ({a} : Set H) ⊓ UnbalancedLayer.coreActionKernel J) →
        ∃ t ∈ R ⊓ generalizedFitting H, orderOf t = 2 ∧ ∃ M : Subgroup H,
          M ≤ centralizer ({t} : Set H) ∧ IsComponent (M.subgroupOf (centralizer ({t} : Set H))) ∧
          conjugate M a ≠ M ∧ J ≤ M ⊔ conjugate M a

end CFSG.ComponentClassification.GSThmB
