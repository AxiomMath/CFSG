module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog8L4
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7L2b

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup

@[expose] def CF82L2Comm : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (p f : ℕ), p.Prime → p ≠ 2 → 1 ≤ f →
    Blueprint.LieModel Y .PSL 2 p f → ∀ T : Sylow 2 Y, 8 ≤ Nat.card T →
    ∀ σ ∈ commutator (MulAut Y), σ ∈ centralizer (innOf (T : Subgroup Y) : Set (MulAut Y)) →
      ∃ t ∈ (T : Subgroup Y), t ∈ centralizer ((T : Subgroup Y) : Set Y) ∧ σ = MulAut.conj t

@[expose] def CF82L2Cyc : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (p f : ℕ), p.Prime → p ≠ 2 → 1 ≤ f →
    Blueprint.LieModel Y .PSL 2 p (2 * f) → ∀ T : Sylow 2 Y,
    ∀ C E : Subgroup (MulAut Y), IsCyclic C → 2 * Nat.card C = Nat.card T → IsPGroup 2 E →
      E ≤ centralizer (C : Set (MulAut Y)) → C ⊓ E = ⊥ → Nat.card E ≤ 2

@[expose] def CF82AZ : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (p f : ℕ), p.Prime → p ≠ 2 → 1 ≤ f →
    IsSimpleGroup ↥(generalizedFitting H) →
    centralizer (generalizedFitting H : Set H) = ⊥ →
    IsSec82LType ↥(generalizedFitting H) p f →
    (Blueprint.LieModel ↥(generalizedFitting H) .PSL 4 p f → p ^ f % 4 = 3) →
    (Blueprint.LieModel ↥(generalizedFitting H) .PSU 4 p f → p ^ f % 4 = 1) →
    ∀ ι : H, ι ∈ generalizedFitting H → orderOf ι = 2 →
    ∀ J₁ : Subgroup H, J₁ ≤ centralizer ({ι} : Set H) →
      IsPComponent 2 (J₁.subgroupOf (centralizer ({ι} : Set H))) →
      IsSec8JType (↥J₁ ⧸ pPrimeCore 2 ↥J₁) p f →
      ∀ z₁ ∈ J₁, orderOf z₁ = 2 → ∃ g ∈ generalizedFitting H, g⁻¹ * ι * g = z₁

end CFSG.ComponentClassification.GSThmB
