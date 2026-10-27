module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBHyp

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup

@[expose] def CFSp4RecognitionCI : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (h : Hyp59 H),
    (Blueprint.OddLieType ↥(generalizedFitting H) ∨
      Blueprint.NativeSporadic.IsSporadic ↥(generalizedFitting H) .M11) →
    Nat.card h.B = 2 → conjugate h.K h.a ≠ h.K →
    Nat.card (center (h.K ⧸ pPrimeCore 2 h.K)) = 2 →
    ((∃ n : ℕ, (n = 5 ∨ n = 6 ∨ n = 7) ∧
        Nonempty (h.J ⧸ pPrimeCore 2 h.J ≃* alternatingGroup (Fin n))) ∨
      ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧
        Blueprint.LieModel (h.J ⧸ pPrimeCore 2 h.J) .PSL 2 p f) →
    ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧
      Blueprint.LieModel ↥(generalizedFitting H) .PSp 2 p f ∧
      Blueprint.LieModel (h.J ⧸ pPrimeCore 2 h.J) .PSL 2 p f

@[expose] def CFSp4CoverInv : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p f : ℕ), p.Prime → p ≠ 2 → 1 ≤ f →
    ∀ Y : Subgroup G, IsQuasisimple ↥Y → center ↥Y ≠ ⊥ →
    Blueprint.LieModel (↥Y ⧸ center ↥Y) .PSp 2 p f →
    ∀ t : G, t * t = 1 → t ∈ normalizer (Y : Set G) →
    ∀ M : Subgroup G, M ≤ Y ⊓ centralizer ({t} : Set G) →
      IsPComponent 2 (M.subgroupOf (Y ⊓ centralizer ({t} : Set G))) →
      center (↥M ⧸ pPrimeCore 2 ↥M) ≠ ⊥

end CFSG.ComponentClassification.GSThmB
