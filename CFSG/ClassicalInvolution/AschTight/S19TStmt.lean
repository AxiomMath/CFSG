module

public import CFSG.ClassicalInvolution.Asc77.AscIH8Model
public import CFSG.ClassicalInvolution.Asc77.AscL62Aut

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19T

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77
open scoped MatrixGroups

@[expose] def FactFL : Prop :=
  ∀ (p e : ℕ) [Fact p.Prime], p ≠ 2 → 5 ≤ p ^ e →
    ∀ (E : Type) [Group E] [Finite E] [IsSimpleGroup E] (Ω : Set (Subgroup E))
      (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (k e' : ℕ),
        ((t = .PSL ∧ k = 3) ∨ (t = .PSU ∧ k = 3)) → Nonempty (Ih8Model p e Ω t k e') →
        ∀ L ∈ Ω, ∀ φ : MulAut E,
          (∃ (ι : ↥L ≃* SL(2, GaloisField p e))
              (g : Matrix.GeneralLinearGroup (Fin 2) (GaloisField p e)),
            ∀ x : ↥L,
              ((ι.symm (AscL62.semilinHom g (RingEquiv.refl _) (ι x)) : ↥L) : E) = φ x) →
          ((∀ c ∈ Subgroup.centralizer (L : Set E), φ c = c) ∨
              (∀ c ∈ Subgroup.centralizer (L : Set E), φ c = c⁻¹)) ∧
            (φ * φ = 1 → (∃ c ∈ Subgroup.centralizer (L : Set E), φ c = c ∧ c * c ≠ 1) →
              ∃ y : E, φ = MulAut.conj y)

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19T
