module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticRepresentation
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticTwoTypePreservation
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticTwoGeneration

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBSymplecticRepresentation

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticFlag SymplecticHigher
open CFSG.ComponentClassification.CatalogueBHigherLinearField (glFieldEquiv)

variable {r : ℕ} {K : Type} [Field K]

theorem automorphism_standard [Finite K] (hodd : ringChar K ≠ 2) (hr : 2 ≤ r)
    (α : MulAut (StatedProj (StatedSp r K))) :
    ∃ (A : gsp r K) (σ : K ≃+* K), α = conjAut r K A * fieldAut r K σ := by
  rcases Nat.lt_or_ge r 3 with h | h
  · obtain rfl : r = 2 := by omega
    obtain ⟨-, htop, -⟩ := CatalogueBSymplecticTwo.odd_symplectic_two_type_preservation hodd
    exact (CatalogueBSymplecticTwo.kernel_generation (K := K)).2.1 α (htop ▸ Subgroup.mem_top α)
  · exact (automorphism_generation (K := K) h).2 α

theorem odd_symplectic_automorphism_semilinear_representation [Finite K]
    (hodd : ringChar K ≠ 2) (hr : 2 ≤ r) :
    (∀ α : MulAut (StatedProj (StatedSp r K)), ∃ (A : gsp r K) (σ : K ≃+* K),
      α = conjAut r K A * fieldAut r K σ) ∧
    (∀ (A : gsp r K) (σ : K ≃+* K), conjAut r K A * fieldAut r K σ = 1 ↔
      σ = 1 ∧ ∃ c : Kˣ,
        (A : GL (Fin r ⊕ Fin r) K) = GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c) ∧
    ∀ α : MulAut (StatedProj (StatedSp r K)), α * α = 1 → α ≠ 1 →
      ∃ (A : gsp r K) (σ : K ≃+* K), α = conjAut r K A * fieldAut r K σ ∧ σ ^ 2 = 1 ∧
        (∃ d : Kˣ, (A : GL (Fin r ⊕ Fin r) K) * glFieldEquiv (Fin r ⊕ Fin r) σ A =
          GeneralLinearGroup.scalar (Fin r ⊕ Fin r) d) ∧
        (σ = 1 → ∀ c : Kˣ,
          (A : GL (Fin r ⊕ Fin r) K) ≠ GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c) ∧
        (σ ≠ 1 → Nat.card K = Nat.card {c : K // σ c = c} ^ 2 ∧
          ∀ τ : K ≃+* K, τ ^ 2 = 1 → τ ≠ 1 → τ = σ) :=
  ⟨automorphism_standard hodd hr, conjAut_mul_fieldAut_eq_one_iff (by omega),
    involution_representative (by omega) (automorphism_standard hodd hr)⟩

end CFSG.ComponentClassification.CatalogueBSymplecticRepresentation
