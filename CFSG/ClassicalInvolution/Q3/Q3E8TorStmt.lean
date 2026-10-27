module

public import CFSG.ClassicalInvolution.ModelFacts.E7ModelRoots
public import CFSG.ClassicalInvolution.RouteD.LocalTwinWeyl
public import CFSG.ClassicalInvolution.ModelFacts.ChevAutTorusStdBasic

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.Minuscule CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.ModelFacts CFSG.ClassicalInvolution.ModelFacts.E7Model

set_option linter.unusedSectionVars false


@[expose] def ToralStdE73 : Prop :=
  ∀ (Γ : Set (Fin Tag.E7.rank → ℤ)) (l : Fin Tag.E7.rank → ℤ),
    (∀ γ ∈ Γ, γ ∈ (e7Datum (GaloisField 3 1)).roots) → l ∈ Submodule.span ℤ Γ →
    (∀ σ ∈ rootFinset .E7, iform l σ ≠ 0) →
    ∀ {Y : Type} [Group Y] (ψ : ↥(e7Data_valid.minGroup (GaloisField 3 1)) →* Y),
      ψ.ker ≤ Subgroup.center ↥(e7Data_valid.minGroup (GaloisField 3 1)) →
      ∀ σ : Y ≃* Y, (∀ y, σ (σ y) = y) → (∀ k, σ (ψ k) ∈ ψ.range) →
      ∀ k₀ : ↥(e7Data_valid.minGroup (GaloisField 3 1)),
        (∀ γ ∈ Γ, ∀ y ∈ (e7Datum (GaloisField 3 1)).rootGroup γ ⊔
            (e7Datum (GaloisField 3 1)).rootGroup (-γ),
          σ (ψ (k₀ * y * k₀⁻¹)) = ψ (k₀ * y * k₀⁻¹)) →
      ∃ v : Fin Tag.E7.rank → ZMod 2, ∀ γ ∈ (e7Datum (GaloisField 3 1)).roots,
        (∀ y ∈ (conjSub k₀ ((e7Datum (GaloisField 3 1)).rootGroup γ ⊔
            (e7Datum (GaloisField 3 1)).rootGroup (-γ))).map ψ,
          σ y ∈ (conjSub k₀ ((e7Datum (GaloisField 3 1)).rootGroup γ ⊔
            (e7Datum (GaloisField 3 1)).rootGroup (-γ))).map ψ) ∧
        ((∀ y ∈ (conjSub k₀ ((e7Datum (GaloisField 3 1)).rootGroup γ ⊔
            (e7Datum (GaloisField 3 1)).rootGroup (-γ))).map ψ, σ y = y) ↔ charOf v γ = 0)

end CFSG.ClassicalInvolution.Q3.Q3W
