module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFModelK4IVAux6

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem ff_K4IV_layerModel (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) {ρ : ↥(simGroup Q)}
    (hρ : IsSimilitude Q (ρ : V ≃ₗ[ZMod 3] V) (-1))
    (hρρ : ∀ v, (ρ : V ≃ₗ[ZMod 3] V) ((ρ : V ≃ₗ[ZMod 3] V) v) = -v) :
    LayerModel ↥(ffFix hQ (by omega) (QuotientGroup.mk ρ : ProjSim Q)) .PSL 2 2 := by
  obtain ⟨e, -⟩ := ff_fixEquiv_sim hQ hdim hsgn ρ
  exact ff_layerModel_congr e (ff_aux_layerModel_core hQ hdim hsgn hρ hρρ)

theorem ff_K4IV_cover (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) {ρ : ↥(simGroup Q)}
    (hρ : IsSimilitude Q (ρ : V ≃ₗ[ZMod 3] V) (-1))
    (hρρ : ∀ v, (ρ : V ≃ₗ[ZMod 3] V) ((ρ : V ≃ₗ[ZMod 3] V) v) = -v) :
    ∃ w : ↥(omegaProj hQ),
      w ∈ twoPrimeRes (twoRes (ffFix hQ (by omega) (QuotientGroup.mk ρ : ProjSim Q))) ∧
      w * w = 1 ∧ KM0 (projOrthToProjSim Q (w : ProjOrth Q)) ∧
      ∃ a : ↥(omegaProj hQ),
        ffSimOmegaAct hQ (by omega) (QuotientGroup.mk ρ : ProjSim Q) a * a⁻¹ = w := by
  obtain ⟨u₁, u₂, hu₁, hu₂, h12, h1R1, h2R2, h1R2, h2R1⟩ :=
    ff_aux_pair_facts hQ hdim hsgn hρ hρρ
  exact ff_K4IV_cover_of_data hQ hdim hsgn hρ hρρ hu₁ hu₂ h12 h1R1 h2R2 h1R2 h2R1

end CFSG.OddStandard.SmallF3.Omega
