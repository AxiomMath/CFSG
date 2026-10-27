module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFModelK4IIIAux5

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem ff_K4III_layerModel (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) {ρ : ↥(simGroup Q)}
    (hρ : IsSimilitude Q (ρ : V ≃ₗ[ZMod 3] V) (-1))
    (hρρ : ∀ v, (ρ : V ≃ₗ[ZMod 3] V) ((ρ : V ≃ₗ[ZMod 3] V) v) = v) :
    LayerModel ↥(ffFix hQ (by omega) (QuotientGroup.mk ρ : ProjSim Q)) .PSL 3 1 := by
  obtain ⟨e, -⟩ := ff_fixEquiv_sim hQ hdim hsgn ρ
  exact ff_layerModel_congr e (ff_K4III_C_layerModel hQ hdim hsgn hρ hρρ)

theorem ff_K4III_cover (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) {ρ : ↥(simGroup Q)}
    (hρ : IsSimilitude Q (ρ : V ≃ₗ[ZMod 3] V) (-1))
    (hρρ : ∀ v, (ρ : V ≃ₗ[ZMod 3] V) ((ρ : V ≃ₗ[ZMod 3] V) v) = v) :
    ∃ w : ↥(omegaProj hQ),
      w ∈ twoPrimeRes (twoRes (ffFix hQ (by omega) (QuotientGroup.mk ρ : ProjSim Q))) ∧
      w * w = 1 ∧ KM0 (projOrthToProjSim Q (w : ProjOrth Q)) ∧
      ∃ a : ↥(omegaProj hQ),
        ffSimOmegaAct hQ (by omega) (QuotientGroup.mk ρ : ProjSim Q) a * a⁻¹ = w := by
  obtain ⟨u₂, u₃, v₂, v₃, hu₂, hu₃, hv₂, hv₃, hvu₂, hvu₃, hvu₂₃, hvu₃₂, hvv, huu,
    hρu₂, hρu₃⟩ := ff_exists_cover_vectors hQ hdim hsgn hρ hρρ
  exact ff_K4III_cover_of_data hQ hdim hsgn hρ hρρ hu₂ hu₃ hv₂ hv₃ hvu₂ hvu₃ hvu₂₃ hvu₃₂
    hvv huu hρu₂ hρu₃

end CFSG.OddStandard.SmallF3.Omega
