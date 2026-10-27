module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGCplxGrp
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGCplxCls
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGFixMem
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGCyc4
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MK4Core
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFShapes

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem fg_cent_typeIV (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (h2 : 2 ≤ Module.finrank (ZMod 3) V) {ρ : ↥(simGroup Q)}
    (hρ : IsSimilitude Q (ρ : V ≃ₗ[ZMod 3] V) (-1))
    (hρρ : ∀ v, (ρ : V ≃ₗ[ZMod 3] V) ((ρ : V ≃ₗ[ZMod 3] V) v) = -v)
    (hLM : LayerModel ↥(ffFix hQ h2 (QuotientGroup.mk ρ : ProjSim Q)) .PSL 2 2)
    {J : Subgroup ↥(omegaProj hQ)}
    (hJ : IsComponentIn J (ffFix hQ h2 (QuotientGroup.mk ρ : ProjSim Q)))
    {A : Subgroup (ProjSim Q)}
    (hAJ : ∀ a ∈ A, ∀ j ∈ J, projSimAct Q a (j : ProjOrth Q) = (j : ProjOrth Q)) :
    Nat.card A ≤ 2 := by
  haveI : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ZMod 3) (by rw [hdim]; norm_num)
  obtain ⟨hlie, hΩ, -⟩ := ff6m_K4_core hQ hdim hρ hρρ
  have hsn := ff_simple_of_lieModel_psl2 hlie
  have hperf : Group.IsPerfect ↥⁅fixSub (simAct Q ρ), fixSub (simAct Q ρ)⁆ :=
    (ff_isQuasisimple_of_simple hsn.1 hsn.2).1
  have hcard : ¬ Nat.card ↥⁅fixSub (simAct Q ρ), fixSub (simAct Q ρ)⁆ ∣ 11232 := by
    rw [ff_card_model_psl2 hlie]
    norm_num
  have hcplx : FGCplx Q.polarBilin (ρ : V ≃ₗ[ZMod 3] V).toLinearMap (-1) := by
    have h := fg_cplx_of_similitude hρ hρρ
    simpa using h
  have hB : Q.polarBilin.Nondegenerate := QuadraticMap.nondegenerate_polar_iff.mpr hQ
  have ha := fg_ha_of_component hQ h2 (fun E _ hE => ff_simple_of_lieModel_psl2 hE) hLM hJ hΩ
    (fg_comm_le_self _) hperf hAJ
  refine fg_card_le_two_of_le_zpowers (fg_mk_sq_eq_one hρρ) (fun a haA => ?_)
  obtain ⟨γ, α, β, rfl, hγ⟩ := fg_cplx_lifts hQ hdim hcplx hsn.1 hsn.2 hcard (ha a haA)
  rcases fg_cplx_neg_class hB hcplx hγ with h | h
  · rw [h]
    exact one_mem _
  · rw [h]
    exact mem_zpowers _

end CFSG.OddStandard.SmallF3.Omega
