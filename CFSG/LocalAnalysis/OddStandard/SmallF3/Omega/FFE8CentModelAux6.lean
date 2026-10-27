module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFE8CentModelAux5
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFE8CentModelAux4

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {ε : ZMod 3}

theorem ffOutFFE8CentModel_inf_eq_map (hQ : Q.Nondegenerate) {ι : Type} [Fintype ι]
    [DecidableEq ι] {c : ι → ZMod 3} (fr : PFrame Q ι c) (γ : simGroup Q)
    (frP : PFrame Q (Option (Fin 5)) ffC)
    (hB : ffOutFFE8CentModel_grp fr ⊓ omegaGroup hQ =
      (ffB0p frP).map (simAct Q γ).toMonoidHom) :
    ffOmegaSim hQ ⊓ (ffOutFFE8CentModel_grp fr).map (ffSim Q) =
      (ffB1Sim hQ frP).map (MulAut.conj (QuotientGroup.mk γ : ProjSim Q)).toMonoidHom := by
  ext x
  rw [Subgroup.mem_inf]
  constructor
  · rintro ⟨hxΩ, s, hs, hsx⟩
    obtain ⟨t, htΩ, htx⟩ := ffOutFFE8CentModel_exists_of_mem hQ hxΩ
    have hts : t ∈ ffOutFFE8CentModel_grp fr ⊓ omegaGroup hQ := by
      refine ⟨?_, htΩ⟩
      rcases (ffOutFFE8CentModel_ffSim_eq_iff t s).mp (htx.trans hsx.symm) with h | h
      · rw [← h]
        exact hs
      · have : t = piOrth Q * s := by
          rw [h, ← mul_assoc, piOrth_mul_self, one_mul]
        rw [this]
        exact mul_mem (ffOutFFE8CentModel_piOrth_mem fr) hs
    rw [hB] at hts
    obtain ⟨g, hg, rfl⟩ := hts
    refine ⟨ffSim Q g, (ffOutFFE8CentModel_mem_ffB1Sim_iff hQ frP).mpr ⟨g, hg, rfl⟩, ?_⟩
    rw [← htx, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← ffOutFFE8CentModel_ffSim_simAct]
    rfl
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨g, hg, rfl⟩ := (ffOutFFE8CentModel_mem_ffB1Sim_iff hQ frP).mp hy
    have hmem : simAct Q γ g ∈ ffOutFFE8CentModel_grp fr ⊓ omegaGroup hQ := by
      rw [hB]
      exact ⟨g, hg, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← ffOutFFE8CentModel_ffSim_simAct]
    exact ⟨ffOutFFE8CentModel_ffSim_mem hQ hmem.2, simAct Q γ g, hmem.1, rfl⟩

theorem ffOutFFE8CentModel_cent_sylow_of_frame (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hsgn : quadSign Q = 1) (hε : ε = 1 ∨ ε = -1)
    (fr : PFrame Q FFE8Idx (ffE8Norm ε)) :
    ∃ P : Subgroup (ProjSim Q), IsSylow2Of P (ffOmegaSim hQ) ∧
      IsNormalE16In P (ffOmegaSim hQ ⊓ (ffOutFFE8CentModel_grp fr).map (ffSim Q)) := by
  obtain ⟨γ, frP, hB⟩ := ffOutFFE8CentModel_exists_conj hQ hdim hε fr
  have h2 : 2 ≤ Module.finrank (ZMod 3) V := by omega
  have hπ := ff_piOrth_not_mem_omegaGroup_six_plus hQ hdim hsgn
  have hf := ffOmegaToSim_injective hQ
  have hc : Function.Injective (MulAut.conj (QuotientGroup.mk γ : ProjSim Q)).toMonoidHom :=
    (MulAut.conj (QuotientGroup.mk γ : ProjSim Q)).injective
  have hP1 : IsSylow2Of (ffP1Sim hQ frP) (ffOmegaSim hQ) := by
    have h := ffOutFFE8CentModel_sylow_map (ffOmegaToSim hQ) hf (ffP1p_sylow hQ hdim hsgn frP)
    rwa [← MonoidHom.range_eq_map] at h
  have hN1 : IsNormalE16In (ffP1Sim hQ frP) (ffB1Sim hQ frP) :=
    ffOutFFE8CentModel_normalE16_map (ffOmegaToSim hQ) hf (ffB1p_normalE16 hQ hπ frP)
  refine ⟨(ffP1Sim hQ frP).map (MulAut.conj (QuotientGroup.mk γ : ProjSim Q)).toMonoidHom, ?_, ?_⟩
  · have h := ffOutFFE8CentModel_sylow_map _ hc hP1
    rwa [ffOutFFE8CentModel_conj_ffOmegaSim hQ h2 γ] at h
  · rw [ffOutFFE8CentModel_inf_eq_map hQ fr γ frP hB]
    exact ffOutFFE8CentModel_normalE16_map _ hc hN1

end CFSG.OddStandard.SmallF3.Omega
