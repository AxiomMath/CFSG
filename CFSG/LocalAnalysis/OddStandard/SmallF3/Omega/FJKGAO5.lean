module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FJKGAIso
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.BridgeLow
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGClosureFive
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFAutSurj

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem fjIsomInv_five (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 5)
    (hs : quadSign Q = 1) : FJIsomInv hQ := by
  have h2 : 2 ≤ Module.finrank (ZMod 3) V := by omega
  have hbij := ffSimOmegaAct_bijective_five hQ hdim hs
  intro α hα
  obtain ⟨x, rfl⟩ := hbij.2 α
  have hx2 : x * x = 1 := hbij.1 (by rw [map_mul, map_one]; exact hα)
  obtain ⟨y, hy⟩ := fg_simInGStar_of_odd hQ (by omega) (by rw [hdim]; decide) x
  obtain ⟨A, rfl⟩ := QuotientGroup.mk_surjective y
  have hαA : ffSimOmegaAct hQ h2 x = projAut hQ A := by
    rw [← hy, ffSimOmegaAct_projOrthToProjSim]
    rfl
  have hy' : projOrthToProjSim Q (toProj Q A) = x := hy
  have hy2 : toProj Q A * toProj Q A = 1 :=
    projOrthToProjSim_injective (by rw [map_mul, hy', hx2, map_one])
  exact ⟨A, fj_mul_self_eq_one_of_odd hQ (by rw [hdim]; decide) hy2, hαA⟩

theorem fjKGAAt_omegaProj_five (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 5)
    (hs : quadSign Q = 1) : FJKGAAt ↥(omegaProj hQ) :=
  fjKGAAt_of_isomInv hQ (by omega) (fjIsomInv_five hQ hdim hs)

theorem fjKGAAt_of_lieModel_psp {Y : Type} [Group Y] (h : LieModel Y .PSp 2 3 1) :
    FJKGAAt Y := by
  obtain ⟨W, i1, i2, i3, R, hR, hdim, hs, ⟨f⟩⟩ := isOmegaStar_of_lieModel_psp h
  letI := i1
  letI := i2
  letI := i3
  exact fjKGAAt_of_mulEquiv f.symm (fjKGAAt_omegaProj_five hR hdim hs)

end CFSG.OddStandard.SmallF3.Omega
