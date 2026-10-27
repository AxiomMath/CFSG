module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84C2Cen
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84C3Odd
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84C4Wr
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84C5Pull
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84C7Fus
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Z2A5L128
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.XbarGen
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Inputs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Open

theorem asc82Lemma810K_of (F : Sec8T84Base) (h89 : Asc82Lemma89)
    (hSol : CFSG.EvenSporadicStandard.Fin76b.SolomonZ2A6) (hA5 : Sec8T84FactA5)
    (hInv : Sec8T84FactInv) : Asc82Lemma810K := by
  intro G _ _ hK t L S z g B E hE
  let κ := E.normalizerMonoidHom
  let H : Subgroup (MulAut ↥E) := κ.range
  let u : MulAut ↥E := B89.rhoG hE t
  let A : Subgroup (MulAut ↥E) := B89.Abar hE
  have hS : C10.HCtx E B u A H := C10.hctx_of F h89 hE
  haveI : Finite ↥E := Nat.finite_of_card_ne_zero (by rw [hE.elem.2]; norm_num)
  haveI : Finite (MulAut ↥E) := inferInstance
  haveI : IsSimpleGroup (alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; norm_num)
  have hH : H = secNb E := C10.range_kappa E
  have hKH : CFSG.SectionRank.IsKGroupCat ↥H := by
    rw [hH]
    exact isKGroupCat_secNb hE.ctx.simple hK hE.elem
  have hAe : Even (Nat.card (alternatingGroup (Fin 6))) := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    norm_num
  have hcenA : Subgroup.center (alternatingGroup (Fin 6)) = ⊥ :=
    alternatingGroup.center_eq_bot (by rw [Nat.card_fin]; norm_num)
  have hSol' : CFSG.EvenSporadicStandard.SolomonGen (alternatingGroup (Fin 6)) := hSol
  have hz2 : (⟨u, hS.u_H⟩ : ↥H) * ⟨u, hS.u_H⟩ = 1 := by
    apply Subtype.ext
    simpa using hS.u_sq
  have hu1 : u ≠ 1 := by
    intro h
    apply hS.u_A
    rw [h]
    exact A.one_mem
  have hz1 : (⟨u, hS.u_H⟩ : ↥H) ≠ 1 := by
    intro h
    exact hu1 (by simpa using congrArg Subtype.val h)
  have hcent : Nonempty (↥(centralizer ({(⟨u, hS.u_H⟩ : ↥H)} : Set ↥H)) ≃*
      Multiplicative (ZMod 2) × alternatingGroup (Fin 6)) :=
    C10.HCtx.exists_equiv_cent hS
  rcases CFSG.EvenSporadicStandard.M22Std.xbar_dichotomy_of_solomon_gen
      hAe hcenA hSol' hKH hz2 hz1 hcent.some with hcen | hdich
  · exfalso
    exact C10.bad_case_false F h89 hA5 hInv hE (C10.oddNormal_fusionOddCore H)
      (C10.commutator_mem_of_central H hS.u_H hcen)
  · obtain ⟨N₁, N₂, hN₁, hN₂, hcomm, hdisj, hnorm, hidx, hnot, hconj⟩ := hdich
    obtain ⟨M1, M2, hW⟩ := C10.wreathMod_of_dichotomy H u hS.u_H hS.u_sq N₁ N₂
      hN₁ hN₂ hcomm hdisj hnorm hidx hnot hconj
    have hO : C10.OddNormal H ((fusionOddCore ↥H).map H.subtype) :=
      C10.oddNormal_fusionOddCore H
    have hPbot : (fusionOddCore ↥H).map H.subtype = ⊥ :=
      C10.oddCore_eq_bot_of_wreath hA5 E B hE.elem hE.ctx.B_e16 (B89.B_le_E hE) u A H
        ((fusionOddCore ↥H).map H.subtype) M1 M2 hS.u_sq hS.fix hS.A_iso hS.A_comm hS.A_faith
        hS.u_H hS.A_H hO.le hO.norm hO.odd (C10.HCtx.cent_P hS hO) hW
    have hu : u = κ ⟨t, B89.t_mem_X hE⟩ := (C10.kappa_t hE).symm
    have hW' : C10.WreathMod H ⊥ M1 M2 (κ ⟨t, B89.t_mem_X hE⟩) := by
      rw [hu, hPbot] at hW
      exact hW
    exact C10.sec8X_of_wreathMod t E κ (C10.kappa_eq_one_iff E) (B89.t_mem_X hE) H M1 M2
      rfl hW'

end CFSG.OddStandard.SmallF3.Omega
