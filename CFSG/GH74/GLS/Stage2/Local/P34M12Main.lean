module

public import CFSG.GH74.GLS.Stage2.Local.P34M12Glue
public import CFSG.GH74.GLS.Stage2.Local.P34M12Facts

public section

namespace CFSG.GH74.GLS.Stage2.Local.P34M12

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Local.P34
open scoped commutatorElement

@[expose] def M12Card : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S : Subgroup G), Stage2Ctx G z Kind.m12 S →
    Nat.card {u : G // u ∈ S ∧ u ∈ WC z ∧ orderOf u = 2 ∧ IsConj z u} = 7

theorem prop34M12_core {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G}
    (hcard : Nat.card {u : G // u ∈ S ∧ u ∈ WC z ∧ orderOf u = 2 ∧ IsConj z u} = 7)
    (ctx : Stage2Ctx G z Kind.m12 S) {H : Subgroup G} (hCH : Cen z ≤ H)
    (hV : pCore 2 (HBar H) ≠ ⊥) : ConclA z H := by
  classical
  have hM := stage1M12_of_ctx ctx
  have hz2 := ctx.orderOf_z
  have hzH : z ∈ H := z_mem_of_cen_le hCH
  obtain ⟨a, hB⟩ := exists_barFacts hz2 hM
  have hS := setup_of hz2 hzH hCH hB
  have hzb2 := hS.zb_sq
  have hzb1 := hS.zb_ne
  have hVn : (pCore 2 (HBar H)).Normal := pCore_normal
  have hVp : IsPGroup 2 ↥(pCore 2 (HBar H)) := pCore_isPGroup
  obtain ⟨a₀, ha₀, ha₀1⟩ := exists_omegaZ_ne_one hVp hV
  have hAn : (omegaZ (pCore 2 (HBar H))).Normal := omegaZ_normal hVn
  have hA2 : ∀ e ∈ omegaZ (pCore 2 (HBar H)), e * e = 1 := fun e he => he.2.2
  obtain ⟨b, hbA, hbz, hb1⟩ := exists_fixed hAn hA2 ha₀ ha₀1 hzb2
  have hzA : mkH H ⟨z, hzH⟩ ∈ omegaZ (pCore 2 (HBar H)) :=
    hS.zb_mem_of_fixed hAn hA2 hbA ((hS.Cb_iff b).2 hbz) hb1
  have hAC : omegaZ (pCore 2 (HBar H)) ≤ barIn H (Cen z) := fun x hx =>
    (hS.Cb_iff x).2 (hx.2.1 _ hzA.1).symm
  rcases hS.dich hAn hA2 hAC hzA with hd | h8
  ·
    refine conclA_of_center hz2 hzH (mem_center_of_normal_zpowers hzb2 hzb1 ?_)
    rw [← hd]
    exact hAn
  · by_cases hcen : mkH H ⟨z, hzH⟩ ∈ center (HBar H)
    · exact conclA_of_center hz2 hzH hcen
    · exfalso
      have hnc : ∃ g : HBar H, g * mkH H ⟨z, hzH⟩ ≠ mkH H ⟨z, hzH⟩ * g := by
        by_contra hcon
        push Not at hcon
        exact hcen (Subgroup.mem_center_iff.2 hcon)
      obtain ⟨t, htS, htW, ht2, htc⟩ := hM.fuse_out
      obtain ⟨tb, htbC, htb2, htbW, htbCls⟩ :=
        fuse_out_data hCH ctx.S_le_Cen htS htW ht2 htc
      exact hS.final_contra (Cls := ZCls H z) hnc hAn hA2 hAC hzA h8
        (normal_le_bar ctx.sylow_top (ctx.S_le_Cen.trans hCH) hAn hA2)
        (fun u hu hu2 => exists_conj_into_bar ctx.sylow_top ctx.S_le_Cen hCH hu hu2)
        (fun x y hx hxy => ZCls.conj hx hxy) (zCls_self hzH) htb2 htbC htbW htbCls
        (ncard_le_seven ctx.sylow.isPGroup ctx.S_le_Cen hCH hz2 hcard)

theorem prop34M12_of_card (hcard : M12Card) : P34.Prop34M12 := by
  intro G _ _ z S ctx H _ hCH hV
  exact prop34M12_core (hcard G z S ctx) ctx hCH hV

end CFSG.GH74.GLS.Stage2.Local.P34M12
