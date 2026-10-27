module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftPieceDelTools
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftDelDecomp

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
  CFSG.QuasithinUnique.Setup.Lift.PieceDel

theorem delResidualProp : DelResidualProp := by
  intro G _ _ R M V n F _ r Lc ctx i Fs P hcore hbase hseed hH0 hmin hbasic himage hW
  classical
  have hX := ctx.hX
  have hS := ctx.setting
  have hSR : baum R ≤ R := inf_le_left
  have hSM : baum R ≤ M := hSR.trans hS.max.1
  have hSP : baum R ≤ P := hbasic.lt.le
  have hVn : V.Normal := Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp hX)
  have hPV : P ≤ Subgroup.normalizer (V : Set G) := le_top.trans hX
  have hnotN : ¬ P ≤ Subgroup.normalizer (baum R : Set G) := fun h =>
    hbasic.not_normal ((Subgroup.normal_subgroupOf_iff_le_normalizer hSP).2 h)
  have hMP : M ⊓ P < P := lt_of_le_of_ne inf_le_right fun h =>
    hmin.not_le (h.symm.le.trans inf_le_left)
  have hmax : ∀ Y : Subgroup G, baum R ≤ Y → Y < P → Y ≤ M ⊓ P := fun Y hY hYP =>
    le_inf (hbasic.max Y hY hYP) hYP.le
  have hJS : thompsonJ (baum R) = thompsonJ R := hbase.base.J_S
  have hJW : ¬ thompsonJ (baum R) ≤ Subgroup.centralizer (modComm V Fs : Set G) := fun h =>
    hW.thompson_ne (Subgroup.commutator_eq_bot_iff_le_centralizer.2 h)
  have hJP : thompsonJ (baum R) ≤ P := (B6.thompsonJ_le (baum R)).trans hSP
  have hVH : ¬ P ≤ Subgroup.centralizer (modComm V Fs : Set G) := fun h => hJW (hJP.trans h)
  obtain ⟨hPeq, -, -, -, -⟩ := reduced_detects_commutator hbasic.sylow hnotN (le_inf hSM hSP) hMP
    hmax hW.reduced hVH
  have hthomp := reduced_detects_commutator_thompsonJ hbasic.sylow hnotN (le_inf hSM hSP) hMP
    hmax hW.reduced hVH
  have hperf : ⁅oddOrderSubgroup P, thompsonJ R⁆ = oddOrderSubgroup P := by
    rw [← hJS]
    have hle : ⁅oddOrderSubgroup P, thompsonJ (baum R)⁆ ≤ oddOrderSubgroup P :=
      Campbell.commutator_le_left_of_normalizes (hJP.trans (Subgroup.le_normalizer.trans
        (normalizer_le_normalizer_oddOrderSubgroup P)))
    exact eq_of_le_of_not_lt hle fun h => hJW (hthomp.2.1 (hthomp.1.1 h))
  have hS2 : IsPGroup 2 (baum R) := hS.sylow.2.1.to_le hSR
  have hDp : IsPGroup 2 (autOn (baum R) V) := by
    rw [autOn_eq_map_conjNormal V]
    exact hS2.map _
  have himg : autOn (oddOrderSubgroup P) V = Fs := by
    rw [autOn_oddOrderSubgroup hPV, himage.image]
    exact oddOrderSubgroup_sup_seed hseed.card hDp hseed.normalized
  have hfixed : modComm V Fs ⊓ Subgroup.centralizer (oddOrderSubgroup P : Set G) = ⊥ := by
    refine eq_bot_iff.2 fun w hw => ?_
    have hwW : w ∈ modComm V Fs := hw.1
    have hwC : w ∈ Subgroup.centralizer (oddOrderSubgroup P : Set G) := hw.2
    have hwV : w ∈ V := modComm_le_V V Fs hwW
    have hfix : ∀ a ∈ Fs, ((a ⟨w, hwV⟩ : V) : G) = w := by
      intro a ha
      rw [← himg] at ha
      obtain ⟨g, hgB, rfl⟩ := mem_autOn_iff.1 ha
      rw [coe_conjAct_apply]
      have h1 := Subgroup.mem_centralizer_iff.1 hwC (g : G) hgB
      show (g : G) * w * (g : G)⁻¹ = w
      rw [h1, mul_inv_cancel_right]
    exact Subgroup.mem_bot.2 (eq_one_of_mem_modComm_of_fixed
      (fun a ha b hb => congrArg Subtype.val
        (hS.reduced.2.2.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩))
      (fun a ha => hS.reduced.2.2.1.2 a ha) hseed.card hwW hwV hfix)
  have hgen : oddOrderSubgroup P ⊔ R = ⊤ := by
    have hPle : P ≤ oddOrderSubgroup P ⊔ R := hPeq.le.trans (sup_le_sup_left hSR _)
    refine top_unique ?_
    rw [← hbasic.gen]
    exact sup_le hPle le_sup_right
  exact ⟨hPeq, hperf, himg, hfixed, hgen⟩

end CFSG.QuasithinUnique.Setup.Lift
