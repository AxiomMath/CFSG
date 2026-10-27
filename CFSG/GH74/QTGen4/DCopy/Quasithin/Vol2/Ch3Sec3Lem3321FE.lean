module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Lem3321FA
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Lem3321FC
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3321FE
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3321FB
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3321FEFix

public section
namespace CFSG.Quasithin.H13.L3321

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Quasithin.H13.L3316 (liftPre liftCore liftCore_le)
open scoped commutatorElement IsMulCommutative

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L D : Subgroup G} {α : ↥L →* SL4}
  {ρ : FLc.SLt 4 →* MulAut ↥(vPlus L T)} [IsMulCommutative ↥(vPlus L T)]

omit [IsMulCommutative ↥(vPlus L T)] in
theorem comm_pCoreOf_le_of_inner_ext_F4 (h7 : Stmt3_3_7) (h14 : Stmt3_3_14_F4)
    (hGA : GriessAllModelsStatement) (he : Step3_3_21e_F4) (h15 : Step3_3_15R_F4)
    (hC34 : CFSG.Quasithin.C134L32Corr_F4) (h : Hyp331 G T M L D)
    (e : ↥(autOn L (vPlus L T)) ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2))
    [IsMulCommutative ↥(vPlus L T)] (hmod : Mod3321Ext T L) (hin : InducesInnerOn T L) :
    ⁅pCoreOf 2 L, L⁆ ≤ vPlus L T := by
  obtain ⟨α, ρ, Z₀, hD, hαv, -, -, ⟨D₀⟩⟩ := exists_fdata_ext_F4 h14 hGA h e hmod hin
  have hcomm := commV_eq_top_F4 h7 h14 he h ⟨e⟩ ⟨inferInstance, Or.inl hmod⟩
  have he' := he G T M L D h ⟨e⟩ ⟨inferInstance, Or.inl hmod⟩
  have hU' : ∀ v : ↥(vPlus L T), v ∈ commV (autOn L (vPlus L T)) := fun v => by
    rw [hcomm]
    exact Subgroup.mem_top _
  have hLperf : ⁅L, L⁆ = L := h.Lmax.1.2.1.2.1
  have hLV : L ≤ Subgroup.normalizer (vPlus L T : Set G) :=
    le_sup_left.trans (Hyp331.vPlus_reduced h.toSetup331).2.2.2.1
  obtain ⟨i, hi, -, -, j, hj⟩ := hD.exists_case_F4 h15 hC34
  rcases hi with rfl | rfl
  · obtain ⟨ψ, hψs, hψk, -⟩ := hD.exists_levi_one
    have hα₂ := isModO2Surj_comp hψs hψk
    have hV64 := card_comm_ge_ext_one h hD.surj hαv D₀
    have hY1 : ∃ y : ↥L, (y : G) ∈ liftCore α (FLc.QI 4 {1}) ∧ α y ≠ 1 := by
      obtain ⟨y, hy, hye⟩ := L3318.exists_mem_liftCore hD.surj
        (tr_mem_one_levi (a := 1) (c := 2) (by decide) (by decide) (by decide))
      refine ⟨⟨y, liftCore_le α _ hy⟩, hy, ?_⟩
      rw [hye]
      intro h1
      have := congrArg (fun g : SL4 => (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) 1 2) h1
      simp [SpecialLinearGroup.transvection_coe] at this
    rcases j with _ | _ | _ | _ | _ | _ | j
    · exact hj.elim
    · exact (hD.not_case12 (liftCore_le α _) (hD.le_normalizer_Y {1}) hα₂ hD.card_Q_ge_one
        (by omega) (Or.inl rfl) hj).elim
    · exact (hD.not_case12 (liftCore_le α _) (hD.le_normalizer_Y {1}) hα₂ hD.card_Q_ge_one
        (by omega) (Or.inr rfl) hj).elim
    · exact comm_pCoreOf_le_of hD.surj hD.ker hLperf hLV (liftCore_le α _) hY1
        ((hD.comm_le_of_case3 (liftCore_le α _) (hD.le_normalizer_Y {1}) hα₂ hD.card_Q_ge_one
          hV64 hj).trans (Ch1Sec3.commutator_le_left_of_le_normalizer
            ((liftCore_le α _).trans hLV)))
    · exact (not_case4Corr_ext hD h hαv hU' D₀ hfix_wedge_one he'
        (hD.le_normalizer_Y {1}) hj).elim
    · exact (hD.not_case5_one hj).elim
    · exact hj.elim
  · obtain ⟨ψ, hψs, hψk, -⟩ := hD.exists_levi_three
    have hα₂ := isModO2Surj_comp hψs hψk
    have hV64 := card_comm_ge_ext_three h hD.surj hαv D₀
    have hY1 : ∃ y : ↥L, (y : G) ∈ liftCore α (FLc.QI 4 {3}) ∧ α y ≠ 1 := by
      obtain ⟨y, hy, hye⟩ := L3318.exists_mem_liftCore hD.surj
        (tr_mem_three_levi (a := 0) (c := 1) (by decide) (by decide) (by decide))
      refine ⟨⟨y, liftCore_le α _ hy⟩, hy, ?_⟩
      rw [hye]
      intro h1
      have := congrArg (fun g : SL4 => (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) 0 1) h1
      simp [SpecialLinearGroup.transvection_coe] at this
    rcases j with _ | _ | _ | _ | _ | _ | j
    · exact hj.elim
    · exact (hD.not_case12 (liftCore_le α _) (hD.le_normalizer_Y {3}) hα₂ hD.card_Q_ge_three
        (by omega) (Or.inl rfl) hj).elim
    · exact (hD.not_case12 (liftCore_le α _) (hD.le_normalizer_Y {3}) hα₂ hD.card_Q_ge_three
        (by omega) (Or.inr rfl) hj).elim
    · exact comm_pCoreOf_le_of hD.surj hD.ker hLperf hLV (liftCore_le α _) hY1
        ((hD.comm_le_of_case3 (liftCore_le α _) (hD.le_normalizer_Y {3}) hα₂ hD.card_Q_ge_three
          hV64 hj).trans (Ch1Sec3.commutator_le_left_of_le_normalizer
            ((liftCore_le α _).trans hLV)))
    · exact (not_case4Corr_ext hD h hαv hU' D₀ hfix_wedge_three he'
        (hD.le_normalizer_Y {3}) hj).elim
    · exact (hD.not_case5_three hj).elim
    · exact hj.elim

end CFSG.Quasithin.H13.L3321
