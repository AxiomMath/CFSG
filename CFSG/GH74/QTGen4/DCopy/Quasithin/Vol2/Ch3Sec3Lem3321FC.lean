module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Lem3321Steps
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Statements
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3321FC

public section
namespace CFSG.Quasithin.H13.L3321

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped commutatorElement IsMulCommutative

variable {G : Type} [Group G]

variable [CFSG.GH74.QTGen4.Finite4 G] {T M L D : Subgroup G}

theorem vPlus_eq_comm_F4 (h7 : Stmt3_3_7) (h14 : Stmt3_3_14_F4) (he : Step3_3_21e_F4)
    (h : Hyp331 G T M L D)
    (e : Nonempty (↥(autOn L (vPlus L T)) ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)))
    (hmod : Mod3321 T L) : ⁅vPlus L T, L⁆ = vPlus L T := by
  obtain ⟨hML, -⟩ := h14 G T M L D h
  obtain ⟨-, -, -, -, hV⟩ := h7 G T M L D h
  rw [hML, he G T M L D h e hmod, sup_bot_eq] at hV
  exact hV.symm

theorem commV_eq_top_F4 (h7 : Stmt3_3_7) (h14 : Stmt3_3_14_F4) (he : Step3_3_21e_F4)
    (h : Hyp331 G T M L D)
    (e : Nonempty (↥(autOn L (vPlus L T)) ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)))
    [IsMulCommutative ↥(vPlus L T)] (hmod : Mod3321 T L) :
    commV (autOn L (vPlus L T)) = ⊤ := by
  rw [Ln2.commV_autOn_eq h]
  show (⁅vPlus L T, L⁆).subgroupOf (vPlus L T) = ⊤
  rw [vPlus_eq_comm_F4 h7 h14 he h e hmod]
  exact Subgroup.subgroupOf_self _

theorem exists_fdata_sum_F4 (h14 : Stmt3_3_14_F4) (hGA : GriessAllModelsStatement)
    (h : Hyp331 G T M L D)
    (e : ↥(autOn L (vPlus L T)) ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2))
    [IsMulCommutative ↥(vPlus L T)] (hmod : Mod3321Sum T L) (hin : InducesInnerOn T L) :
    ∃ (α : ↥L →* SL4) (ρ : FLc.SLt 4 →* MulAut ↥(vPlus L T)) (U₁ U₂ : Subgroup ↥(vPlus L T)),
      FData G T M L D α ∧
      (∀ l : ↥L, ρ (α l) = conjAct (vPlus L T) ⟨l, L3317.le_normalizer_vPlus h l.2⟩) ∧
      IsIntDirect U₁ U₂ (commV (autOn L (vPlus L T))) ∧
      Nonempty (FLc.VModel 4 ρ U₁ ⊥ (Multiplicative (FLc.Vt 4)) (fun g a => FLc.actM g a)) ∧
      Nonempty (FLc.VModel 4 ρ U₂ ⊥ (Multiplicative (FLc.Vt 4)) FLc.actDl) := by
  obtain ⟨hML, hMN⟩ := h14 G T M L D h
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := h.TM.trans hMN
  obtain ⟨hVe, hLV, -, -, -, -, -⟩ := setting_facts h hTL
  obtain ⟨-, π, U₁, U₂, hdirect, hreal1, hreal2⟩ := hmod
  obtain ⟨D₁⟩ := FLc.vmodelNat hreal1
    (fun g _ z hz => by rw [Subgroup.mem_bot.1 hz]; exact map_one g)
  obtain ⟨D₂⟩ := FLc.vmodelDual hreal2
    (fun g _ z hz => by rw [Subgroup.mem_bot.1 hz]; exact map_one g)
  obtain ⟨h', hinj, hr1, hr2, hU⟩ := exists_normalized_eq hVe hLV (L3317.isSylowTwoOf_inf h hTL)
    (by norm_num) (FLc.rhoOf π) (FLc.rhoOf_surj hreal1.1) (FLc.rhoOf_mem π)
    (exists_ne_one e (FLc.rhoOf_surj hreal1.1))
  obtain ⟨α, hαs, hαk, hαU, hαv⟩ := exists_alpha_of_rho h hGA hTL e hinj hr1 hr2 hU
  exact ⟨α, _, U₁, U₂, ⟨h, hTL, hαs, hαk, kerV_of_rho h hinj hαv, hαU, hin⟩, hαv, hdirect,
    ⟨D₁.rtwist h'⟩, ⟨D₂.rtwist h'⟩⟩

theorem exists_fdata_ext_F4 (h14 : Stmt3_3_14_F4) (hGA : GriessAllModelsStatement)
    (h : Hyp331 G T M L D)
    (e : ↥(autOn L (vPlus L T)) ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2))
    [IsMulCommutative ↥(vPlus L T)] (hmod : Mod3321Ext T L) (hin : InducesInnerOn T L) :
    ∃ (α : ↥L →* SL4) (ρ : FLc.SLt 4 →* MulAut ↥(vPlus L T)) (Z₀ : Subgroup ↥(vPlus L T)),
      FData G T M L D α ∧
      (∀ l : ↥L, ρ (α l) = conjAct (vPlus L T) ⟨l, L3317.le_normalizer_vPlus h l.2⟩) ∧
      Z₀ ≤ fixV (autOn L (vPlus L T)) ⊓ commV (autOn L (vPlus L T)) ∧ Nat.card ↥Z₀ ≤ 2 ∧
      Nonempty (FLc.VModel 4 ρ (commV (autOn L (vPlus L T))) Z₀
        (Multiplicative (⋀[ZMod 2]^2 (Fin 4 → ZMod 2))) FLc.actW) := by
  obtain ⟨hML, hMN⟩ := h14 G T M L D h
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := h.TM.trans hMN
  obtain ⟨hVe, hLV, -, -, -, -, -⟩ := setting_facts h hTL
  obtain ⟨Z₀, hZ₀, hZ₀2, π, hπ⟩ := hmod
  obtain ⟨D₀⟩ := FLc.vmodelExtSq hπ (fun g hg z hz => (hZ₀.trans inf_le_left) hz g hg)
  obtain ⟨h', hinj, hr1, hr2, hU⟩ := exists_normalized_eq hVe hLV (L3317.isSylowTwoOf_inf h hTL)
    (by norm_num) (FLc.rhoOf π) (FLc.rhoOf_surj hπ.1) (FLc.rhoOf_mem π)
    (exists_ne_one e (FLc.rhoOf_surj hπ.1))
  obtain ⟨α, hαs, hαk, hαU, hαv⟩ := exists_alpha_of_rho h hGA hTL e hinj hr1 hr2 hU
  exact ⟨α, _, Z₀, ⟨h, hTL, hαs, hαk, kerV_of_rho h hinj hαv, hαU, hin⟩, hαv, hZ₀, hZ₀2,
    ⟨D₀.rtwist h'⟩⟩

end CFSG.Quasithin.H13.L3321
