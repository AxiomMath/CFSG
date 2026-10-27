module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Lem3321FC
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Lem3321GP
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Ln2C
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3321GT
public import CFSG.Quasithin.Vol2.Ch3Sec3Case4CountRPf

public section
namespace CFSG.Quasithin.H13

open CFSG.Open hiding StatedSL StatedSp StatedProj
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.Quasithin.H13.L3316 (liftPre liftCore liftCore_le liftCore_eq)
open scoped commutatorElement IsMulCommutative

namespace L3321

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L D : Subgroup G}

theorem exists_coords_sum_F4 (h14 : Stmt3_3_14_F4) (hGA : GriessAllModelsStatement)
    (h : Hyp331 G T M L D)
    (e : ↥(autOn L (vPlus L T)) ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2))
    [IsMulCommutative ↥(vPlus L T)] (hmod : Mod3321Sum T L) :
    ∃ (α : ↥L →* SL4) (ρ : FLc.SLt 4 →* MulAut ↥(vPlus L T)) (U₁ U₂ : Subgroup ↥(vPlus L T)),
      Function.Surjective α ∧ α.ker = CFSG.pCore 2 ↥L ∧
      (∀ l : ↥L, α l = 1 ↔ (l : G) ∈ Subgroup.centralizer (vPlus L T : Set G)) ∧
      ((T ⊓ L).subgroupOf L).map α = FLc.Ut 4 ∧
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
  exact ⟨α, _, U₁, U₂, hαs, hαk, kerV_of_rho h hinj hαv, hαU, hαv, hdirect,
    ⟨D₁.rtwist h'⟩, ⟨D₂.rtwist h'⟩⟩

theorem false_of_char_F4 (h5 : Stmt3_3_5) (h14 : Stmt3_3_14_F4) (h : Hyp331 G T M L D)
    {S Y₁ Y₃ : Subgroup G} (hST : S ≤ T) (hTS : T ≤ Subgroup.normalizer (S : Set G))
    (hDS : D ≤ Subgroup.normalizer (S : Set G)) (hL : L ≤ Y₁ ⊔ Y₃ ⊔ T) {t₀ : G} (ht₀ : t₀ ∈ T)
    (h31 : ∀ y ∈ Y₃, t₀⁻¹ * y * t₀ ∈ Y₁) {C : Subgroup G} (hCS : C ≤ S) (hC1 : C ≠ ⊥)
    (hchar : (C.subgroupOf S).Characteristic) (hCN : Y₁ ⊔ S ≤ Subgroup.normalizer (C : Set G)) :
    False := by
  have hNS := normalizer_le_of_char hCS hchar
  have hTC : T ≤ Subgroup.normalizer (C : Set G) := hTS.trans hNS
  have hY₁ : Y₁ ≤ Subgroup.normalizer (C : Set G) := le_sup_left.trans hCN
  have hY₃ : Y₃ ≤ Subgroup.normalizer (C : Set G) := by
    intro y hy
    have h1 := hY₁ (h31 y hy)
    have h2 := hTC ht₀
    have e : y = t₀ * (t₀⁻¹ * y * t₀) * t₀⁻¹ := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ h2 h1) (Subgroup.inv_mem _ h2)
  have hN : L ⊔ T ≤ Subgroup.normalizer (C : Set G) :=
    sup_le (hL.trans (sup_le (sup_le hY₁ hY₃) hTC)) hTC
  obtain ⟨hML, -⟩ := h14 G T M L D h
  have hU := (h5 G T M L h.toSetup331).2.1
  rw [hML] at hU
  have hloc : IsTwoLocal (Subgroup.normalizer (C : Set G)) :=
    ⟨C, hC1, h.sylow.1.to_le (hCS.trans hST), rfl⟩
  obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge hloc
  have hM'eq := hU.2 M' ⟨hM', hN.trans hle⟩
  exact Hyp331.not_D_le h ((hDS.trans hNS).trans (hM'eq ▸ hle))

end L3321

theorem L3321.step3_3_21gSum_of_F4 (h5 : Stmt3_3_5) (h7 : Stmt3_3_7) (h13 : Stmt3_3_13LT_F4)
    (h14 : Stmt3_3_14_F4) (hGA : GriessAllModelsStatement) (he : Step3_3_21e_F4)
    (hC34 : CFSG.Quasithin.C134L32Corr_F4) :
    ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L D : Subgroup G), Hyp331 G T M L D →
      Nonempty (↥(autOn L (vPlus L T)) ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) →
      ∀ _ : IsMulCommutative ↥(vPlus L T), Mod3321Sum T L → InducesInnerOn T L := by
  intro G _ _ T M L D h ⟨e⟩ hc hmod
  by_contra hout
  obtain ⟨hML, hMN⟩ := h14 G T M L D h
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := h.TM.trans hMN
  obtain ⟨α, ρ, U₁, U₂, hαs, hαk, hαkV, hαU, hαv, hdirect, ⟨D₁⟩, ⟨D₂⟩⟩ :=
    L3321.exists_coords_sum_F4 h14 hGA h e hmod
  have hmod' : Mod3321 T L := ⟨hc, Or.inr hmod⟩
  have hcomm := L3321.commV_eq_top_F4 h7 h14 he h ⟨e⟩ hmod'
  rw [hcomm] at hdirect
  have he' := he G T M L D h ⟨e⟩ hmod'
  obtain ⟨S, hST, hTS, hTLS, hQS, hconj, ⟨t₀, ht₀, ht₀S, u₀, hu₀, hact, hdich⟩, hDS⟩ :=
    L3321.exists_inner_F4 h13 h hTL hαs hαk hαU hout
  have hR : L3321.RData G T M L D S α := ⟨h, hTL, hαs, hαk, hαkV, hαU, hST, hTLS, hQS, hconj⟩
  have h13' := fun y (hy : y ∈ liftCore α (FLc.QI 4 {1})) =>
    L3321.conj_Y_one (hTL ht₀) hu₀ hact hy
  have h31' := fun y (hy : y ∈ liftCore α (FLc.QI 4 {3})) =>
    L3321.conj_Y_three (hTL ht₀) hu₀ hact hy
  have hkT : α.ker.map L.subtype ≤ T := by
    rw [hαk]
    rintro _ ⟨l, hl, rfl⟩
    exact hR.RT (hR.pCoreOf_L_le_R ((Lem3328.mem_pCore_iff l).mp hl))
  have hL : L ≤ liftCore α (FLc.QI 4 {1}) ⊔ liftCore α (FLc.QI 4 {3}) ⊔ T :=
    le_sup_left.trans (Ln2.sup_liftCore_eq (Nat.card_zmod 2) le_rfl (by norm_num) hαs hkT hαU).le
  rcases hR.isMSPair_or_one with hMS | ⟨C, hCS, hC1, hchar, hCN⟩
  · obtain ⟨ψ, hψs, hψk, -⟩ := hR.exists_levi_one
    have hα₂ := L3321.isModO2Surj_comp hψs hψk
    obtain ⟨j, hj⟩ := Ln2.exists_isC134Case_F4 hC34 hMS hR.isLocal_one.2.1
      (hR.le_normalizer_Y {1}) hα₂.1 hα₂.2
    have hV16 := L3321.card_comm_ge_one h hαs hαv D₁
    rcases j with _ | _ | _ | _ | _ | _ | j
    · exact hj.elim
    · exact hR.not_case12_one hV16 (Or.inl rfl) hj
    · exact hR.not_case12_one hV16 (Or.inr rfl) hj
    · exact hR.not_case3_one hj (L3321.exists_fixed_comm_one h hαs hαv D₁)
    · exact Case4Count.case4CorrA1Twist_holds G T M L D S α t₀ hR ⟨hc, hmod⟩ ht₀ ht₀S hdich
        h13' h31' hj
    · exact hR.not_case5_one hj
    · exact hj.elim
  · exact L3321.false_of_char_F4 h5 h14 h hST hTS hDS hL ht₀ h31' hCS hC1 hchar hCN

end CFSG.Quasithin.H13
