module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Lem3321FA
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Lem3321FC
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3321FSD
public import CFSG.Quasithin.Vol2.Ch3Sec3Case4CountBoth

public section
namespace CFSG.Quasithin.H13.L3321

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Quasithin.H13.L3316 (liftPre liftCore liftCore_le)
open scoped IsMulCommutative

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L D : Subgroup G} {α : ↥L →* SL4}

variable {ρ : FLc.SLt 4 →* MulAut ↥(vPlus L T)} [IsMulCommutative ↥(vPlus L T)]

omit [IsMulCommutative ↥(vPlus L T)] in
theorem false_of_inner_sum_of_h12_F4 (h7 : Stmt3_3_7) (h14 : Stmt3_3_14_F4)
    (hGA : GriessAllModelsStatement) (he : Step3_3_21e_F4) (h15 : Step3_3_15R_F4)
    (hC34 : CFSG.Quasithin.C134L32Corr_F4) (h12 : Step3_3_12R_F4) (h : Hyp331 G T M L D)
    (e : ↥(autOn L (vPlus L T)) ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2))
    [IsMulCommutative ↥(vPlus L T)] (hmod : Mod3321Sum T L) (hin : InducesInnerOn T L) :
    False := by
  obtain ⟨α, ρ, U₁, U₂, hD, hαv, hdirect, ⟨D₁⟩, ⟨D₂⟩⟩ := exists_fdata_sum_F4 h14 hGA h e hmod hin
  have hcomm := commV_eq_top_F4 h7 h14 he h ⟨e⟩ ⟨inferInstance, Or.inr hmod⟩
  rw [hcomm] at hdirect
  obtain ⟨hsup, hdisj⟩ := hdirect
  obtain ⟨a, b, haZ, hbZ, ha1, hb1, hab, ha2, hb2, haY, hbY, hZ, hZY1, hZY3⟩ :=
    exists_Z_coords h hD hαv hsup hdisj D₁ D₂
  have hZ' : ∀ z ∈ quasithinOmegaOneCenter T, z = 1 ∨ z = b ∨ z = a ∨ z = b * a := by
    have hcomm' : a * b = b * a :=
      Subgroup.mem_centralizer_iff.mp
        ((B2F.omegaOneCenter_le_inf_centralizer T) haZ).2 b
        ((B2F.omegaOneCenter_le_inf_centralizer T) hbZ).1 |>.symm
    intro z hz
    rcases hZ z hz with h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inr (Or.inl h1))
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inr (h1.trans hcomm')))
  obtain ⟨ψ₁, hψ₁s, hψ₁k, -⟩ := hD.exists_levi_one
  obtain ⟨ψ₃, hψ₃s, hψ₃k, -⟩ := hD.exists_levi_three
  have hcase₁ : ∀ j : ℕ, C134CorrLocal.IsC134CaseCorr j (liftCore α (FLc.QI 4 {1}) ⊔ T) T
      (liftCore α (FLc.QI 4 {1})) →
      C134CorrLocal.IsC134Case4Corr (liftCore α (FLc.QI 4 {1}) ⊔ T) T
        (liftCore α (FLc.QI 4 {1})) := by
    intro j hj
    have hα₂ := isModO2Surj_comp hψ₁s hψ₁k
    have hV16 := card_comm_ge_one h hD.surj hαv D₁
    rcases j with _ | _ | _ | _ | _ | _ | j
    · exact hj.elim
    · exact (hD.not_case12 (liftCore_le α _) (hD.le_normalizer_Y {1}) hα₂ hD.card_Q_ge_one hV16
        (Or.inl rfl) hj).elim
    · exact (hD.not_case12 (liftCore_le α _) (hD.le_normalizer_Y {1}) hα₂ hD.card_Q_ge_one hV16
        (Or.inr rfl) hj).elim
    · exact (hD.not_case3 (liftCore_le α _) (hD.le_normalizer_Y {1}) hj
        (exists_fixed_comm_one h hD.surj hαv D₁)).elim
    · exact hj
    · exact (hD.not_case5_one hj).elim
    · exact hj.elim
  have hcase₃ : ∀ j : ℕ, C134CorrLocal.IsC134CaseCorr j (liftCore α (FLc.QI 4 {3}) ⊔ T) T
      (liftCore α (FLc.QI 4 {3})) →
      C134CorrLocal.IsC134Case4Corr (liftCore α (FLc.QI 4 {3}) ⊔ T) T
        (liftCore α (FLc.QI 4 {3})) := by
    intro j hj
    have hα₂ := isModO2Surj_comp hψ₃s hψ₃k
    have hV16 := card_comm_ge_three h hD.surj hαv D₂
    rcases j with _ | _ | _ | _ | _ | _ | j
    · exact hj.elim
    · exact (hD.not_case12 (liftCore_le α _) (hD.le_normalizer_Y {3}) hα₂ hD.card_Q_ge_three
        hV16 (Or.inl rfl) hj).elim
    · exact (hD.not_case12 (liftCore_le α _) (hD.le_normalizer_Y {3}) hα₂ hD.card_Q_ge_three
        hV16 (Or.inr rfl) hj).elim
    · exact (hD.not_case3 (liftCore_le α _) (hD.le_normalizer_Y {3}) hj
        (exists_fixed_comm_three h hD.surj hαv D₂)).elim
    · exact hj
    · exact (hD.not_case5_three hj).elim
    · exact hj.elim
  have ht₁ : L3312.Type3312R (↥(liftCore α (FLc.QI 4 {1})) ⧸
      CFSG.pCore 2 ↥(liftCore α (FLc.QI 4 {1}))) :=
    Or.inr (Or.inl (L3318.isPSL_of_hom le_rfl hψ₁s hψ₁k))
  have ht₃ : L3312.Type3312R (↥(liftCore α (FLc.QI 4 {3})) ⧸
      CFSG.pCore 2 ↥(liftCore α (FLc.QI 4 {3}))) :=
    Or.inr (Or.inl (L3318.isPSL_of_hom le_rfl hψ₃s hψ₃k))
  obtain ⟨i, hi, hO, -, j, hj⟩ := hD.exists_case_F4 h15 hC34
  rcases hi with rfl | rfl
  ·
    have hO₃ : pCoreOf 2 (liftCore α (FLc.QI 4 {3}) ⊔ T ⊔ D) = ⊥ := by
      by_contra hne
      obtain ⟨K, -, -, -, hc⟩ := h12 G T M L D _ h hD.mem_lFamilyOf_three hne ht₃
      rcases hc with hDY | ⟨hpsl, -, -⟩
      · exact pCoreOf_ne_bot_of_le_normalizer h haZ hbZ ha1 hb1 hab ha2 hb2 haY hbY hZ hZY3 hDY
          hO
      · exact L3318.not_isPSL_two_two le_rfl (by norm_num) hψ₃s hψ₃k hpsl
    obtain ⟨-, j', hj'⟩ := hD.msPair_case_F4 hC34 hD.mem_lFamilyOf_three (hD.le_normalizer_Y {3})
      hψ₃s hψ₃k hO₃
    exact hD.toCountData.not_case4Corr_both (hcase₁ j hj) (hcase₃ j' hj')
  ·
    have hO₁ : pCoreOf 2 (liftCore α (FLc.QI 4 {1}) ⊔ T ⊔ D) = ⊥ := by
      by_contra hne
      obtain ⟨K, -, -, -, hc⟩ := h12 G T M L D _ h hD.mem_lFamilyOf_one hne ht₁
      rcases hc with hDY | ⟨hpsl, -, -⟩
      · exact pCoreOf_ne_bot_of_le_normalizer h hbZ haZ hb1 ha1 (Ne.symm hab) hb2 ha2 hbY haY hZ'
          hZY1 hDY hO
      · exact L3318.not_isPSL_two_two le_rfl (by norm_num) hψ₁s hψ₁k hpsl
    obtain ⟨-, j', hj'⟩ := hD.msPair_case_F4 hC34 hD.mem_lFamilyOf_one (hD.le_normalizer_Y {1})
      hψ₁s hψ₁k hO₁
    exact hD.toCountData.not_case4Corr_both (hcase₁ j' hj') (hcase₃ j hj)

end CFSG.Quasithin.H13.L3321
