module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Lem3321FE
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Lem3321FF
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Lem3321StepsB
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3321FH

public section
namespace CFSG.Quasithin.H13.L3321

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.ChiefCount
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.QuasithinUnique.Vol2Native.A312L CFSG.QuasithinUnique.Setup.Lift
open CFSG.Quasithin.H13.L3316 (liftPre liftCore liftCore_le liftPre_le)
open CFSG.Quasithin.H13.Gen3324 (pre₀ mem_pre₀)
open scoped commutatorElement IsMulCommutative

variable {G : Type} [Group G]

variable [CFSG.GH74.QTGen4.Finite4 G] {T M L D : Subgroup G} {α : ↥L →* SL4}

theorem false_of_inner_ext_F4 (h7 : Stmt3_3_7) (h9 : Stmt3_3_9) (h14 : Stmt3_3_14_F4)
    (hGA : GriessAllModelsStatement) (he : Step3_3_21e_F4) (h15 : Step3_3_15R_F4)
    (hC34 : CFSG.Quasithin.C134L32Corr_F4)
    (h20 : Stmt3_3_20) (hd : Step3_3_21d_F4)
    (hfQ : Step3_3_21fQ_F4) (h : Hyp331 G T M L D)
    (e : ↥(autOn L (vPlus L T)) ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2))
    [IsMulCommutative ↥(vPlus L T)] (hmod : Mod3321Ext T L) (hin : InducesInnerOn T L) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcommL := comm_pCoreOf_le_of_inner_ext_F4 h7 h14 hGA he h15 hC34 h e hmod hin
  have hfQ' := hfQ G T M L D h ⟨e⟩ inferInstance hmod hin hcommL
  obtain ⟨α, ρ, Z₀, hD, hαv, hZ₀, -, ⟨D₀⟩⟩ := exists_fdata_ext_F4 h14 hGA h e hmod hin
  have hmod' : Mod3321 T L := ⟨inferInstance, Or.inl hmod⟩
  have hCZ := inf_centralizer_eq_of_model_F4 h9 h14 h e hD hαv D₀
  have hVL0 := vPlus_inf_centralizer_eq_bot_F4 he h ⟨e⟩ hmod' hD.TL
  have hZ₀b : Z₀ = ⊥ := eq_bot_of_le_fixV h hVL0 (hZ₀.trans inf_le_left)
  subst hZ₀b
  have hcomm := commV_eq_top_F4 h7 h14 he h ⟨e⟩ hmod'
  have hV64 := card_vPlus hcomm D₀
  have hVc := vPlus_eq_comm_F4 h7 h14 he h ⟨e⟩ hmod'
  have hVL := vPlus_le_L h hD.TL hVc
  have hTL := le_L_F4 h7 h14 hD hfQ' hVL
  have hT12 := card_le hD hTL hfQ' hV64
  have hLV : L ≤ Subgroup.normalizer (vPlus L T : Set G) :=
    le_sup_left.trans (Hyp331.vPlus_reduced h.toSetup331).2.2.2.1
  have hV2 : IsPGroup 2 ↥(vPlus L T) := h.sylow.1.to_le (vPlus_le_T h)
  have hVO : pCoreOf 2 L = vPlus L T := le_antisymm (hfQ' ▸ hD.pCoreOf_L_le le_rfl)
    (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hVL hLV hV2)
  have hTP : ∀ {P : Subgroup SL4}, FLc.Ut 4 ≤ P → T ≤ liftPre α P := fun hUP t ht =>
    ⟨⟨t, hTL ht⟩, hUP (hD.mem_Ut _ ht), rfl⟩
  have hR : L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ⊔ T =
      liftPre α P2 := by
    rw [hCZ]
    exact sup_eq_left.2 (hTP Ut_le_P2)
  have hXZ : ∀ {P : Subgroup SL4}, P ≤ P2 → liftPre α P ≤
      Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := fun hP =>
    (liftPre_mono hP).trans (hCZ ▸ inf_le_right)
  obtain ⟨hXa1, hXa2, hXa3, ⟨ea⟩, hRa, hRaT⟩ := parabolic_pkg h.sylow.1 h.sylow.2
    (hTP (FLc.Ut_le_QI 4 {2, 3})) (leviA α) (leviA_surjective hD.surj) (two_pow_of_leviA hD.ker)
  obtain ⟨hXb1, hXb2, hXb3, ⟨eb⟩, hRb, hRbT⟩ := parabolic_pkg h.sylow.1 h.sylow.2
    (hTP (FLc.Ut_le_QI 4 {1, 2})) (leviC α) (leviC_surjective hD.surj) (two_pow_of_leviC hD.ker)
  have hS : IsSylowTwoOf T (liftPre α P2) :=
    isSylowTwoOf_of_quasithinIsSylowTwo h.sylow (hTP Ut_le_P2)
  have hRle : ∀ {P : Subgroup SL4}, P ≤ P2 → FLc.Ut 4 ≤ P →
      pCoreOf 2 (liftPre α P2) ≤ pCoreOf 2 (liftPre α P) := fun hP hUP =>
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((EscapingLocal.pCoreOf_le_of_isSylowTwoOf hS).trans (hTP hUP))
      ((liftPre_mono hP).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
  have hRab : pre₀ (leviA α) ⊥ ⊓ pre₀ (leviC α) ⊥ = pCoreOf 2 (liftPre α P2) :=
    le_antisymm (inf_pre₀_le hD.ker)
      (le_inf (hRa ▸ hRle QI23_le_P2 (FLc.Ut_le_QI 4 _))
        (hRb ▸ hRle QI12_le_P2 (FLc.Ut_le_QI 4 _)))
  have hDR := hd G T M L D h ⟨e⟩ hmod'
  rw [hR] at hDR
  have hnot : ¬ (D ≤ Subgroup.normalizer (pre₀ (leviA α) ⊥ : Set G) ∧
      D ≤ Subgroup.normalizer (pre₀ (leviC α) ⊥ : Set G)) := by
    rintro ⟨ha, hb⟩
    apply Hyp331.not_D_le h
    have hDN : D ≤ Subgroup.normalizer (pCoreOf 2 (liftPre α P2) : Set G) := fun d hd' => by
      rw [← hRab]
      exact ChiefCount.mem_normalizer_inf (ha hd') (hb hd')
    exact hDN.trans hDR
  have hVR : ∀ {K : Subgroup G}, K ≤ L → T ≤ K → vPlus L T ≤ pCoreOf 2 K := fun hKL hTK =>
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ((vPlus_le_T h).trans hTK)
      (hKL.trans hLV) hV2
  have hfinal : ∀ (K : Subgroup G) (ρK : ↥K →* SL2F2), K ≤ liftPre α P2 → K ≤ L → T ≤ K →
      oTwoUpper (oTwoUpper K) = oTwoUpper K → T ≤ Subgroup.normalizer (oTwoUpper K : Set G) →
      oTwoUpper K ⊔ T = K → Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* Equiv.Perm (Fin 3)) →
      pCoreOf 2 K = pre₀ ρK ⊥ →
      (oTwoUpper K ⊓ vPlus L T).relIndex (oTwoUpper K ⊓ pre₀ ρK ⊥) ≤ 32 →
      ¬ D ≤ Subgroup.normalizer (pre₀ ρK ⊥ : Set G) → False := by
    intro K ρK hKP hKL hTK hX1 hX2 hX3 hK3 hRK hR32 hDK
    have hS3 : Nonempty (↥(oTwoUpper K ⊔ T) ⧸ CFSG.pCore 2 ↥(oTwoUpper K ⊔ T) ≃*
        Equiv.Perm (Fin 3)) := by
      rw [hX3]
      exact hK3
    have hDX : ¬ D ≤ Subgroup.normalizer (pCoreOf 2 (oTwoUpper K ⊔ T) : Set G) := by
      rw [hX3, hRK]
      exact hDK
    have key := (h20 G T M L D (oTwoUpper K) h hX1 hX2 hS3 hDX).2.2.2.2
    have hXZ' : oTwoUpper K ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
      (oTwoUpper_le K).trans (hKP.trans (hXZ le_rfl))
    have hnc := not_hasNoncentralTwoChief_five (le_conjClosure _ _) hXZ'
      (Setup.omegaOneCenterOf_ne_bot h.sylow.1 h.toSetup331.T_ne_bot) hV64
      (hRK ▸ hVR hKL hTK) ((oTwoUpper_le K).trans (hKL.trans hLV))
      ((oTwoUpper_le K).trans (hRK ▸ CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K))
      hR32 (relIndex_le_three ρK)
    have h12 := (key hnc).2.2 (center_ne_bot h hXZ')
    omega
  have hR32a := relIndex_le_32 hD QI23_le_P2 blkA (X := oTwoUpper (liftPre α (FLc.QI 4 {2, 3})))
    (oTwoUpper_le _) hVO hRaT (hRa ▸ hVR (liftPre_le α _) (hTP (FLc.Ut_le_QI 4 _)))
    (elU3_mem 0) (Ut_le_P2 (elU3_mem 0)) blkA_elU3_ne
  have hR32b := relIndex_le_32 hD QI12_le_P2 blkC (X := oTwoUpper (liftPre α (FLc.QI 4 {1, 2})))
    (oTwoUpper_le _) hVO hRbT (hRb ▸ hVR (liftPre_le α _) (hTP (FLc.Ut_le_QI 4 _)))
    (elU3_mem 2) (Ut_le_P2 (elU3_mem 2)) blkC_elU3_ne
  by_cases ha : D ≤ Subgroup.normalizer (pre₀ (leviA α) ⊥ : Set G)
  · exact hfinal _ (leviC α) (liftPre_mono QI12_le_P2) (liftPre_le α _)
      (hTP (FLc.Ut_le_QI 4 _)) hXb1 hXb2 hXb3 ⟨eb⟩ hRb hR32b fun hb => hnot ⟨ha, hb⟩
  · exact hfinal _ (leviA α) (liftPre_mono QI23_le_P2) (liftPre_le α _)
      (hTP (FLc.Ut_le_QI 4 _)) hXa1 hXa2 hXa3 ⟨ea⟩ hRa hR32a ha

end CFSG.Quasithin.H13.L3321
