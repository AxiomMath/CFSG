module

public import CFSG.GH74.Generic.BProg.B3.DictS1Three

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg
  CFSG.Assembly.LowTwoRank Subgroup DictS1Three

namespace DictS1High

section E8

variable {F : Type} [Field F] [Finite F]

theorem exists_e8_xy (M : ModelData F) (h2 : (2 : F) ≠ 0)
    (hr : CFSG.GH74.GLS.Stage2.Final.ModelBlock.dRefl F ∈ M.U2)
    (hcenter : ∀ g : ↥M.K4, g ∈ Subgroup.center ↥M.K4 ↔
      (g : GL (Fin 4) F) = 1 ∨ (g : GL (Fin 4) F) = xGL F)
    (hone : ∀ t : ↥M.K4, t * t = 1 → t ≠ 1 → t ∉ Subgroup.center ↥M.K4 →
      ∃ k : ↥M.K4, k * t * k⁻¹ = M.yK) :
    ∃ E : Subgroup ↥M.K4, CFSG.IsElementaryAbelian 2 ↥E ∧ Nat.card ↥E = 8 ∧ M.xK ∈ E ∧ M.yK ∈ E := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨E, hEel, hE8⟩ := B1.PilotS1.exists_e8_model M h2 hr
  have hxE := B1.PilotS1.e8_mem_xK M h2 hcenter hone E hEel hE8
  obtain ⟨t, htE, ht1, htx⟩ : ∃ t ∈ E, t ≠ 1 ∧ t ≠ M.xK := by
    by_contra hcon
    push Not at hcon
    have hle : E ≤ zpowers M.xK := by
      intro v hv
      by_cases h1 : v = 1
      · rw [h1]
        exact Subgroup.one_mem _
      · rw [hcon v hv h1]
        exact Subgroup.mem_zpowers _
    have := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers, M.orderOf_xK h2] at this
    omega
  have htt : t * t = 1 := by
    rw [← pow_two]
    exact elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := E) t htE
  have htc : t ∉ Subgroup.center ↥M.K4 := by
    intro hc
    rcases (hcenter t).1 hc with h | h
    · exact ht1 (Subtype.ext h)
    · exact htx (Subtype.ext h)
  obtain ⟨k, hk⟩ := hone t htt ht1 htc
  have hxc : M.xK ∈ Subgroup.center ↥M.K4 := (hcenter _).2 (Or.inr rfl)
  refine ⟨E.map (MulAut.conj k).toMonoidHom, IsElementaryAbelian.map _, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective (MulAut.conj k).injective, hE8]
  · refine ⟨M.xK, hxE, ?_⟩
    change k * M.xK * k⁻¹ = M.xK
    rw [Subgroup.mem_center_iff.1 hxc k, mul_inv_cancel_right]
  · exact ⟨t, htE, hk⟩

end E8

section Uni

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]

open DictS1Model in
theorem uniBlk_zero_one_eq_J2 (hF : Nat.card F = (p ^ f) ^ 2) :
    S1.SymBlocksUni.uniBlk F (p ^ f) 0 1 = (ModelData.uni hF).J2 := by
  ext g
  constructor
  · intro hg
    have hid : S1.IsBlockAt 0 1 ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := hg.1
    set A : Matrix (Fin 2) (Fin 2) F :=
      !![((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) 0 0, ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) 0 1;
        ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) 1 0, ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) 1 1]
      with hA
    have hM : ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = blk4 A 1 := eq_blk4_left hid
    obtain ⟨hdet, hU⟩ := S1.SymBlocksUni.unitary_of_mem_statedSU hF g
    have hdetA : A.det = 1 := by
      have := congrArg Matrix.det hM
      rw [det_blk4, Matrix.det_one, mul_one, hdet] at this
      exact this.symm
    have hUA : CFSG.LieType.Universal.Unitary.conjTr (CFSG.LieType.BorelTits.unitaryInvolution F p f) A * A = 1 := by
      rw [hM, conjTr_blk4, blk4_mul, CFSG.LieType.Universal.Unitary.conjTr_one, Matrix.one_mul,
        ← blk4_one] at hU
      exact (blk4_inj hU).1
    let a : GL (Fin 2) F := Matrix.GeneralLinearGroup.mkOfDetNeZero A (by rw [hdetA]; exact one_ne_zero)
    change (g : GL (Fin 4) F) ∈ (StatedSU 2 (p ^ f) F).map (blkL F)
    refine ⟨a, ?_, ?_⟩
    · rw [SetLike.mem_coe, ← CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hF 2]
      exact ⟨hdetA, hUA⟩
    · apply Units.ext
      rw [blkL_apply, coe_diagGL, hM]
      rfl
  · intro hg
    have hg' : (g : GL (Fin 4) F) ∈ (StatedSU 2 (p ^ f) F).map (blkL F) := hg
    obtain ⟨a, -, hga⟩ := hg'
    rw [S1.SymBlocksUni.mem_uniBlk_iff hF]
    show S1.IsBlockAt 0 1 ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)
    rw [← hga, blkL_apply, coe_diagGL]
    exact isBlockAt_blk4_left _

open DictS1Model in
theorem uniBlk_two_three_eq_J4 (hF : Nat.card F = (p ^ f) ^ 2) :
    S1.SymBlocksUni.uniBlk F (p ^ f) 2 3 = (ModelData.uni hF).J4 := by
  ext g
  constructor
  · intro hg
    have hid : S1.IsBlockAt 2 3 ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := hg.1
    set B : Matrix (Fin 2) (Fin 2) F :=
      !![((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) 2 2, ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) 2 3;
        ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) 3 2, ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) 3 3]
      with hB
    have hM : ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = blk4 1 B := eq_blk4_right hid
    obtain ⟨hdet, hU⟩ := S1.SymBlocksUni.unitary_of_mem_statedSU hF g
    have hdetB : B.det = 1 := by
      have := congrArg Matrix.det hM
      rw [det_blk4, Matrix.det_one, one_mul, hdet] at this
      exact this.symm
    have hUB : CFSG.LieType.Universal.Unitary.conjTr (CFSG.LieType.BorelTits.unitaryInvolution F p f) B * B = 1 := by
      rw [hM, conjTr_blk4, blk4_mul, CFSG.LieType.Universal.Unitary.conjTr_one, Matrix.one_mul,
        ← blk4_one] at hU
      exact (blk4_inj hU).2
    let b : GL (Fin 2) F := Matrix.GeneralLinearGroup.mkOfDetNeZero B (by rw [hdetB]; exact one_ne_zero)
    change (g : GL (Fin 4) F) ∈ (StatedSU 2 (p ^ f) F).map (blkR F)
    refine ⟨b, ?_, ?_⟩
    · rw [SetLike.mem_coe, ← CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hF 2]
      exact ⟨hdetB, hUB⟩
    · apply Units.ext
      rw [blkR_apply, coe_diagGL, hM]
      rfl
  · intro hg
    have hg' : (g : GL (Fin 4) F) ∈ (StatedSU 2 (p ^ f) F).map (blkR F) := hg
    obtain ⟨b, -, hgb⟩ := hg'
    rw [S1.SymBlocksUni.mem_uniBlk_iff hF]
    show S1.IsBlockAt 2 3 ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)
    rw [← hgb, blkR_apply, coe_diagGL]
    exact isBlockAt_blk4_right _

omit [Finite F] [Fact p.Prime] in
theorem two_ne_zero_of_uni (hp2 : p ≠ 2) : (2 : F) ≠ 0 :=
  Ring.two_ne_zero (by rw [ringChar.eq F p]; exact hp2)

omit [Fact p.Prime] [CharP F p] in
theorem five_le_of_uni (hF : Nat.card F = (p ^ f) ^ 2) (hq : p ^ f % 4 = 1) : 5 ≤ p ^ f := by
  have h1 : 1 < Nat.card F := Finite.one_lt_card
  rw [hF] at h1
  have h2 : 1 < p ^ f := by
    by_contra hle
    have h' : p ^ f ≤ 1 := by omega
    have : (p ^ f) ^ 2 ≤ 1 := by
      calc (p ^ f) ^ 2 ≤ 1 ^ 2 := Nat.pow_le_pow_left h' 2
        _ = 1 := by norm_num
    omega
  omega

theorem splitAt_uniBlk (hF : Nat.card F = (p ^ f) ^ 2) (hq : p ^ f % 4 = 1) (hp2 : p ≠ 2) :
    B1.PilotS1.SplitAt ↥(CFSG.LieType.Steinberg.fixedSubfield F p f)
      (⊤ : Subgroup ↥(StatedSU 4 (p ^ f) F)) (ModelData.uni hF).xK (ModelData.uni hF).yK
      (S1.SymBlocksUni.uniBlk F (p ^ f) 0 1) (S1.SymBlocksUni.uniBlk F (p ^ f) 2 3) := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_uni hp2
  obtain ⟨e2⟩ := nonempty_sl2_equiv_uni_H2 hF
  have hsq : Nat.card ↥(CFSG.LieType.Steinberg.fixedSubfield F p f) < 4 →
      ∀ c : F, c ≠ 0 → c * c = 1 := fun hlt => by
    rw [CFSG.LieType.Steinberg.card_fixedSubfield hF] at hlt
    have := five_le_of_uni hF hq
    omega
  rw [uniBlk_zero_one_eq_J2 hF, uniBlk_two_three_eq_J4 hF]
  exact B1.PilotS1.splitAt_yK (ModelData.uni hF) h2 e2 hsq

@[expose] noncomputable def uniFrameModel (hF : Nat.card F = (p ^ f) ^ 2) (hq : p ^ f % 4 = 1)
    (hp2 : p ≠ 2) :
    FrameModel (StatedSU 4 (p ^ f) F) ↥(CFSG.LieType.Steinberg.fixedSubfield F p f) where
  x0 := (ModelData.uni hF).xK
  y0 := (ModelData.uni hF).yK
  B01 := S1.SymBlocksUni.uniBlk F (p ^ f) 0 1
  B23 := S1.SymBlocksUni.uniBlk F (p ^ f) 2 3
  split := splitAt_uniBlk hF hq hp2
  cen := fun s hs hs1 => by
    rcases (mem_center_statedSU_four_iff hF hq s).1 hs with h | h
    · exact absurd (Subtype.ext h) hs1
    · exact Subtype.ext h
  inv := fun z hz hzz hz1 => by
    have h2 : (2 : F) ≠ 0 := two_ne_zero_of_uni hp2
    obtain ⟨hdet, -⟩ := S1.SymBlocksUni.unitary_of_mem_statedSU hF z
    have hsq : ((z : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
        ((z : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = 1 := by
      have := congrArg (fun w : ↥(StatedSU 4 (p ^ f) F) =>
        ((w : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) hzz
      simpa using this
    have hne : ((z : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) ≠ 1 := by
      intro h
      apply hz1
      exact Subtype.ext (Units.ext (by simpa using h))
    have hzmat := S1.eq_zblk_of_involution h2 (by decide : (2 : Fin 4) ≠ 3) hz.1 hsq hdet hne
    apply Subtype.ext
    apply Units.ext
    change ((xGL F : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
        ((z : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = ((yGL F : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)
    rw [xGL_eq_neg_one, hzmat, ← zblkMat_zero_one_eq_yGL, Units.val_neg, Units.val_one, neg_mul, one_mul,
      S1.neg_zblkMat_eq (a := 0) (b := 1) (c := 2) (d := 3) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)]
  x0_ord := (ModelData.uni hF).orderOf_xK (two_ne_zero_of_uni hp2)
  y0_ne_one := (ModelData.uni hF).yK_ne_one (two_ne_zero_of_uni hp2)
  y0_ne_x0 := (ModelData.uni hF).yK_ne_xK (two_ne_zero_of_uni hp2)
  e8 := exists_e8_xy (ModelData.uni hF) (two_ne_zero_of_uni hp2)
    (CFSG.GH74.GLS.Stage2.Final.ModelBlock.dRefl_mem_uni (F := F)) (mem_center_uni_iff hF hq)
    (hone_of_model _ (mem_center_uni_iff hF hq)
      (fun t hT h1 hm1 => hmat_uni hF (two_ne_zero_of_uni hp2) t hT h1 hm1))
  grp := by
    have h2 : (2 : F) ≠ 0 := two_ne_zero_of_uni hp2
    obtain ⟨e2⟩ := nonempty_sl2_equiv_uni_H2 hF
    have hsq : Nat.card ↥(CFSG.LieType.Steinberg.fixedSubfield F p f) < 4 →
        ∀ c : F, c ≠ 0 → c * c = 1 := fun hlt => by
      rw [CFSG.LieType.Steinberg.card_fixedSubfield hF] at hlt
      have := five_le_of_uni hF hq
      omega
    exact ⟨(ModelData.uni hF).xK, B1.PilotS1.grpS1_of_model (ModelData.uni hF) h2
      (CFSG.GH74.GLS.Stage2.Final.ModelBlock.dRefl_mem_uni (F := F)) e2 hsq (mem_center_uni_iff hF hq)
      (hone_of_model _ (mem_center_uni_iff hF hq) (fun t hT h1 hm1 => hmat_uni hF h2 t hT h1 hm1))⟩

end Uni

end DictS1High

section Assembly

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F]

theorem nbhdDataJ_of_frameModel {S : Subgroup (GL (Fin 4) F)} {F' : Type} [Field F'] [Finite F']
    (M : FrameModel S F') (hodd' : Odd (Nat.card F')) (hbig' : 4 ≤ Nat.card F')
    {x : G} {K : Subgroup (CentralizerBar x)} (hset : S1.S1Setup G x K) (hmax : IsJMax x K)
    (hfront : S1.S1Front G x K) (D : S1.LayerData x S) (hDK : D.K = K)
    {L : Subgroup G} {c : G} (hcJ : c ∈ M.B23.map D.ι) (hc2 : orderOf c = 2)
    (hLC : L ≤ centralizer ({c} : Set G)) (hLq : IsQuasisimple ↥L) (hJL : M.B01.map D.ι ≤ L)
    (hLcen : ∀ z ∈ L, (∀ w ∈ L, z * w = w * z) → Odd (orderOf z)) :
    NbhdDataJ G x c L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hx : orderOf x = 2 := hset.inv
  have hg2 : GLS.InG2 ↥K := hmax.1.2.2
  have hmin : ∀ (z : G) (L : Subgroup (CentralizerBar z)), G2Pair z L → d2 ↥K ≤ d2 ↥L :=
    fun z L hp => (hmax.2 z L hp).1
  have hNo : NoAltJ2 G :=
    noAltJ2_of_minDepth hset.simple hset.nonab hset.rank hset.kgh hx hset.comp hg2 hmin
      (Or.inl (d2_eq_six_of_shapeS1 hset.comp hg2 hset.shape))
  have hxK : xbar x ∈ D.K := by
    rw [hDK]
    exact hset.shape.2
  obtain ⟨hxι, hxcι, -, hy2, hyne, hJle, hS⟩ := frame_split_gen M hx D hxK hcJ hc2
  rw [hDK] at hS
  set Iw : Subgroup G := (⊤ : Subgroup ↥S).map D.ι with hIw
  have hKq : IsQuasisimple ↥D.K := by
    rw [hDK]
    exact hset.comp.1
  have hIwP : IsPCompIn 2 (centralizer ({x} : Set G)) Iw := isPCompIn_range_ι D hKq
  have himg : S3.imgBar x Iw = K := (imgBar_range_ι D).trans hDK
  have hOnly : S3.OnlyInvX x K := by
    intro w hw' hw2
    rw [hfront.cent_eq] at hw'
    rcases B1.PilotS5.mem_zpowers_of_two (B1.PilotS5.orderOf_xbar hx) hw' with h | h
    · rw [h, orderOf_one] at hw2
      omega
    · exact h
  have hJ2 : IsJ2 x Iw :=
    isJ2_of_isPCompIn hset.simple hset.nonab hset.rank hset.kgh hx hset.comp hg2 hmin hOnly hIwP himg
  obtain ⟨E, hEel, hE8, hxE, hyE⟩ := M.e8
  set A : Subgroup G := E.map D.ι with hA
  have hAIw : A ≤ Iw := Subgroup.map_mono le_top
  have hAel : CFSG.IsElementaryAbelian 2 ↥A := IsElementaryAbelian.map _
  have hA8 : Nat.card ↥A = 8 := by
    rw [hA, Subgroup.card_map_of_injective D.ι_injective, hE8]
  have hxA : x ∈ A := by
    rw [hxι]
    exact ⟨_, hxE, rfl⟩
  have hyA : x * c ∈ A := by
    rw [hxcι]
    exact ⟨_, hyE, rfl⟩
  obtain ⟨eK⟩ := B1.PilotS5.hat_equiv_imgBar hIwP
  have eKK : (↥Iw ⧸ pPrimeCore 2 ↥Iw) ≃* ↥K := eK.trans (MulEquiv.subgroupCongr himg)
  have hQ1 : QShape1 (↥Iw ⧸ pPrimeCore 2 ↥Iw) := hset.shape.1.of_mulEquiv eKK.symm
  have hsrc : IsSource2 x Iw A := ⟨hAIw.trans hIwP.1, hAel, hA8, Or.inl ⟨hAIw, hQ1⟩⟩
  have eP : (↥Iw ⧸ pPrimeCore 2 ↥Iw) ≃* ↥S :=
    eKK.trans ((MulEquiv.subgroupCongr hDK).symm.trans D.iso)
  obtain ⟨z₀, hP⟩ := M.grp
  obtain ⟨-, -, -, hY, hCY, -⟩ := B1.PilotS1.shape1_data hset.gen4 hx hIwP eP hP hQ1
  have hS' : B1.PilotS1.SplitAt F' (S3.imgBar x Iw) (xbar x) (bar x (x * c))
      (S3.imgBar x (M.B01.map D.ι)) (S3.imgBar x (M.B23.map D.ι)) := by
    rw [himg]
    exact hS
  have hadm := isAdmPair_of_splitAt hodd' hbig' hx hIwP hY hCY hAIw hAel hA8 hxA hyA hy2 hyne hS'
  have hy01 : x * c ∈ M.B01.map D.ι := by
    rw [hxcι]
    exact ⟨_, M.split.u_mem, rfl⟩
  have hyy : (x * c) * (x * c) = 1 := by
    rw [← sq, ← hy2]
    exact pow_orderOf_eq_one _
  refine nbhdDataJ_of_parts (B := oPrimeResidualOf 2 (M.B01.map D.ι)) hNo hJ2 hsrc hadm ?_ ?_ hLC ?_ ?_
  · have e : c = x⁻¹ * (x * c) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.subset_closure (by simp)))
      (Subgroup.subset_closure (by simp))
  · rintro rfl
    rw [orderOf_one] at hc2
    omega
  · exact oPrimeResidual_le_liftAt (fun a ha => (hJle ha).1) (fun a ha => (hJle ha).2) le_rfl
  · refine le_iSup_conj_of_quasisimple hLq ((Subgroup.map_subtype_le _).trans hJL)
      ⟨x * c, B1.PilotS1.mem_oPrimeResidualOf_of_two hy01 hyy, ?_⟩
    by_contra hall
    push Not at hall
    have hodd2 := hLcen (x * c) (hJL hy01) hall
    rw [hy2] at hodd2
    exact absurd hodd2 (by decide)

end Assembly

open DictS1High in
theorem dictS1HighJ_proved : DictS1HighJ := by
  intro hExact G _ _ x K hset hmax _hthin hfront hbig u hu hf hsym c hcJ hc2 _hcc
  obtain ⟨hLC, hLq⟩ := S1.s1_Lxy_data_high hExact hset hfront hbig hf hsym hcJ
  obtain ⟨-, -, hXc, -, -⟩ := S1.symX_facts hset.shape.2 hset.inv hf
  have hw : ∀ e j, S1.symX x u (e.succAbove j) ∈ centralizer ({S1.symX x u e} : Set G) := fun e j =>
    Subgroup.mem_centralizer_singleton_iff.2 (hXc _ _)
  rcases id hsym with ⟨F, _, _, hF, hlin⟩ | ⟨q, F, _, _, hF, hq, huni⟩
  ·
    have h4 : 3 < Nat.card F := S1.three_lt_card_of_largeModel hbig hF (S1.sym_model_four hfront hlin)
    have h2 : (2 : F) ≠ 0 := two_ne_zero_of_mod_four hF
    have hloc : ∀ e : Fin 5, ∃ (K' : Subgroup (CentralizerBar (S1.symX x u e)))
        (hw' : ∀ j, S1.symX x u (e.succAbove j) ∈ centralizer ({S1.symX x u e} : Set G)),
          S1.S1Setup G (S1.symX x u e) K' ∧ S1.S1Front G (S1.symX x u e) K' ∧
          ∃ e' : ↥K' ≃* ↥(StatedSL 4 F), ∀ j,
            S1.ActsAsReflOn e' (barOf (hw' j)) (S1.reflDiag F j) := by
      intro e
      obtain ⟨K', hw', hset', hfront', -, e', he'⟩ := hlin e
      exact ⟨K', hw', hset', hfront', e', he'⟩
    choose D hDK hDact using S1.sym_layerData hExact x u hw hloc
    have h1 := S1.symJ_one (S1.linBlockOps hF h4) (S1.symX x u) D hw hDact
    have h3 := S1.symJ_three (S1.linBlockOps hF h4) (S1.symX x u) D hw hDact
    rw [S1.linBlockOps_blk] at h1 h3
    set D4 : S1.LayerData x (StatedSL 4 F) := D 4 with hD4
    have h1' : S1.symJ (S1.symX x u) 1 = (S1.blkLin (F := F) 0 1).map D4.ι := h1
    have h3' : S1.symJ (S1.symX x u) 3 = (S1.blkLin (F := F) 2 3).map D4.ι := h3
    have hDK4 : D4.K = K := (hDK 4).trans hfront.layer_eq
    obtain ⟨⟨-, hpair⟩, -⟩ := S1.sym_a4_lin hExact hset hf hF h4 hlin
    obtain ⟨W, hW⟩ := hpair 0 1 rfl
    obtain ⟨hWe, -⟩ := S1.lin_pair_fusion h2 hW
    obtain ⟨-, hWc⟩ := S1.lin_pair_W_facts hW
    have hcJ3 : c ∈ (linFrameModel hF).B23.map D4.ι := by
      change c ∈ (S1.blkLin (F := F) 2 3).map D4.ι
      rw [← h3']
      exact hcJ
    have hJL : (linFrameModel hF).B01.map D4.ι ≤ S1.symJ (S1.symX x u) 0 ⊔ S1.symJ (S1.symX x u) 1 := by
      change (S1.blkLin (F := F) 0 1).map D4.ι ≤ _
      rw [← h1']
      exact le_sup_right
    refine nbhdDataJ_of_frameModel (linFrameModel hF) (Nat.odd_iff.2 (by omega)) (by omega) hset hmax
      hfront D4 hDK4 hcJ3 hc2 hLC hLq hJL ?_
    intro z hz hzc
    rw [← hWe] at hz hzc
    exact hWc z hz hzc
  ·
    obtain ⟨p, f, hud, hqpf, hp2⟩ := S1.FrameUni.exists_unitaryFieldData hF hq
    have : Fact p.Prime := ⟨hud.prime⟩
    have : CharP F p := hud.charP
    subst hqpf
    have hodd : Odd (p ^ f) := Nat.odd_iff.2 (by omega)
    have hloc : ∀ e : Fin 5, ∃ (K' : Subgroup (CentralizerBar (S1.symX x u e)))
        (hw' : ∀ j, S1.symX x u (e.succAbove j) ∈ centralizer ({S1.symX x u e} : Set G)),
          S1.S1Setup G (S1.symX x u e) K' ∧ S1.S1Front G (S1.symX x u e) K' ∧
          ∃ e' : ↥K' ≃* ↥(StatedSU 4 (p ^ f) F), ∀ j,
            S1.ActsAsReflOn e' (barOf (hw' j)) (S1.reflDiag F j) := by
      intro e
      obtain ⟨K', hw', hset', hfront', -, e', he'⟩ := huni e
      exact ⟨K', hw', hset', hfront', e', he'⟩
    choose D hDK hDact using S1.sym_layerData hExact x u hw hloc
    have h1 := S1.symJ_one (S1.uniBlockOps hF hq) (S1.symX x u) D hw hDact
    have h3 := S1.symJ_three (S1.uniBlockOps hF hq) (S1.symX x u) D hw hDact
    rw [S1.uniBlockOps_blk] at h1 h3
    set D4 : S1.LayerData x (StatedSU 4 (p ^ f) F) := D 4 with hD4
    have h1' : S1.symJ (S1.symX x u) 1 = (S1.SymBlocksUni.uniBlk F (p ^ f) 0 1).map D4.ι := h1
    have h3' : S1.symJ (S1.symX x u) 3 = (S1.SymBlocksUni.uniBlk F (p ^ f) 2 3).map D4.ι := h3
    have hDK4 : D4.K = K := (hDK 4).trans hfront.layer_eq
    obtain ⟨⟨-, hpair⟩, -⟩ := S1.sym_a4_uni hExact hset hf hF hq huni p f hp2 rfl
    obtain ⟨W, hW⟩ := hpair 0 1 rfl
    obtain ⟨hWe, -⟩ := S1.uni_pair_fusion hF hodd hW
    obtain ⟨-, hWc⟩ := S1.uni_pair_W_facts hF hodd hW
    have hcJ3 : c ∈ (uniFrameModel hF hq hp2).B23.map D4.ι := by
      change c ∈ (S1.SymBlocksUni.uniBlk F (p ^ f) 2 3).map D4.ι
      rw [← h3']
      exact hcJ
    have hJL : (uniFrameModel hF hq hp2).B01.map D4.ι ≤
        S1.symJ (S1.symX x u) 0 ⊔ S1.symJ (S1.symX x u) 1 := by
      change (S1.SymBlocksUni.uniBlk F (p ^ f) 0 1).map D4.ι ≤ _
      rw [← h1']
      exact le_sup_right
    have hcard := CFSG.LieType.Steinberg.card_fixedSubfield hF
    refine nbhdDataJ_of_frameModel (uniFrameModel hF hq hp2) (by rw [hcard]; exact hodd)
      (by rw [hcard]; have := five_le_of_uni hF hq; omega) hset hmax hfront D4 hDK4 hcJ3 hc2 hLC hLq
      hJL ?_
    intro z hz hzc
    rw [← hWe] at hz hzc
    exact hWc z hz hzc

end CFSG.GH74.Generic.BProg.B3
