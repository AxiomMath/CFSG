module

public import CFSG.GH74.Generic.BProg.B3.DictS1Adm
public import CFSG.GH74.Generic.BProg.B3.DictS1Model
public import CFSG.GH74.Generic.BProg.B3.DictRepair
public import CFSG.GH74.Generic.BProg.B3.DictCommon

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg
  CFSG.Assembly.LowTwoRank Subgroup

theorem d2_eq_six_of_shapeS1 {G : Type} [Group G] {x : G} {K : Subgroup (CentralizerBar x)}
    (hc : IsComponent K) (hG2 : GLS.InG2 ↥K) (hsh : ShapeS1 x K) : d2 ↥K = 6 := by
  have hlie : OfLieType ↥K := ofLieType_of_isSL4Model hsh.1
  have h6 : InG2Depth 6 ↥K := ⟨hG2, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
    ⟨rfl, hlie, not_isL3Odd_of_isSL4Model hc.1 hsh.1⟩)))))⟩
  refine le_antisymm (Nat.sInf_le h6) (le_csInf ⟨6, h6⟩ fun i hi => ?_)
  obtain ⟨-, hi⟩ := hi
  rcases hi with ⟨rfl, hn, -⟩ | ⟨rfl, hn, -⟩ | ⟨rfl, hn, -⟩ | ⟨rfl, hn, -⟩ | ⟨rfl, hn, -⟩ |
    ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
  · exact absurd hlie hn
  · exact absurd hlie hn
  · exact absurd hlie hn
  · exact absurd hlie hn
  · exact absurd hlie hn
  · exact le_rfl
  · omega
  · omega

namespace DictS1Three

variable {G : Type} [Group G] {F : Type} [Field F]

section Lift

variable {x : G} {S : Subgroup (GL (Fin 4) F)}

@[expose] noncomputable def ιbar (D : S1.LayerData x S) : ↥S →* CentralizerBar x :=
  D.K.subtype.comp D.iso.symm.toMonoidHom

theorem ιbar_apply (D : S1.LayerData x S) (s : ↥S) :
    ιbar D s = ((D.iso.symm s : ↥D.K) : CentralizerBar x) := rfl

theorem ιbar_injective (D : S1.LayerData x S) : Function.Injective (ιbar D) :=
  D.K.subtype_injective.comp D.iso.symm.injective

theorem map_top_ιbar (D : S1.LayerData x S) : (⊤ : Subgroup ↥S).map (ιbar D) = D.K := by
  ext g
  constructor
  · rintro ⟨s, -, rfl⟩
    exact (D.iso.symm s).2
  · intro hg
    refine ⟨D.iso ⟨g, hg⟩, trivial, ?_⟩
    rw [ιbar_apply, MulEquiv.symm_apply_apply]

variable [Finite G]

theorem proj_ιC_eq (D : S1.LayerData x S) (s : ↥S) : proj x (D.ιC s) = ιbar D s :=
  D.proj_ιC s

theorem bar_ι (D : S1.LayerData x S) (s : ↥S) : bar x (D.ι s) = ιbar D s := by
  rw [bar_of_mem (D.ι_mem_cent s)]
  exact D.proj_ιC s

theorem imgBar_map_ι (D : S1.LayerData x S) (J : Subgroup ↥S) :
    S3.imgBar x (J.map D.ι) = J.map (ιbar D) := by
  ext g
  rw [S3.mem_imgBar]
  constructor
  · rintro ⟨h, ⟨s, hs, hsh⟩, rfl⟩
    have e : h = D.ιC s := Subtype.ext hsh.symm
    subst e
    exact ⟨s, hs, (D.proj_ιC s).symm⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨D.ιC s, ⟨s, hs, rfl⟩, D.proj_ιC s⟩

theorem isPCompIn_range_ι (D : S1.LayerData x S) (hq : IsQuasisimple ↥D.K) :
    IsPCompIn 2 (centralizer ({x} : Set G)) ((⊤ : Subgroup ↥S).map D.ι) := by
  have hn : D.K.Normal := D.normal
  refine S1.isPCompIn_of_normal_block ?_ ?_ ?_
  · rintro _ ⟨s, -, rfl⟩
    exact D.ι_mem_cent s
  · rintro g hg _ ⟨s, -, rfl⟩
    have hL : (S1.liftL x D.K).Normal := S1.liftL_normal
    have hmem := hL.conj_mem _ (D.ιC_mem s) ⟨g, hg⟩
    refine ⟨D.liftIso.symm ⟨_, hmem⟩, trivial, ?_⟩
    change (((D.liftIso (D.liftIso.symm ⟨_, hmem⟩) : ↥(S1.liftL x D.K)) :
      ↥(centralizer ({x} : Set G))) : G) = _
    rw [MulEquiv.apply_symm_apply]
    rfl
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (D.iso.trans (Subgroup.topEquiv.symm.trans
        ((⊤ : Subgroup ↥S).equivMapOfInjective D.ι D.ι_injective))) hq

theorem imgBar_range_ι (D : S1.LayerData x S) :
    S3.imgBar x ((⊤ : Subgroup ↥S).map D.ι) = D.K := by
  rw [imgBar_map_ι, map_top_ιbar]

end Lift

section Model

@[expose] def xS (F : Type) [Field F] : ↥(StatedSL 4 F) := (ModelData.lin F).xK

@[expose] def yS (F : Type) [Field F] : ↥(StatedSL 4 F) := (ModelData.lin F).yK

theorem orderOf_xS (h2 : (2 : F) ≠ 0) : orderOf (xS F) = 2 := (ModelData.lin F).orderOf_xK h2

theorem yS_ne_one (h2 : (2 : F) ≠ 0) : yS F ≠ 1 := (ModelData.lin F).yK_ne_one h2

theorem yS_ne_xS (h2 : (2 : F) ≠ 0) : yS F ≠ xS F := (ModelData.lin F).yK_ne_xK h2

variable [Finite F]

theorem xS_mem_center (hF : Nat.card F % 4 = 3) : xS F ∈ Subgroup.center ↥(StatedSL 4 F) :=
  (mem_center_statedSL_four_iff hF _).2 (Or.inr rfl)

theorem splitAt_xS_yS (hF : Nat.card F % 4 = 3) :
    B1.PilotS1.SplitAt F (⊤ : Subgroup ↥(StatedSL 4 F)) (xS F) (yS F) (S1.blkLin (F := F) 0 1)
      (S1.blkLin (F := F) 2 3) :=
  splitAt_blkLin hF

theorem exists_e8_lin (hF : Nat.card F % 4 = 3) :
    ∃ E : Subgroup ↥(StatedSL 4 F), CFSG.IsElementaryAbelian 2 ↥E ∧ Nat.card ↥E = 8 ∧
      xS F ∈ E ∧ yS F ∈ E := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : Odd (Nat.card F) := Nat.odd_iff.2 (by omega)
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card hodd
  have hone0 := hone_of_model (ModelData.lin F) (mem_center_lin_iff hF)
    (fun t hT h1 hm1 => hmat_lin h2 t hT h1 hm1)
  have hone : ∀ t : ↥(StatedSL 4 F), t * t = 1 → t ≠ 1 → t ∉ Subgroup.center ↥(StatedSL 4 F) →
      ∃ k : ↥(StatedSL 4 F), k * t * k⁻¹ = yS F := hone0
  obtain ⟨E, hEel, hE8⟩ : ∃ E : Subgroup ↥(StatedSL 4 F), CFSG.IsElementaryAbelian 2 ↥E ∧
      Nat.card ↥E = 8 :=
    B1.PilotS1.exists_e8_model (ModelData.lin F) h2 (Subgroup.mem_top _)
  have hxE : xS F ∈ E := B1.PilotS1.e8_mem_xK (ModelData.lin F) h2 (mem_center_lin_iff hF) hone0 E hEel hE8
  obtain ⟨t, htE, ht1, htx⟩ : ∃ t ∈ E, t ≠ 1 ∧ t ≠ xS F := by
    by_contra hcon
    push Not at hcon
    have hle : E ≤ zpowers (xS F) := by
      intro v hv
      by_cases h1 : v = 1
      · rw [h1]
        exact Subgroup.one_mem _
      · rw [hcon v hv h1]
        exact Subgroup.mem_zpowers _
    have := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers, orderOf_xS h2] at this
    omega
  have htt : t * t = 1 := by
    rw [← pow_two]
    exact elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := E) t htE
  have htc : t ∉ Subgroup.center ↥(StatedSL 4 F) := by
    intro hc
    rcases (mem_center_statedSL_four_iff hF t).1 hc with h | h
    · exact ht1 (Subtype.ext h)
    · exact htx (Subtype.ext h)
  obtain ⟨k, hk⟩ := hone t htt ht1 htc
  refine ⟨E.map (MulAut.conj k).toMonoidHom, IsElementaryAbelian.map _, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective (MulAut.conj k).injective, hE8]
  · refine ⟨xS F, hxE, ?_⟩
    change k * xS F * k⁻¹ = xS F
    rw [Subgroup.mem_center_iff.1 (xS_mem_center hF) k, mul_inv_cancel_right]
  · exact ⟨t, htE, hk⟩

omit [Finite F] in
theorem zblkMat_zero_one_eq_yGL :
    S1.zblkMat F 0 1 = ((yGL F : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
  rw [yGL_matrix]
  unfold S1.zblkMat
  congr 1
  funext i
  fin_cases i <;> simp

theorem two_ne_zero_of_mod_four (hF : Nat.card F % 4 = 3) : (2 : F) ≠ 0 :=
  two_ne_zero_of_odd_card (Nat.odd_iff.2 (by omega))

structure FrameModel (S : Subgroup (GL (Fin 4) F)) (F' : Type) [Field F'] [Finite F'] where
  x0 : ↥S
  y0 : ↥S
  B01 : Subgroup ↥S
  B23 : Subgroup ↥S
  split : B1.PilotS1.SplitAt F' (⊤ : Subgroup ↥S) x0 y0 B01 B23
  cen : ∀ s ∈ Subgroup.center ↥S, s ≠ 1 → s = x0
  inv : ∀ z ∈ B23, z * z = 1 → z ≠ 1 → x0 * z = y0
  x0_ord : orderOf x0 = 2
  y0_ne_one : y0 ≠ 1
  y0_ne_x0 : y0 ≠ x0
  e8 : ∃ E : Subgroup ↥S, CFSG.IsElementaryAbelian 2 ↥E ∧ Nat.card ↥E = 8 ∧ x0 ∈ E ∧ y0 ∈ E
  grp : ∃ z₀ : ↥S, B1.PilotS1.GrpS1 F' ↥S z₀

@[expose] noncomputable def linFrameModel (hF : Nat.card F % 4 = 3) : FrameModel (StatedSL 4 F) F where
  x0 := xS F
  y0 := yS F
  B01 := S1.blkLin (F := F) 0 1
  B23 := S1.blkLin (F := F) 2 3
  split := splitAt_xS_yS hF
  cen := fun s hs hs1 => by
    rcases (mem_center_statedSL_four_iff hF s).1 hs with h | h
    · exact absurd (Subtype.ext h) hs1
    · exact Subtype.ext h
  inv := fun z hz hzz hz1 => by
    have h2 := two_ne_zero_of_mod_four hF
    have hx1 : xS F ≠ 1 := by
      intro h
      have := orderOf_xS h2
      rw [h, orderOf_one] at this
      omega
    have hmat := S1.Q3Frame.central_mul_mat hF h2 (xS_mem_center hF) hx1 hz hzz hz1
    apply Subtype.ext
    apply Units.ext
    rw [hmat, zblkMat_zero_one_eq_yGL]
    rfl
  x0_ord := orderOf_xS (two_ne_zero_of_mod_four hF)
  y0_ne_one := yS_ne_one (two_ne_zero_of_mod_four hF)
  y0_ne_x0 := yS_ne_xS (two_ne_zero_of_mod_four hF)
  e8 := exists_e8_lin hF
  grp := B1.PilotS1.grpS1_lin hF

end Model

section Frame

variable [Finite G] [Finite F]

omit [Finite F] in
theorem frame_split_gen {S : Subgroup (GL (Fin 4) F)} {F' : Type} [Field F'] [Finite F']
    (M : FrameModel S F') {x : G} (hx : orderOf x = 2) (D : S1.LayerData x S) (hxK : xbar x ∈ D.K)
    {c : G} (hcJ : c ∈ M.B23.map D.ι) (hc2 : orderOf c = 2) :
    x = D.ι M.x0 ∧ x * c = D.ι M.y0 ∧
      c * x = x * c ∧ orderOf (x * c) = 2 ∧ bar x (x * c) ∉ zpowers (xbar x) ∧
      M.B01.map D.ι ≤ centralizer ({x} : Set G) ⊓ centralizer ({x * c} : Set G) ∧
      B1.PilotS1.SplitAt F' D.K (xbar x) (bar x (x * c)) (S3.imgBar x (M.B01.map D.ι))
        (S3.imgBar x (M.B23.map D.ι)) := by
  have hS0 := M.split
  obtain ⟨s₀, hs₀c, -, hs₀1, hs₀x⟩ := S1.exists_center_involution_of_layer hx D hxK
  have hs₀ : s₀ = M.x0 := M.cen s₀ hs₀c hs₀1
  obtain ⟨z, hz, rfl⟩ := hcJ
  have hz2 : orderOf z = 2 := by rwa [orderOf_injective D.ι D.ι_injective] at hc2
  have hzz : z * z = 1 := by
    rw [← sq, ← hz2]
    exact pow_orderOf_eq_one z
  have hz1 : z ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hz2
    omega
  have hy : s₀ * z = M.y0 := by
    rw [hs₀]
    exact M.inv z hz hzz hz1
  have hxι : x = D.ι M.x0 := by rw [← hs₀, hs₀x]
  have hxc : x * D.ι z = D.ι M.y0 := by
    have e : D.ι s₀ * D.ι z = D.ι M.y0 := by rw [← map_mul, hy]
    rwa [hs₀x] at e
  have hxC : x ∈ centralizer ({x} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hxb : xbar x = ιbar D M.x0 := by
    have e : D.ιC M.x0 = ⟨x, hxC⟩ := Subtype.ext hxι.symm
    have h := proj_ιC_eq D M.x0
    rw [e] at h
    exact h
  refine ⟨hxι, hxc, D.ι_comm_self z, ?_, ?_, ?_, ?_⟩
  · rw [hxc, orderOf_injective D.ι D.ι_injective M.y0]
    exact M.split.ord
  · rw [hxc, bar_ι, hxb]
    intro hmem
    have hxo : orderOf (ιbar D M.x0) = 2 := by
      rw [orderOf_injective _ (ιbar_injective D) M.x0]
      exact M.x0_ord
    rcases B1.PilotS5.mem_zpowers_of_two hxo hmem with h | h
    · rw [← map_one (ιbar D)] at h
      exact M.y0_ne_one (ιbar_injective D h)
    · exact M.y0_ne_x0 (ιbar_injective D h)
  · rintro _ ⟨g, hg, rfl⟩
    refine Subgroup.mem_inf.2 ⟨D.ι_mem_cent g, ?_⟩
    have hgy : g * M.y0 = M.y0 * g := Subgroup.mem_centralizer_singleton_iff.1 (hS0.le₁ hg).1
    rw [Subgroup.mem_centralizer_singleton_iff, hxc, ← map_mul, ← map_mul, hgy]
  · have hS := hS0.map (ιbar D) (ιbar_injective D)
    rw [map_top_ιbar, ← hxb] at hS
    rw [hxc, bar_ι, imgBar_map_ι, imgBar_map_ι]
    exact hS

theorem frame_split_core (hF : Nat.card F % 4 = 3) {x : G} (hx : orderOf x = 2)
    (D : S1.LayerData x (StatedSL 4 F)) (hxK : xbar x ∈ D.K) {c : G}
    (hcJ : c ∈ (S1.blkLin (F := F) 2 3).map D.ι) (hc2 : orderOf c = 2) :
    x = D.ι (xS F) ∧ x * c = D.ι (yS F) ∧
      c * x = x * c ∧ orderOf (x * c) = 2 ∧ bar x (x * c) ∉ zpowers (xbar x) ∧
      (S1.blkLin (F := F) 0 1).map D.ι ≤ centralizer ({x} : Set G) ⊓ centralizer ({x * c} : Set G) ∧
      B1.PilotS1.SplitAt F D.K (xbar x) (bar x (x * c))
        (S3.imgBar x ((S1.blkLin (F := F) 0 1).map D.ι))
        (S3.imgBar x ((S1.blkLin (F := F) 2 3).map D.ι)) :=
  frame_split_gen (linFrameModel hF) hx D hxK hcJ hc2

end Frame

end DictS1Three

open DictS1Three in
theorem dictS1ThreeJ_proved : DictS1ThreeJ := by
  intro G _ _ x K hset hmax _hthin hfront u hu hf F _ _ hF3 hlin hodd c hcJ hc2 _hcc
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hx : orderOf x = 2 := hset.inv
  have hF4 : Nat.card F % 4 = 3 := by rw [hF3]
  have h2 : (2 : F) ≠ 0 := S1.q3_two_ne_zero hF3
  have hg2 : GLS.InG2 ↥K := hmax.1.2.2
  have hmin : ∀ (z : G) (L : Subgroup (CentralizerBar z)), G2Pair z L → d2 ↥K ≤ d2 ↥L :=
    fun z L hp => (hmax.2 z L hp).1
  have hNo : NoAltJ2 G :=
    noAltJ2_of_minDepth hset.simple hset.nonab hset.rank hset.kgh hx hset.comp hg2 hmin
      (Or.inl (d2_eq_six_of_shapeS1 hset.comp hg2 hset.shape))
  obtain ⟨-, -, hXc, -, -⟩ := S1.symX_facts hset.shape.2 hset.inv hf
  have hw : ∀ e j, S1.symX x u (e.succAbove j) ∈ centralizer ({S1.symX x u e} : Set G) := fun e j =>
    Subgroup.mem_centralizer_singleton_iff.2 (hXc _ _)
  have hloc : ∀ e : Fin 5, ∃ (K' : Subgroup (CentralizerBar (S1.symX x u e)))
      (hw' : ∀ j, S1.symX x u (e.succAbove j) ∈ centralizer ({S1.symX x u e} : Set G)),
        S1.S1Setup G (S1.symX x u e) K' ∧ S1.S1Front G (S1.symX x u e) K' ∧
        ∃ e' : ↥K' ≃* ↥(StatedSL 4 F), ∀ j, S1.ActsAsReflOn e' (barOf (hw' j)) (S1.reflDiag F j) := by
    intro e
    obtain ⟨K', hw', hset', hfront', -, e', he'⟩ := hlin e
    exact ⟨K', hw', hset', hfront', e', he'⟩
  choose D hDK hDact using S1.sym_layerData3 x u hF3 hodd hw hloc
  have h1 := S1.symJ3_one (S1.linBlockOps3 hF3) (S1.symX x u) D hw hDact
  have h3 := S1.symJ3_three (S1.linBlockOps3 hF3) (S1.symX x u) D hw hDact
  rw [S1.linBlockOps3_blk] at h1 h3
  set D4 : S1.LayerData x (StatedSL 4 F) := (D 4).toLayerData with hD4
  have h1' : S1.symJ3 (S1.symX x u) 1 = (S1.blkLin (F := F) 0 1).map D4.ι := h1
  have h3' : S1.symJ3 (S1.symX x u) 3 = (S1.blkLin (F := F) 2 3).map D4.ι := h3
  have hDK4 : D4.K = K := (hDK 4).trans hfront.layer_eq
  have hxK : xbar x ∈ D4.K := by
    rw [hDK4]
    exact hset.shape.2
  have hcJ3 : c ∈ (S1.blkLin (F := F) 2 3).map D4.ι := by
    rw [← h3']
    exact hcJ
  obtain ⟨hxι, hxcι, -, hy2, hyne, hJle, hS⟩ := frame_split_core hF4 hx D4 hxK hcJ3 hc2
  rw [hDK4] at hS
  set Iw : Subgroup G := (⊤ : Subgroup ↥(StatedSL 4 F)).map D4.ι with hIw
  have hKq : IsQuasisimple ↥D4.K := by
    rw [hDK4]
    exact hset.comp.1
  have hIwP : IsPCompIn 2 (centralizer ({x} : Set G)) Iw := isPCompIn_range_ι D4 hKq
  have himg : S3.imgBar x Iw = K := (imgBar_range_ι D4).trans hDK4
  have hOnly : S3.OnlyInvX x K := by
    intro w hw' hw2
    rw [hfront.cent_eq] at hw'
    rcases B1.PilotS5.mem_zpowers_of_two (B1.PilotS5.orderOf_xbar hx) hw' with h | h
    · rw [h, orderOf_one] at hw2
      omega
    · exact h
  have hJ2 : IsJ2 x Iw :=
    isJ2_of_isPCompIn hset.simple hset.nonab hset.rank hset.kgh hx hset.comp hg2 hmin hOnly hIwP himg
  obtain ⟨E, hEel, hE8, hxE, hyE⟩ := exists_e8_lin hF4
  set A : Subgroup G := E.map D4.ι with hA
  have hAIw : A ≤ Iw := Subgroup.map_mono le_top
  have hAel : CFSG.IsElementaryAbelian 2 ↥A := IsElementaryAbelian.map _
  have hA8 : Nat.card ↥A = 8 := by
    rw [hA, Subgroup.card_map_of_injective D4.ι_injective, hE8]
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
  have eP : (↥Iw ⧸ pPrimeCore 2 ↥Iw) ≃* ↥(StatedSL 4 F) :=
    eKK.trans ((MulEquiv.subgroupCongr hDK4).symm.trans D4.iso)
  obtain ⟨z₀, hP⟩ := B1.PilotS1.grpS1_lin hF4
  obtain ⟨-, hSq, hSZ, hY, hCY, -⟩ := B1.PilotS1.shape1_data hset.gen4 hx hIwP eP hP hQ1
  have hS' : B1.PilotS1.SplitAt F (S3.imgBar x Iw) (xbar x) (bar x (x * c))
      (S3.imgBar x ((S1.blkLin (F := F) 0 1).map D4.ι))
      (S3.imgBar x ((S1.blkLin (F := F) 2 3).map D4.ι)) := by
    rw [himg]
    exact hS
  have hadm := isAdmPair_of_splitAt_three hF3 hx hIwP hY hCY hSq hSZ hAIw hAel hA8 hxA hyA hy2 hyne hS'
  obtain ⟨⟨-, hpair⟩, -⟩ := S1.sym_a4_q3 hset hf hF3 hlin hodd
  obtain ⟨W, hW⟩ := hpair 0 1 rfl
  obtain ⟨hWe, -⟩ := S1.lin_pair_fusion h2 hW
  obtain ⟨hWq, hWc⟩ := S1.lin_pair_W_facts hW
  have hy1 : x * c ∈ S1.symJ3 (S1.symX x u) 1 := by
    rw [h1', hxcι]
    exact ⟨_, (splitAt_xS_yS hF4).u_mem, rfl⟩
  have hyy : (x * c) * (x * c) = 1 := by
    rw [← sq, ← hy2]
    exact pow_orderOf_eq_one _
  refine nbhdDataJ_of_parts (B := oPrimeResidualOf 2 (S1.symJ3 (S1.symX x u) 1)) hNo hJ2 hsrc hadm
    ?_ ?_ ?_ ?_ ?_
  · have e : c = x⁻¹ * (x * c) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.subset_closure (by simp)))
      (Subgroup.subset_closure (by simp))
  · rintro rfl
    rw [orderOf_one] at hc2
    omega
  · refine sup_le (fun a ha => ?_) (fun a ha => ?_)
    · exact Subgroup.mem_centralizer_singleton_iff.2
        (S1.symSystem3_comm (S1.linBlockOps3 hF3) (S1.symX x u) D hw hDact 0 3 (by decide) a ha c hcJ)
    · exact Subgroup.mem_centralizer_singleton_iff.2
        (S1.symSystem3_comm (S1.linBlockOps3 hF3) (S1.symX x u) D hw hDact 1 3 (by decide) a ha c hcJ)
  · rw [h1']
    exact oPrimeResidual_le_liftAt (fun a ha => (hJle ha).1) (fun a ha => (hJle ha).2) le_rfl
  · have hLq : IsQuasisimple ↥(S1.symJ3 (S1.symX x u) 0 ⊔ S1.symJ3 (S1.symX x u) 1) := by
      rw [← hWe]
      exact hWq
    refine le_iSup_conj_of_quasisimple hLq ((Subgroup.map_subtype_le _).trans le_sup_right)
      ⟨x * c, B1.PilotS1.mem_oPrimeResidualOf_of_two hy1 hyy, ?_⟩
    by_contra hall
    push Not at hall
    have hyW : x * c ∈ W := by
      rw [hWe]
      exact le_sup_right (a := S1.symJ3 (S1.symX x u) 0) hy1
    have hcen : ∀ w ∈ W, (x * c) * w = w * (x * c) := by
      intro w hw'
      rw [hWe] at hw'
      exact hall w hw'
    have hodd2 := hWc (x * c) hyW hcen
    rw [hy2] at hodd2
    exact absurd hodd2 (by decide)

end CFSG.GH74.Generic.BProg.B3
