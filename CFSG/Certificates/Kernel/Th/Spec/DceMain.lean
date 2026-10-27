module

public import CFSG.Certificates.Kernel.Th.Spec.DceChk
public import CFSG.Certificates.Kernel.Th.Spec.DceHyp
public import CFSG.Certificates.Kernel.Th.Spec.DceRun
public import CFSG.Certificates.Kernel.Th.Spec.DceModel

public section

namespace CFSG.KC.Th.Spec.Dce

open CFSG.KC.Th CFSG.KC.Th.DceS CFSG.KC.Loop CFSG.Certificates.DceLoop
  CFSG.Certificates.DceWord CFSG.Certificates.DceTw CFSG.KC.Th.Gen CFSG.Certificates.LCE

set_option exponentiation.threshold 700

theorem litOK_spec {RT : ℕ → ℕ} : ∀ {R : ℕ}, TcS.litOK RT R = true → ∀ r < R, RT r = Hsw.sel r
  | 0, _, r, hr => absurd hr (Nat.not_lt_zero _)
  | R + 1, h, r, hr => by
    change CFSG.KC.andB (TcS.litOK RT R) (Nat.beq (RT R) (Hsw.sel R)) = true at h
    obtain ⟨h1, h2⟩ := andBK_iff.1 h
    rcases Nat.lt_succ_iff_lt_or_eq.mp hr with hr | rfl
    · exact litOK_spec h1 r hr
    · exact Nat.eq_of_beq_eq_true h2

theorem lettersSub_spec {LT LC TL VL NL LTB : ℕ} (h : lettersSub LT LC TL VL NL LTB = true) :
    ∀ c < NL, isN TL VL NL c = true → let24 LT c = let24 LTB (byte LC c) := by
  unfold lettersSub at h
  have := (allB_iff (fun c => Bool.rec (motive := fun _ => Bool) true
    (Nat.beq (let24 LT c) (let24 LTB (byte LC c))) (isN TL VL NL c)) NL).1 h
  intro c hc hN
  have e := this c hc
  rw [hN] at e
  exact Nat.eq_of_beq_eq_true e

theorem Lm_mem_Mgrp {LT LC LI TL VL NL : ℕ} (hL : LetOK LT LC LI TL VL NL) (hNL : NL = 16)
    (hLC : LC = lcB) {c : ℕ} (hc : isN TL VL NL c = true) :
    Lm LT LI TL VL NL c ∈ Mgrp LT LI TL VL NL := by
  obtain ⟨-, -, hl, hli⟩ := bLetters hL hNL hLC
  have hc14 := (hl c).1 hc
  rw [← letV_Lgen hL hl hli hc14]
  exact letV_mem _ hc14

theorem Lm_sub {LTA LCA LIA TLA VLA NLA LTB LCB LIB TLB VLB NLB : ℕ}
    (hLA : LetOK LTA LCA LIA TLA VLA NLA) (hLB : LetOK LTB LCB LIB TLB VLB NLB)
    (hsub : lettersSub LTA LCA TLA VLA NLA LTB = true) (hNL : NLB = 16) (hLC : LCB = lcB) {c : ℕ}
    (hN : isN TLA VLA NLA c = true) :
    isN TLB VLB NLB (byte LCA c) = true ∧
      Lm LTA LIA TLA VLA NLA c = Lm LTB LIB TLB VLB NLB (byte LCA c) := by
  obtain ⟨-, -, hl, -⟩ := bLetters hLB hNL hLC
  have hN' : isN TLB VLB NLB (byte LCA c) = true := (hl _).2 (hLA.nval c hN).1
  refine ⟨hN', Units.ext ?_⟩
  rw [Lm_val hLA hN, Lm_val hLB hN', lettersSub_spec hsub c (isN_iff.1 hN).1 hN]

theorem mctxA {G : Type*} [Group G] (xg : ℕ → G)
    {LTA LCA LIA TLA VLA NLA LTB LCB LIB TLB VLB NLB : ℕ}
    (hLA : LetOK LTA LCA LIA TLA VLA NLA) (hLB : LetOK LTB LCB LIB TLB VLB NLB)
    (hsub : lettersSub LTA LCA TLA VLA NLA LTB = true) (hNL : NLB = 16) (hLC : LCB = lcB)
    {φ : Mgrp LTB LIB TLB VLB NLB →* G}
    (hC : MCtx (Mgrp LTB LIB TLB VLB NLB) LTB LCB LIB TLB VLB NLB (xl xg LCB) φ) :
    MCtx (Mgrp LTB LIB TLB VLB NLB) LTA LCA LIA TLA VLA NLA (xl xg LCA) φ := by
  obtain ⟨-, -, hl, -⟩ := bLetters hLB hNL hLC
  have hM : ∀ c, isN TLA VLA NLA c = true →
      Lm LTA LIA TLA VLA NLA c ∈ Mgrp LTB LIB TLB VLB NLB := fun c hc => by
    obtain ⟨hN', e⟩ := Lm_sub hLA hLB hsub hNL hLC hc
    rw [e]
    exact Lm_mem_Mgrp hLB hNL hLC hN'
  refine ⟨hLA, hM, fun c hc => ?_, ?_⟩
  · obtain ⟨hN', e⟩ := Lm_sub hLA hLB hsub hNL hLC hc
    have h := hC.hφ _ hN'
    have e2 : (⟨Lm LTA LIA TLA VLA NLA c, hM c hc⟩ : Mgrp LTB LIB TLB VLB NLB) =
        ⟨Lm LTB LIB TLB VLB NLB (byte LCA c), hC.hM _ hN'⟩ := Subtype.ext e
    rw [e2, h]
    unfold xl
    have hlt := (hl _).1 hN'
    rw [hLC, lcB_byte _ (by omega)]
  · obtain ⟨h1, h2⟩ := xl_u xg hLA
    rw [h1, h2]

theorem impOK_spec {FA : ℕ → ℕ} {shA wdA NFA f : ℕ} (h : impOK FA shA wdA NFA f = true) :
    f < NFA ∧ rD (rec FA shA wdA f) = 1 ∧ rJ (rec FA shA wdA f) = 0 ∧
      rDp (rec FA shA wdA f) = 1 := by
  unfold impOK at h
  beta_reduce at h
  obtain ⟨e1, r⟩ := andB_iff.1 h
  obtain ⟨e2, r⟩ := andB_iff.1 r
  obtain ⟨e3, e4⟩ := andB_iff.1 r
  exact ⟨Nat.blt_eq.mp e1, Nat.eq_of_beq_eq_true e2, Nat.eq_of_beq_eq_true e3,
    Nat.eq_of_beq_eq_true e4⟩

section Import

variable {M : Subgroup Mat24ˣ} {G : Type*} [Group G] {φ : M →* G} {x : ℕ → G} {HB GB FA : ℕ → ℕ}
  {TL ND NO shA wdA NFA : ℕ} {N : Subgroup G} {w : ℕ → G}

theorem impSem_of_facts (hw1 : 0 < NFA → 2 ≤ ND → w 1 = x TL)
    (hfacts : ∀ i < NFA, FOK N true φ HB GB (x TL) w ND NO (rec FA shA wdA i)) :
    ImpSem φ x TL FA shA wdA NFA := by
  intro f hf
  obtain ⟨hfl, hD, hJ, hDp⟩ := impOK_spec hf
  obtain ⟨hR, hPi, hN, ν, hν, hνe, hFM⟩ := hfacts f hfl
  have hNm := hN rfl
  have hND2 : 2 ≤ ND := by
    have := hR.d
    omega
  have hI := InM_invR hPi (rFI_lt _) hR.pf
  refine ⟨hNm, hI, ?_⟩
  unfold FMeq at hFM
  rw [hD, hJ, hDp, hw1 (by omega) hND2, uv, if_pos rfl, mul_one] at hFM
  rw [rc_invR φ hPi (rFI_lt _) hR.pf, ← hνe rfl]
  have h2 : ν * (x TL * rc φ (rPi (rec FA shA wdA f))) = x TL := hFM.symm
  calc (x TL)⁻¹ * ν * x TL
      = (x TL)⁻¹ * (ν * (x TL * rc φ (rPi (rec FA shA wdA f)))) *
          (rc φ (rPi (rec FA shA wdA f)))⁻¹ := by group
    _ = (rc φ (rPi (rec FA shA wdA f)))⁻¹ := by rw [h2]; group

variable {TB FB WD : ℕ → ℕ} {LT VL NL nH nT nW W Wi sh wd NF : ℕ} {el : Bool}

theorem w_one_eq {nxf : ℕ → ℕ}
    (hf : ∀ i < NF, FChk HB GB TB FB WD LT TL VL NL ND NO nH nT nW W Wi sh wd el i (nxf i)
      (nxf (i + 1)))
    (h0 : nxf 0 = 1) (hN : nxf NF = ND) (hND : 2 ≤ ND)
    (hwt : ∀ i < NF, nxf (i + 1) = nxf i + 1 → w (rDp (rec FB sh wd i)) =
      w (rD (rec FB sh wd i)) * uv φ HB GB (x TL) (rJ (rec FB sh wd i)))
    (hw0 : w 0 = 1) : w 1 = x TL := by
  obtain ⟨i, hi, h1, h2⟩ := exists_first_tree h0 hN hND (fun i hi => by
    rcases (hf i hi).2 with ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ <;> omega)
  have htree : DceS.treeOK HB GB el (nxf i) (rec FB sh wd i) = true := by
    rcases (hf i hi).2 with ⟨-, h⟩ | ⟨e, -⟩ | ⟨e, -⟩
    · exact h
    · omega
    · omega
  obtain ⟨hJ, hDp, hD, hPi, -, hgm⟩ := treeOK_spec htree
  rw [h1] at hDp hD hgm
  have hD0 : rD (rec FB sh wd i) = 0 := by omega
  have := hwt i hi (by omega)
  rw [hDp, hD0, hw0, one_mul] at this
  rw [this, uv, if_neg (by omega), hgm rfl, rc_one, inv_one, one_mul, mul_one]

end Import

theorem kbound (D : DceData) (hc : Chk D) {H : Type*} [Group H] (y : ℕ → H)
    (hy : ∀ k < 27, bval y (LceS.wWord (Hsw.sel k)) (LceS.wLen (Hsw.sel k)) = 1) :
    Finite (Subgroup.closure (y '' {g | g < 7})) ∧
      Nat.card (Subgroup.closure (y '' {g | g < 7})) ≤ D.ThK1_nLive * D.ThK3_nLive := by
  have hn1 := hc.k1_nc
  have hn3 := hc.k3_nc
  have h1 : lceOk D.ThK1_blk D.ThK1_selWT D.ThK1_selRT D.ThK1_selST D.ThK1_LVs D.ThK1_INV
      D.ThK1_INV8 10 D.ThK1_nC 16923 5 D.ThK1_nLive 256 D.ThK1_HS 14 0 77723 D.cs43 D.cs42
      4294967296 D.sf43 1 D.sf42 = true :=
    lceOk_of_parts hc.k1_inv hc.k1_words hc.k1_hints hc.k1_alive hn1 (by omega) (by omega)
      (by omega) hc.k1_per
      (by rw [lceRelsNorm_congr 14 (fun r hr => litOK_spec hc.k1_rt r hr)]; exact hsw_norm14)
      rfl hc.k1_facts (by rw [hc.k1_sf43, hn1]) rfl hc.k1_cover (by rw [hc.k1_sf42, hn1])
  have h3 : lceOk D.ThK3_blk D.ThK3_selWT D.ThK3_selRT D.ThK3_selST D.ThK3_LVs D.ThK3_INV
      D.ThK3_INV8 14 D.ThK3_nC 106919 27 D.ThK3_nLive 512 D.ThK3_HS 27 5 551839 D.cs47 D.cs46
      4294967296 D.sf47 1 D.sf46 = true :=
    lceOk_of_parts hc.k3_inv hc.k3_words hc.k3_hints hc.k3_alive hn3 (by omega) (by omega)
      (by omega) hc.k3_per
      (by rw [lceRelsNorm_congr 27 (fun r hr => litOK_spec hc.k3_rt r hr)]; exact hsw_norm27)
      rfl hc.k3_facts (by rw [hc.k3_sf47, hn3]) rfl hc.k3_cover (by rw [hc.k3_sf46, hn3])
  have hS3 : ∀ j < 5, D.ThK3_selST j = 4 + 4096 * (2 * j) := by
    intro j hj
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl | rfl | rfl
    · exact hc.k3_st0
    · exact hc.k3_st1
    · exact hc.k3_st2
    · exact hc.k3_st3
    · exact hc.k3_st4
  exact kchain y hy h1 (litOK_spec hc.k1_rt) h3 (litOK_spec hc.k3_rt) hS3

section LevelA

variable {G : Type*} [Group G] (D : DceData) (hc : Chk D) {M : Subgroup Mat24ˣ} {φ : M →* G}
  {x : ℕ → G} {N : Subgroup G}
include hc

theorem a_facts
    (hC : MCtx M D.ThA_LT D.ThA_LC D.ThA_LI D.ThA_TL D.ThA_VL D.ThA_NL x φ)
    (hφN : ∀ m, φ m ∈ N) (hrels : ∀ r < D.ThA_NR, rval x (D.ThA_RR r) = 1)
    (hxi : ∀ c < D.ThA_NL, isN D.ThA_TL D.ThA_VL D.ThA_NL c = true →
      x (byte D.ThA_LI c) = (x c)⁻¹) :
    ∃ w : ℕ → G, (∀ i < D.ThA_NF, FOK N true φ D.ThA_HB D.ThA_GB (x D.ThA_TL) w D.ThA_ND
        D.ThA_NO (rec D.ThA_FB 4 2336 i)) ∧
      (0 < D.ThA_NF → 2 ≤ D.ThA_ND → w 1 = x D.ThA_TL) := by
  have hnorm : CFSG.KC.relsNorm D.ThA_RR D.ThA_NR = true := relsNorm_mono hc.a_nr hc.a_norm
  have himp : ImpSem φ x D.ThA_TL D.ThA_FB 4 2336 0 := fun f hf =>
    absurd (impOK_spec hf).1 (Nat.not_lt_zero _)
  have hSC := sctx_of_chk hC hrels hnorm hxi himp hc.a_hdr hc.a_gom hc.a_psi hc.a_usq
  have hhdr := hdr_mem hC himp hc.a_hdr
  have hwords := words_sem hC.hL hrels hnorm hxi hC.hu hc.a_words
  have hrun : factsG (factG (DceS.recOK D.ThA_ND D.ThA_NO true)
      (DceS.treeOK D.ThA_HB D.ThA_GB true) (DceS.axiomOK D.ThA_HB D.ThA_nH true)
      (fun i Jf R => walkOK D.ThA_FB D.ThA_HB D.ThA_GB D.ThA_TB D.ThA_WD 4 2336 D.ThA_LT
        D.ThA_TL D.ThA_VL D.ThA_NL D.ThA_ND D.ThA_nH D.ThA_nT D.ThA_nW D.ThA_W D.ThA_Wi true
        i Jf R) (rec D.ThA_FB 4 2336)) D.cs12 (mkSG 0 1) = mkSG D.ThA_NF D.ThA_ND := hc.a_facts
  have hterm : DceS.recOK D.ThA_ND D.ThA_NO true (rec D.ThA_FB 4 2336 D.ThA_NF) = false :=
    notB_iff.1 hc.a_term
  obtain ⟨nxf, hN0, hf⟩ := factsT_of_mk hc.a_nf hterm hrun
  obtain ⟨w, hw0, hwt⟩ := exists_w (φ := φ) (x := x) hf
  have hfm := facts_mean hSC hφN (by have := hc.a_nd; omega) hhdr hwords hf w hw0 hwt
  refine ⟨w, hfm, fun hNF hND2 => ?_⟩
  obtain ⟨h0, hN⟩ := hN0 hNF
  exact w_one_eq hf h0 hN hND2 hwt hw0

end LevelA

section Punit

variable (D : DceData) (hc : Chk D)
include hc

theorem impSem_punit : ImpSem (1 : Mgrp D.ThB_LT D.ThB_LI D.ThB_TL D.ThB_VL D.ThB_NL →*
    PUnit.{1}) (fun _ => (1 : PUnit.{1})) D.ThB_TL D.ThA_FB 4 2336 D.ThA_NF := by
  have hLA := lettersOK_spec hc.a_letters
  have hLB := lettersOK_spec hc.b_letters
  have hC0 : MCtx (Mgrp D.ThB_LT D.ThB_LI D.ThB_TL D.ThB_VL D.ThB_NL) D.ThA_LT D.ThA_LC D.ThA_LI
      D.ThA_TL D.ThA_VL D.ThA_NL (fun _ => (1 : PUnit.{1})) 1 :=
    MCtx.trivial hLA (fun c hcN => by
      obtain ⟨hN', e⟩ := Lm_sub hLA hLB hc.a_sub hc.b_nl hc.b_lc hcN
      rw [e]
      exact Lm_mem_Mgrp hLB hc.b_nl hc.b_lc hN')
  obtain ⟨w, hfm, -⟩ := a_facts D hc hC0 (N := ⊤) (fun _ => Subgroup.mem_top _)
    (fun _ _ => Subsingleton.elim _ _) (fun _ _ _ => Subsingleton.elim _ _)
  exact impSem_of_facts (fun _ _ => Subsingleton.elim _ _) hfm

theorem orb_B : Orb (Mgrp D.ThB_LT D.ThB_LI D.ThB_TL D.ThB_VL D.ThB_NL)
    (D.ThK1_nLive * D.ThK3_nLive) (Finset (Fin 24 → ZMod 2)) actP
    (ptS D.ThB_NB (pt D.ThB_OB D.ThB_osh D.ThB_owd D.ThB_om D.ThB_I0))
    (fun j => ptS D.ThB_NB (pt D.ThB_OB D.ThB_osh D.ThB_owd D.ThB_om j))
    (fun j => mEl (Mgrp D.ThB_LT D.ThB_LI D.ThB_TL D.ThB_VL D.ThB_NL) (gm D.ThB_HB D.ThB_GB j))
    D.ThB_NO D.ThB_I0
    (fun e => mEl (Mgrp D.ThB_LT D.ThB_LI D.ThB_TL D.ThB_VL D.ThB_NL) (tSig D.ThB_HB D.ThB_TB e))
    D.ThB_nT := by
  have hLB := lettersOK_spec hc.b_letters
  have himp := impSem_punit D hc
  have hC0 : MCtx (Mgrp D.ThB_LT D.ThB_LI D.ThB_TL D.ThB_VL D.ThB_NL) D.ThB_LT D.ThB_LC D.ThB_LI
      D.ThB_TL D.ThB_VL D.ThB_NL (fun _ => (1 : PUnit.{1})) 1 :=
    MCtx.trivial hLB (fun c hcN => Lm_mem_Mgrp hLB hc.b_nl hc.b_lc hcN)
  have hnormB : CFSG.KC.relsNorm D.ThB_RR D.ThB_NR = true := by
    rw [hc.b_nr]
    exact hc.b_norm
  have hgom := gom_mem hC0 (fun _ _ => Subsingleton.elim _ _) hnormB himp hc.b_hdr hc.b_gom
  have hpsi := psi_sem hC0 (fun _ _ => Subsingleton.elim _ _) hnormB himp hc.b_hdr hc.b_psi
  have hinjO := sorted_inj hc.b_pts hc.b_cntpts
  have hinjT := sorted_inj hc.b_tsig hc.b_cnttsig
  have hcard := (kbound D hc (Lgen D.ThB_LT D.ThB_LI D.ThB_TL D.ThB_VL D.ThB_NL)
    (Lgen_rel hLB hc.b_nl hc.b_lc hc.b_nr hc.b_rh hc.b_rels)).2
  exact orb_of (M := Mgrp D.ThB_LT D.ThB_LI D.ThB_TL D.ThB_VL D.ThB_NL) hc.b_sel hc.b_om
    (fun j hj => ⟨(hgom j hj).1, (hgom j hj).2.2.2.1, (hgom j hj).2.2.2.2⟩)
    (fun e he => ⟨(hpsi e he).1, tab_stab hc.b_psi e he⟩) hinjO hinjT hc.b_i0 hc.b_nord hcard

theorem card_model :
    D.ThK1_nLive * D.ThK3_nLive ≤
      Nat.card (Mgrp D.ThB_LT D.ThB_LI D.ThB_TL D.ThB_VL D.ThB_NL) :=
  (decompO (orb_B D hc)).1.ge

end Punit

theorem ImpSem.congr {M : Subgroup Mat24ˣ} {G : Type*} [Group G] {φ : M →* G} {x x' : ℕ → G}
    {TL TL' : ℕ} {FA : ℕ → ℕ} {shA wdA NFA : ℕ} (h : x TL = x' TL')
    (hi : ImpSem φ x TL FA shA wdA NFA) : ImpSem φ x' TL' FA shA wdA NFA := by
  intro f hf
  obtain ⟨h1, h2, h3⟩ := hi f hf
  refine ⟨h1, h2, ?_⟩
  rw [← h]
  exact h3

theorem sortedCount_lt (S : ℕ) : sortedCount S < 2 ^ 20 := by
  have h : Nat.land S M20 ≤ M20 := Nat.and_le_right
  have h2 : M20 < 2 ^ 20 := by decide
  show Nat.land S M20 - 1 < 2 ^ 20
  omega

section Main

theorem main_core {G : Type*} [Group G] (xg : ℕ → G)
    (hrel : ∀ k < 39, bval xg (LceS.wWord (Hsw.sel k)) (LceS.wLen (Hsw.sel k)) = 1)
    (hgen : Subgroup.closure (xg '' {g | g < 8}) = ⊤) (D : DceData) (hc : Chk D) :
    Finite G ∧ Nat.card G ≤ 90745943887872000 := by
  have hLB := lettersOK_spec hc.b_letters
  have hLA := lettersOK_spec hc.a_letters
  obtain ⟨φ, hCB, hφN, hNφ⟩ := model_hom xg hrel hLB hc.b_nl hc.b_lc hc.b_nr hc.b_rh hc.b_rels
    (fun H _ y hy => kbound D hc y hy) (card_model D hc)
  have hCA := mctxA xg hLA hLB hc.a_sub hc.b_nl hc.b_lc hCB
  have hrelsA := level_hrels xg hrel hc.a_rels
  obtain ⟨wA, hfmA, hw1A⟩ := a_facts D hc hCA hφN hrelsA
    (fun c hc' hN => xl_inv xg hLA hc' hN)
  have himpA : ImpSem φ (xl xg D.ThA_LC) D.ThA_TL D.ThA_FB 4 2336 D.ThA_NF :=
    impSem_of_facts hw1A hfmA
  have hu : xl xg D.ThA_LC D.ThA_TL = xl xg D.ThB_LC D.ThB_TL := by
    rw [(xl_u xg hLA).1, (xl_u xg hLB).1]
  have himpB : ImpSem φ (xl xg D.ThB_LC) D.ThB_TL D.ThA_FB 4 2336 D.ThA_NF :=
    ImpSem.congr hu himpA
  have hrelsB := level_hrels xg hrel hc.b_rels
  have hnormB : CFSG.KC.relsNorm D.ThB_RR D.ThB_NR = true := by
    rw [hc.b_nr]
    exact hc.b_norm
  have hSB := sctx_of_chk hCB hrelsB hnormB (fun c hc' hN => xl_inv xg hLB hc' hN) himpB
    hc.b_hdr hc.b_gom hc.b_psi hc.b_usq
  have hhdrB := hdr_mem hCB himpB hc.b_hdr
  have hwordsB := words_sem hLB hrelsB hnormB (fun c hc' hN => xl_inv xg hLB hc' hN) hCB.hu
    hc.b_words
  let fsB : ℕ → ℕ → ℕ := factG (DceS.recOK D.ThB_ND D.ThB_NO false)
    (DceS.treeOK D.ThB_HB D.ThB_GB false) (DceS.axiomOK D.ThB_HB D.ThB_nH false)
    (fun i Jf R => walkOK D.ThB_FB D.ThB_HB D.ThB_GB D.ThB_TB D.ThB_WD 5 1184 D.ThB_LT D.ThB_TL
      D.ThB_VL D.ThB_NL D.ThB_ND D.ThB_nH D.ThB_nT D.ThB_nW D.ThB_W D.ThB_Wi false i Jf R)
    (rec D.ThB_FB 5 1184)
  have hr1 : factsG fsB D.cs39 (mkSG 0 1) = mkSG D.ThB_NF D.ThB_ND := by
    have h := hc.b_facts1
    rw [hc.b_sf39] at h
    exact h
  obtain ⟨nxfB, hfB⟩ := factsG_of_mk hc.b_nf hr1
  obtain ⟨wB, hw0B, hwtB⟩ := exists_w (φ := φ) (x := xl xg D.ThB_LC) hfB
  have hfmB := facts_mean hSB hφN (by have := hc.b_nd; omega) hhdrB hwordsB hfB wB hw0B hwtB
  have hsum' : sumG D.ThB_AL D.ThB_MD D.ThB_ND (D.ThK1_nLive * D.ThK3_nLive) D.ThB_SUM = true :=
    hc.b_sum
  obtain ⟨hA0, hAL, hmD, hSUM⟩ := sumG_spec hsum'
  have hND0 : 0 < D.ThB_ND := by
    rcases Nat.eq_zero_or_pos D.ThB_ND with h | h
    · rw [h, pow_zero] at hAL
      have h1 : D.ThB_AL = 0 := by omega
      rw [h1, Nat.zero_testBit] at hA0
      exact absurd hA0 Bool.false_ne_true
    · exact h
  have hNO20 : D.ThB_NO < 2 ^ 20 := by
    rw [← hc.b_cntpts]
    exact sortedCount_lt _
  have hNO0 : 0 < D.ThB_NO := Nat.lt_of_le_of_lt (Nat.zero_le _) hc.b_i0
  have hgomB := gom_mem hCB hrelsB hnormB himpB hc.b_hdr hc.b_gom
  have hpsiB := psi_sem hCB hrelsB hnormB himpB hc.b_hdr hc.b_psi
  have hcov : DceS.runCover D.ThB_FB D.ThB_OB 5 1184 D.ThB_osh D.ThB_owd D.ThB_om D.ThB_NB
      D.ThB_sel D.ThB_NF D.ThB_NO D.ThB_AL D.cs13 1 = 1 + D.ThB_ND * 2 ^ 20 := by
    rw [hc.b_cover]
    change 1 + (D.ThB_ND <<< 20) = _
    rw [Nat.shiftLeft_eq]
  have hcover := cover_of (φ := φ) hc.b_sel hc.b_om (fun j hj => (hgomB j hj).2.2.2.1) hfmB
    hNO20 hNO0 hcov
  let A := (Finset.range D.ThB_ND).filter (fun D' => D.ThB_AL.testBit D' = true)
  have stabD : ∀ D' ∈ A, D' ≠ 0 → mDG D.ThB_MD D' = 1 ∨ ∃ E : ℕ → Mgrp D.ThB_LT D.ThB_LI
      D.ThB_TL D.ThB_VL D.ThB_NL, (∀ k < mDG D.ThB_MD D', ∀ k' < mDG D.ThB_MD D',
        E k = E k' → k = k') ∧ ∀ k < mDG D.ThB_MD D',
          wB D' * φ (E k) * (wB D')⁻¹ ∈ Subgroup.closure (xg '' {g | g < 7}) := by
    intro D' hD' hD0
    rw [Finset.mem_filter, Finset.mem_range] at hD'
    right
    have hD11 : D' < 11 := by
      have := hc.b_nd
      omega
    have h1 : 1 ≤ D' := Nat.pos_of_ne_zero hD0
    rcases (by omega : D' = 1 ∨ D' = 2 ∨ D' = 3 ∨ D' = 4 ∨ D' = 5 ∨ D' = 6 ∨ D' = 7 ∨ D' = 8 ∨
        D' = 9 ∨ D' = 10) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact stab_sem wB hfmB hc.b_start1 hc.b_stab1 hc.b_sorted1 hc.b_cnt1
    · exact stab_sem wB hfmB hc.b_start2 hc.b_stab2 hc.b_sorted2 hc.b_cnt2
    · exact stab_sem wB hfmB hc.b_start3 hc.b_stab3 hc.b_sorted3 hc.b_cnt3
    · exact stab_sem wB hfmB hc.b_start4 hc.b_stab4 hc.b_sorted4 hc.b_cnt4
    · exact stab_sem wB hfmB hc.b_start5 hc.b_stab5 hc.b_sorted5 hc.b_cnt5
    · exact stab_sem wB hfmB hc.b_start6 hc.b_stab6 hc.b_sorted6 hc.b_cnt6
    · exact stab_sem wB hfmB hc.b_start7 hc.b_stab7 hc.b_sorted7 hc.b_cnt7
    · exact stab_sem wB hfmB hc.b_start8 hc.b_stab8 hc.b_sorted8 hc.b_cnt8
    · exact stab_sem wB hfmB hc.b_start9 hc.b_stab9 hc.b_sorted9 hc.b_cnt9
    · exact stab_sem wB hfmB hc.b_start10 hc.b_stab10 hc.b_sorted10 hc.b_cnt10
  have hyp : Hyp (Subgroup.closure (xg '' {g | g < 7})) (xl xg D.ThB_LC D.ThB_TL)
      (Mgrp D.ThB_LT D.ThB_LI D.ThB_TL D.ThB_VL D.ThB_NL) φ (D.ThK1_nLive * D.ThK3_nLive)
      (Finset (Fin 24 → ZMod 2)) actP
      (ptS D.ThB_NB (pt D.ThB_OB D.ThB_osh D.ThB_owd D.ThB_om D.ThB_I0))
      (fun j => ptS D.ThB_NB (pt D.ThB_OB D.ThB_osh D.ThB_owd D.ThB_om j))
      (fun j => mEl (Mgrp D.ThB_LT D.ThB_LI D.ThB_TL D.ThB_VL D.ThB_NL) (gm D.ThB_HB D.ThB_GB j))
      D.ThB_NO D.ThB_I0
      (fun e => mEl (Mgrp D.ThB_LT D.ThB_LI D.ThB_TL D.ThB_VL D.ThB_NL)
        (tSig D.ThB_HB D.ThB_TB e)) D.ThB_nT wB A (mDG D.ThB_MD) :=
    { φN := hφN
      Nφ := hNφ
      orb := orb_B D hc
      psi := psi_hyp (fun e he => (hpsiB e he).2.2) hc.b_psi
      usq := ⟨mEl (Mgrp D.ThB_LT D.ThB_LI D.ThB_TL D.ThB_VL D.ThB_NL) D.ThB_W, hSB.wW.2.2.2⟩
      zero_mem := Finset.mem_filter.2 ⟨Finset.mem_range.2 hND0, hA0⟩
      w_zero := hw0B
      cover := hcover
      mD_dvd := fun D' hD' hD0 => by
        rw [Finset.mem_filter, Finset.mem_range] at hD'
        exact (hmD D' hD'.1 hD'.2 hD0).2
      stabD := stabD }
  have hX : ∀ y ∈ xg '' {g | g < 8}, y ∈ Subgroup.closure (xg '' {g | g < 7}) ∨
      y = xl xg D.ThB_LC D.ThB_TL ∨ y = (xl xg D.ThB_LC D.ThB_TL)⁻¹ := by
    rintro _ ⟨g, hg, rfl⟩
    by_cases h7 : g < 7
    · exact Or.inl (Subgroup.subset_closure ⟨g, h7, rfl⟩)
    · have h8 : g = 7 := by
        simp only [Set.mem_setOf_eq] at hg
        omega
      subst h8
      exact Or.inr (Or.inl (xl_u xg hLB).1.symm)
  obtain ⟨hfin, hcard⟩ := dceTw_bound hyp (xg '' {g | g < 8}) hX
  rw [hgen] at hfin hcard
  have hset : A.erase 0 = aliveSet D.ThB_AL D.ThB_ND := by
    ext D'
    simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_range, aliveSet, A]
    tauto
  rw [hset, ← hSUM] at hcard
  have hord := hc.b_order
  have hG : Finite G := Finite.of_equiv _ (Subgroup.topEquiv (G := G)).toEquiv
  refine ⟨hG, ?_⟩
  rw [← Subgroup.card_top (G := G)]
  exact hcard.trans (le_of_eq hord)

end Main

end CFSG.KC.Th.Spec.Dce

end
