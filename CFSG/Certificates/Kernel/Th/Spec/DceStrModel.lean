
module

public import CFSG.Certificates.Kernel.Th.Spec.DceStrMain

public section

namespace CFSG.KC.Th.Spec.DceStr

open CFSG.KC.Th CFSG.KC.Th.DceS CFSG.KC.Loop CFSG.Certificates.DceLoop
  CFSG.Certificates.DceWord CFSG.Certificates.DceTw CFSG.KC.Th.Gen CFSG.Certificates.LCE
  CFSG.KC.Th.Spec.Dce

set_option exponentiation.threshold 700

@[expose] def tabB (D : DceStructData) (c : ℕ) : ℕ → ℕ :=
  if c = 1 then D.ThB_E1 else if c = 2 then D.ThB_E2 else if c = 3 then D.ThB_E3 else
  if c = 4 then D.ThB_E4 else if c = 5 then D.ThB_E5 else if c = 6 then D.ThB_E6 else
  if c = 7 then D.ThB_E7 else if c = 8 then D.ThB_E8 else if c = 9 then D.ThB_E9 else
  if c = 10 then D.ThB_E10 else fun _ => 0

section Core

variable {G : Type*} [Group G] (xg : ℕ → G)
  (hrel : ∀ k < 39, bval xg (LceS.wWord (Hsw.sel k)) (LceS.wLen (Hsw.sel k)) = 1)
  (hgen : Subgroup.closure (xg '' {g | g < 8}) = ⊤)

set_option maxHeartbeats 4000000 in
include hrel hgen in
theorem struct_model (D : DceStructData) (h : dceStructChk D = true)
    (hG : Nat.card G = 90745943887872000) :
    ∃ (φ : Mgrp D.ThB_LT D.ThB_LI D.ThB_TL D.ThB_VL D.ThB_NL →* G) (v : Fin 11 → G),
      Function.Injective φ ∧
      (∀ m, φ m ∈ Subgroup.closure (xg '' {g | g < 7})) ∧
      (∀ n ∈ Subgroup.closure (xg '' {g | g < 7}), ∃ m, φ m = n) ∧
      (∀ c < 14, InM (Mgrp D.ThB_LT D.ThB_LI D.ThB_TL D.ThB_VL D.ThB_NL) (let24 D.ThB_LT c) ∧
        rc φ (let24 D.ThB_LT c) = letV xg c) ∧
      (∀ g < 7, ((Lgen D.ThB_LT D.ThB_LI D.ThB_TL D.ThB_VL D.ThB_NL g : Mat24ˣ) : Mat24) =
        toMat (let24 D.ThB_LT (2 * g))) ∧
      v 0 = 1 ∧
      (∀ g : G, ∃ D', ∃ k ∈ Subgroup.closure (xg '' {g | g < 7}),
        ∃ k' ∈ Subgroup.closure (xg '' {g | g < 7}), g = k * v D' * k') ∧
      (∀ D' : Fin 11, D' ≠ 0 → Nat.card ↥(Subgroup.closure (xg '' {g | g < 7}) ⊓
        (Subgroup.closure (xg '' {g | g < 7})).map (MulAut.conj (v D')).toMonoidHom) =
          CFSG.Sporadic.Th.Kernel.mD D') ∧
      (∀ D' : Fin 11, D' ≠ 0 → ∀ j < CFSG.Sporadic.Th.Kernel.mD D',
        InM (Mgrp D.ThB_LT D.ThB_LI D.ThB_TL D.ThB_VL D.ThB_NL) (mat (tabB D (cosetOrder D')) j)) ∧
      (∀ D' : Fin 11, D' ≠ 0 → ∀ s ∈ Subgroup.closure (xg '' {g | g < 7}) ⊓
          (Subgroup.closure (xg '' {g | g < 7})).map (MulAut.conj (v D')).toMonoidHom,
        ∃ j < CFSG.Sporadic.Th.Kernel.mD D', rc φ (mat (tabB D (cosetOrder D')) j) = s) ∧
      Orb (Mgrp D.ThB_LT D.ThB_LI D.ThB_TL D.ThB_VL D.ThB_NL)
        (D.ThK1_nLive * D.ThK3_nLive) (Finset (Fin 24 → ZMod 2)) actP
        (ptS D.ThB_NB (pt D.ThB_OB D.ThB_osh D.ThB_owd D.ThB_om D.ThB_I0))
        (fun j => ptS D.ThB_NB (pt D.ThB_OB D.ThB_osh D.ThB_owd D.ThB_om j))
        (fun j => mEl (Mgrp D.ThB_LT D.ThB_LI D.ThB_TL D.ThB_VL D.ThB_NL) (gm D.ThB_HB D.ThB_GB j))
        D.ThB_NO D.ThB_I0
        (fun e => mEl (Mgrp D.ThB_LT D.ThB_LI D.ThB_TL D.ThB_VL D.ThB_NL) (tSig D.ThB_HB D.ThB_TB e))
        D.ThB_nT ∧
      (∀ k < 819, InM (Mgrp D.ThB_LT D.ThB_LI D.ThB_TL D.ThB_VL D.ThB_NL) (mat D.ThA_CB k) ∧
        ∃ m : Mgrp D.ThB_LT D.ThB_LI D.ThB_TL D.ThB_VL D.ThB_NL,
          mEl (Mgrp D.ThB_LT D.ThB_LI D.ThB_TL D.ThB_VL D.ThB_NL) (mat D.ThA_CB k) =
            m⁻¹ * mEl (Mgrp D.ThB_LT D.ThB_LI D.ThB_TL D.ThB_VL D.ThB_NL) (let24 D.ThB_LT 0) * m) ∧
      (∀ k < 819, ∀ k' < 819, mat D.ThA_CB k = mat D.ThA_CB k' → k = k') ∧
      (∀ j < D.ThB_NO, InM (Mgrp D.ThB_LT D.ThB_LI D.ThB_TL D.ThB_VL D.ThB_NL)
        (gm D.ThB_HB D.ThB_GB j)) ∧
      (∀ e < D.ThB_nT, InM (Mgrp D.ThB_LT D.ThB_LI D.ThB_TL D.ThB_VL D.ThB_NL)
        (tSig D.ThB_HB D.ThB_TB e)) := by
  unfold dceStructChk at h
  have hgenC := andB_left h
  have hpin := andB_right h
  unfold dceStructPins at hpin
  have pND := Nat.eq_of_beq_eq_true (andB_left hpin)
  have pAL := Nat.eq_of_beq_eq_true (andB_left (andB_right hpin))
  have pMD := Nat.eq_of_beq_eq_true (andB_left (andB_right (andB_right hpin)))
  have pNCL := Nat.eq_of_beq_eq_true
    (andB_left (andB_right (andB_right (andB_right (andB_right hpin)))))
  set E := toDce D with hE
  have hc : Chk E := chk_of E (dceChk_toDce D hgenC)
  have hLB := lettersOK_spec hc.b_letters
  have hLA := lettersOK_spec hc.a_letters
  obtain ⟨φ, hCB, hφN, hNφ⟩ := model_hom xg hrel hLB hc.b_nl hc.b_lc hc.b_nr hc.b_rh hc.b_rels
    (fun H _ y hy => kbound E hc y hy) (card_model E hc)
  have hCA := mctxA xg hLA hLB hc.a_sub hc.b_nl hc.b_lc hCB
  have hrelsA := level_hrels xg hrel hc.a_rels
  obtain ⟨wA, hfmA, hw1A⟩ := a_facts E hc hCA hφN hrelsA
    (fun c hc' hN => xl_inv xg hLA hc' hN)
  have himpA : ImpSem φ (xl xg E.ThA_LC) E.ThA_TL E.ThA_FB 4 2336 E.ThA_NF :=
    impSem_of_facts hw1A hfmA
  have hu : xl xg E.ThA_LC E.ThA_TL = xl xg E.ThB_LC E.ThB_TL := by
    rw [(xl_u xg hLA).1, (xl_u xg hLB).1]
  have himpB : ImpSem φ (xl xg E.ThB_LC) E.ThB_TL E.ThA_FB 4 2336 E.ThA_NF :=
    ImpSem.congr hu himpA
  have hrelsB := level_hrels xg hrel hc.b_rels
  have hnormB : CFSG.KC.relsNorm E.ThB_RR E.ThB_NR = true := by
    rw [hc.b_nr]
    exact hc.b_norm
  have hSB := sctx_of_chk hCB hrelsB hnormB (fun c hc' hN => xl_inv xg hLB hc' hN) himpB
    hc.b_hdr hc.b_gom hc.b_psi hc.b_usq
  have hhdrB := hdr_mem hCB himpB hc.b_hdr
  have hwordsB := words_sem hLB hrelsB hnormB (fun c hc' hN => xl_inv xg hLB hc' hN) hCB.hu
    hc.b_words
  let fsB : ℕ → ℕ → ℕ := factG (DceS.recOK E.ThB_ND E.ThB_NO false)
    (DceS.treeOK E.ThB_HB E.ThB_GB false) (DceS.axiomOK E.ThB_HB E.ThB_nH false)
    (fun i Jf R => walkOK E.ThB_FB E.ThB_HB E.ThB_GB E.ThB_TB E.ThB_WD 5 1184 E.ThB_LT E.ThB_TL
      E.ThB_VL E.ThB_NL E.ThB_ND E.ThB_nH E.ThB_nT E.ThB_nW E.ThB_W E.ThB_Wi false i Jf R)
    (rec E.ThB_FB 5 1184)
  have hr1 : factsG fsB E.cs39 (mkSG 0 1) = mkSG E.ThB_NF E.ThB_ND := by
    have h' := hc.b_facts1
    rw [hc.b_sf39] at h'
    exact h'
  obtain ⟨nxfB, hfB⟩ := factsG_of_mk hc.b_nf hr1
  obtain ⟨wB, hw0B, hwtB⟩ := exists_w (φ := φ) (x := xl xg E.ThB_LC) hfB
  have hfmB := facts_mean hSB hφN (by have := hc.b_nd; omega) hhdrB hwordsB hfB wB hw0B hwtB
  have hsum' : sumG E.ThB_AL E.ThB_MD E.ThB_ND (E.ThK1_nLive * E.ThK3_nLive) E.ThB_SUM = true :=
    hc.b_sum
  obtain ⟨hA0, hAL, hmD, hSUM⟩ := sumG_spec hsum'
  have hND0 : 0 < E.ThB_ND := by
    rcases Nat.eq_zero_or_pos E.ThB_ND with h' | h'
    · rw [h', pow_zero] at hAL
      have h1 : E.ThB_AL = 0 := by omega
      rw [h1, Nat.zero_testBit] at hA0
      exact absurd hA0 Bool.false_ne_true
    · exact h'
  have hNO20 : E.ThB_NO < 2 ^ 20 := by
    rw [← hc.b_cntpts]
    exact sortedCount_lt _
  have hNO0 : 0 < E.ThB_NO := Nat.lt_of_le_of_lt (Nat.zero_le _) hc.b_i0
  have hgomB := gom_mem hCB hrelsB hnormB himpB hc.b_hdr hc.b_gom
  have hpsiB := psi_sem hCB hrelsB hnormB himpB hc.b_hdr hc.b_psi
  have hcov : DceS.runCover E.ThB_FB E.ThB_OB 5 1184 E.ThB_osh E.ThB_owd E.ThB_om E.ThB_NB
      E.ThB_sel E.ThB_NF E.ThB_NO E.ThB_AL E.cs13 1 = 1 + E.ThB_ND * 2 ^ 20 := by
    rw [hc.b_cover]
    change 1 + (E.ThB_ND <<< 20) = _
    rw [Nat.shiftLeft_eq]
  have hcover := cover_of (φ := φ) hc.b_sel hc.b_om (fun j hj => (hgomB j hj).2.2.2.1) hfmB
    hNO20 hNO0 hcov
  let A := (Finset.range E.ThB_ND).filter (fun D' => E.ThB_AL.testBit D' = true)
  have st1 := stab_sem_mat wB hfmB hc.b_start1 hc.b_stab1 hc.b_sorted1 hc.b_cnt1
  have st2 := stab_sem_mat wB hfmB hc.b_start2 hc.b_stab2 hc.b_sorted2 hc.b_cnt2
  have st3 := stab_sem_mat wB hfmB hc.b_start3 hc.b_stab3 hc.b_sorted3 hc.b_cnt3
  have st4 := stab_sem_mat wB hfmB hc.b_start4 hc.b_stab4 hc.b_sorted4 hc.b_cnt4
  have st5 := stab_sem_mat wB hfmB hc.b_start5 hc.b_stab5 hc.b_sorted5 hc.b_cnt5
  have st6 := stab_sem_mat wB hfmB hc.b_start6 hc.b_stab6 hc.b_sorted6 hc.b_cnt6
  have st7 := stab_sem_mat wB hfmB hc.b_start7 hc.b_stab7 hc.b_sorted7 hc.b_cnt7
  have st8 := stab_sem_mat wB hfmB hc.b_start8 hc.b_stab8 hc.b_sorted8 hc.b_cnt8
  have st9 := stab_sem_mat wB hfmB hc.b_start9 hc.b_stab9 hc.b_sorted9 hc.b_cnt9
  have st10 := stab_sem_mat wB hfmB hc.b_start10 hc.b_stab10 hc.b_sorted10 hc.b_cnt10
  have stabD : ∀ D' ∈ A, D' ≠ 0 → mDG E.ThB_MD D' = 1 ∨ ∃ Ef : ℕ → Mgrp E.ThB_LT E.ThB_LI
      E.ThB_TL E.ThB_VL E.ThB_NL, (∀ k < mDG E.ThB_MD D', ∀ k' < mDG E.ThB_MD D',
        Ef k = Ef k' → k = k') ∧ ∀ k < mDG E.ThB_MD D',
          wB D' * φ (Ef k) * (wB D')⁻¹ ∈ Subgroup.closure (xg '' {g | g < 7}) := by
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
  have hyp : Hyp (Subgroup.closure (xg '' {g | g < 7})) (xl xg E.ThB_LC E.ThB_TL)
      (Mgrp E.ThB_LT E.ThB_LI E.ThB_TL E.ThB_VL E.ThB_NL) φ (E.ThK1_nLive * E.ThK3_nLive)
      (Finset (Fin 24 → ZMod 2)) actP
      (ptS E.ThB_NB (pt E.ThB_OB E.ThB_osh E.ThB_owd E.ThB_om E.ThB_I0))
      (fun j => ptS E.ThB_NB (pt E.ThB_OB E.ThB_osh E.ThB_owd E.ThB_om j))
      (fun j => mEl (Mgrp E.ThB_LT E.ThB_LI E.ThB_TL E.ThB_VL E.ThB_NL) (gm E.ThB_HB E.ThB_GB j))
      E.ThB_NO E.ThB_I0
      (fun e => mEl (Mgrp E.ThB_LT E.ThB_LI E.ThB_TL E.ThB_VL E.ThB_NL)
        (tSig E.ThB_HB E.ThB_TB e)) E.ThB_nT wB A (mDG E.ThB_MD) :=
    { φN := hφN
      Nφ := hNφ
      orb := orb_B E hc
      psi := psi_hyp (fun e he => (hpsiB e he).2.2) hc.b_psi
      usq := ⟨mEl (Mgrp E.ThB_LT E.ThB_LI E.ThB_TL E.ThB_VL E.ThB_NL) E.ThB_W, hSB.wW.2.2.2⟩
      zero_mem := Finset.mem_filter.2 ⟨Finset.mem_range.2 hND0, hA0⟩
      w_zero := hw0B
      cover := hcover
      mD_dvd := fun D' hD' hD0 => by
        rw [Finset.mem_filter, Finset.mem_range] at hD'
        exact (hmD D' hD'.1 hD'.2 hD0).2
      stabD := stabD }
  have hX : ∀ y ∈ xg '' {g | g < 8}, y ∈ Subgroup.closure (xg '' {g | g < 7}) ∨
      y = xl xg E.ThB_LC E.ThB_TL ∨ y = (xl xg E.ThB_LC E.ThB_TL)⁻¹ := by
    rintro _ ⟨g, hg, rfl⟩
    by_cases h7 : g < 7
    · exact Or.inl (Subgroup.subset_closure ⟨g, h7, rfl⟩)
    · have h8 : g = 7 := by
        simp only [Set.mem_setOf_eq] at hg
        omega
      subst h8
      exact Or.inr (Or.inl (xl_u xg hLB).1.symm)
  have hset : A.erase 0 = aliveSet E.ThB_AL E.ThB_ND := by
    ext D'
    simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_range, aliveSet, A]
    tauto
  have hcardEq : Nat.card G = E.ThK1_nLive * E.ThK3_nLive *
      (1 + ∑ D' ∈ A.erase 0, E.ThK1_nLive * E.ThK3_nLive / mDG E.ThB_MD D') := by
    rw [hset, ← hSUM, hG]
    exact hc.b_order.symm
  obtain ⟨hφinj, -, hcov', hstabc⟩ := dceTw_eq hyp (xg '' {g | g < 8}) hX hgen hcardEq
  have hS : dceStructChkGen D = true := hgenC
  unfold dceStructChkGen at hS
  have L5 : DceS.runSorted (mat E.ThA_CB) 10 E.ThA_NCL E.cs5 1 = E.sf5 :=
    Nat.eq_of_beq_eq_true (andB_left (andB_left (andB_right (andB_left (andB_left (andB_left (andB_left (andB_left hS))))))))
  have L6 : DceS.runClass E.ThA_CB E.ThB_LT E.ThB_LI E.ThB_TL E.ThB_VL E.ThB_NL E.cs6 2 = Nat.succ E.ThA_NCL :=
    Nat.eq_of_beq_eq_true (andB_right (andB_left (andB_right (andB_left (andB_left (andB_left (andB_left (andB_left hS))))))))
  have L52 : sortedCount E.sf5 = E.ThA_NCL :=
    Nat.eq_of_beq_eq_true (andB_right (andB_left (andB_left (andB_right (andB_left (andB_right (andB_left (andB_left hS))))))))
  have L69 : mat E.ThA_CB 0 = let24 E.ThB_LT 0 :=
    Nat.eq_of_beq_eq_true (andB_left (andB_right (andB_right (andB_right (andB_left (andB_right (andB_right (andB_left (andB_left hS)))))))))
  have hfinG : Finite G := Nat.finite_of_card_ne_zero (by rw [hG]; norm_num)
  have eND : E.ThB_ND = 11 := pND
  have eAL : E.ThB_AL = 2047 := pAL
  have eMD : E.ThB_MD = 5669277530485510631759370250422092589367217792282136242055806976 := pMD
  have eNCL : E.ThA_NCL = 819 := pNCL
  have hAmem : ∀ D', D' ∈ A ↔ D' < 11 := by
    intro D'
    simp only [A, Finset.mem_filter, Finset.mem_range, eND, eAL]
    constructor
    · exact fun h' => h'.1
    · intro h'
      exact ⟨h', by interval_cases D' <;> decide⟩
  obtain ⟨-, -, hisN, -⟩ := bLetters hLB hc.b_nl hc.b_lc
  have hxl : ∀ c < 16, xl xg E.ThB_LC c = letV xg c := by
    intro c hc16
    show letV xg (byte E.ThB_LC c) = letV xg c
    rw [show E.ThB_LC = lcB from hc.b_lc, lcB_byte c hc16]
  have hlet : ∀ c < 14, InM (Mgrp E.ThB_LT E.ThB_LI E.ThB_TL E.ThB_VL E.ThB_NL)
      (let24 E.ThB_LT c) ∧ rc φ (let24 E.ThB_LT c) = letV xg c := by
    intro c hc
    have hN : isN E.ThB_TL E.ThB_VL E.ThB_NL c = true := (hisN c).2 hc
    exact ⟨hCB.inM_letter hN, by rw [hCB.rc_letter hN, hxl c (by omega)]⟩
  have hLgen : ∀ g < 7, ((Lgen E.ThB_LT E.ThB_LI E.ThB_TL E.ThB_VL E.ThB_NL g : Mat24ˣ) : Mat24) =
      toMat (let24 E.ThB_LT (2 * g)) := fun g hg =>
    Lm_val hLB ((hisN (2 * g)).2 (by omega))
  have hIa : InM (Mgrp E.ThB_LT E.ThB_LI E.ThB_TL E.ThB_VL E.ThB_NL) (let24 E.ThB_LT 0) :=
    (hlet 0 (by norm_num)).1
  have mEl_inj : ∀ {X Y : ℕ}, InM (Mgrp E.ThB_LT E.ThB_LI E.ThB_TL E.ThB_VL E.ThB_NL) X →
      InM (Mgrp E.ThB_LT E.ThB_LI E.ThB_TL E.ThB_VL E.ThB_NL) Y →
      mEl (Mgrp E.ThB_LT E.ThB_LI E.ThB_TL E.ThB_VL E.ThB_NL) X =
        mEl (Mgrp E.ThB_LT E.ThB_LI E.ThB_TL E.ThB_VL E.ThB_NL) Y → X = Y := by
    intro X Y hX' hY' he
    have e : ((mEl (Mgrp E.ThB_LT E.ThB_LI E.ThB_TL E.ThB_VL E.ThB_NL) X : Mat24ˣ) : Mat24) =
        ((mEl (Mgrp E.ThB_LT E.ThB_LI E.ThB_TL E.ThB_VL E.ThB_NL) Y : Mat24ˣ) : Mat24) := by
      rw [he]
    rw [mEl_val hX', mEl_val hY'] at e
    exact eq_of_toMat_eq hX'.1 hY'.1 e
  have gm : ∀ D' : Fin 11, D' ≠ 0 →
      mDG E.ThB_MD (cosetOrder D') = CFSG.Sporadic.Th.Kernel.mD D' := by
    rw [eMD]
    exact mDG_cosetOrder
  have hstab : ∀ D' : Fin 11, D' ≠ 0 → Nat.card ↥(Subgroup.closure (xg '' {g | g < 7}) ⊓
      (Subgroup.closure (xg '' {g | g < 7})).map
        (MulAut.conj (wB (cosetOrder D'))⁻¹).toMonoidHom) = CFSG.Sporadic.Th.Kernel.mD D' := by
    intro D' hD0
    rw [card_stabK, hstabc _ ((hAmem _).2 (cosetOrder_lt D')) (cosetOrder_ne_zero D' hD0),
      gm D' hD0]
  have sttab : ∀ c, 1 ≤ c → c ≤ 10 →
      (∀ k < mDG E.ThB_MD c, InM (Mgrp E.ThB_LT E.ThB_LI E.ThB_TL E.ThB_VL E.ThB_NL)
        (mat (tabB D c) k) ∧
        wB c * rc φ (mat (tabB D c) k) * (wB c)⁻¹ ∈ Subgroup.closure (xg '' {g | g < 7})) ∧
      ∀ k < mDG E.ThB_MD c, ∀ k' < mDG E.ThB_MD c, mat (tabB D c) k = mat (tabB D c) k' →
        k = k' := by
    intro c hc1 hc10
    rcases (by omega : c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 ∨ c = 6 ∨ c = 7 ∨ c = 8 ∨
        c = 9 ∨ c = 10) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [show mDG E.ThB_MD 1 = bits E.ThB_MD 20 20 by rw [eMD]; decide +kernel,
        show tabB D 1 = D.ThB_E1 by simp [tabB]]
      exact st1
    · rw [show mDG E.ThB_MD 2 = bits E.ThB_MD 40 20 by rw [eMD]; decide +kernel,
        show tabB D 2 = D.ThB_E2 by simp [tabB]]
      exact st2
    · rw [show mDG E.ThB_MD 3 = bits E.ThB_MD 60 20 by rw [eMD]; decide +kernel,
        show tabB D 3 = D.ThB_E3 by simp [tabB]]
      exact st3
    · rw [show mDG E.ThB_MD 4 = bits E.ThB_MD 80 20 by rw [eMD]; decide +kernel,
        show tabB D 4 = D.ThB_E4 by simp [tabB]]
      exact st4
    · rw [show mDG E.ThB_MD 5 = bits E.ThB_MD 100 20 by rw [eMD]; decide +kernel,
        show tabB D 5 = D.ThB_E5 by simp [tabB]]
      exact st5
    · rw [show mDG E.ThB_MD 6 = bits E.ThB_MD 120 20 by rw [eMD]; decide +kernel,
        show tabB D 6 = D.ThB_E6 by simp [tabB]]
      exact st6
    · rw [show mDG E.ThB_MD 7 = bits E.ThB_MD 140 20 by rw [eMD]; decide +kernel,
        show tabB D 7 = D.ThB_E7 by simp [tabB]]
      exact st7
    · rw [show mDG E.ThB_MD 8 = bits E.ThB_MD 160 20 by rw [eMD]; decide +kernel,
        show tabB D 8 = D.ThB_E8 by simp [tabB]]
      exact st8
    · rw [show mDG E.ThB_MD 9 = bits E.ThB_MD 180 20 by rw [eMD]; decide +kernel,
        show tabB D 9 = D.ThB_E9 by simp [tabB]]
      exact st9
    · rw [show mDG E.ThB_MD 10 = bits E.ThB_MD 200 20 by rw [eMD]; decide +kernel,
        show tabB D 10 = D.ThB_E10 by simp [tabB]]
      exact st10
  have hCB0 : InM (Mgrp E.ThB_LT E.ThB_LI E.ThB_TL E.ThB_VL E.ThB_NL) (mat E.ThA_CB 0) := by
    rw [L69]
    exact hIa
  have hcls := DceClass.runClass_conj hCB hCB0 (n := 819) (by rw [L6, eNCL])
  have hinjC : ∀ k < 819, ∀ k' < 819, mat E.ThA_CB k = mat E.ThA_CB k' → k = k' := by
    have := sorted_inj L5 L52
    rwa [eNCL] at this
  refine ⟨φ, fun D' => (wB (cosetOrder D'))⁻¹, hφinj, hφN, hNφ, hlet, hLgen, ?_, ?_, ?_, ?_, ?_,
    orb_B E hc, ?_, hinjC, fun j hj => (hgomB j hj).1, fun e he => (hpsiB e he).1⟩
  · show (wB 0)⁻¹ = 1
    rw [hw0B, inv_one]
  · intro g
    obtain ⟨Dc, hDc, a', ha', b', hb', hab⟩ := hcov' g⁻¹
    obtain ⟨D', hD'⟩ := cosetOrder_surj Dc ((hAmem Dc).1 hDc)
    refine ⟨D', b'⁻¹, (Subgroup.closure _).inv_mem hb', a'⁻¹, (Subgroup.closure _).inv_mem ha', ?_⟩
    show g = b'⁻¹ * (wB (cosetOrder D'))⁻¹ * a'⁻¹
    rw [hD']
    calc g = (g⁻¹)⁻¹ := (inv_inv g).symm
      _ = (a' * wB Dc * b')⁻¹ := by rw [hab]
      _ = b'⁻¹ * (wB Dc)⁻¹ * a'⁻¹ := by group
  · exact hstab
  · intro D' hD0 j hj
    have hc1 := cosetOrder_ne_zero D' hD0
    have hc11 := cosetOrder_lt D'
    rw [← gm D' hD0] at hj
    exact ((sttab (cosetOrder D') (by omega) (by omega)).1 j hj).1
  · intro D' hD0 s hs
    have hc1 := cosetOrder_ne_zero D' hD0
    have hc11 := cosetOrder_lt D'
    obtain ⟨hst, hinj⟩ := sttab (cosetOrder D') (by omega) (by omega)
    have hcard := hstabc (cosetOrder D') ((hAmem _).2 hc11) hc1
    have hex := stab_exhaust hφinj hcard
      (E := fun k => mEl (Mgrp E.ThB_LT E.ThB_LI E.ThB_TL E.ThB_VL E.ThB_NL)
        (mat (tabB D (cosetOrder D')) k))
      (fun k hk k' hk' he => hinj k hk k' hk' (mEl_inj (hst k hk).1 (hst k' hk').1 he))
      (fun k hk => ⟨hφN _, (hst k hk).2⟩)
    rw [Subgroup.mem_inf, mem_map_conj_inv] at hs
    obtain ⟨j, hj, hje⟩ := hex s hs.1 hs.2
    rw [gm D' hD0] at hj
    exact ⟨j, hj, hje⟩
  · intro k hk
    obtain ⟨hIk, m, hm⟩ := hcls k hk
    refine ⟨hIk, m, ?_⟩
    change mEl (Mgrp E.ThB_LT E.ThB_LI E.ThB_TL E.ThB_VL E.ThB_NL) (mat E.ThA_CB k) = _
    rw [hm, L69]
    rfl

end Core

end CFSG.KC.Th.Spec.DceStr

end
