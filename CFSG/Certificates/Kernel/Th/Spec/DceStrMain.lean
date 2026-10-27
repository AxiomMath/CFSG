
module

public import CFSG.Certificates.Kernel.Th.Spec.DceMain
public import CFSG.Certificates.Kernel.Th.Spec.DceStr
public import CFSG.Certificates.Kernel.Th.Spec.DceClass
public import CFSG.Certificates.Kernel.Th.Spec.Rank24
public import CFSG.Certificates.Kernel.DceTwEq
public import CFSG.Sporadic.Th.KernelInputsBase

public section

namespace CFSG.KC.Th.Spec.DceStr

open CFSG.KC.Th CFSG.KC.Th.DceS CFSG.KC.Loop CFSG.Certificates.DceLoop
  CFSG.Certificates.DceWord CFSG.Certificates.DceTw CFSG.KC.Th.Gen CFSG.Certificates.LCE
  CFSG.KC.Th.Spec.Dce

set_option exponentiation.threshold 700

section Stab

variable {M : Subgroup Mat24ˣ} {G : Type*} [Group G] {φ : M →* G} {HB GB FB : ℕ → ℕ}
  {ND NO sh wd NF : ℕ} {el : Bool} {N : Subgroup G} {u : G} (w : ℕ → G)
  (hfacts : ∀ i < NF, FOK N el φ HB GB u w ND NO (rec FB sh wd i))
include hfacts

theorem stab_sem_mat {EB : ℕ → ℕ} {D SG m Y1 : ℕ} {Cs Ce : List ℕ}
    (h1 : DceS.stabStart EB = true) (h2 : DceS.runStab FB EB sh wd NF D SG Cs 2 = m + 1)
    (h3 : DceS.runSorted (mat EB) 17 m Ce 1 = Y1) (h4 : sortedCount Y1 = m) :
    (∀ k < m, InM M (mat EB k) ∧ w D * rc φ (mat EB k) * (w D)⁻¹ ∈ N) ∧
      ∀ k < m, ∀ k' < m, mat EB k = mat EB k' → k = k' := by
  obtain ⟨hpos, hinj⟩ := sortRun_spec (runSorted_eq _ _ _ _ _ ▸ h3) h4
  have h0 : mat EB 0 = ident24 := Nat.eq_of_beq_eq_true h1
  rw [runStab_eq] at h2
  have hi := cntRun_spec (a := 1) h2
  refine ⟨fun k => ?_, hinj⟩
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [h0]
      refine ⟨InM_one, ?_⟩
      rw [rc_one φ, mul_one, mul_inv_cancel]
      exact N.one_mem
    obtain ⟨J, hJ⟩ := hi k hk0 hk
    obtain ⟨e1, e2⟩ := andB_iff.1 hJ
    have hp : bits J 0 17 < k := Nat.blt_eq.mp e1
    have he : mat EB k = mul24 (mat EB (bits J 0 17))
        (DceS.stabGen FB sh wd NF D SG (bits J 17 5)) := Nat.eq_of_beq_eq_true e2
    obtain ⟨mp, np⟩ := ih _ hp (by omega)
    rcases stabGen_spec FB sh wd NF D SG (bits J 17 5) with h0' | ⟨g, hg, gD, gJ, gDp, hgv⟩
    · rw [h0', mul24_zero_right] at he
      have := hpos k hk
      rw [he] at this
      exact absurd this (Nat.lt_irrefl 0)
    · obtain ⟨-, gm', -, ν, hνN, -, hFM⟩ := hfacts g hg
      rw [hgv] at he
      rw [he]
      refine ⟨InM_mul mp gm', ?_⟩
      rw [rc_mul φ mp gm']
      unfold FMeq at hFM
      rw [gD, gJ, gDp, uv, ite_eq_left rfl, mul_one] at hFM
      have e3 : w D * (rc φ (mat EB (bits J 0 17)) * rc φ (rPi (rec FB sh wd g))) * (w D)⁻¹ =
          (w D * rc φ (mat EB (bits J 0 17)) * (w D)⁻¹) *
            (w D * rc φ (rPi (rec FB sh wd g)) * (w D)⁻¹) := by group
      have e4 : w D * rc φ (rPi (rec FB sh wd g)) * (w D)⁻¹ = ν⁻¹ := by
        calc w D * rc φ (rPi (rec FB sh wd g)) * (w D)⁻¹
            = ν⁻¹ * (ν * (w D * rc φ (rPi (rec FB sh wd g)))) * (w D)⁻¹ := by group
          _ = ν⁻¹ * w D * (w D)⁻¹ := by rw [← hFM]
          _ = ν⁻¹ := by group
      rw [e3, e4]
      exact N.mul_mem np (N.inv_mem hνN)

end Stab

@[expose] def cosetOrder : Fin 11 → ℕ := ![0, 5, 7, 6, 9, 8, 3, 2, 4, 10, 1]

theorem cosetOrder_surj : ∀ Dc < 11, ∃ D : Fin 11, cosetOrder D = Dc := by decide

theorem cosetOrder_lt : ∀ D : Fin 11, cosetOrder D < 11 := by decide

theorem cosetOrder_ne_zero : ∀ D : Fin 11, D ≠ 0 → cosetOrder D ≠ 0 := by decide

theorem mDG_cosetOrder : ∀ D : Fin 11, D ≠ 0 →
    mDG 5669277530485510631759370250422092589367217792282136242055806976 (cosetOrder D) =
      CFSG.Sporadic.Th.Kernel.mD D := by decide +kernel

theorem mem_map_conj_inv {G : Type*} [Group G] (N : Subgroup G) (w x : G) :
    x ∈ N.map (MulAut.conj w⁻¹).toMonoidHom ↔ w * x * w⁻¹ ∈ N := by
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    convert hy using 1
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    group
  · intro h
    refine ⟨w * x * w⁻¹, h, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    group

theorem card_stabK {G : Type*} [Group G] (N : Subgroup G) (w : G) :
    Nat.card ↥(N ⊓ N.map (MulAut.conj w⁻¹).toMonoidHom) =
      Nat.card {n : G // n ∈ N ∧ w * n * w⁻¹ ∈ N} :=
  Nat.card_congr (Equiv.subtypeEquivRight fun x => by rw [Subgroup.mem_inf, mem_map_conj_inv])

theorem card_filter_add (P : ℕ → Prop) [DecidablePred P] (a b : ℕ) :
    ((Finset.range (a + b)).filter P).card =
      ((Finset.range a).filter P).card + ((Finset.range b).filter fun i => P (a + i)).card := by
  rw [Finset.card_filter, Finset.card_filter, Finset.card_filter, Finset.sum_range_add]

theorem sum_countA (EB : ℕ → ℕ) {c hi : ℕ} (hc : c ≤ 64 * hi) : ∀ n,
    ((Finset.range (c * n)).filter fun j => OutS.invRank 6 (mat EB j) = true).card =
      ∑ t ∈ Finset.range n, OutS.countA EB (c * t) c hi := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih, DceClass.countA_eq EB hc, Nat.mul_succ, card_filter_add]

theorem countA_zero (EB : ℕ → ℕ) {n hi : ℕ} (hn : n ≤ 64 * hi) :
    ((Finset.range n).filter fun j => OutS.invRank 6 (mat EB j) = true).card =
      OutS.countA EB 0 n hi := by
  rw [DceClass.countA_eq EB hn]
  simp only [Nat.zero_add]

section Core

variable {G : Type*} [Group G] (xg : ℕ → G)
  (hrel : ∀ k < 39, bval xg (LceS.wWord (Hsw.sel k)) (LceS.wLen (Hsw.sel k)) = 1)
  (hgen : Subgroup.closure (xg '' {g | g < 8}) = ⊤)

set_option maxHeartbeats 4000000 in
include hrel hgen in
theorem struct_core (D : DceStructData) (h : dceStructChk D = true)
    (hG : Nat.card G = 90745943887872000) :
    ∃ v : Fin 11 → G, v 0 = 1 ∧
      (∀ g : G, ∃ D', ∃ k ∈ Subgroup.closure (xg '' {g | g < 7}),
        ∃ k' ∈ Subgroup.closure (xg '' {g | g < 7}), g = k * v D' * k') ∧
      (∀ D', CFSG.Sporadic.Th.Kernel.mD D' ≤ Nat.card ↥(Subgroup.closure (xg '' {g | g < 7}) ⊓
        (Subgroup.closure (xg '' {g | g < 7})).map (MulAut.conj (v D')).toMonoidHom)) ∧
      (∀ D', D' ≠ 0 → Nat.card {k // k ∈ Subgroup.closure (xg '' {g | g < 7}) ⊓
          (Subgroup.closure (xg '' {g | g < 7})).map (MulAut.conj (v D')).toMonoidHom ∧
          ∃ g ∈ Subgroup.closure (xg '' {g | g < 7}), g * xg 0 * g⁻¹ = k} ≤
        CFSG.Sporadic.Th.Kernel.nD D') ∧
      Nat.card ↥(Subgroup.closure (xg '' {g | g < 7})) ≤ 634023936 ∧
      819 ≤ Nat.card {k // ∃ g ∈ Subgroup.closure (xg '' {g | g < 7}), g * xg 0 * g⁻¹ = k} ∧
      69615 ≤ Nat.card {k // k ∈ Subgroup.closure (xg '' {g | g < 7}) ∧ orderOf k = 2} ∧
      (∀ s ∈ Subgroup.closure (xg '' {g | g < 7}) ⊓
          (Subgroup.closure (xg '' {g | g < 7})).map (MulAut.conj (v 3)).toMonoidHom,
        (xg 1)⁻¹ * s * xg 1 ∈ Subgroup.closure (xg '' {g | g < 7}) ⊓
          (Subgroup.closure (xg '' {g | g < 7})).map (MulAut.conj (v 3)).toMonoidHom → s = 1) := by
  unfold dceStructChk at h
  have hgenC := andB_left h
  have hpin := andB_right h
  unfold dceStructPins at hpin
  have pND := Nat.eq_of_beq_eq_true (andB_left hpin)
  have pAL := Nat.eq_of_beq_eq_true (andB_left (andB_right hpin))
  have pMD := Nat.eq_of_beq_eq_true (andB_left (andB_right (andB_right hpin)))
  have pNORD := Nat.eq_of_beq_eq_true (andB_left (andB_right (andB_right (andB_right hpin))))
  have pNCL := Nat.eq_of_beq_eq_true
    (andB_left (andB_right (andB_right (andB_right (andB_right hpin)))))
  have psf48 := Nat.eq_of_beq_eq_true
    (andB_right (andB_right (andB_right (andB_right (andB_right hpin)))))
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
  obtain ⟨hφinj, hNcard, hcov', hstabc⟩ := dceTw_eq hyp (xg '' {g | g < 8}) hX hgen hcardEq
  have hS : dceStructChkGen D = true := hgenC
  unfold dceStructChkGen at hS
  have L5 : DceS.runSorted (mat E.ThA_CB) 10 E.ThA_NCL E.cs5 1 = E.sf5 :=
    Nat.eq_of_beq_eq_true (andB_left (andB_left (andB_right (andB_left (andB_left (andB_left (andB_left (andB_left hS))))))))
  have L6 : DceS.runClass E.ThA_CB E.ThB_LT E.ThB_LI E.ThB_TL E.ThB_VL E.ThB_NL E.cs6 2 = Nat.succ E.ThA_NCL :=
    Nat.eq_of_beq_eq_true (andB_right (andB_left (andB_right (andB_left (andB_left (andB_left (andB_left (andB_left hS))))))))
  have L48 : OutS.runClass2 D.ThO_CB2 E.ThB_LT E.ThB_LI E.ThB_TL E.ThB_VL E.ThB_NL D.cs48 2 = D.sf48 :=
    Nat.eq_of_beq_eq_true (andB_left (andB_right (andB_right (andB_left (andB_left (andB_right (andB_left (andB_left hS))))))))
  have L49 : DceS.runSorted (mat D.ThO_CB2) 17 68796 D.cs49 1 = D.sf49 :=
    Nat.eq_of_beq_eq_true (andB_left (andB_right (andB_right (andB_right (andB_left (andB_left (andB_right (andB_left (andB_left hS)))))))))
  have L52 : sortedCount E.sf5 = E.ThA_NCL :=
    Nat.eq_of_beq_eq_true (andB_right (andB_left (andB_left (andB_right (andB_left (andB_right (andB_left (andB_left hS))))))))
  have L69 : mat E.ThA_CB 0 = let24 E.ThB_LT 0 :=
    Nat.eq_of_beq_eq_true (andB_left (andB_right (andB_right (andB_right (andB_left (andB_right (andB_right (andB_left (andB_left hS)))))))))
  have L124 : OutS.invRank 6 (let24 E.ThB_LT 0) = true :=
    andB_right (andB_left (andB_left (andB_left (andB_left (andB_right (andB_right (andB_left hS)))))))
  have L159 : OutS.coreOK E.ThB_E6 E.ThB_LT E.ThB_LI 2 6 = true :=
    andB_left (andB_left (andB_right (andB_right (andB_right (andB_right (andB_right (andB_left hS)))))))
  have L160 : mat D.ThO_CB2 0 = mat E.ThB_E1 3 :=
    Nat.eq_of_beq_eq_true (andB_left (andB_right (andB_left (andB_right (andB_right (andB_right (andB_right (andB_right (andB_left hS)))))))))
  have L161 : OutS.invRank 12 (mat D.ThO_CB2 0) = true :=
    andB_right (andB_right (andB_left (andB_right (andB_right (andB_right (andB_right (andB_right (andB_left hS))))))))
  have L162 : sortedCount D.sf49 = 68796 :=
    Nat.eq_of_beq_eq_true (andB_left (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_left hS))))))))
  have C125 : OutS.countA E.ThB_E1 0 2048 32 = 15 :=
    Nat.eq_of_beq_eq_true (andB_left (andB_right (andB_left (andB_left (andB_left (andB_right (andB_right (andB_left hS))))))))
  have C126 : OutS.countA E.ThB_E1 2048 2048 32 = 6 :=
    Nat.eq_of_beq_eq_true (andB_left (andB_right (andB_right (andB_left (andB_left (andB_left (andB_right (andB_right (andB_left hS)))))))))
  have C127 : OutS.countA E.ThB_E1 4096 2048 32 = 4 :=
    Nat.eq_of_beq_eq_true (andB_right (andB_right (andB_right (andB_left (andB_left (andB_left (andB_right (andB_right (andB_left hS)))))))))
  have C128 : OutS.countA E.ThB_E1 6144 2048 32 = 2 :=
    Nat.eq_of_beq_eq_true (andB_left (andB_left (andB_right (andB_left (andB_left (andB_right (andB_right (andB_left hS))))))))
  have C129 : OutS.countA E.ThB_E1 8192 2048 32 = 2 :=
    Nat.eq_of_beq_eq_true (andB_right (andB_left (andB_right (andB_left (andB_left (andB_right (andB_right (andB_left hS))))))))
  have C130 : OutS.countA E.ThB_E1 10240 2048 32 = 2 :=
    Nat.eq_of_beq_eq_true (andB_left (andB_right (andB_right (andB_left (andB_left (andB_right (andB_right (andB_left hS))))))))
  have C131 : OutS.countA E.ThB_E1 12288 2048 32 = 0 :=
    Nat.eq_of_beq_eq_true (andB_left (andB_right (andB_right (andB_right (andB_left (andB_left (andB_right (andB_right (andB_left hS)))))))))
  have C132 : OutS.countA E.ThB_E1 14336 2048 32 = 2 :=
    Nat.eq_of_beq_eq_true (andB_right (andB_right (andB_right (andB_right (andB_left (andB_left (andB_right (andB_right (andB_left hS)))))))))
  have C133 : OutS.countA E.ThB_E1 16384 2048 32 = 0 :=
    Nat.eq_of_beq_eq_true (andB_left (andB_left (andB_left (andB_right (andB_left (andB_right (andB_right (andB_left hS))))))))
  have C134 : OutS.countA E.ThB_E1 18432 2048 32 = 0 :=
    Nat.eq_of_beq_eq_true (andB_right (andB_left (andB_left (andB_right (andB_left (andB_right (andB_right (andB_left hS))))))))
  have C135 : OutS.countA E.ThB_E1 20480 2048 32 = 1 :=
    Nat.eq_of_beq_eq_true (andB_left (andB_right (andB_left (andB_right (andB_left (andB_right (andB_right (andB_left hS))))))))
  have C136 : OutS.countA E.ThB_E1 22528 2048 32 = 1 :=
    Nat.eq_of_beq_eq_true (andB_left (andB_right (andB_right (andB_left (andB_right (andB_left (andB_right (andB_right (andB_left hS)))))))))
  have C137 : OutS.countA E.ThB_E1 24576 2048 32 = 2 :=
    Nat.eq_of_beq_eq_true (andB_right (andB_right (andB_right (andB_left (andB_right (andB_left (andB_right (andB_right (andB_left hS)))))))))
  have C138 : OutS.countA E.ThB_E1 26624 2048 32 = 4 :=
    Nat.eq_of_beq_eq_true (andB_left (andB_left (andB_right (andB_right (andB_left (andB_right (andB_right (andB_left hS))))))))
  have C139 : OutS.countA E.ThB_E1 28672 2048 32 = 0 :=
    Nat.eq_of_beq_eq_true (andB_left (andB_right (andB_left (andB_right (andB_right (andB_left (andB_right (andB_right (andB_left hS)))))))))
  have C140 : OutS.countA E.ThB_E1 30720 2048 32 = 0 :=
    Nat.eq_of_beq_eq_true (andB_right (andB_right (andB_left (andB_right (andB_right (andB_left (andB_right (andB_right (andB_left hS)))))))))
  have C141 : OutS.countA E.ThB_E1 32768 2048 32 = 8 :=
    Nat.eq_of_beq_eq_true (andB_left (andB_right (andB_right (andB_right (andB_left (andB_right (andB_right (andB_left hS))))))))
  have C142 : OutS.countA E.ThB_E1 34816 2048 32 = 2 :=
    Nat.eq_of_beq_eq_true (andB_left (andB_right (andB_right (andB_right (andB_right (andB_left (andB_right (andB_right (andB_left hS)))))))))
  have C143 : OutS.countA E.ThB_E2 0 2048 32 = 5 :=
    Nat.eq_of_beq_eq_true (andB_right (andB_right (andB_right (andB_right (andB_right (andB_left (andB_right (andB_right (andB_left hS)))))))))
  have C144 : OutS.countA E.ThB_E2 2048 2048 32 = 2 :=
    Nat.eq_of_beq_eq_true (andB_left (andB_left (andB_left (andB_left (andB_right (andB_right (andB_right (andB_left hS))))))))
  have C145 : OutS.countA E.ThB_E2 4096 2048 32 = 0 :=
    Nat.eq_of_beq_eq_true (andB_right (andB_left (andB_left (andB_left (andB_right (andB_right (andB_right (andB_left hS))))))))
  have C146 : OutS.countA E.ThB_E2 6144 2048 32 = 0 :=
    Nat.eq_of_beq_eq_true (andB_left (andB_right (andB_left (andB_left (andB_right (andB_right (andB_right (andB_left hS))))))))
  have C147 : OutS.countA E.ThB_E2 8192 2048 32 = 0 :=
    Nat.eq_of_beq_eq_true (andB_left (andB_right (andB_right (andB_left (andB_left (andB_right (andB_right (andB_right (andB_left hS)))))))))
  have C148 : OutS.countA E.ThB_E2 10240 2048 32 = 4 :=
    Nat.eq_of_beq_eq_true (andB_right (andB_right (andB_right (andB_left (andB_left (andB_right (andB_right (andB_right (andB_left hS)))))))))
  have C149 : OutS.countA E.ThB_E2 12288 1536 24 = 8 :=
    Nat.eq_of_beq_eq_true (andB_left (andB_left (andB_right (andB_left (andB_right (andB_right (andB_right (andB_left hS))))))))
  have C150 : OutS.countA E.ThB_E3 0 486 8 = 0 :=
    Nat.eq_of_beq_eq_true (andB_right (andB_left (andB_right (andB_left (andB_right (andB_right (andB_right (andB_left hS))))))))
  have C151 : OutS.countA E.ThB_E4 0 288 5 = 3 :=
    Nat.eq_of_beq_eq_true (andB_left (andB_right (andB_right (andB_left (andB_right (andB_right (andB_right (andB_left hS))))))))
  have C152 : OutS.countA E.ThB_E5 0 54 1 = 0 :=
    Nat.eq_of_beq_eq_true (andB_left (andB_right (andB_right (andB_right (andB_left (andB_right (andB_right (andB_right (andB_left hS)))))))))
  have C153 : OutS.countA E.ThB_E6 0 6 1 = 0 :=
    Nat.eq_of_beq_eq_true (andB_right (andB_right (andB_right (andB_right (andB_left (andB_right (andB_right (andB_right (andB_left hS)))))))))
  have C154 : OutS.countA E.ThB_E7 0 126 2 = 0 :=
    Nat.eq_of_beq_eq_true (andB_left (andB_left (andB_left (andB_right (andB_right (andB_right (andB_right (andB_left hS))))))))
  have C155 : OutS.countA E.ThB_E8 0 78 2 = 0 :=
    Nat.eq_of_beq_eq_true (andB_right (andB_left (andB_left (andB_right (andB_right (andB_right (andB_right (andB_left hS))))))))
  have C156 : OutS.countA E.ThB_E9 0 72 2 = 0 :=
    Nat.eq_of_beq_eq_true (andB_left (andB_right (andB_left (andB_right (andB_right (andB_right (andB_right (andB_left hS))))))))
  have C157 : OutS.countA E.ThB_E10 0 2048 32 = 0 :=
    Nat.eq_of_beq_eq_true (andB_left (andB_right (andB_right (andB_left (andB_right (andB_right (andB_right (andB_right (andB_left hS)))))))))
  have C158 : OutS.countA E.ThB_E10 2048 1480 24 = 0 :=
    Nat.eq_of_beq_eq_true (andB_right (andB_right (andB_right (andB_left (andB_right (andB_right (andB_right (andB_right (andB_left hS)))))))))
  have eND : E.ThB_ND = 11 := pND
  have eAL : E.ThB_AL = 2047 := pAL
  have eMD : E.ThB_MD = 5669277530485510631759370250422092589367217792282136242055806976 := pMD
  have eNORD : E.ThK1_nLive * E.ThK3_nLive = 634023936 := pNORD
  have eNCL : E.ThA_NCL = 819 := pNCL
  haveI hfinG : Finite G := Nat.finite_of_card_ne_zero (by rw [hG]; norm_num)
  have hAmem : ∀ D', D' ∈ A ↔ D' < 11 := by
    intro D'
    simp only [A, Finset.mem_filter, Finset.mem_range, eND, eAL]
    constructor
    · exact fun h' => h'.1
    · intro h'
      exact ⟨h', by interval_cases D' <;> decide⟩
  obtain ⟨-, -, hisN, hLI⟩ := bLetters hLB hc.b_nl hc.b_lc
  have hxl : ∀ c < 16, xl xg E.ThB_LC c = letV xg c := by
    intro c hc16
    show letV xg (byte E.ThB_LC c) = letV xg c
    rw [show E.ThB_LC = lcB from hc.b_lc, lcB_byte c hc16]
  have hN0 : isN E.ThB_TL E.ThB_VL E.ThB_NL 0 = true := (hisN 0).2 (by norm_num)
  have hN2 : isN E.ThB_TL E.ThB_VL E.ThB_NL 2 = true := (hisN 2).2 (by norm_num)
  have hN3 : isN E.ThB_TL E.ThB_VL E.ThB_NL 3 = true := (hisN 3).2 (by norm_num)
  have hLI2 : byte E.ThB_LI 2 = 3 := by
    rw [hLI 2 (by norm_num)]
    rfl
  have hx0 : rc φ (let24 E.ThB_LT 0) = xg 0 := by
    rw [hCB.rc_letter hN0, hxl 0 (by norm_num)]
    simp [letV]
  have hx2 : rc φ (let24 E.ThB_LT 2) = xg 1 := by
    rw [hCB.rc_letter hN2, hxl 2 (by norm_num)]
    simp [letV]
  have hx3 : rc φ (let24 E.ThB_LT (byte E.ThB_LI 2)) = (xg 1)⁻¹ := by
    rw [hLI2, hCB.rc_letter hN3, hxl 3 (by norm_num)]
    simp [letV]
  have hIa : InM (Mgrp E.ThB_LT E.ThB_LI E.ThB_TL E.ThB_VL E.ThB_NL) (let24 E.ThB_LT 0) :=
    hCB.inM_letter hN0
  have hI2 : InM (Mgrp E.ThB_LT E.ThB_LI E.ThB_TL E.ThB_VL E.ThB_NL) (let24 E.ThB_LT 2) :=
    hCB.inM_letter hN2
  have hI3 : InM (Mgrp E.ThB_LT E.ThB_LI E.ThB_TL E.ThB_VL E.ThB_NL)
      (let24 E.ThB_LT (byte E.ThB_LI 2)) := by
    rw [hLI2]
    exact hCB.inM_letter hN3
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
  have rc_inj : ∀ {X Y : ℕ}, InM (Mgrp E.ThB_LT E.ThB_LI E.ThB_TL E.ThB_VL E.ThB_NL) X →
      InM (Mgrp E.ThB_LT E.ThB_LI E.ThB_TL E.ThB_VL E.ThB_NL) Y → rc φ X = rc φ Y → X = Y :=
    fun hX' hY' he => mEl_inj hX' hY' (hφinj he)
  have invRank_of_conj : ∀ (r : ℕ) {X Y : ℕ},
      InM (Mgrp E.ThB_LT E.ThB_LI E.ThB_TL E.ThB_VL E.ThB_NL) X →
      InM (Mgrp E.ThB_LT E.ThB_LI E.ThB_TL E.ThB_VL E.ThB_NL) Y →
      ∀ m : Mgrp E.ThB_LT E.ThB_LI E.ThB_TL E.ThB_VL E.ThB_NL,
      mEl (Mgrp E.ThB_LT E.ThB_LI E.ThB_TL E.ThB_VL E.ThB_NL) X =
        m⁻¹ * mEl (Mgrp E.ThB_LT E.ThB_LI E.ThB_TL E.ThB_VL E.ThB_NL) Y * m →
      OutS.invRank r X = OutS.invRank r Y := by
    intro r X Y hX' hY' m he
    have e : ((mEl (Mgrp E.ThB_LT E.ThB_LI E.ThB_TL E.ThB_VL E.ThB_NL) X : Mat24ˣ) : Mat24) =
        ((m⁻¹ * mEl (Mgrp E.ThB_LT E.ThB_LI E.ThB_TL E.ThB_VL E.ThB_NL) Y * m :
          Mgrp E.ThB_LT E.ThB_LI E.ThB_TL E.ThB_VL E.ThB_NL) : Mat24ˣ) := by
      rw [he]
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, mEl_val hX',
      mEl_val hY', Subgroup.coe_inv] at e
    have hQP : ((((m : Mat24ˣ)⁻¹ : Mat24ˣ) : Mat24)) * ((m : Mat24ˣ) : Mat24) = 1 :=
      Units.inv_mul _
    exact Rank24.invRank_conj (Q := (((m : Mat24ˣ)⁻¹ : Mat24ˣ) : Mat24))
      (P := ((m : Mat24ˣ) : Mat24)) hY'.1 hX'.1 hQP e
  have order_two : ∀ {X r : ℕ}, InM (Mgrp E.ThB_LT E.ThB_LI E.ThB_TL E.ThB_VL E.ThB_NL) X →
      OutS.invRank r X = true → r ≠ 0 → orderOf (rc φ X) = 2 := by
    intro X r hX' hr hr0
    obtain ⟨hsq, hrk⟩ := (Rank24.invRank_iff hX'.1).1 hr
    have hy := mEl_val hX'
    have hyy : mEl (Mgrp E.ThB_LT E.ThB_LI E.ThB_TL E.ThB_VL E.ThB_NL) X ^ 2 = 1 := by
      apply Subtype.ext
      apply Units.ext
      rw [pow_two, Subgroup.coe_mul, Units.val_mul, hy, hsq]
      rfl
    have hy1 : mEl (Mgrp E.ThB_LT E.ThB_LI E.ThB_TL E.ThB_VL E.ThB_NL) X ≠ 1 := by
      intro h1
      have e1 : toMat X = 1 := by
        rw [← hy, h1]
        rfl
      have e2 : (1 : Mat24) + 1 = 0 := by
        rw [← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl, zero_smul]
      rw [e1, e2, Matrix.rank_zero] at hrk
      exact hr0 hrk.symm
    apply orderOf_eq_prime
    · rw [rc, ← map_pow, hyy, map_one]
    · intro h1
      exact hy1 (hφinj (h1.trans (map_one φ).symm))
  have b1 : bits E.ThB_MD 20 20 = 36864 := by rw [eMD]; decide +kernel
  have b2 : bits E.ThB_MD 40 20 = 13824 := by rw [eMD]; decide +kernel
  have b3 : bits E.ThB_MD 60 20 = 486 := by rw [eMD]; decide +kernel
  have b4 : bits E.ThB_MD 80 20 = 288 := by rw [eMD]; decide +kernel
  have b5 : bits E.ThB_MD 100 20 = 54 := by rw [eMD]; decide +kernel
  have b6 : bits E.ThB_MD 120 20 = 6 := by rw [eMD]; decide +kernel
  have b7 : bits E.ThB_MD 140 20 = 126 := by rw [eMD]; decide +kernel
  have b8 : bits E.ThB_MD 160 20 = 78 := by rw [eMD]; decide +kernel
  have b9 : bits E.ThB_MD 180 20 = 72 := by rw [eMD]; decide +kernel
  have b10 : bits E.ThB_MD 200 20 = 3528 := by rw [eMD]; decide +kernel
  rw [b1] at st1
  rw [b2] at st2
  rw [b3] at st3
  rw [b4] at st4
  rw [b5] at st5
  rw [b6] at st6
  rw [b7] at st7
  rw [b8] at st8
  rw [b9] at st9
  rw [b10] at st10
  have gm : ∀ D' : Fin 11, D' ≠ 0 → mDG E.ThB_MD (cosetOrder D') = CFSG.Sporadic.Th.Kernel.mD D' := by
    rw [eMD]
    exact mDG_cosetOrder
  have hstab : ∀ D' : Fin 11, D' ≠ 0 → Nat.card ↥(Subgroup.closure (xg '' {g | g < 7}) ⊓
      (Subgroup.closure (xg '' {g | g < 7})).map
        (MulAut.conj (wB (cosetOrder D'))⁻¹).toMonoidHom) = CFSG.Sporadic.Th.Kernel.mD D' := by
    intro D' hD0
    rw [card_stabK, hstabc _ ((hAmem _).2 (cosetOrder_lt D')) (cosetOrder_ne_zero D' hD0),
      gm D' hD0]
  have nDgen : ∀ {EB : ℕ → ℕ} {m Dc : ℕ}, Dc ∈ A → Dc ≠ 0 → mDG E.ThB_MD Dc = m →
      (∀ k < m, InM (Mgrp E.ThB_LT E.ThB_LI E.ThB_TL E.ThB_VL E.ThB_NL) (mat EB k) ∧
        wB Dc * rc φ (mat EB k) * (wB Dc)⁻¹ ∈ Subgroup.closure (xg '' {g | g < 7})) →
      (∀ k < m, ∀ k' < m, mat EB k = mat EB k' → k = k') →
      Nat.card {k // k ∈ Subgroup.closure (xg '' {g | g < 7}) ⊓
          (Subgroup.closure (xg '' {g | g < 7})).map (MulAut.conj (wB Dc)⁻¹).toMonoidHom ∧
          ∃ g ∈ Subgroup.closure (xg '' {g | g < 7}), g * xg 0 * g⁻¹ = k} ≤
        ((Finset.range m).filter fun j => OutS.invRank 6 (mat EB j) = true).card := by
    intro EB m Dc hDc hDc0 hm hst1 hst2
    have hcard := hstabc Dc hDc hDc0
    rw [hm] at hcard
    have hex := stab_exhaust hφinj hcard
      (E := fun k => mEl (Mgrp E.ThB_LT E.ThB_LI E.ThB_TL E.ThB_VL E.ThB_NL) (mat EB k))
      (fun k hk k' hk' he => hst2 k hk k' hk' (mEl_inj (hst1 k hk).1 (hst1 k' hk').1 he))
      (fun k hk => ⟨hφN _, (hst1 k hk).2⟩)
    have key : ∀ x : {k // k ∈ Subgroup.closure (xg '' {g | g < 7}) ⊓
        (Subgroup.closure (xg '' {g | g < 7})).map (MulAut.conj (wB Dc)⁻¹).toMonoidHom ∧
        ∃ g ∈ Subgroup.closure (xg '' {g | g < 7}), g * xg 0 * g⁻¹ = k},
        ∃ j, j ∈ (Finset.range m).filter (fun j => OutS.invRank 6 (mat EB j) = true) ∧
          rc φ (mat EB j) = x.1 := by
      rintro ⟨k, hk1, g, hg, rfl⟩
      rw [Subgroup.mem_inf, mem_map_conj_inv] at hk1
      obtain ⟨j, hj, hje⟩ := hex _ hk1.1 hk1.2
      refine ⟨j, Finset.mem_filter.2 ⟨Finset.mem_range.2 hj, ?_⟩, hje⟩
      obtain ⟨m', rfl⟩ := hNφ g hg
      have e1 : mEl (Mgrp E.ThB_LT E.ThB_LI E.ThB_TL E.ThB_VL E.ThB_NL) (mat EB j) =
          m' * mEl (Mgrp E.ThB_LT E.ThB_LI E.ThB_TL E.ThB_VL E.ThB_NL) (let24 E.ThB_LT 0) *
            m'⁻¹ := by
        apply hφinj
        rw [map_mul, map_mul, map_inv, hje, ← hx0]
        rfl
      rw [invRank_of_conj 6 (hst1 j hj).1 hIa m'⁻¹ (by rw [inv_inv]; exact e1)]
      exact L124
    choose f hf using key
    have hinj : Function.Injective fun x => (⟨f x, (hf x).1⟩ :
        ↥((Finset.range m).filter fun j => OutS.invRank 6 (mat EB j) = true)) := by
      intro x y hxy
      have e := congrArg Subtype.val hxy
      dsimp only at e
      apply Subtype.ext
      rw [← (hf x).2, ← (hf y).2, e]
    have := Nat.card_le_card_of_injective _ hinj
    rwa [Nat.card_eq_fintype_card (α := ↥((Finset.range m).filter _)), Fintype.card_coe] at this
  have g1 : mDG E.ThB_MD 1 = 36864 := by rw [eMD]; decide +kernel
  have g2 : mDG E.ThB_MD 2 = 13824 := by rw [eMD]; decide +kernel
  have g3 : mDG E.ThB_MD 3 = 486 := by rw [eMD]; decide +kernel
  have g4 : mDG E.ThB_MD 4 = 288 := by rw [eMD]; decide +kernel
  have g5 : mDG E.ThB_MD 5 = 54 := by rw [eMD]; decide +kernel
  have g6 : mDG E.ThB_MD 6 = 6 := by rw [eMD]; decide +kernel
  have g7 : mDG E.ThB_MD 7 = 126 := by rw [eMD]; decide +kernel
  have g8 : mDG E.ThB_MD 8 = 78 := by rw [eMD]; decide +kernel
  have g9 : mDG E.ThB_MD 9 = 72 := by rw [eMD]; decide +kernel
  have g10 : mDG E.ThB_MD 10 = 3528 := by rw [eMD]; decide +kernel
  have n1 : ((Finset.range 36864).filter fun j => OutS.invRank 6 (mat E.ThB_E1 j) = true).card =
      51 := by
    rw [show (36864 : ℕ) = 2048 * 18 from rfl,
      sum_countA E.ThB_E1 (by norm_num : 2048 ≤ 64 * 32) 18]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceMul, C125, C126, C127,
      C128, C129, C130, C131, C132, C133, C134, C135, C136, C137, C138, C139, C140, C141, C142]
  have n2 : ((Finset.range 13824).filter fun j => OutS.invRank 6 (mat E.ThB_E2 j) = true).card =
      19 := by
    rw [show (13824 : ℕ) = 2048 * 6 + 1536 from rfl, card_filter_add]
    beta_reduce
    rw [sum_countA E.ThB_E2 (by norm_num : 2048 ≤ 64 * 32) 6,
      ← DceClass.countA_eq E.ThB_E2 (by norm_num : 1536 ≤ 64 * 24)]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceMul, C143, C144, C145,
      C146, C147, C148, C149]
  have n3 : ((Finset.range 486).filter fun j => OutS.invRank 6 (mat E.ThB_E3 j) = true).card =
      0 := by rw [countA_zero E.ThB_E3 (by norm_num : 486 ≤ 64 * 8), C150]
  have n4 : ((Finset.range 288).filter fun j => OutS.invRank 6 (mat E.ThB_E4 j) = true).card =
      3 := by rw [countA_zero E.ThB_E4 (by norm_num : 288 ≤ 64 * 5), C151]
  have n5 : ((Finset.range 54).filter fun j => OutS.invRank 6 (mat E.ThB_E5 j) = true).card =
      0 := by rw [countA_zero E.ThB_E5 (by norm_num : 54 ≤ 64 * 1), C152]
  have n6 : ((Finset.range 6).filter fun j => OutS.invRank 6 (mat E.ThB_E6 j) = true).card =
      0 := by rw [countA_zero E.ThB_E6 (by norm_num : 6 ≤ 64 * 1), C153]
  have n7 : ((Finset.range 126).filter fun j => OutS.invRank 6 (mat E.ThB_E7 j) = true).card =
      0 := by rw [countA_zero E.ThB_E7 (by norm_num : 126 ≤ 64 * 2), C154]
  have n8 : ((Finset.range 78).filter fun j => OutS.invRank 6 (mat E.ThB_E8 j) = true).card =
      0 := by rw [countA_zero E.ThB_E8 (by norm_num : 78 ≤ 64 * 2), C155]
  have n9 : ((Finset.range 72).filter fun j => OutS.invRank 6 (mat E.ThB_E9 j) = true).card =
      0 := by rw [countA_zero E.ThB_E9 (by norm_num : 72 ≤ 64 * 2), C156]
  have n10 : ((Finset.range 3528).filter fun j => OutS.invRank 6 (mat E.ThB_E10 j) = true).card =
      0 := by
    rw [show (3528 : ℕ) = 2048 + 1480 from rfl, card_filter_add]
    beta_reduce
    rw [countA_zero E.ThB_E10 (by norm_num : 2048 ≤ 64 * 32),
      ← DceClass.countA_eq E.ThB_E10 (by norm_num : 1480 ≤ 64 * 24), C157, C158]
  have hA' : ∀ Dc, Dc < 11 → Dc ∈ A := fun Dc h' => (hAmem Dc).2 h'
  have hCB0 : InM (Mgrp E.ThB_LT E.ThB_LI E.ThB_TL E.ThB_VL E.ThB_NL) (mat E.ThA_CB 0) := by
    rw [L69]
    exact hIa
  have hCB0v : rc φ (mat E.ThA_CB 0) = xg 0 := by
    rw [L69]
    exact hx0
  have hcls := DceClass.runClass_conj hCB hCB0 (n := 819) (by rw [L6, eNCL])
  have hinjC : ∀ k < 819, ∀ k' < 819, mat E.ThA_CB k = mat E.ThA_CB k' → k = k' := by
    have := sorted_inj L5 L52
    rwa [eNCL] at this
  have hCB2 : InM (Mgrp E.ThB_LT E.ThB_LI E.ThB_TL E.ThB_VL E.ThB_NL) (mat D.ThO_CB2 0) := by
    rw [L160]
    exact (st1.1 3 (by norm_num)).1
  have hcls2 := DceClass.runClass2_conj hCB hCB2 (n := 68796) (by rw [L48, psf48])
  have hinjC2 := sorted_inj L49 L162
  have inv6 : ∀ k < 819, OutS.invRank 6 (mat E.ThA_CB k) = true := by
    intro k hk
    obtain ⟨hIk, m, hm⟩ := hcls k hk
    rw [invRank_of_conj 6 hIk hCB0 m hm, L69]
    exact L124
  have inv12 : ∀ k < 68796, OutS.invRank 12 (mat D.ThO_CB2 k) = true := by
    intro k hk
    obtain ⟨hIk, m, hm⟩ := hcls2 k hk
    rw [invRank_of_conj 12 hIk hCB2 m hm]
    exact L161
  have hval : ∀ k < 819, ∃ g ∈ Subgroup.closure (xg '' {g | g < 7}),
      g * xg 0 * g⁻¹ = rc φ (mat E.ThA_CB k) := by
    intro k hk
    obtain ⟨-, m, hm⟩ := hcls k hk
    refine ⟨(φ m)⁻¹, (Subgroup.closure _).inv_mem (hφN m), ?_⟩
    show (φ m)⁻¹ * xg 0 * (φ m)⁻¹⁻¹ =
      φ (mEl (Mgrp E.ThB_LT E.ThB_LI E.ThB_TL E.ThB_VL E.ThB_NL) (mat E.ThA_CB k))
    rw [hm, map_mul, map_mul, map_inv, inv_inv, ← hCB0v]
    rfl
  refine ⟨fun D' => (wB (cosetOrder D'))⁻¹, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
  · intro D'
    by_cases hD0 : D' = 0
    · subst hD0
      show 1 ≤ _
      exact Nat.card_pos
    · exact (hstab D' hD0).ge
  · intro D' hD0
    fin_cases D'
    · exact absurd rfl hD0
    · exact le_trans (nDgen (Dc := 5) (hA' 5 (by norm_num)) (by norm_num) g5 st5.1 st5.2)
        (by rw [n5]; decide)
    · exact le_trans (nDgen (Dc := 7) (hA' 7 (by norm_num)) (by norm_num) g7 st7.1 st7.2)
        (by rw [n7]; decide)
    · exact le_trans (nDgen (Dc := 6) (hA' 6 (by norm_num)) (by norm_num) g6 st6.1 st6.2)
        (by rw [n6]; decide)
    · exact le_trans (nDgen (Dc := 9) (hA' 9 (by norm_num)) (by norm_num) g9 st9.1 st9.2)
        (by rw [n9]; decide)
    · exact le_trans (nDgen (Dc := 8) (hA' 8 (by norm_num)) (by norm_num) g8 st8.1 st8.2)
        (by rw [n8]; decide)
    · exact le_trans (nDgen (Dc := 3) (hA' 3 (by norm_num)) (by norm_num) g3 st3.1 st3.2)
        (by rw [n3]; decide)
    · exact le_trans (nDgen (Dc := 2) (hA' 2 (by norm_num)) (by norm_num) g2 st2.1 st2.2)
        (by rw [n2]; decide)
    · exact le_trans (nDgen (Dc := 4) (hA' 4 (by norm_num)) (by norm_num) g4 st4.1 st4.2)
        (by rw [n4]; decide)
    · exact le_trans (nDgen (Dc := 10) (hA' 10 (by norm_num)) (by norm_num) g10 st10.1 st10.2)
        (by rw [n10]; decide)
    · exact le_trans (nDgen (Dc := 1) (hA' 1 (by norm_num)) (by norm_num) g1 st1.1 st1.2)
        (by rw [n1]; decide)
  · rw [hNcard, eNORD]
  · let f : Fin 819 → {k // ∃ g ∈ Subgroup.closure (xg '' {g | g < 7}), g * xg 0 * g⁻¹ = k} :=
      fun i => ⟨rc φ (mat E.ThA_CB i), hval i i.2⟩
    have hf : Function.Injective f := by
      intro i j hij
      exact Fin.ext (hinjC i i.2 j j.2
        (rc_inj (hcls i i.2).1 (hcls j j.2).1 (congrArg Subtype.val hij)))
    have := Nat.card_le_card_of_injective f hf
    rwa [Nat.card_fin] at this
  · let f : Fin 819 ⊕ Fin 68796 → {k // k ∈ Subgroup.closure (xg '' {g | g < 7}) ∧
        orderOf k = 2} := fun x => match x with
      | .inl i => ⟨rc φ (mat E.ThA_CB i), hφN _,
          order_two (hcls i i.2).1 (inv6 i i.2) (by norm_num)⟩
      | .inr i => ⟨rc φ (mat D.ThO_CB2 i), hφN _,
          order_two (hcls2 i i.2).1 (inv12 i i.2) (by norm_num)⟩
    have hrk : ∀ (i : Fin 819) (j : Fin 68796), mat E.ThA_CB i ≠ mat D.ThO_CB2 j := by
      intro i j e
      have h6 := inv6 i i.2
      rw [e] at h6
      have r6 := ((Rank24.invRank_iff (mat_lt _ _)).1 h6).2
      have r12 := ((Rank24.invRank_iff (mat_lt _ _)).1 (inv12 j j.2)).2
      omega
    have hf : Function.Injective f := by
      rintro (i | i) (j | j) hij
      · exact congrArg Sum.inl (Fin.ext (hinjC i i.2 j j.2
          (rc_inj (hcls i i.2).1 (hcls j j.2).1 (congrArg Subtype.val hij))))
      · exact absurd (rc_inj (hcls i i.2).1 (hcls2 j j.2).1 (congrArg Subtype.val hij)) (hrk i j)
      · exact absurd (rc_inj (hcls j j.2).1 (hcls2 i i.2).1 (congrArg Subtype.val hij).symm)
          (hrk j i)
      · exact congrArg Sum.inr (Fin.ext (hinjC2 i i.2 j j.2
          (rc_inj (hcls2 i i.2).1 (hcls2 j j.2).1 (congrArg Subtype.val hij))))
    have := Nat.card_le_card_of_injective f hf
    rwa [Nat.card_sum, Nat.card_fin, Nat.card_fin] at this
  · intro s hs hbs
    rw [Subgroup.mem_inf, mem_map_conj_inv] at hs hbs
    have hcard6 := hstabc 6 (hA' 6 (by norm_num)) (by norm_num)
    rw [g6] at hcard6
    have hex := stab_exhaust hφinj hcard6
      (E := fun k => mEl (Mgrp E.ThB_LT E.ThB_LI E.ThB_TL E.ThB_VL E.ThB_NL) (mat E.ThB_E6 k))
      (fun k hk k' hk' he => st6.2 k hk k' hk' (mEl_inj (st6.1 k hk).1 (st6.1 k' hk').1 he))
      (fun k hk => ⟨hφN _, (st6.1 k hk).2⟩)
    obtain ⟨j, hj, hje⟩ := hex s hs.1 hs.2
    obtain ⟨i, hi, hie⟩ := hex _ hbs.1 hbs.2
    have hIj := (st6.1 j hj).1
    have hje' : rc φ (mat E.ThB_E6 j) = s := hje
    have hprod : rc φ (mul24 (mul24 (let24 E.ThB_LT (byte E.ThB_LI 2)) (mat E.ThB_E6 j))
        (let24 E.ThB_LT 2)) = (xg 1)⁻¹ * s * xg 1 := by
      rw [rc_mul φ (InM_mul hI3 hIj) hI2, rc_mul φ hI3 hIj, hx3, hx2, hje']
    have hmat : mat E.ThB_E6 i = mul24 (mul24 (let24 E.ThB_LT (byte E.ThB_LI 2))
        (mat E.ThB_E6 j)) (let24 E.ThB_LT 2) :=
      rc_inj (st6.1 i hi).1 (InM_mul (InM_mul hI3 hIj) hI2) (hie.trans hprod.symm)
    rcases DceClass.coreOK_spec L159 j hj with h1 | h2
    · rw [← hje', h1, rc_one]
    · exact absurd hmat.symm (h2 i hi)

end Core

end CFSG.KC.Th.Spec.DceStr

end
