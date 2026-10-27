module

public import CFSG.Certificates.Kernel.DceS5Cover
public import CFSG.Certificates.Kernel.DceS5Walk

public section

namespace CFSG.Certificates.DS5

open CFSG.KC.Loop CFSG.KC.LL.Ly7 CFSG.KC.LyA.DceS CFSG.Certificates.DceLoop
  CFSG.Certificates.DceWord CFSG.Certificates.DceTw
open scoped Classical

set_option exponentiation.threshold 400

theorem tab_psi {TB OB RR : ℕ → ℕ} {LT TL VL NL NR nT I0 : ℕ} {Ct : List ℕ}
    (hT : runT TB OB RR LT TL VL NL NR nT I0 Ct 1 = nT + 1) :
    ∀ e < nT, ∃ ep < nT, tP TB e = tS TB ep := by
  rw [runT_eq] at hT
  intro e he
  obtain ⟨J, ht⟩ := cntRun_spec (a := 0) hT e (Nat.zero_le _) he
  exact (tOK_spec ht).2.2.1

theorem sortedCount_lt (S : ℕ) : sortedCount S < 2 ^ 20 := by
  unfold sortedCount
  change (S &&& 1048575) - 1 < 2 ^ 20
  rw [m20_eq, land_low]
  have := Nat.mod_lt S (Nat.two_pow_pos 20)
  omega

theorem dceOk_sound {FB HB GB TB WD OB RR : ℕ → ℕ}
    {sh wd LT LI TL VL NL ND NO nH nT nW NR NF I0 W Wi USQ UH WH AL MD NORD SUM qO qT : ℕ}
    {Cs : List ℕ} {S0 S1 : ℕ} {Hs : List ℕ} {H0 H1 : ℕ} {Gs : List ℕ} {G0 G1 : ℕ}
    {Os : List ℕ} {O0 O1 : ℕ} {TSs : List ℕ} {T0 T1 : ℕ} {Ts : List ℕ} {P0 P1 : ℕ}
    {Vs : List ℕ} {V0 V1 : ℕ}
    {stabs : List (ℕ × ((ℕ → ℕ) × (ℕ × (ℕ × (List ℕ × (ℕ × (ℕ × (List ℕ × (ℕ × ℕ)))))))))}
    (hok : dceOk FB HB GB TB WD OB RR sh wd LT LI TL VL NL ND NO nH nT nW NR NF I0 W Wi USQ UH WH
      AL MD NORD SUM qO qT Cs S0 S1 Hs H0 H1 Gs G0 G1 Os O0 O1 TSs T0 T1 Ts P0 P1 Vs V0 V1 stabs =
        true)
    (hN : ∀ (H : Type) [Group H] (y : ℕ → H),
      (∀ r < NR, nOnly TL VL NL (RR r) → rval y (RR r) = 1) →
      (∀ c < NL, isN TL VL NL c = true → y (byte LI c) = (y c)⁻¹) →
      Finite (Subgroup.closure (y '' {c | c < NL ∧ isN TL VL NL c = true})) ∧
        Nat.card (Subgroup.closure (y '' {c | c < NL ∧ isN TL VL NL c = true})) ≤ NORD)
    {G : Type*} [Group G] (x : ℕ → G)
    (hrels : ∀ r < NR, rval x (RR r) = 1)
    (hinv : ∀ c < NL, isN TL VL NL c = true → x (byte LI c) = (x c)⁻¹)
    (hu : x VL = (x TL)⁻¹) :
    Finite (Subgroup.closure (x '' {c | c < NL})) ∧
      Nat.card (Subgroup.closure (x '' {c | c < NL})) ≤ NORD * SUM := by
  unfold dceOk at hok
  obtain ⟨hc, hok⟩ := andL_iff.1 hok
  obtain ⟨hlet, hok⟩ := andL_iff.1 hok
  obtain ⟨hrel, hok⟩ := andL_iff.1 hok
  obtain ⟨hnorm, hok⟩ := andL_iff.1 hok
  obtain ⟨hwd, hok⟩ := andL_iff.1 hok
  obtain ⟨husq, hok⟩ := andL_iff.1 hok
  obtain ⟨hND, hok⟩ := andL_iff.1 hok
  obtain ⟨hI0, hok⟩ := andL_iff.1 hok
  obtain ⟨hnord, hok⟩ := andL_iff.1 hok
  obtain ⟨hsum, hok⟩ := andL_iff.1 hok
  obtain ⟨-, hok⟩ := andL_iff.1 hok
  obtain ⟨hH0, hok⟩ := andL_iff.1 hok
  obtain ⟨hhdr, hok⟩ := andL_iff.1 hok
  obtain ⟨hH1, hok⟩ := andL_iff.1 hok
  obtain ⟨hG0, hok⟩ := andL_iff.1 hok
  obtain ⟨hgom, hok⟩ := andL_iff.1 hok
  obtain ⟨hG1, hok⟩ := andL_iff.1 hok
  obtain ⟨hO0, hok⟩ := andL_iff.1 hok
  obtain ⟨hO, hok⟩ := andL_iff.1 hok
  obtain ⟨hO1, hok⟩ := andL_iff.1 hok
  obtain ⟨hT0, hok⟩ := andL_iff.1 hok
  obtain ⟨hTs, hok⟩ := andL_iff.1 hok
  obtain ⟨hT1, hok⟩ := andL_iff.1 hok
  obtain ⟨hP0, hok⟩ := andL_iff.1 hok
  obtain ⟨hT, hok⟩ := andL_iff.1 hok
  obtain ⟨hP1, hok⟩ := andL_iff.1 hok
  obtain ⟨hS0, hok⟩ := andL_iff.1 hok
  obtain ⟨hfac, hok⟩ := andL_iff.1 hok
  obtain ⟨hS1, hok⟩ := andL_iff.1 hok
  obtain ⟨hNF, hok⟩ := andL_iff.1 hok
  obtain ⟨hV0, hok⟩ := andL_iff.1 hok
  obtain ⟨hcov, hok⟩ := andL_iff.1 hok
  obtain ⟨hV1, hok⟩ := andL_iff.1 hok
  obtain ⟨hstabs, hscov⟩ := andL_iff.1 hok
  have hND' : ND < 255 := Nat.blt_eq.mp hND
  have hI0' : I0 < NO := Nat.blt_eq.mp hI0
  have hnord' : nT * NO = NORD := Nat.eq_of_beq_eq_true hnord
  obtain rfl : H0 = 1 := Nat.eq_of_beq_eq_true hH0
  obtain rfl : G0 = 1 := Nat.eq_of_beq_eq_true hG0
  obtain rfl : O0 = 1 := Nat.eq_of_beq_eq_true hO0
  obtain rfl : T0 = 1 := Nat.eq_of_beq_eq_true hT0
  obtain rfl : P0 = 1 := Nat.eq_of_beq_eq_true hP0
  obtain rfl : V0 = 1 := Nat.eq_of_beq_eq_true hV0
  obtain rfl : S0 = mkS 0 1 := Nat.eq_of_beq_eq_true hS0
  obtain rfl : H1 = nH + 1 := Nat.eq_of_beq_eq_true hH1
  obtain rfl : G1 = NO + 1 := Nat.eq_of_beq_eq_true hG1
  obtain rfl : P1 = nT + 1 := Nat.eq_of_beq_eq_true hP1
  have hhdr' := Nat.eq_of_beq_eq_true hhdr
  have hgom' := Nat.eq_of_beq_eq_true hgom
  have hO' := Nat.eq_of_beq_eq_true hO
  have hO1' := Nat.eq_of_beq_eq_true hO1
  have hTs' := Nat.eq_of_beq_eq_true hTs
  have hT1' := Nat.eq_of_beq_eq_true hT1
  have hT' := Nat.eq_of_beq_eq_true hT
  have hNO : NO < 2 ^ 20 := hO1' ▸ sortedCount_lt O1
  have hL := lettersOK_spec hlet
  obtain ⟨hm1, hm2⟩ := (relSet_iff (Lm LT LI TL VL NL)).1 (model_rels hc hL hrel)
  obtain ⟨hfin, hcard⟩ := hN Mat7ˣ (Lm LT LI TL VL NL) hm1 hm2
  have o := orb hc hL hfin hcard hhdr' hgom' hT' hI0' hO' hO1' hTs' hT1' hnord'
  have hM : NORD ≤ Nat.card (Mg LT LI TL VL NL) := (decompO o).1.ge
  obtain ⟨φ, hφ, hφN, hNφ⟩ := model_hom hc hL hrel hN hM x (fun r hr _ => hrels r hr) hinv
  have hg := gom_spec hc hL hhdr' hgom'
  have hθ : canonP (pt OB I0) = true := (hg I0 hI0').2.2.2.1
  have htab := tab_mem hc hL hT' hθ
  have hpsi := psi_sem hc hL φ hφ hrels hnorm hu hT' hθ
  have hus := usq_sem hc hL φ hφ hrels hnorm hinv husq
  have hSC : SCtx HB GB TB LT LI TL VL NL NO nT W Wi x φ :=
    ⟨hc, hL, hφ, hu, fun j hj => ⟨(hg j hj).1, (hg j hj).2.1, (hg j hj).2.2.1⟩,
      fun e he => ⟨(htab e he).1, (hpsi e he).1, (hpsi e he).2⟩,
      ⟨hus.1, hus.2.1, hus.2.2.1, hus.2.2.2.1⟩⟩
  have hwords' := words_sem hL hrels hnorm hinv hu hwd
  have hrun := Nat.eq_of_beq_eq_true hfac
  rw [runFacts_eq] at hrun
  obtain ⟨nxf, hf⟩ := factsG_spec hrun (Nat.blt_eq.mp hS1) (Nat.eq_of_beq_eq_true hNF)
  obtain ⟨w, hw0, hwt⟩ := exists_w (φ := φ) (x := x) hf
  have hfm := facts_mean hSC hND' hφN (hdr_mem hc hL hhdr') hwords' hf w hw0 hwt
  obtain ⟨hA0, hAL, hmD, hSUM⟩ := sumG_spec ((sumOK_eq AL MD ND NORD SUM) ▸ hsum)
  have hND0 : 0 < ND := by
    rcases Nat.eq_zero_or_pos ND with h0 | h0
    · rw [h0, pow_zero] at hAL
      have : AL = 0 := by omega
      rw [this, Nat.zero_testBit] at hA0
      exact absurd hA0 Bool.false_ne_true
    · exact h0
  let A : Finset ℕ := (Finset.range ND).filter fun D => AL.testBit D = true
  have hAmem : ∀ {D}, D ∈ A ↔ D < ND ∧ AL.testBit D = true := by
    intro D
    simp [A]
  have hAlt : ∀ D, AL.testBit D = true → D < ND := by
    intro D hD
    by_contra hge
    have : AL < 2 ^ D := lt_of_lt_of_le hAL (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [Nat.testBit_eq_false_of_lt this] at hD
    exact absurd hD Bool.false_ne_true
  have hcovS := coverRun_spec hNO (by omega) ((runCover_eq _ _ _ _ _ _ _ _ _) ▸
    Nat.eq_of_beq_eq_true hcov ▸ Nat.eq_of_beq_eq_true hV1)
  have hyp : Hyp (Ncl x TL VL NL) (x TL) (Mg LT LI TL VL NL) φ NORD Pt actP (ptS (pt OB I0))
      (fun j => ptS (pt OB j)) (fun j => mEl LT LI TL VL NL (gm HB GB j)) NO I0
      (fun e => mEl LT LI TL VL NL (tS TB e)) nT w A (mDG MD) := by
    refine ⟨hφN, hNφ, o, fun e he => ?_, ⟨mEl LT LI TL VL NL W, hus.2.2.2.1⟩, hAmem.2 ⟨hND0, hA0⟩,
      hw0, fun D hD j hj => ?_, fun D hD hD0 => (hmD D (hAmem.1 hD).1 (hAmem.1 hD).2 hD0).2,
      fun D hD hD0 => ?_⟩
    · obtain ⟨ep, hep, hPe⟩ := tab_psi hT' e he
      refine ⟨ep, hep, ?_⟩
      have := (hpsi e he).2
      rw [hPe] at this
      exact this
    · obtain ⟨xs, hs, hslot⟩ := hcovS D (hAmem.1 hD).1 (hAmem.1 hD).2 j hj
      obtain ⟨hg', hk⟩ := slotOK_spec hslot
      obtain ⟨hR, hRm, hFM⟩ := hfm _ hg'
      unfold FM RelT at hFM
      rcases hk with ⟨e1, e2, e3⟩ | ⟨e1, e2, e3, e4⟩
      · refine Or.inl ⟨_, hAmem.2 ⟨hR.dp, e3⟩, mEl LT LI TL VL NL (rPi (rec FB sh wd (xs >>> 1))), ?_⟩
        rw [e1, e2, uv, ite_eq_right (by omega), Nat.add_sub_cancel] at hFM
        exact hFM
      · have hj' : rJ (rec FB sh wd (xs >>> 1)) - 1 < NO := rJ_sub hR e2
        refine Or.inr ⟨_, hAmem.2 ⟨hR.d, e3⟩, _, hj', mEl LT LI TL VL NL (rPi (rec FB sh wd (xs >>> 1))),
          actOK_sound hc e4 (hg j hj).2.2.2.1 (hg _ hj').2.2.2.1 (valid7 hc hR.p) (mEl_val hRm), ?_⟩
        rw [e1, uv, ite_eq_right (by omega)] at hFM
        exact hFM
    · rcases stabCover_spec hscov D (hAmem.1 hD).1 hD0 (hAmem.1 hD).2 with h1 | ⟨s, hs, hsD⟩
      · exact Or.inl h1
      right
      obtain ⟨D', EB, SG, mD, C1, X0, X1, C2, Y0, Y1⟩ := s
      simp only [] at hsD
      subst hsD
      obtain ⟨hmd, hE, hEi⟩ := stab_sem hSC w (fun i hi => hfm i hi) (stabAll_spec hstabs _ hs)
      rw [← hmd]
      refine ⟨fun k => mEl LT LI TL VL NL (mat EB k), fun k hk k' hk' e => ?_, fun k hk => (hE k hk).2⟩
      have e' : mEl LT LI TL VL NL (mat EB k) = mEl LT LI TL VL NL (mat EB k') := e
      have e2 : (((mEl LT LI TL VL NL (mat EB k) : Mg LT LI TL VL NL) : Mat7ˣ) : Mat7) =
          (((mEl LT LI TL VL NL (mat EB k') : Mg LT LI TL VL NL) : Mat7ˣ) : Mat7) := by rw [e']
      rw [mEl_val (hE k hk).1, mEl_val (hE k' hk').1] at e2
      exact hEi k hk k' hk' (m7_inj (hE k hk).1.1 (hE k' hk').1.1 e2)
  have hX : ∀ y ∈ x '' {c | c < NL}, y ∈ Ncl x TL VL NL ∨ y = x TL ∨ y = (x TL)⁻¹ := by
    rintro _ ⟨c, hc', rfl⟩
    by_cases hNc : isN TL VL NL c = true
    · exact Or.inl (Subgroup.subset_closure ⟨c, ⟨hc', hNc⟩, rfl⟩)
    · have : c = TL ∨ c = VL := by
        by_contra hne
        push Not at hne
        exact hNc (isN_iff.2 ⟨hc', hne.1, hne.2⟩)
      rcases this with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr hu)
  obtain ⟨hfin', hcard'⟩ := dceTw_bound hyp _ hX
  have hA' : A.erase 0 = aliveSet AL ND := by
    ext D
    rw [Finset.mem_erase, hAmem]
    unfold aliveSet
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨fun ⟨h1, h2, h3⟩ => ⟨h2, h3, h1⟩, fun ⟨h1, h2, h3⟩ => ⟨h3, h1, h2⟩⟩
  refine ⟨hfin', hcard'.trans (le_of_eq ?_)⟩
  rw [hSUM, hA']

end CFSG.Certificates.DS5

end
