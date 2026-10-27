module

public import CFSG.Certificates.Kernel.EvenBN.Thm49ETOKSound
public import CFSG.LocalAnalysis.EvenBN.Tits.Thm49EF6K
public import CFSG.LocalAnalysis.EvenBN.Tits.Thm49ETOBasic
public import CFSG.LocalAnalysis.EvenBN.Tits.Thm49ETOMList

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.Thm49E

open Subgroup Certificates.Thm49E CFSG.Sporadic.Schreier.Tits CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.LocalAnalysis.EvenBN.Tits.Model CFSG.KD.T49 CFSG.KS.Raw.Orb
  CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw

section Gen

variable {W : TOW} {P : MPerms} {Q : KPerms}

structure GenSpec (W : TOW) (P : MPerms) : Prop where
  permF : ∀ j < 4, isPerm (W.F j) (W.FI j) = true
  permD : ∀ j < 2, isPerm (W.D j) (W.DI j) = true
  permZ : isPerm W.Z W.Z = true
  lzp : lettersK 4 zpWord = true
  lu1 : lettersK 4 u1Word = true
  lu2 : lettersK 4 u2Word = true
  ll2 : lettersK 4 l2Word = true
  ll3 : lettersK 4 l3Word = true
  le : lettersK 2 W.ew = true
  le1 : lettersK 2 W.e1w = true
  le1i : lettersK 2 W.e1iw = true
  u1 : P.u1 = wd W.F W.FI u1Word
  u2 : P.u2 = wd W.F W.FI u2Word
  u1i : isPerm P.u1 P.u1i = true
  u2i : isPerm P.u2 P.u2i = true
  zp : P.zp = wd W.F W.FI zpWord
  l1 : P.l1 = pmul (pmul (wd W.D W.DI W.e1w) W.Z) (wd W.D W.DI W.e1iw)
  eZ : pmul (wd W.D W.DI W.ew) W.Z = pmul P.zp (wd W.D W.DI W.ew)
  e0 : ap (wd W.D W.DI W.ew) 0 = W.yp
  e10 : ap (wd W.D W.DI W.e1w) 0 = W.r2
  e1inv : pmul (wd W.D W.DI W.e1w) (wd W.D W.DI W.e1iw) = idP
  u1Z : pmul P.u1 W.Z = pmul W.Z P.u1
  u2Z : pmul P.u2 W.Z = pmul W.Z P.u2
  u10 : ap P.u1 0 = 0
  u20 : ap P.u2 0 = 0
  fixZ : fixedK 1755 11 (mask 11) W.Z W.fz = true
  lenfz : W.fz.length = 91
  fz0 : W.fz.getD 0 0 = 0
  lenlb : W.lb.length = 91
  lenlw : W.lw.length = 91
  lw : ∀ w ∈ W.lw, lettersK 2 w = true
  labels : ∀ i < 91, W.lb.getD i 0 < 3 ∧
    wpt P.U P.UI (W.lw.getD i []) (pick3 0 W.yp W.r2 (W.lb.getD i 0)) = W.fz.getD i 0

theorem genSpec_of (h : checkGen W P = true) : GenSpec W P := by
  unfold checkGen mpermsOK commP at h
  simp only [CFSG.KS.Raw.Orb.bAnd_eq] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, ⟨m1, m2, m3, m4, m5, m6⟩, h13, h14, h15,
    h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27⟩ := h
  refine ⟨CFSG.KS.Raw.Orb.allN_iff.1 h1, CFSG.KS.Raw.Orb.allN_iff.1 h2, h3, h4, h5, h6, h7, h8, h9,
    h10, h11, Nat.eq_of_beq_eq_true m1, Nat.eq_of_beq_eq_true m2, m3,
    m4, Nat.eq_of_beq_eq_true m5, Nat.eq_of_beq_eq_true m6,
    Nat.eq_of_beq_eq_true h13, Nat.eq_of_beq_eq_true h14, Nat.eq_of_beq_eq_true h15,
    Nat.eq_of_beq_eq_true h16, Nat.eq_of_beq_eq_true h17, Nat.eq_of_beq_eq_true h18,
    Nat.eq_of_beq_eq_true h19, Nat.eq_of_beq_eq_true h20, h21, ?_, ?_, ?_, ?_,
    (allK_iff _ _).1 h26, fun i hi => ?_⟩
  · rw [← lenK_eq]
    exact Nat.eq_of_beq_eq_true h22
  · rw [← nthK_eq]
    exact Nat.eq_of_beq_eq_true h23
  · rw [← lenK_eq]
    exact Nat.eq_of_beq_eq_true h24
  · rw [← lenK_eq]
    exact Nat.eq_of_beq_eq_true h25
  · have := CFSG.KS.Raw.Orb.allN_iff.1 h27 i hi
    simp only [CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true] at this
    rw [← nthK_eq, ← nthW_eq, ← nthK_eq]
    exact ⟨Nat.blt_eq.mp this.1, Nat.eq_of_beq_eq_true this.2⟩

@[expose] noncomputable def uG (j : Nat) : Equiv.Perm (Fin 1755) :=
  if j = 0 then wordIn 4 titsGen u1Word else wordIn 4 titsGen u2Word

@[expose] noncomputable def baseG (W : TOW) (b : Nat) : Equiv.Perm (Fin 1755) :=
  if b = 0 then titsZ else if b = 1 then zpHat
    else wordIn 2 titsDGen W.e1w * titsZ * (wordIn 2 titsDGen W.e1w)⁻¹

@[expose] noncomputable def baseD (W : TOW) (b : Nat) : Equiv.Perm (Fin 1755) :=
  if b = 0 then 1 else if b = 1 then wordIn 2 titsDGen W.ew else wordIn 2 titsDGen W.e1w

@[expose] noncomputable def labC (W : TOW) (i : Nat) : Equiv.Perm (Fin 1755) :=
  wordIn 2 uG (W.lw.getD (i - 1) [])

@[expose] noncomputable def lamG (W : TOW) (i : Nat) : Equiv.Perm (Fin 1755) :=
  if i = 0 then 1 else labC W i * baseG W (W.lb.getD (i - 1) 0) * (labC W i)⁻¹

@[expose] noncomputable def mE (W : TOW) (i : Nat) : Cm := tauH * inA (lamG W i)

theorem tprepF (hW : TOOK W P Q) :
    ∀ j < 4, PR (W.F j) (titsGen j) :=
  fun j hj => prep_of_rep (by rw [← hW.bindF j hj]; exact titsGen_rep hj)

theorem tprepFI (hW : TOOK W P Q) :
    ∀ j < 4, PR (W.FI j) (titsGen j)⁻¹ :=
  fun j hj => prep_inv (tprepF hW j hj) ((genSpec_of hW.gen).permF j hj)

theorem tprepD (hW : TOOK W P Q) :
    ∀ j < 2, PR (W.D j) (titsDGen j) :=
  fun j hj => prep_of_rep (by
    rw [← hW.bindD j hj, ← titsDerived_perm hj]
    exact rep_of_allPermsOK titsChains_check.2.2.2.2.2.2.1 (by rw [titsDerivedArrs_size]; omega))

theorem tprepDI (hW : TOOK W P Q) :
    ∀ j < 2, PR (W.DI j) (titsDGen j)⁻¹ :=
  fun j hj => prep_inv (tprepD hW j hj) ((genSpec_of hW.gen).permD j hj)

theorem tprepZ (hW : TOOK W P Q) :
    PR W.Z titsZ :=
  prep_of_rep (by rw [← hW.bindZ]; exact titsZ_rep)

theorem U_zero (P : MPerms) : P.U 0 = P.u1 := rfl
theorem U_one (P : MPerms) : P.U 1 = P.u2 := rfl
theorem UI_zero (P : MPerms) : P.UI 0 = P.u1i := rfl
theorem UI_one (P : MPerms) : P.UI 1 = P.u2i := rfl
theorem uG_zero : uG 0 = wordIn 4 titsGen u1Word := by simp [uG]
theorem uG_one : uG 1 = wordIn 4 titsGen u2Word := by simp [uG]

theorem tprepU (hW : TOOK W P Q) : ∀ j < 2, PR (P.U j) (uG j) := by
  have G := genSpec_of hW.gen
  intro j hj
  rcases j with _ | _ | j
  · rw [U_zero, G.u1, uG_zero]
    exact prep_wd (tprepF hW) (tprepFI hW) G.lu1
  · rw [U_one, G.u2, uG_one]
    exact prep_wd (tprepF hW) (tprepFI hW) G.lu2
  · omega

theorem tprepUI (hW : TOOK W P Q) :
    ∀ j < 2, PR (P.UI j) (uG j)⁻¹ := by
  have G := genSpec_of hW.gen
  intro j hj
  have hU := tprepU hW j hj
  rcases j with _ | _ | j
  · rw [U_zero] at hU
    rw [UI_zero]
    exact prep_inv hU G.u1i
  · rw [U_one] at hU
    rw [UI_one]
    exact prep_inv hU G.u2i
  · omega

theorem e1_inv_eq (hW : TOOK W P Q) :
    wordIn 2 titsDGen W.e1iw = (wordIn 2 titsDGen W.e1w)⁻¹ := by
  have G := genSpec_of hW.gen
  exact eq_inv_of_mul_eq_one_right (eq_of_prep (prep_pmul (prep_wd (tprepD hW) (tprepDI hW) G.le1)
    (prep_wd (tprepD hW) (tprepDI hW) G.le1i)) prep_idP G.e1inv)

theorem tprepBase (hW : TOOK W P Q)
    {b : Nat} (hb : b < 3) : PR (pick3 W.Z P.zp P.l1 b) (baseG W b) := by
  have G := genSpec_of hW.gen
  unfold pick3 baseG
  rw [CFSG.KS.Raw.Orb.nIf_eq, CFSG.KS.Raw.Orb.nIf_eq]
  rcases b with _ | _ | _ | b
  · simpa using tprepZ hW
  · simp only [if_neg (show ¬ (Nat.beq 1 0 = true) by decide), Nat.beq_refl, if_true,
      if_neg (show (1 : Nat) ≠ 0 by decide)]
    rw [G.zp]
    exact prep_wd (tprepF hW) (tprepFI hW) G.lzp
  · simp only [if_neg (show ¬ (Nat.beq 2 0 = true) by decide),
      if_neg (show ¬ (Nat.beq 2 1 = true) by decide), if_neg (show (2 : Nat) ≠ 0 by decide),
      if_neg (show (2 : Nat) ≠ 1 by decide)]
    rw [G.l1, ← e1_inv_eq hW]
    exact prep_pmul (prep_pmul (prep_wd (tprepD hW) (tprepDI hW) G.le1) (tprepZ hW))
      (prep_wd (tprepD hW) (tprepDI hW) G.le1i)
  · omega

theorem lw_letters (hW : TOOK W P Q) {i : Nat} (hi : i < 91) : lettersK 2 (W.lw.getD i []) = true := by
  have G := genSpec_of hW.gen
  apply G.lw
  rw [getD_eq_idx (by rw [G.lenlw]; exact hi)]
  exact List.getElem_mem _

theorem lamK_eq (hW : TOOK W P Q)
    {i : Nat} (hi : i < 92) (x : Fin 1755) : lamK W P i x = (lamG W i x : Nat) := by
  have G := genSpec_of hW.gen
  unfold lamK lamG
  rw [CFSG.KS.Raw.Orb.nIf_eq]
  by_cases h0 : i = 0
  · subst h0
    simp
  · rw [if_neg (by rw [Nat.beq_eq]; exact h0), if_neg h0, nthK_eq, nthW_eq,
      show Nat.sub i 1 = i - 1 from rfl]
    have hl := lw_letters hW (i := i - 1) (by omega)
    have hb := (G.labels (i - 1) (by omega)).1
    unfold lamPt
    rw [wipt_eq (tprepU hW) (tprepUI hW) hl x]
    have e1 := ap_eq (tprepBase hW hb) ((wordIn 2 uG (W.lw.getD (i - 1) []))⁻¹ x)
    rw [e1]
    have e2 := wpt_eq (tprepU hW) (tprepUI hW) hl
      (baseG W (W.lb.getD (i - 1) 0) ((wordIn 2 uG (W.lw.getD (i - 1) []))⁻¹ x))
    rw [e2]
    rfl

theorem uG_mem (hW : TOOK W P Q) :
    ∀ j < 2, uG j ∈ titsHZ0 := by
  have G := genSpec_of hW.gen
  have h0 : (0 : Nat) < 1755 := by norm_num
  intro j hj
  rw [mem_titsHZ0]
  have hU := tprepU hW j hj
  refine ⟨?_, ?_, ?_⟩
  · unfold uG
    split_ifs
    · exact wordIn_mem_titsA' _
    · exact wordIn_mem_titsA' _
  · rcases j with _ | _ | j
    · exact mul_eq_of hU (tprepZ hW) (tprepZ hW) hU G.u1Z
    · exact mul_eq_of hU (tprepZ hW) (tprepZ hW) hU G.u2Z
    · omega
  · rw [fin_zero_eq]
    rcases j with _ | _ | j
    · exact fin_eq_of_ap hU h0 G.u10
    · exact fin_eq_of_ap hU h0 G.u20
    · omega

theorem labC_mem (hW : TOOK W P Q)
    (i : Nat) : labC W i ∈ titsHZ0 :=
  wordIn_mem (uG_mem hW) _

@[expose] noncomputable def baseRoot (W : TOW) (b : Nat) : Nat := pick3 0 W.yp W.r2 b

theorem baseD_spec (hW : TOOK W P Q)
    {b : Nat} (hb : b < 3) : baseD W b ∈ titsD ∧ ((baseD W b 0 : Fin 1755) : Nat) = baseRoot W b ∧
      baseG W b = baseD W b * titsZ * (baseD W b)⁻¹ := by
  have G := genSpec_of hW.gen
  have h0 : (0 : Nat) < 1755 := by norm_num
  rcases b with _ | _ | _ | b
  · have eD : baseD W 0 = 1 := by simp [baseD]
    have eG : baseG W 0 = titsZ := by simp [baseG]
    have eR : baseRoot W 0 = 0 := rfl
    rw [eD, eG, eR]
    exact ⟨one_mem _, rfl, by group⟩
  · have eD : baseD W 1 = wordIn 2 titsDGen W.ew := by simp [baseD]
    have eG : baseG W 1 = zpHat := by simp [baseG]
    have eR : baseRoot W 1 = W.yp := rfl
    rw [eD, eG, eR]
    have he := prep_wd (tprepD hW) (tprepDI hW) G.le
    have hzp : PR P.zp zpHat := by rw [G.zp]; exact prep_wd (tprepF hW) (tprepFI hW) G.lzp
    refine ⟨wordIn_titsD_mem _, by rw [fin_zero_eq, ← ap_eq' he h0, G.e0], ?_⟩
    exact (conj_of_mul (mul_eq_of he (tprepZ hW) hzp he G.eZ)).symm
  · have eD : baseD W 2 = wordIn 2 titsDGen W.e1w := by simp [baseD]
    have eG : baseG W 2 = wordIn 2 titsDGen W.e1w * titsZ * (wordIn 2 titsDGen W.e1w)⁻¹ := by
      simp [baseG]
    have eR : baseRoot W 2 = W.r2 := rfl
    rw [eD, eG, eR]
    have he1 := prep_wd (tprepD hW) (tprepDI hW) G.le1
    exact ⟨wordIn_titsD_mem _, by rw [fin_zero_eq, ← ap_eq' he1 h0, G.e10], rfl⟩
  · omega

@[expose] noncomputable def labD (W : TOW) (i : Nat) : Equiv.Perm (Fin 1755) :=
  labC W i * baseD W (W.lb.getD (i - 1) 0) * (labC W i)⁻¹

theorem labD_spec (hW : TOOK W P Q)
    {i : Nat} (hi1 : 1 ≤ i) (hi : i < 92) : labD W i ∈ titsD ∧
      ((labD W i 0 : Fin 1755) : Nat) = W.fz.getD (i - 1) 0 ∧
      lamG W i = labD W i * titsZ * (labD W i)⁻¹ := by
  have G := genSpec_of hW.gen
  obtain ⟨hb, hlab⟩ := G.labels (i - 1) (by omega)
  obtain ⟨hD, hD0, hDz⟩ := baseD_spec hW hb
  obtain ⟨hcA, hcz, hc0⟩ := mem_titsHZ0.1 (labC_mem hW i)
  obtain ⟨hgD, hg0, hgc⟩ := conj_conj_titsZ hcA hcz hc0 hD
  refine ⟨hgD, ?_, ?_⟩
  · unfold labD
    rw [hg0]
    have hD0' : baseD W (W.lb.getD (i - 1) 0) 0 =
        ⟨baseRoot W (W.lb.getD (i - 1) 0), by rw [← hD0]; exact (baseD W _ 0).2⟩ := Fin.ext hD0
    rw [hD0', ← hlab]
    have hl := lw_letters hW (i := i - 1) (by omega)
    have := wpt_eq (tprepU hW) (tprepUI hW) hl ⟨baseRoot W (W.lb.getD (i - 1) 0), by
      rw [← hD0]; exact (baseD W _ 0).2⟩
    exact this.symm
  · unfold lamG labD
    rw [if_neg (by omega), hDz]
    exact hgc

end Gen

structure LabFacts : Prop where
  conj_iff : ∀ {e e' : Equiv.Perm (Fin 1755)}, e ∈ titsD → e' ∈ titsD →
    (e * titsZ * e⁻¹ = e' * titsZ * e'⁻¹ ↔ e 0 = e' 0)

theorem labFacts :
    LabFacts :=
  ⟨fun he he' => conj_titsZ_eq_iff he he'⟩

section M

variable {W : TOW} {P : MPerms} {Q : KPerms}

theorem lamG_zero : lamG W 0 = 1 := by simp [lamG]

theorem mE_zero : mE W 0 = tauH := by simp [mE, lamG_zero, inA]

theorem fz_facts (hW : TOOK W P Q) :
    W.fz.Nodup ∧ (∀ y ∈ W.fz, y < 1755) ∧ ∀ x : Fin 1755, (x : Nat) ∈ W.fz ↔ titsZ x = x := by
  have G := genSpec_of hW.gen
  refine ⟨?_, ?_, mem_fixed (tprepZ hW) G.fixZ⟩
  · rw [← fixedK_sound G.fixZ, CFSG.Certificates.Native.fixedList]
    exact List.nodup_range.filter _
  · intro y hy
    rw [← fixedK_sound G.fixZ, CFSG.Certificates.Native.fixedList, List.mem_filter,
      List.mem_range] at hy
    exact hy.1

theorem lamG_facts (LF : LabFacts)
    (hW : TOOK W P Q) {i : Nat} (hi : i < 92) :
    lamG W i ∈ titsD ∧ lamG W i * titsZ = titsZ * lamG W i ∧ lamG W i * lamG W i = 1 := by
  have hzD : titsZ ∈ titsD := titsZ_mem_titsD
  have hz2 : titsZ * titsZ = 1 := by
    have G := genSpec_of hW.gen
    have hZi : PR W.Z titsZ⁻¹ := prep_inv (tprepZ hW) G.permZ
    have e : titsZ = titsZ⁻¹ := eq_of_prep (tprepZ hW) hZi rfl
    nth_rewrite 2 [e]
    exact mul_inv_cancel _
  by_cases h0 : i = 0
  · subst h0
    simp [lamG_zero]
  obtain ⟨hD, hD0, hl⟩ := labD_spec hW (by omega) hi
  rw [hl]
  refine ⟨mul_mem (mul_mem hD hzD) (inv_mem hD), ?_, by
    calc labD W i * titsZ * (labD W i)⁻¹ * (labD W i * titsZ * (labD W i)⁻¹) =
        labD W i * (titsZ * titsZ) * (labD W i)⁻¹ := by group
      _ = 1 := by rw [hz2]; group⟩
  have hfix : titsZ (labD W i 0) = labD W i 0 := by
    have hmem : W.fz.getD (i - 1) 0 ∈ W.fz := by
      have G := genSpec_of hW.gen
      rw [getD_eq_idx (by rw [G.lenfz]; omega)]
      exact List.getElem_mem _
    rw [← hD0] at hmem
    exact ((fz_facts hW).2.2 _).1 hmem
  have h1 := (LF.conj_iff (mul_mem hzD hD) hD).2 (by rw [Equiv.Perm.mul_apply, hfix])
  calc labD W i * titsZ * (labD W i)⁻¹ * titsZ =
      (titsZ * labD W i) * titsZ * (titsZ * labD W i)⁻¹ * titsZ := by rw [h1]
    _ = titsZ * (labD W i * titsZ * (labD W i)⁻¹) := by group

theorem titsZ_sq' (hW : TOOK W P Q) :
    titsZ * titsZ = 1 := by
  have G := genSpec_of hW.gen
  have hZi : PR W.Z titsZ⁻¹ := prep_inv (tprepZ hW) G.permZ
  have e : titsZ = titsZ⁻¹ := eq_of_prep (tprepZ hW) hZi rfl
  nth_rewrite 2 [e]
  exact mul_inv_cancel _

theorem mE_mem (LF : LabFacts)
    (hW : TOOK W P Q) {i : Nat} (hi : i < 92) : mE W i ∈ MH ∧ mE W i ∈ GammaH := by
  by_cases h0 : i = 0
  · subst h0
    rw [mE_zero]
    exact ⟨Or.inl rfl, tau_mem_GammaH⟩
  · obtain ⟨hD, -, hl⟩ := labD_spec hW (by omega) hi
    obtain ⟨-, hc, -⟩ := lamG_facts LF hW hi
    exact tau_inA_mem ⟨labD W i, hD, hl.symm⟩ hc

theorem label_fix (LF : LabFacts)
    (hW : TOOK W P Q) {d : Equiv.Perm (Fin 1755)} (hd : d ∈ titsD)
    (hc : d * titsZ * d⁻¹ * titsZ = titsZ * (d * titsZ * d⁻¹)) : titsZ (d 0) = d 0 := by
  have hzD : titsZ ∈ titsD := titsZ_mem_titsD
  have hz2 := titsZ_sq' hW
  have h1 : (titsZ * d) * titsZ * (titsZ * d)⁻¹ = d * titsZ * d⁻¹ := by
    calc (titsZ * d) * titsZ * (titsZ * d)⁻¹ = titsZ * (d * titsZ * d⁻¹) * titsZ⁻¹ := by group
      _ = d * titsZ * d⁻¹ * titsZ * titsZ⁻¹ := by rw [hc]
      _ = d * titsZ * d⁻¹ := by group
  have := (LF.conj_iff (mul_mem hzD hd) hd).1 h1
  rwa [Equiv.Perm.mul_apply] at this

theorem mE_complete (LF : LabFacts)
    (hW : TOOK W P Q) {m : Cm} (hm : m ∈ MH) : ∃ i < 92, mE W i = m := by
  have G := genSpec_of hW.gen
  rcases hm with rfl | ⟨l, ⟨d, hd, rfl⟩, hc, rfl⟩
  · exact ⟨0, by norm_num, mE_zero⟩
  · have hfix := label_fix LF hW hd hc
    have hmem : ((d 0 : Fin 1755) : Nat) ∈ W.fz := ((fz_facts hW).2.2 _).2 hfix
    obtain ⟨k, hk, hkv⟩ := List.mem_iff_getElem.1 hmem
    have hk' : k < 91 := by rw [← G.lenfz]; exact hk
    obtain ⟨hD, hD0, hl⟩ := labD_spec hW (i := k + 1) (by omega) (by omega)
    refine ⟨k + 1, by omega, ?_⟩
    unfold mE
    rw [hl, (LF.conj_iff hD hd).2 (Fin.ext (by
      rw [hD0, show k + 1 - 1 = k from rfl, getD_eq_idx hk, hkv]))]

structure TabSpec (W : TOW) (P : MPerms) : Prop where
  s1 : W.s1 < 1755
  s2 : W.s2 < 1755
  keys : ∀ i < 92, ∀ j < i, tg 22 (keysK W P) i ≠ tg 22 (keysK W P) j
  mt : ∀ i < 92, ∀ m < 92, mtK W i m = mactK W P (fzIdx W.fz) i m
  pt : ∀ p < 92, ∀ q < 92, ptOK (keysK W P) (keyPQ W P p q) (ptK W p q) = true
  abt : ∀ p < 92, ∀ q < 92, abK W p q = tg 10 W.RK (lamK W P p (lamK W P q W.b1))

theorem tabSpec_of (h : checkTab W P = true) : TabSpec W P := by
  unfold checkTab at h
  simp only [CFSG.KS.Raw.Orb.bAnd_eq, CFSG.KS.Raw.Orb.strictB_eq] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨Nat.blt_eq.mp h1, Nat.blt_eq.mp h2, fun i hi j hj => ?_,
    fun i hi m hm => Nat.eq_of_beq_eq_true
      (CFSG.KS.Raw.Orb.allN_iff.1 (CFSG.KS.Raw.Orb.allN_iff.1 h4 i hi) m hm),
    fun p hp q hq => CFSG.KS.Raw.Orb.allN_iff.1 (CFSG.KS.Raw.Orb.allN_iff.1 h5 p hp) q hq,
    fun p hp q hq => Nat.eq_of_beq_eq_true
      (CFSG.KS.Raw.Orb.allN_iff.1 (CFSG.KS.Raw.Orb.allN_iff.1 h6 p hp) q hq)⟩
  have := CFSG.KS.Raw.Orb.allN_iff.1 (CFSG.KS.Raw.Orb.allN_iff.1 h3 i hi) j hj
  intro e
  rw [CFSG.KS.Raw.Orb.bIf_eq, if_pos (by rw [Nat.beq_eq]; exact e)] at this
  exact Bool.noConfusion this

theorem lamK_lt (hW : TOOK W P Q)
    {i : Nat} (hi : i < 92) {x : Nat} (hx : x < 1755) : lamK W P i x < 1755 := by
  rw [lamK_eq hW hi ⟨x, hx⟩]
  exact (lamG W i _).2

theorem tg_keysK (hW : TOOK W P Q)
    {i : Nat} (hi : i < 92) : tg 22 (keysK W P) i = keyM W P i := by
  have T := tabSpec_of hW.tab
  unfold keysK
  rw [tg_recSet 92 (fun m hm => by
    unfold keyM
    have h1 := lamK_lt hW hm T.s1
    have h2 := lamK_lt hW hm T.s2
    change lamK W P m W.s1 + lamK W P m W.s2 <<< 11 < 2 ^ 22
    rw [Nat.shiftLeft_eq]
    have : (2 : Nat) ^ 22 = 2048 * 2 ^ 11 := by norm_num
    have : (2 : Nat) ^ 11 = 2048 := by norm_num
    nlinarith) i, if_pos hi]

theorem lamG_inj (hW : TOOK W P Q)
    {i j : Nat} (hi : i < 92) (hj : j < 92) (e : lamG W i = lamG W j) : i = j := by
  have T := tabSpec_of hW.tab
  have hk : keyM W P i = keyM W P j := by
    unfold keyM
    rw [lamK_eq hW hi ⟨_, T.s1⟩, lamK_eq hW hi ⟨_, T.s2⟩, lamK_eq hW hj ⟨_, T.s1⟩,
      lamK_eq hW hj ⟨_, T.s2⟩, e]
  rw [← tg_keysK hW hi, ← tg_keysK hW hj] at hk
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · exact T.keys j hj i h hk.symm
  · exact T.keys i hi j h hk

theorem mE_inj (hW : TOOK W P Q)
    {i j : Nat} (hi : i < 92) (hj : j < 92) (e : mE W i = mE W j) : i = j := by
  apply lamG_inj hW hi hj
  unfold mE at e
  have := congrArg Prod.snd e
  simpa [inA, tauH] using this

theorem fz_getD_lt (hW : TOOK W P Q)
    {k : Nat} (hk : k < 91) : W.fz.getD k 0 < 1755 := by
  have G := genSpec_of hW.gen
  apply (fz_facts hW).2.1
  rw [getD_eq_idx (by rw [G.lenfz]; exact hk)]
  exact List.getElem_mem _

theorem mE_mt (LF : LabFacts)
    (hW : TOOK W P Q) {i m : Nat} (hi : i < 92) (hm : m < 92) :
    mtK W i m < 92 ∧ mE W (mtK W i m) = mE W i * mE W m * mE W i := by
  have G := genSpec_of hW.gen
  have T := tabSpec_of hW.tab
  have htc : ∀ x : Cm, tauH * x = x * tauH := fun x => by
    ext <;> simp [tauH]
  have htt : tauH * tauH = 1 := by
    ext <;> simp [tauH]
  rw [T.mt i hi m hm]
  unfold mactK
  rw [CFSG.KS.Raw.Orb.nIf_eq]
  by_cases h0 : i = 0
  · subst h0
    rw [if_pos (Nat.beq_refl 0)]
    refine ⟨hm, ?_⟩
    rw [mE_zero, htc, mul_assoc, htt, mul_one]
  rw [if_neg (by rw [Nat.beq_eq]; exact h0), CFSG.KS.Raw.Orb.nIf_eq]
  obtain ⟨-, -, hii⟩ := lamG_facts LF hW hi
  by_cases hm0 : m = 0
  · subst hm0
    rw [if_pos (Nat.beq_refl 0)]
    refine ⟨by norm_num, ?_⟩
    rw [mE_zero]
    unfold mE
    refine Prod.ext ?_ ?_
    · simp [tauH, inA]
    · simp [tauH, inA, hii]
  rw [if_neg (by rw [Nat.beq_eq]; exact hm0), nthK_eq, show Nat.sub m 1 = m - 1 from rfl]
  have hy := fz_getD_lt hW (k := m - 1) (by omega)
  obtain ⟨hDm, hDm0, hlm⟩ := labD_spec hW (i := m) (by omega) hm
  obtain ⟨hDi, -, hcz, -⟩ : lamG W i ∈ titsD ∧ True ∧ lamG W i * titsZ = titsZ * lamG W i ∧ True :=
    ⟨(lamG_facts LF hW hi).1, trivial, (lamG_facts LF hW hi).2.1, trivial⟩
  set y : Fin 1755 := lamG W i ⟨W.fz.getD (m - 1) 0, hy⟩ with hydef
  have hyfix : titsZ y = y := by
    have hz0 : titsZ ⟨W.fz.getD (m - 1) 0, hy⟩ = ⟨W.fz.getD (m - 1) 0, hy⟩ := by
      apply ((fz_facts hW).2.2 _).1
      change W.fz.getD (m - 1) 0 ∈ W.fz
      rw [getD_eq_idx (by rw [G.lenfz]; omega)]
      exact List.getElem_mem _
    rw [hydef, ← Equiv.Perm.mul_apply, ← hcz, Equiv.Perm.mul_apply, hz0]
  obtain ⟨k, hk, hkv⟩ := List.mem_iff_getElem.1 (((fz_facts hW).2.2 y).2 hyfix)
  have hk' : k < 91 := by rw [← G.lenfz]; exact hk
  have hidx : tg 7 (fzIdx W.fz) (lamK W P i (W.fz.getD (m - 1) 0)) = k + 1 := by
    rw [lamK_eq hW hi ⟨_, hy⟩, ← hydef, ← hkv, ← getD_eq_idx hk]
    exact tg_fzIdx (fz_facts hW).1 (by rw [G.lenfz]; norm_num) hk
  rw [hidx]
  refine ⟨by omega, ?_⟩
  obtain ⟨hDk, hDk0, hlk⟩ := labD_spec hW (i := k + 1) (by omega) (by omega)
  have hl : lamG W (k + 1) = lamG W i * lamG W m * lamG W i := by
    have hinv : (lamG W i)⁻¹ = lamG W i := inv_eq_of_mul_eq_one_right hii
    rw [hlk, hlm]
    have e2 : lamG W i * (labD W m * titsZ * (labD W m)⁻¹) * lamG W i =
        (lamG W i * labD W m) * titsZ * (lamG W i * labD W m)⁻¹ := by
      nth_rewrite 2 [← hinv]
      group
    rw [e2]
    refine (LF.conj_iff hDk (mul_mem hDi hDm)).2 (Fin.ext ?_)
    rw [hDk0, Equiv.Perm.mul_apply]
    have : labD W m 0 = ⟨W.fz.getD (m - 1) 0, hy⟩ := Fin.ext hDm0
    rw [this, ← hydef, ← hkv, show k + 1 - 1 = k from rfl, getD_eq_idx hk]
  unfold mE
  rw [hl]
  refine Prod.ext ?_ ?_
  · simp [tauH, inA]
  · simp [tauH, inA, mul_assoc]

theorem pt_eq (hW : TOOK W P Q)
    {p q w : Nat} (hp : p < 92) (hq : q < 92) (hw : w < 92)
    (h : lamG W w = titsZ * lamG W p * lamG W q) : ptK W p q = w := by
  have T := tabSpec_of hW.tab
  have hk : keyPQ W P p q = tg 22 (keysK W P) w := by
    rw [tg_keysK hW hw]
    unfold keyPQ keyM
    have hZ := tprepZ hW
    rw [lamK_eq hW hq ⟨_, T.s1⟩, lamK_eq hW hp ⟨_, (lamG W q _).2⟩, ap_eq hZ,
      lamK_eq hW hq ⟨_, T.s2⟩, lamK_eq hW hp ⟨_, (lamG W q _).2⟩, ap_eq hZ,
      lamK_eq hW hw ⟨_, T.s1⟩, lamK_eq hW hw ⟨_, T.s2⟩, h, Equiv.Perm.mul_apply,
      Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
  have := T.pt p hp q hq
  unfold ptOK at this
  rw [CFSG.KS.Raw.Orb.bIf_eq] at this
  by_cases hlt : ptK W p q < 92
  · rw [if_pos (Nat.blt_eq.mpr hlt), Nat.beq_eq, hk] at this
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h1 | h1
    · exact T.keys w hw _ h1 this.symm
    · exact T.keys _ hlt w h1 this
  · rw [if_neg (by rw [Nat.blt_eq]; exact hlt)] at this
    have := CFSG.KS.Raw.Orb.allN_iff.1 this w hw
    rw [CFSG.KS.Raw.Orb.bIf_eq, if_pos (by rw [Nat.beq_eq]; exact hk.symm)] at this
    exact absurd this Bool.false_ne_true

structure StepsSpec (W : TOW) (P : MPerms) : Prop where
  ig0 : igK W 0 = 0
  ig1 : igK W 1 = 1
  ig2 : igK W 2 < 92
  ig3 : igK W 3 < 92
  ig4 : igK W 4 < 92
  ig2pos : 0 < igK W 2
  ig2y : W.fz.getD (igK W 2 - 1) 0 = W.yp
  l2 : ∀ x < 1755, lamK W P (igK W 3) x = ap (wd W.F W.FI l2Word) x
  l3 : ∀ x < 1755, lamK W P (igK W 4) x = ap (wd W.F W.FI l3Word) x
  igd : ∀ l < 5, ∀ l' < l, igK W l ≠ igK W l'
  steps : stepsOK W W.steps (rootMask W) = true
  closed : ∀ x ∈ covK W, ∀ l < 5, mtK W (igK W l) x ∈ covK W
  ps : ∀ r ∈ W.psteps, fy r < 92 ∧ fx r ∈ covK W ∧ fl r ∈ covK W ∧
    ∀ x < 1755, lamK W P (fy r) x = lamK W P (fx r) (lamK W P (fl r) x)
  cover : ∀ y < 92, y ∈ covK W ∨ y ∈ W.psteps.map fy

theorem stepsSpec_of (h : checkSteps W P = true) : StepsSpec W P := by
  unfold checkSteps at h
  simp only [CFSG.KS.Raw.Orb.bAnd_eq, CFSG.KS.Raw.Orb.strictB_eq] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  refine ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2, Nat.blt_eq.mp h3, Nat.blt_eq.mp h4,
    Nat.blt_eq.mp h5, Nat.blt_eq.mp h6, ?_,
    fun x hx => Nat.eq_of_beq_eq_true (CFSG.KS.Raw.Orb.allN_iff.1 h8 x hx),
    fun x hx => Nat.eq_of_beq_eq_true (CFSG.KS.Raw.Orb.allN_iff.1 h9 x hx), ?_, h11, ?_, ?_, ?_⟩
  · rw [← nthK_eq]
    exact Nat.eq_of_beq_eq_true h7
  · intro l hl l' hl' e
    have := CFSG.KS.Raw.Orb.allN_iff.1 (CFSG.KS.Raw.Orb.allN_iff.1 h10 l hl) l' hl'
    rw [CFSG.KS.Raw.Orb.bIf_eq, if_pos (by rw [Nat.beq_eq]; exact e)] at this
    exact Bool.noConfusion this
  · intro x hx l hl
    have := CFSG.KS.Raw.Orb.allN_iff.1 ((allK_iff _ _).1 h12 x hx) l hl
    exact (maskL_iff _ _).1 this
  · intro r hr
    have := (allK_iff _ _).1 h13 r hr
    simp only [CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true] at this
    obtain ⟨a1, a2, a3, a4⟩ := this
    exact ⟨Nat.blt_eq.mp a1, (maskL_iff _ _).1 a2, (maskL_iff _ _).1 a3,
      fun x hx => Nat.eq_of_beq_eq_true (CFSG.KS.Raw.Orb.allN_iff.1 a4 x hx)⟩
  · intro y hy
    have := CFSG.KS.Raw.Orb.allN_iff.1 h14 y hy
    rw [CFSG.KS.Raw.Orb.bIf_eq] at this
    by_cases hb : bitK (maskL (covK W)) y = true
    · exact Or.inl ((maskL_iff _ _).1 hb)
    · rw [if_neg hb, memK_iff, mapFy_eq] at this
      exact Or.inr this

end M

section Codes

variable {W : TOW} {P : MPerms} {Q : KPerms}

@[expose] noncomputable def RgK (W : TOW) (j : Nat) : Cm :=
  if j = 0 then inA (wordIn 4 titsGen h1Word) else if j = 1 then inA (wordIn 4 titsGen h2Word)
    else if j = 2 then inA (lamG W W.a * lamG W W.b) else tauH

noncomputable def kap (W : TOW) (c : Nat) : Cm :=
  if h : parK W c < c then kap W (parK W c) * RgK W (genK W c) else 1
termination_by c
decreasing_by exact h

theorem kap_of_lt {c : Nat} (h : parK W c < c) : kap W c = kap W (parK W c) * RgK W (genK W c) := by
  rw [kap, dif_pos h]

theorem kap_zero : kap W 0 = 1 := by
  rw [kap, dif_neg (Nat.not_lt_zero _)]

@[expose] noncomputable def bitOf (x : Cm) : Nat := if x.1 = 1 then 0 else 1

@[expose] noncomputable def keyCm (W : TOW) (hb : W.b1 < 1755) (x : Cm) : Nat :=
  bitOf x * 2048 + (x.2 ⟨W.b1, hb⟩ : Nat)

structure KSpec (W : TOW) (P : MPerms) (Q : KPerms) : Prop where
  h1 : Q.h1 = wd W.F W.FI h1Word
  h2 : Q.h2 = wd W.F W.FI h2Word
  y0 : Q.y0 = wd W.F W.FI y0Word
  y0i : isPerm Q.y0 Q.y0i = true
  zp : Q.zp = P.zp
  la : ∀ x < 1755, ap Q.la x = lamK W P W.a x
  lbb : ∀ x < 1755, ap Q.lbb x = lamK W P W.b x
  lh1 : lettersK 4 h1Word = true
  lh2 : lettersK 4 h2Word = true
  ly0 : lettersK 4 y0Word = true
  a : W.a < 92
  b : W.b < 92
  b1 : W.b1 < 1755
  h1Z : pmul Q.h1 W.Z = pmul W.Z Q.h1
  h1zp : pmul Q.h1 Q.zp = pmul Q.zp Q.h1
  h10 : ap Q.h1 0 = 0
  h2Z : pmul Q.h2 W.Z = pmul W.Z Q.h2
  h2zp : pmul Q.h2 Q.zp = pmul Q.zp Q.h2
  h20 : ap Q.h2 0 = 0
  abZ : pmul (pmul Q.la Q.lbb) W.Z = pmul W.Z (pmul Q.la Q.lbb)
  abzp : pmul (pmul Q.la Q.lbb) Q.zp = pmul Q.zp (pmul Q.la Q.lbb)
  par1 : parK W 1 = 0
  gen1 : genK W 1 = 0
  par2 : parK W 2 = 0
  gen2 : genK W 2 = 1
  tree : ∀ c < 512, c ≠ 0 → parK W c < c ∧ genK W c < 4 ∧ reachF W 16 c = true
  rk : ∀ c < 512, tg 10 W.RK (keyF W Q c) = c + 1
  tT : ∀ c < 512, ∀ j < 4, tg 10 W.RK (Nat.mul (Nat.xor (bitF W 16 c) (bitR j)) 2048 +
    kptF W Q.R 16 c (Q.R j W.b1)) = tg 9 W.T (4 * c + j) + 1
  tY : ∀ c < 512, tg 10 W.RK (Nat.mul (bitF W 16 c) 2048 +
    ap Q.y0 (kptF W Q.R 16 c (ap Q.y0i W.b1))) = tg 9 W.Y c + 1
  mc1 : tg 10 W.RK (2048 + ap W.Z W.b1) = W.mc1 + 1
  lenKA : W.KA.length = 512
  ka : kaOK W (fzIdx W.fz) Q W.KA 0 = true
  t0 : W.t0 < 512
  t1 : W.t1 < 512
  mc1lt : W.mc1 < 512
  cl0lt : ∀ c ∈ W.cl0, c < 512
  cl1lt : ∀ c ∈ W.cl1, c < 512
  cl0 : ∀ d < 512, ∃ c ∈ W.cl0, mulF W 16 c d = mulF W 16 d W.t0
  cl1 : ∀ d < 512, ∃ c ∈ W.cl1, mulF W 16 c d = mulF W 16 d W.t1

theorem anyCl_iff (W : TOW) (d t : Nat) : ∀ l : List Nat,
    List.rec (motive := fun _ => Bool) false
      (fun c _ ih => bIf(Nat.beq (mulF W 16 c d) (mulF W 16 d t), true, ih)) l = true ↔
    ∃ c ∈ l, mulF W 16 c d = mulF W 16 d t
  | [] => by simp
  | c :: l => by
    have ih := anyCl_iff W d t l
    change Bool.rec (motive := fun _ => Bool) _ true (Nat.beq (mulF W 16 c d) (mulF W 16 d t)) =
      true ↔ _
    rw [CFSG.KS.Raw.Orb.bIf_eq]
    by_cases h : mulF W 16 c d = mulF W 16 d t
    · rw [if_pos (by rw [Nat.beq_eq]; exact h)]
      exact ⟨fun _ => ⟨c, List.mem_cons_self, h⟩, fun _ => rfl⟩
    · rw [if_neg (by rw [Nat.beq_eq]; exact h), ih]
      constructor
      · rintro ⟨c', hc', e⟩
        exact ⟨c', List.mem_cons_of_mem _ hc', e⟩
      · rintro ⟨c', hc', e⟩
        rcases List.mem_cons.1 hc' with rfl | hc'
        · exact absurd e h
        · exact ⟨c', hc', e⟩

theorem kSpec_of (h : checkK W P Q = true) : KSpec W P Q := by
  unfold checkK kpermsOK commP at h
  simp only [CFSG.KS.Raw.Orb.bAnd_eq, CFSG.KS.Raw.Orb.strictB_eq] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨k1, k2, k3, k4, k5, k6, k7⟩, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14,
    h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, e1, e2, e3, e4, e5, h27, h28⟩ := h
  refine ⟨Nat.eq_of_beq_eq_true k1, Nat.eq_of_beq_eq_true k2, Nat.eq_of_beq_eq_true k3, k4,
    Nat.eq_of_beq_eq_true k5,
    fun x hx => Nat.eq_of_beq_eq_true (CFSG.KS.Raw.Orb.allN_iff.1 k6 x hx),
    fun x hx => Nat.eq_of_beq_eq_true (CFSG.KS.Raw.Orb.allN_iff.1 k7 x hx), h2, h3, h4,
    Nat.blt_eq.mp h5, Nat.blt_eq.mp h6, Nat.blt_eq.mp h7, Nat.eq_of_beq_eq_true h8,
    Nat.eq_of_beq_eq_true h9, Nat.eq_of_beq_eq_true h10, Nat.eq_of_beq_eq_true h11,
    Nat.eq_of_beq_eq_true h12, Nat.eq_of_beq_eq_true h13, Nat.eq_of_beq_eq_true h14,
    Nat.eq_of_beq_eq_true h15, Nat.eq_of_beq_eq_true h16, Nat.eq_of_beq_eq_true h17,
    Nat.eq_of_beq_eq_true h18, Nat.eq_of_beq_eq_true h19, fun c hc hc0 => ?_,
    fun c hc => Nat.eq_of_beq_eq_true (CFSG.KS.Raw.Orb.allN_iff.1 h21 c hc),
    fun c hc j hj => Nat.eq_of_beq_eq_true
      (CFSG.KS.Raw.Orb.allN_iff.1 (CFSG.KS.Raw.Orb.allN_iff.1 h22 c hc) j hj),
    fun c hc => Nat.eq_of_beq_eq_true (CFSG.KS.Raw.Orb.allN_iff.1 h23 c hc),
    Nat.eq_of_beq_eq_true h24, by rw [← lenK_eq]; exact Nat.eq_of_beq_eq_true h25, h26,
    Nat.blt_eq.mp e1, Nat.blt_eq.mp e2, Nat.blt_eq.mp e3,
    fun c hc => Nat.blt_eq.mp ((allK_iff _ _).1 e4 c hc),
    fun c hc => Nat.blt_eq.mp ((allK_iff _ _).1 e5 c hc),
    fun d hd => (anyCl_iff W d W.t0 W.cl0).1 (CFSG.KS.Raw.Orb.allN_iff.1 h27 d hd),
    fun d hd => (anyCl_iff W d W.t1 W.cl1).1 (CFSG.KS.Raw.Orb.allN_iff.1 h28 d hd)⟩
  have := CFSG.KS.Raw.Orb.allN_iff.1 h20 c hc
  simp only [CFSG.KS.Raw.Orb.bIf_eq, CFSG.KS.Raw.Orb.bAnd_eq, Nat.beq_eq, hc0, if_false,
    Bool.and_eq_true, Nat.blt_eq] at this
  exact ⟨this.1, this.2.1, this.2.2⟩

theorem bitOf_mul (x y : Cm) : bitOf (x * y) = Nat.xor (bitOf x) (bitOf y) := by
  unfold bitOf
  rcases Int.units_eq_one_or x.1 with h | h <;> rcases Int.units_eq_one_or y.1 with h' | h' <;>
    simp [Prod.fst_mul, h, h']

theorem rgK_spec (hW : TOOK W P Q)
    {j : Nat} (hj : j < 4) : bitOf (RgK W j) = bitR j ∧
      ∀ x : Fin 1755, Q.R j x = ((RgK W j).2 x : Nat) := by
  have K := kSpec_of hW.codes
  have hh1 : PR Q.h1 (wordIn 4 titsGen h1Word) := by
    rw [K.h1]; exact prep_wd (tprepF hW) (tprepFI hW) K.lh1
  have hh2 : PR Q.h2 (wordIn 4 titsGen h2Word) := by
    rw [K.h2]; exact prep_wd (tprepF hW) (tprepFI hW) K.lh2
  rcases j with _ | _ | _ | _ | j
  · refine ⟨by simp [RgK, bitOf, bitR, inA]; rfl, fun x => ?_⟩
    simp only [KPerms.R, pick4, RgK, inA, if_true]
    exact ap_eq hh1 x
  · refine ⟨by simp [RgK, bitOf, bitR, inA]; rfl, fun x => ?_⟩
    simp only [KPerms.R, pick4, RgK, inA]
    simp only [CFSG.KS.Raw.Orb.nIf_eq, Nat.beq_eq]
    simp only [show (1 : Nat) ≠ 0 by decide, if_false, if_true]
    exact ap_eq hh2 x
  · refine ⟨by simp [RgK, bitOf, bitR, inA]; rfl, fun x => ?_⟩
    simp only [KPerms.R, pick4, RgK, inA]
    simp only [CFSG.KS.Raw.Orb.nIf_eq, Nat.beq_eq]
    simp only [show (2 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 1 by decide, if_false, if_true]
    rw [K.lbb x x.2, lamK_eq hW K.b x, K.la _ (lamG W W.b x).2,
      lamK_eq hW K.a ⟨_, (lamG W W.b x).2⟩, Equiv.Perm.mul_apply]
  · refine ⟨by simp [RgK, bitOf, bitR, tauH], fun x => ?_⟩
    simp only [KPerms.R, pick4, RgK, tauH]
    simp only [CFSG.KS.Raw.Orb.nIf_eq, Nat.beq_eq]
    simp
  · omega

theorem fuel_spec (hW : TOOK W P Q) :
    ∀ k c, c < 512 → reachF W k c = true → bitF W k c = bitOf (kap W c) ∧
      ∀ x : Fin 1755, kptF W Q.R k c x = ((kap W c).2 x : Nat) := by
  have K := kSpec_of hW.codes
  intro k
  induction k with
  | zero =>
    intro c hc hr
    have h0 : c = 0 := Nat.eq_of_beq_eq_true hr
    subst h0
    refine ⟨?_, fun x => ?_⟩
    · rw [kap_zero]
      rfl
    · rw [kap_zero]
      rfl
  | succ k ih =>
    intro c hc hr
    by_cases h0 : c = 0
    · subst h0
      refine ⟨?_, fun x => ?_⟩
      · rw [kap_zero]
        rfl
      · rw [kap_zero]
        rfl
    · obtain ⟨hp, hg, -⟩ := K.tree c hc h0
      have hr' : reachF W k (parK W c) = true := by
        change Bool.rec (motive := fun _ => Bool) (reachF W k (parK W c)) true (Nat.beq c 0) = true
          at hr
        rwa [CFSG.KS.Raw.Orb.bIf_eq, if_neg (by rw [Nat.beq_eq]; exact h0)] at hr
      obtain ⟨ih1, ih2⟩ := ih (parK W c) (lt_trans hp hc) hr'
      obtain ⟨hb, hR⟩ := rgK_spec hW hg
      rw [kap_of_lt hp]
      refine ⟨?_, fun x => ?_⟩
      · change Bool.rec (motive := fun _ => Nat) (Nat.xor (bitF W k (parK W c)) (bitR (genK W c)))
          0 (Nat.beq c 0) = _
        rw [CFSG.KS.Raw.Orb.nIf_eq, if_neg (by rw [Nat.beq_eq]; exact h0), ih1, ← hb, bitOf_mul]
      · change Bool.rec (motive := fun _ => Nat) (kptF W Q.R k (parK W c) (Q.R (genK W c) x))
          x (Nat.beq c 0) = _
        rw [CFSG.KS.Raw.Orb.nIf_eq, if_neg (by rw [Nat.beq_eq]; exact h0), hR x,
          show (((RgK W (genK W c)).2 x : Fin 1755) : Nat) = ((⟨_, ((RgK W (genK W c)).2 x).2⟩ :
            Fin 1755) : Nat) from rfl, ih2]
        rfl

theorem reach_all (K : KSpec W P Q) {c : Nat} (hc : c < 512) : reachF W 16 c = true := by
  by_cases h0 : c = 0
  · subst h0
    rfl
  · exact (K.tree c hc h0).2.2

theorem keyF_eq (hW : TOOK W P Q)
    {c : Nat} (hc : c < 512) : keyF W Q c = keyCm W (kSpec_of hW.codes).b1 (kap W c) := by
  have K := kSpec_of hW.codes
  obtain ⟨h1, h2⟩ := fuel_spec hW 16 c hc (reach_all K hc)
  unfold keyF keyCm
  rw [h1, h2 ⟨W.b1, K.b1⟩]
  rfl

theorem kap_inj (hW : TOOK W P Q)
    {c c' : Nat} (hc : c < 512) (hc' : c' < 512) (e : kap W c = kap W c') : c = c' := by
  have K := kSpec_of hW.codes
  have h1 := K.rk c hc
  have h2 := K.rk c' hc'
  rw [keyF_eq hW hc, e, ← keyF_eq hW hc', h2] at h1
  omega

theorem inA_mem_KH {q : Equiv.Perm (Fin 1755)} (hq : q ∈ titsA)
    (hz : q * titsZ = titsZ * q) (hzp : q * zpHat = zpHat * q) : inA q ∈ KH zpHat := by
  simp only [KH, GammaH, Am, Subgroup.mem_inf, Subgroup.mem_prod, Subgroup.mem_centralizer_iff,
    Set.mem_singleton_iff, forall_eq]
  refine ⟨⟨⟨Subgroup.mem_top _, hq⟩, ?_⟩, ?_⟩
  · refine Prod.ext ?_ ?_
    · simp [inA]
    · simp [inA, hz]
  · refine Prod.ext ?_ ?_
    · simp [inA, tauH]
    · simp [inA, tauH, hzp]

theorem tauH_mem_KH : tauH ∈ KH zpHat := by
  simp only [KH, GammaH, Am, Subgroup.mem_inf, Subgroup.mem_prod, Subgroup.mem_centralizer_iff,
    Set.mem_singleton_iff, forall_eq]
  refine ⟨⟨⟨Subgroup.mem_top _, by simpa [tauH] using one_mem titsA⟩, ?_⟩, ?_⟩
  · refine Prod.ext ?_ ?_ <;> simp [inA, tauH, mul_comm]
  · refine Prod.ext ?_ ?_ <;> simp [inA, tauH, mul_comm]

theorem rgK_mem (LF : LabFacts)
    (hW : TOOK W P Q) {j : Nat} (hj : j < 4) : RgK W j ∈ KH zpHat := by
  have K := kSpec_of hW.codes
  have G := genSpec_of hW.gen
  have hZ := tprepZ hW
  have hzp : PR Q.zp zpHat := by rw [K.zp, G.zp]; exact prep_wd (tprepF hW) (tprepFI hW) G.lzp
  have hh1 : PR Q.h1 (wordIn 4 titsGen h1Word) := by
    rw [K.h1]; exact prep_wd (tprepF hW) (tprepFI hW) K.lh1
  have hh2 : PR Q.h2 (wordIn 4 titsGen h2Word) := by
    rw [K.h2]; exact prep_wd (tprepF hW) (tprepFI hW) K.lh2
  rcases j with _ | _ | _ | _ | j
  · simp only [RgK, if_true]
    exact inA_mem_KH (wordIn_mem_titsA' _) (mul_eq_of hh1 hZ hZ hh1 K.h1Z)
      (mul_eq_of hh1 hzp hzp hh1 K.h1zp)
  · simp only [RgK, show (1 : Nat) ≠ 0 by decide, if_false, if_true]
    exact inA_mem_KH (wordIn_mem_titsA' _) (mul_eq_of hh2 hZ hZ hh2 K.h2Z)
      (mul_eq_of hh2 hzp hzp hh2 K.h2zp)
  · simp only [RgK, show (2 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 1 by decide, if_false, if_true]
    have hla : PR Q.la (lamG W W.a) := fun x => by
      change ap Q.la x = _
      rw [K.la x x.2, lamK_eq hW K.a x]
    have hlb : PR Q.lbb (lamG W W.b) := fun x => by
      change ap Q.lbb x = _
      rw [K.lbb x x.2, lamK_eq hW K.b x]
    have hab := prep_pmul hla hlb
    have hA : lamG W W.a * lamG W W.b ∈ titsA :=
      mul_mem (titsD_le_titsA (lamG_facts LF hW K.a).1) (titsD_le_titsA (lamG_facts LF hW K.b).1)
    exact inA_mem_KH hA (mul_eq_of hab hZ hZ hab K.abZ) (mul_eq_of hab hzp hzp hab K.abzp)
  · simp only [RgK, show (3 : Nat) ≠ 0 by decide, show (3 : Nat) ≠ 1 by decide,
      show (3 : Nat) ≠ 2 by decide, if_false]
    exact tauH_mem_KH
  · omega

theorem kap_mem (LF : LabFacts)
    (hW : TOOK W P Q) : ∀ c, c < 512 → kap W c ∈ KH zpHat := by
  have K := kSpec_of hW.codes
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    intro hc
    by_cases h0 : c = 0
    · subst h0
      rw [kap_zero]
      exact one_mem _
    · obtain ⟨hp, hg, -⟩ := K.tree c hc h0
      rw [kap_of_lt hp]
      exact mul_mem (ih _ hp (lt_trans hp hc)) (rgK_mem LF hW hg)

theorem card_KH_le' (hcard : Nat.card ↥(titsA ⊓ centralizer ({titsZ} : Set (Equiv.Perm (Fin 1755))) ⊓
      centralizer ({zpHat} : Set (Equiv.Perm (Fin 1755)))) ≤ 256) : Nat.card ↥(KH zpHat) ≤ 512 := by
  have hT : ∀ x : ↥(KH zpHat), x.1.2 ∈ titsA ⊓ centralizer ({titsZ} : Set (Equiv.Perm (Fin 1755))) ⊓
      centralizer ({zpHat} : Set (Equiv.Perm (Fin 1755))) := by
    intro x
    have hx := x.2
    simp only [KH, GammaH, Am, Subgroup.mem_inf, Subgroup.mem_prod, Subgroup.mem_centralizer_iff,
      Set.mem_singleton_iff, forall_eq] at hx
    obtain ⟨⟨⟨-, h1⟩, h2⟩, h3⟩ := hx
    have e2 := congrArg Prod.snd h2
    have e3 := congrArg Prod.snd h3
    simp only [inA, tauH, Prod.snd_mul, one_mul, mul_one] at e2 e3
    simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
    exact ⟨⟨h1, e2⟩, e3⟩
  have hinj : Function.Injective (fun x : ↥(KH zpHat) =>
      ((x.1.1, (⟨x.1.2, hT x⟩ : ↥(titsA ⊓ centralizer ({titsZ} : Set (Equiv.Perm (Fin 1755))) ⊓
        centralizer ({zpHat} : Set (Equiv.Perm (Fin 1755)))))) : ℤˣ × _)) := by
    intro x y hxy
    simp only [Prod.mk.injEq, Subtype.mk.injEq] at hxy
    exact Subtype.ext (Prod.ext hxy.1 hxy.2)
  have := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_prod] at this
  have hu : Nat.card ℤˣ = 2 := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_units_int
  rw [hu] at this
  omega

theorem kap_complete (LF : LabFacts)
    (hW : TOOK W P Q) (hcard : Nat.card ↥(titsA ⊓ centralizer ({titsZ} : Set (Equiv.Perm (Fin 1755))) ⊓
      centralizer ({zpHat} : Set (Equiv.Perm (Fin 1755)))) ≤ 256) {x : Cm} (hx : x ∈ KH zpHat) :
    ∃ c < 512, kap W c = x := by
  classical
  by_contra hne
  push Not at hne
  have hle := card_KH_le' hcard
  let S : Finset Cm := (Finset.range 512).image (kap W) ∪ {x}
  have hS : S.card = 513 := by
    rw [Finset.card_union_of_disjoint (by
      rw [Finset.disjoint_singleton_right, Finset.mem_image]
      rintro ⟨c, hc, e⟩
      exact hne c (Finset.mem_range.1 hc) e), Finset.card_singleton,
      Finset.card_image_of_injOn (fun a ha b hb e => kap_inj hW (Finset.mem_range.1 ha)
        (Finset.mem_range.1 hb) e), Finset.card_range]
  have hsub : ∀ y ∈ S, y ∈ KH zpHat := by
    intro y hy
    rw [Finset.mem_union, Finset.mem_image, Finset.mem_singleton] at hy
    rcases hy with ⟨c, hc, rfl⟩ | rfl
    · exact kap_mem LF hW c (Finset.mem_range.1 hc)
    · exact hx
  have hcardS : S.card ≤ Nat.card ↥(KH zpHat) := by
    rw [← Nat.card_eq_finsetCard]
    exact Nat.card_mono (Set.toFinite _) (fun y hy => hsub y hy)
  omega

theorem code_of (LF : LabFacts)
    (hW : TOOK W P Q) (hcard : Nat.card ↥(titsA ⊓ centralizer ({titsZ} : Set (Equiv.Perm (Fin 1755))) ⊓
      centralizer ({zpHat} : Set (Equiv.Perm (Fin 1755)))) ≤ 256) {x : Cm} (hx : x ∈ KH zpHat)
    {v : Nat} (hv : tg 10 W.RK (keyCm W (kSpec_of hW.codes).b1 x) = v + 1) :
    v < 512 ∧ kap W v = x := by
  obtain ⟨c, hc, rfl⟩ := kap_complete LF hW hcard hx
  have K := kSpec_of hW.codes
  have h1 := K.rk c hc
  rw [keyF_eq hW hc, hv] at h1
  have hcv : v = c := by omega
  subst hcv
  exact ⟨hc, rfl⟩

abbrev KCard : Prop := Nat.card ↥(titsA ⊓ centralizer ({titsZ} : Set (Equiv.Perm (Fin 1755))) ⊓
  centralizer ({zpHat} : Set (Equiv.Perm (Fin 1755)))) ≤ 256

theorem kap_T (LF : LabFacts)
    (hW : TOOK W P Q) (hcard : KCard) {c j : Nat} (hc : c < 512) (hj : j < 4) :
    tg 9 W.T (4 * c + j) < 512 ∧ kap W (tg 9 W.T (4 * c + j)) = kap W c * RgK W j := by
  have K := kSpec_of hW.codes
  obtain ⟨h1, h2⟩ := fuel_spec hW 16 c hc (reach_all K hc)
  obtain ⟨hb, hR⟩ := rgK_spec hW hj
  refine code_of LF hW hcard (mul_mem (kap_mem LF hW c hc) (rgK_mem LF hW hj)) ?_
  have := K.tT c hc j hj
  rw [h1, ← hb, hR ⟨W.b1, K.b1⟩, show (((RgK W j).2 ⟨W.b1, K.b1⟩ : Fin 1755) : Nat) =
    ((⟨_, ((RgK W j).2 ⟨W.b1, K.b1⟩).2⟩ : Fin 1755) : Nat) from rfl, h2] at this
  unfold keyCm
  rw [bitOf_mul, Prod.snd_mul, Equiv.Perm.mul_apply]
  exact this

theorem prepY0 (hW : TOOK W P Q) :
    PR Q.y0 y0Hat ∧ PR Q.y0i y0Hat⁻¹ := by
  have K := kSpec_of hW.codes
  have h : PR Q.y0 y0Hat := by rw [K.y0]; exact prep_wd (tprepF hW) (tprepFI hW) K.ly0
  exact ⟨h, prep_inv h K.y0i⟩

theorem conj_y0_mem_KH (hF6 : F6Facts zpHat y0Hat) {x : Cm} (hx : x ∈ KH zpHat) :
    inA y0Hat * x * (inA y0Hat)⁻¹ ∈ KH zpHat := by
  simp only [KH, GammaH, Am, Subgroup.mem_inf, Subgroup.mem_prod, Subgroup.mem_centralizer_iff,
    Set.mem_singleton_iff, forall_eq] at hx ⊢
  obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := hx
  have e2 := congrArg Prod.snd h2
  have e3 := congrArg Prod.snd h3
  simp only [inA, tauH, Prod.snd_mul, one_mul, mul_one] at e2 e3
  have hy0z : titsZ = y0Hat * zpHat * y0Hat⁻¹ := hF6.y0_zp.symm
  have hy0zp : zpHat = y0Hat * titsZ * y0Hat⁻¹ := hF6.y0_z.symm
  refine ⟨⟨⟨Subgroup.mem_top _, ?_⟩, ?_⟩, ?_⟩
  · simp only [inA, Prod.snd_mul, Prod.snd_inv]
    exact mul_mem (mul_mem hF6.y0_mem h1) (inv_mem hF6.y0_mem)
  · refine Prod.ext ?_ ?_
    · simp [inA, mul_comm]
    · simp only [inA, Prod.snd_mul, Prod.snd_inv, one_mul, mul_one]
      calc titsZ * (y0Hat * x.2 * y0Hat⁻¹) = y0Hat * (zpHat * x.2) * y0Hat⁻¹ := by
            rw [hy0z]; group
        _ = y0Hat * (x.2 * zpHat) * y0Hat⁻¹ := by rw [e3]
        _ = y0Hat * x.2 * y0Hat⁻¹ * titsZ := by rw [hy0z]; group
  · refine Prod.ext ?_ ?_
    · simp [inA, tauH, mul_comm]
    · simp only [inA, tauH, Prod.snd_mul, Prod.snd_inv, one_mul, mul_one]
      calc zpHat * (y0Hat * x.2 * y0Hat⁻¹) = y0Hat * (titsZ * x.2) * y0Hat⁻¹ := by
            rw [hy0zp]; group
        _ = y0Hat * (x.2 * titsZ) * y0Hat⁻¹ := by rw [e2]
        _ = y0Hat * x.2 * y0Hat⁻¹ * zpHat := by rw [hy0zp]; group

theorem kap_Y (LF : LabFacts)
    (hW : TOOK W P Q) (hcard : KCard) (hF6 : F6Facts zpHat y0Hat) {c : Nat} (hc : c < 512) :
    tg 9 W.Y c < 512 ∧ kap W (tg 9 W.Y c) = inA y0Hat * kap W c * (inA y0Hat)⁻¹ := by
  have K := kSpec_of hW.codes
  obtain ⟨h1, h2⟩ := fuel_spec hW 16 c hc (reach_all K hc)
  obtain ⟨hy, hyi⟩ := prepY0 hW
  refine code_of LF hW hcard (conj_y0_mem_KH hF6 (kap_mem LF hW c hc)) ?_
  have := K.tY c hc
  have e1 : ap Q.y0i W.b1 = ((y0Hat⁻¹ ⟨W.b1, K.b1⟩ : Fin 1755) : Nat) := ap_eq hyi ⟨W.b1, K.b1⟩
  have e2 : kptF W Q.R 16 c (ap Q.y0i W.b1) = (((kap W c).2 (y0Hat⁻¹ ⟨W.b1, K.b1⟩) : Fin 1755) : Nat) := by
    rw [e1]
    exact h2 _
  have e3 : ap Q.y0 (kptF W Q.R 16 c (ap Q.y0i W.b1)) =
      ((y0Hat ((kap W c).2 (y0Hat⁻¹ ⟨W.b1, K.b1⟩)) : Fin 1755) : Nat) := by
    rw [e2]
    exact ap_eq hy _
  rw [h1, e3] at this
  unfold keyCm
  have hb : bitOf (inA y0Hat * kap W c * (inA y0Hat)⁻¹) = bitOf (kap W c) := by
    rw [bitOf_mul, bitOf_mul]
    unfold bitOf inA
    simp
  have e4 : ((inA y0Hat * kap W c * (inA y0Hat)⁻¹).2 ⟨W.b1, K.b1⟩ : Fin 1755) =
      y0Hat ((kap W c).2 (y0Hat⁻¹ ⟨W.b1, K.b1⟩)) := by
    rw [Prod.snd_mul, Prod.snd_mul, Prod.snd_inv, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
    rfl
  rw [hb, e4]
  exact this

theorem kap_mc1 (LF : LabFacts)
    (hW : TOOK W P Q) (hcard : KCard) (hF6 : F6Facts zpHat y0Hat) :
    W.mc1 < 512 ∧ kap W W.mc1 = tauH * inA titsZ := by
  have K := kSpec_of hW.codes
  have hz : inA titsZ ∈ KH zpHat :=
    inA_mem_KH (titsD_le_titsA titsZ_mem_titsD) rfl hF6.zp_comm
  refine code_of LF hW hcard (mul_mem tauH_mem_KH hz) ?_
  have := K.mc1
  rw [ap_eq (tprepZ hW) ⟨W.b1, K.b1⟩] at this
  unfold keyCm
  have hb : bitOf (tauH * inA titsZ) = 1 := by simp [bitOf, tauH, inA]
  rw [hb]
  simpa [tauH, inA] using this

theorem kap_mulF (LF : LabFacts)
    (hW : TOOK W P Q) (hcard : KCard) : ∀ k a b, a < 512 → b < 512 → reachF W k b = true →
    mulF W k a b < 512 ∧ kap W (mulF W k a b) = kap W a * kap W b := by
  have K := kSpec_of hW.codes
  intro k
  induction k with
  | zero =>
    intro a b ha hb hr
    have h0 : b = 0 := Nat.eq_of_beq_eq_true hr
    subst h0
    exact ⟨ha, by rw [kap_zero, mul_one]; rfl⟩
  | succ k ih =>
    intro a b ha hb hr
    by_cases h0 : b = 0
    · subst h0
      exact ⟨ha, by rw [kap_zero, mul_one]; rfl⟩
    · obtain ⟨hp, hg, -⟩ := K.tree b hb h0
      have hr' : reachF W k (parK W b) = true := by
        change Bool.rec (motive := fun _ => Bool) (reachF W k (parK W b)) true (Nat.beq b 0) = true
          at hr
        rwa [CFSG.KS.Raw.Orb.bIf_eq, if_neg (by rw [Nat.beq_eq]; exact h0)] at hr
      obtain ⟨ih1, ih2⟩ := ih a (parK W b) ha (lt_trans hp hb) hr'
      have e : mulF W (k + 1) a b = tg 9 W.T (4 * mulF W k a (parK W b) + genK W b) := by
        change Bool.rec (motive := fun _ => Nat) (tg 9 W.T (Nat.add (Nat.mul 4
          (mulF W k a (parK W b))) (genK W b))) a (Nat.beq b 0) = _
        rw [CFSG.KS.Raw.Orb.nIf_eq, if_neg (by rw [Nat.beq_eq]; exact h0)]
        rfl
      obtain ⟨t1, t2⟩ := kap_T LF hW hcard ih1 hg
      rw [e]
      refine ⟨t1, ?_⟩
      rw [t2, ih2, kap_of_lt hp, mul_assoc]

theorem kap_homF (LF : LabFacts)
    (hW : TOOK W P Q) (hcard : KCard) {φ : Cm → Cm}
    (hφ : ∀ x ∈ KH zpHat, ∀ y ∈ KH zpHat, φ (x * y) = φ x * φ y) (hφ1 : φ 1 = 1)
    {thr : Nat → Nat} (hthr : ∀ j < 4, thr j < 512 ∧ kap W (thr j) = φ (RgK W j)) :
    ∀ k c, c < 512 → reachF W k c = true →
      homF W thr k c < 512 ∧ kap W (homF W thr k c) = φ (kap W c) := by
  have K := kSpec_of hW.codes
  have e0 : ∀ k, homF W thr k 0 = 0 := by
    intro k
    cases k <;> rfl
  intro k
  induction k with
  | zero =>
    intro c hc hr
    have h0 : c = 0 := Nat.eq_of_beq_eq_true hr
    subst h0
    rw [e0, kap_zero, hφ1]
    exact ⟨by norm_num, rfl⟩
  | succ k ih =>
    intro c hc hr
    by_cases h0 : c = 0
    · subst h0
      rw [e0, kap_zero, hφ1]
      exact ⟨by norm_num, rfl⟩
    · obtain ⟨hp, hg, -⟩ := K.tree c hc h0
      have hr' : reachF W k (parK W c) = true := by
        change Bool.rec (motive := fun _ => Bool) (reachF W k (parK W c)) true (Nat.beq c 0) = true
          at hr
        rwa [CFSG.KS.Raw.Orb.bIf_eq, if_neg (by rw [Nat.beq_eq]; exact h0)] at hr
      obtain ⟨ih1, ih2⟩ := ih (parK W c) (lt_trans hp hc) hr'
      obtain ⟨t1, t2⟩ := hthr (genK W c) hg
      have e : homF W thr (k + 1) c = mulF W 16 (homF W thr k (parK W c)) (thr (genK W c)) := by
        change Bool.rec (motive := fun _ => Nat) (mulF W 16 (homF W thr k (parK W c))
          (thr (genK W c))) 0 (Nat.beq c 0) = _
        rw [CFSG.KS.Raw.Orb.nIf_eq, if_neg (by rw [Nat.beq_eq]; exact h0)]
      obtain ⟨m1, m2⟩ := kap_mulF LF hW hcard 16 _ _ ih1 t1 (reach_all K t1)
      rw [e]
      refine ⟨m1, ?_⟩
      rw [m2, ih2, t2, kap_of_lt hp, hφ _ (kap_mem LF hW _ (lt_trans hp hc)) _ (rgK_mem LF hW hg)]

theorem kap_cl (LF : LabFacts)
    (hW : TOOK W P Q) (hcard : KCard) {t : Nat} {cl : List Nat} (ht : t < 512)
    (hcl : ∀ c ∈ cl, c < 512) (h : ∀ d < 512, ∃ c ∈ cl, mulF W 16 c d = mulF W 16 d t)
    {d : Nat} (hd : d < 512) : ∃ c ∈ cl, kap W c = kap W d * kap W t * (kap W d)⁻¹ := by
  have K := kSpec_of hW.codes
  obtain ⟨c, hc, e⟩ := h d hd
  refine ⟨c, hc, ?_⟩
  obtain ⟨-, e1⟩ := kap_mulF LF hW hcard 16 c d (hcl c hc) hd (reach_all K hd)
  obtain ⟨-, e2⟩ := kap_mulF LF hW hcard 16 d t hd ht (reach_all K ht)
  rw [e] at e1
  rw [e1] at e2
  rw [eq_mul_inv_iff_mul_eq, ← e2]

theorem kaOK_spec {FZ : Nat} : ∀ (l : List Nat) (c0 : Nat), kaOK W FZ Q l c0 = true →
    ∀ i < l.length, (c0 + i = 0 → l.getD i 0 = rowK (fun m => m)) ∧
      (c0 + i ≠ 0 → l.getD i 0 = rowK (fun m => tg 7 (nthK W.KA (parK W (c0 + i)))
        (tg 7 (rowR W FZ Q (genK W (c0 + i))) m)))
  | [], _, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | r :: l, c0, h, i, hi => by
    change Bool.rec (motive := fun _ => Bool) false (kaOK W FZ Q l (Nat.succ c0))
      (Bool.rec (motive := fun _ => Bool) (strictB (nthK W.KA (parK W c0)) (fun A =>
        strictB (rowR W FZ Q (genK W c0)) (fun B => Nat.beq r (rowK (fun m => tg 7 A (tg 7 B m))))))
        (Nat.beq r (rowK (fun m => m))) (Nat.beq c0 0)) = true at h
    rw [CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true, CFSG.KS.Raw.Orb.bIf_eq,
      CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.strictB_eq] at h
    obtain ⟨h1, h2⟩ := h
    rcases i with _ | i
    · simp only [Nat.add_zero, List.getD_cons_zero]
      refine ⟨fun h0 => ?_, fun h0 => ?_⟩
      · rw [if_pos (by rw [Nat.beq_eq]; exact h0)] at h1
        exact Nat.eq_of_beq_eq_true h1
      · rw [if_neg (by rw [Nat.beq_eq]; exact h0)] at h1
        exact Nat.eq_of_beq_eq_true h1
    · have := kaOK_spec l (Nat.succ c0) h2 i (by simpa using hi)
      simp only [List.getD_cons_succ]
      rw [show c0 + (i + 1) = Nat.succ c0 + i by omega]
      exact this

theorem rowR_spec (LF : LabFacts)
    (hW : TOOK W P Q) {j m : Nat} (hj : j < 4) (hm : m < 92) :
    tg 7 (rowR W (fzIdx W.fz) Q j) m < 92 ∧
      mE W (tg 7 (rowR W (fzIdx W.fz) Q j) m) = RgK W j * mE W m * (RgK W j)⁻¹ := by
  have K := kSpec_of hW.codes
  have G := genSpec_of hW.gen
  have hZ := tprepZ hW
  have hzp : PR Q.zp zpHat := by rw [K.zp, G.zp]; exact prep_wd (tprepF hW) (tprepFI hW) G.lzp
  have htc : ∀ x : Cm, tauH * x = x * tauH := fun x => by
    refine Prod.ext ?_ ?_ <;> simp [tauH, mul_comm]
  have hrowH : ∀ {H : Nat} {h : Equiv.Perm (Fin 1755)}, PR H h → h ∈ titsA →
      h * titsZ = titsZ * h → h 0 = 0 →
      tg 7 (rowH W (fzIdx W.fz) (ap H)) m < 92 ∧
        mE W (tg 7 (rowH W (fzIdx W.fz) (ap H)) m) = inA h * mE W m * (inA h)⁻¹ := by
    intro H h hH hA hz h0
    unfold rowH
    rw [tg_rowK (fun m _ => by
      rw [CFSG.KS.Raw.Orb.nIf_eq]
      split_ifs
      · norm_num
      · exact tg_lt 7 _ _) hm, CFSG.KS.Raw.Orb.nIf_eq]
    by_cases hm0 : m = 0
    · subst hm0
      rw [if_pos (Nat.beq_refl 0), mE_zero]
      refine ⟨by norm_num, ?_⟩
      rw [← htc, mul_assoc, mul_inv_cancel, mul_one]
    · rw [if_neg (by rw [Nat.beq_eq]; exact hm0), nthK_eq, show Nat.sub m 1 = m - 1 from rfl]
      have hy := fz_getD_lt hW (k := m - 1) (by omega)
      obtain ⟨hDm, hDm0, hlm⟩ := labD_spec hW (i := m) (by omega) hm
      obtain ⟨hgD, hg0, hgc⟩ := conj_conj_titsZ hA hz h0 hDm
      set y : Fin 1755 := h ⟨W.fz.getD (m - 1) 0, hy⟩ with hydef
      have hyfix : titsZ y = y := by
        have hz0 : titsZ ⟨W.fz.getD (m - 1) 0, hy⟩ = ⟨W.fz.getD (m - 1) 0, hy⟩ := by
          apply ((fz_facts hW).2.2 _).1
          change W.fz.getD (m - 1) 0 ∈ W.fz
          rw [getD_eq_idx (by rw [G.lenfz]; omega)]
          exact List.getElem_mem _
        rw [hydef, ← Equiv.Perm.mul_apply, ← hz, Equiv.Perm.mul_apply, hz0]
      obtain ⟨k, hk, hkv⟩ := List.mem_iff_getElem.1 (((fz_facts hW).2.2 y).2 hyfix)
      have hk' : k < 91 := by rw [← G.lenfz]; exact hk
      have hidx : tg 7 (fzIdx W.fz) (ap H (W.fz.getD (m - 1) 0)) = k + 1 := by
        rw [ap_eq' hH hy, ← hydef, ← hkv, ← getD_eq_idx hk]
        exact tg_fzIdx (fz_facts hW).1 (by rw [G.lenfz]; norm_num) hk
      rw [hidx]
      refine ⟨by omega, ?_⟩
      obtain ⟨hDk, hDk0, hlk⟩ := labD_spec hW (i := k + 1) (by omega) (by omega)
      have hl : lamG W (k + 1) = h * lamG W m * h⁻¹ := by
        rw [hlk, hlm, hgc]
        refine (LF.conj_iff hDk hgD).2 (Fin.ext ?_)
        rw [hDk0, hg0]
        have : labD W m 0 = ⟨W.fz.getD (m - 1) 0, hy⟩ := Fin.ext hDm0
        rw [this, ← hydef, ← hkv, show k + 1 - 1 = k from rfl, getD_eq_idx hk]
      unfold mE
      rw [hl]
      refine Prod.ext ?_ ?_
      · simp [tauH, inA]
      · simp [tauH, inA, mul_assoc]
  have hh1 : PR Q.h1 (wordIn 4 titsGen h1Word) := by
    rw [K.h1]; exact prep_wd (tprepF hW) (tprepFI hW) K.lh1
  have hh2 : PR Q.h2 (wordIn 4 titsGen h2Word) := by
    rw [K.h2]; exact prep_wd (tprepF hW) (tprepFI hW) K.lh2
  have h0 : (0 : Nat) < 1755 := by norm_num
  rcases j with _ | _ | _ | _ | j
  · have e : rowR W (fzIdx W.fz) Q 0 = rowH W (fzIdx W.fz) (ap Q.h1) := rfl
    rw [e]
    have := hrowH hh1 (wordIn_mem_titsA' _) (mul_eq_of hh1 hZ hZ hh1 K.h1Z)
      (by rw [fin_zero_eq]; exact fin_eq_of_ap hh1 h0 K.h10)
    simpa [RgK] using this
  · have e : rowR W (fzIdx W.fz) Q 1 = rowH W (fzIdx W.fz) (ap Q.h2) := rfl
    rw [e]
    have := hrowH hh2 (wordIn_mem_titsA' _) (mul_eq_of hh2 hZ hZ hh2 K.h2Z)
      (by rw [fin_zero_eq]; exact fin_eq_of_ap hh2 h0 K.h20)
    simpa [RgK] using this
  · have e : rowR W (fzIdx W.fz) Q 2 = rowK (fun m => mtK W W.a (mtK W W.b m)) := rfl
    rw [e]
    obtain ⟨b1, b2⟩ := mE_mt LF hW K.b hm
    obtain ⟨a1, a2⟩ := mE_mt LF hW K.a b1
    have hb : ∀ m < 92, mtK W W.a (mtK W W.b m) < 2 ^ 7 := fun m _ => tg_lt 7 _ _
    rw [tg_rowK hb hm]
    refine ⟨a1, ?_⟩
    have hinv : ∀ {i}, i < 92 → (mE W i)⁻¹ = mE W i := by
      intro i hi
      obtain ⟨-, -, hii⟩ := lamG_facts LF hW hi
      unfold mE
      refine Prod.ext ?_ ?_
      · simp [tauH, inA]
      · simp only [tauH, inA, Prod.snd_inv, Prod.snd_mul, inv_one, one_mul]
        exact inv_eq_of_mul_eq_one_right hii
    have hR : RgK W 2 = mE W W.a * mE W W.b := by
      simp only [RgK, show (2 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 1 by decide, if_false,
        if_true, mE]
      refine Prod.ext ?_ ?_
      · simp [tauH, inA]
      · simp [tauH, inA]
    rw [a2, b2, hR, mul_inv_rev, hinv K.a, hinv K.b]
    group
  · have e : rowR W (fzIdx W.fz) Q 3 = rowK (fun m => m) := rfl
    rw [e, tg_rowK (fun m hm => lt128_of_lt92 hm) hm]
    refine ⟨hm, ?_⟩
    have hR : RgK W 3 = tauH := by
      simp [RgK]
    rw [hR, htc, mul_assoc, mul_inv_cancel, mul_one]
  · omega

theorem ka_spec (LF : LabFacts)
    (hW : TOOK W P Q) : ∀ c, c < 512 → W.KA.getD c 0 >>> (92 * 7) = 0 ∧
      ∀ m < 92, tg 7 (W.KA.getD c 0) m < 92 ∧
        mE W (tg 7 (W.KA.getD c 0) m) = kap W c * mE W m * (kap W c)⁻¹ := by
  have K := kSpec_of hW.codes
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    intro hc
    obtain ⟨h0, h1⟩ := kaOK_spec W.KA 0 K.ka c (by rw [K.lenKA]; exact hc)
    rw [Nat.zero_add] at h0 h1
    by_cases hc0 : c = 0
    · subst hc0
      rw [h0 rfl, kap_zero]
      refine ⟨rowK_shr (fun m hm => lt128_of_lt92 hm), fun m hm => ?_⟩
      rw [tg_rowK (fun m hm => lt128_of_lt92 hm) hm]
      exact ⟨hm, by group⟩
    · obtain ⟨hp, hg, -⟩ := K.tree c hc hc0
      have hpc := lt_trans hp hc
      have hb : ∀ m < 92, tg 7 (nthK W.KA (parK W c)) (tg 7 (rowR W (fzIdx W.fz) Q (genK W c)) m) <
          2 ^ 7 := fun m _ => tg_lt 7 _ _
      rw [h1 hc0]
      refine ⟨rowK_shr hb, fun m hm => ?_⟩
      rw [tg_rowK hb hm, nthK_eq]
      obtain ⟨r1, r2⟩ := rowR_spec LF hW hg hm
      obtain ⟨-, ihA⟩ := ih (parK W c) hp hpc
      obtain ⟨a1, a2⟩ := ihA _ r1
      refine ⟨a1, ?_⟩
      rw [a2, r2, kap_of_lt hp, mul_inv_rev]
      group

end Codes

section Search

variable {W : TOW} {P : MPerms} {Q : KPerms}

theorem ig_lt (hW : TOOK W P Q) : ∀ l < 5, igK W l < 92 := by
  have S := stepsSpec_of hW.steps
  intro l hl
  rcases l with _ | _ | _ | _ | _ | l
  · rw [S.ig0]; norm_num
  · rw [S.ig1]; norm_num
  · exact S.ig2
  · exact S.ig3
  · exact S.ig4
  · omega

theorem stage1_inv (hW : TOOK W P Q) {π : Nat → Nat}
    (hπmt : ∀ i < 92, ∀ m < 92, π (mtK W i m) = mtK W (π i) (π m)) {i3 i4 : Nat}
    (hia : ∀ l < 5, iaK W i3 i4 l = π (igK W l)) :
    ∀ (rs : List Nat) (S p : Nat), stepsOK W rs S = true →
      (∀ y, bitK S y = true → y < 92 ∧ tg 7 p y = π y) →
      ∀ y, (bitK S y = true ∨ y ∈ rs.map fy) → y < 92 ∧ tg 7 (stage1F W i3 i4 rs p) y = π y
  | [], S, p, _, hS, y, hy => by
    rcases hy with hy | hy
    · exact hS y hy
    · simp at hy
  | r :: rs, S, p, h, hS, y, hy => by
    change Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false
      (Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false
        (stepsOK W rs (setK S (fy r))) (Nat.beq (mtK W (igK W (fl r)) (fx r)) (fy r)))
        (Nat.blt (fy r) 92)) (bitK S (fx r))) (Nat.blt (fl r) 5) = true at h
    simp only [CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true] at h
    obtain ⟨hl, hx, hyl, hmt, hrest⟩ := h
    have hl' := Nat.blt_eq.mp hl
    have hyl' := Nat.blt_eq.mp hyl
    have hmt' := Nat.eq_of_beq_eq_true hmt
    obtain ⟨hx92, hpx⟩ := hS _ hx
    have hv : mtK W (iaK W i3 i4 (fl r)) (tg 7 p (fx r)) = π (fy r) := by
      rw [hia _ hl', hpx, ← hπmt _ (ig_lt hW _ hl') _ hx92, hmt']
    refine stage1_inv hW hπmt hia rs _ _ hrest (fun t ht => ?_) y ?_
    · change t < 92 ∧ tg 7 (tsetK 7 p (fy r) (mtK W (iaK W i3 i4 (fl r)) (tg 7 p (fx r)))) t = π t
      have hb : mtK W (iaK W i3 i4 (fl r)) (tg 7 p (fx r)) < 2 ^ 7 := tg_lt 7 _ _
      rw [tg_tsetK hb]
      rcases (bitK_setK _ _ _).1 ht with ht | rfl
      · obtain ⟨h1, h2⟩ := hS t ht
        refine ⟨h1, ?_⟩
        split_ifs with h
        · subst h
          exact hv
        · exact h2
      · exact ⟨hyl', by rw [if_pos rfl, hv]⟩
    · rcases hy with hy | hy
      · exact Or.inl ((bitK_setK _ _ _).2 (Or.inl hy))
      · rw [List.map_cons, List.mem_cons] at hy
        rcases hy with rfl | hy
        · exact Or.inl ((bitK_setK _ _ _).2 (Or.inr rfl))
        · exact Or.inr hy

theorem stage2_inv {π : Nat → Nat} (hpt : ∀ r ∈ W.psteps, ptK W (π (fx r)) (π (fl r)) = π (fy r))
    (hps : ∀ r ∈ W.psteps, fx r ∈ covK W ∧ fl r ∈ covK W) :
    ∀ (rs : List Nat), (∀ r ∈ rs, r ∈ W.psteps) → ∀ (Ys : List Nat) (p : Nat),
      (∀ y, y ∈ covK W ∨ y ∈ Ys → tg 7 p y = π y) →
      ∀ y, y ∈ covK W ∨ y ∈ Ys ∨ y ∈ rs.map fy → tg 7 (stage2F W rs p) y = π y
  | [], _, Ys, p, hS, y, hy => by
    rcases hy with hy | hy | hy
    · exact hS y (Or.inl hy)
    · exact hS y (Or.inr hy)
    · simp at hy
  | r :: rs, hrs, Ys, p, hS, y, hy => by
    have hr := hrs r List.mem_cons_self
    obtain ⟨hxc, hlc⟩ := hps r hr
    have hv : ptK W (tg 7 p (fx r)) (tg 7 p (fl r)) = π (fy r) := by
      rw [hS _ (Or.inl hxc), hS _ (Or.inl hlc), hpt r hr]
    have hb : ptK W (tg 7 p (fx r)) (tg 7 p (fl r)) < 2 ^ 7 := tg_lt 7 _ _
    refine stage2_inv hpt hps rs (fun r' hr' => hrs r' (List.mem_cons_of_mem _ hr')) (fy r :: Ys)
      (tsetK 7 p (fy r) (ptK W (tg 7 p (fx r)) (tg 7 p (fl r)))) (fun t ht => ?_) y ?_
    · rw [tg_tsetK hb]
      split_ifs with h
      · rw [h, hv]
      · rcases ht with ht | ht
        · exact hS t (Or.inl ht)
        · rcases List.mem_cons.1 ht with ht | ht
          · exact absurd ht h
          · exact hS t (Or.inr ht)
    · rcases hy with hy | hy | hy
      · exact Or.inl hy
      · exact Or.inr (Or.inl (List.mem_cons_of_mem _ hy))
      · rw [List.map_cons, List.mem_cons] at hy
        rcases hy with rfl | hy
        · exact Or.inr (Or.inl List.mem_cons_self)
        · exact Or.inr (Or.inr hy)

theorem p0_spec (hW : TOOK W P Q) {i3 i4 : Nat} (hia : ∀ l < 5, iaK W i3 i4 l < 2 ^ 7) :
    ∀ k ≤ 5, ∀ l < k, tg 7 (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun l ih => tsetK 7 ih (igK W l) (iaK W i3 i4 l)) k) (igK W l) = iaK W i3 i4 l
  | 0, _, l, hl => absurd hl (Nat.not_lt_zero l)
  | k + 1, hk, l, hl => by
    have S := stepsSpec_of hW.steps
    change tg 7 (tsetK 7 (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun l ih => tsetK 7 ih (igK W l) (iaK W i3 i4 l)) k) (igK W k) (iaK W i3 i4 k)) (igK W l) = _
    rw [tg_tsetK (hia k (by omega))]
    by_cases h : l = k
    · subst h
      simp
    · rw [if_neg (fun e => S.igd k (by omega) l (by omega) e.symm)]
      exact p0_spec hW hia k (by omega) l (by omega)

theorem rootMask_iff (W : TOW) (y : Nat) :
    bitK (rootMask W) y = true ↔ ∃ l < 5, y = igK W l := by
  unfold rootMask
  simp only [bitK_setK, bitK_zero, Bool.false_eq_true, false_or]
  constructor
  · rintro ((((h | h) | h) | h) | h)
    · exact ⟨0, by norm_num, h⟩
    · exact ⟨1, by norm_num, h⟩
    · exact ⟨2, by norm_num, h⟩
    · exact ⟨3, by norm_num, h⟩
    · exact ⟨4, by norm_num, h⟩
  · rintro ⟨l, hl, rfl⟩
    rcases l with _ | _ | _ | _ | _ | l
    · exact Or.inl (Or.inl (Or.inl (Or.inl rfl)))
    · exact Or.inl (Or.inl (Or.inl (Or.inr rfl)))
    · exact Or.inl (Or.inl (Or.inr rfl))
    · exact Or.inl (Or.inr rfl)
    · exact Or.inr rfl
    · omega

theorem scan6_spec {Q6 c5 sab : Nat} : ∀ (l : List Nat) (c0 : Nat), scan6 W Q6 c5 sab l c0 = true →
    ∀ i < l.length, l.getD i 0 = Q6 → leafBadK W c5 (c0 + i) sab = true
  | [], _, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | r :: l, c0, h, i, hi => by
    change Bool.rec (motive := fun _ => Bool) false (scan6 W Q6 c5 sab l (Nat.succ c0))
      (Bool.rec (motive := fun _ => Bool) true (leafBadK W c5 c0 sab) (Nat.beq r Q6)) = true at h
    rw [CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true, CFSG.KS.Raw.Orb.bIf_eq] at h
    obtain ⟨h1, h2⟩ := h
    intro hr
    rcases i with _ | i
    · simp only [List.getD_cons_zero] at hr
      rw [if_pos (by rw [Nat.beq_eq]; exact hr)] at h1
      simpa using h1
    · simp only [List.getD_cons_succ] at hr
      rw [show c0 + (i + 1) = Nat.succ c0 + i by omega]
      exact scan6_spec l (Nat.succ c0) h2 i (by simpa using hi) hr

theorem scan5_spec {Q5 Q6 sab : Nat} : ∀ (l : List Nat) (c0 : Nat), scan5 W Q5 Q6 sab l c0 = true →
    ∀ i < l.length, l.getD i 0 = Q5 → scan6 W Q6 (c0 + i) sab W.KA 0 = true
  | [], _, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | r :: l, c0, h, i, hi => by
    change Bool.rec (motive := fun _ => Bool) false (scan5 W Q5 Q6 sab l (Nat.succ c0))
      (Bool.rec (motive := fun _ => Bool) true (scan6 W Q6 c0 sab W.KA 0) (Nat.beq r Q5)) = true at h
    rw [CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true, CFSG.KS.Raw.Orb.bIf_eq] at h
    obtain ⟨h1, h2⟩ := h
    intro hr
    rcases i with _ | i
    · simp only [List.getD_cons_zero] at hr
      rw [if_pos (by rw [Nat.beq_eq]; exact hr)] at h1
      simpa using h1
    · simp only [List.getD_cons_succ] at hr
      rw [show c0 + (i + 1) = Nat.succ c0 + i by omega]
      exact scan5_spec l (Nat.succ c0) h2 i (by simpa using hi) hr

theorem pairK_spec {i3 i4 : Nat} (h : pairK W i3 i4 = true)
    (h1 : allK (fun x => actAt W i3 i4 (stage1F W i3 i4 W.steps (p0K W i3 i4)) x) (covK W) = true)
    (h2 : (allN 92 (fun x => actAt W i3 i4 (stage2F W W.psteps
      (stage1F W i3 i4 W.steps (p0K W i3 i4))) x) &&
      injK (stage2F W W.psteps (stage1F W i3 i4 W.steps (p0K W i3 i4)))) = true)
    (h3 : abK W (tg 7 (stage2F W W.psteps (stage1F W i3 i4 W.steps (p0K W i3 i4))) W.a)
      (tg 7 (stage2F W W.psteps (stage1F W i3 i4 W.steps (p0K W i3 i4))) W.b) ≠ 0) :
    scan5 W (qRowK (stage2F W W.psteps (stage1F W i3 i4 W.steps (p0K W i3 i4))) (nthK W.KA 1))
      (qRowK (stage2F W W.psteps (stage1F W i3 i4 W.steps (p0K W i3 i4))) (nthK W.KA 2))
      (abK W (tg 7 (stage2F W W.psteps (stage1F W i3 i4 W.steps (p0K W i3 i4))) W.a)
        (tg 7 (stage2F W W.psteps (stage1F W i3 i4 W.steps (p0K W i3 i4))) W.b) - 1) W.KA 0 =
      true := by
  unfold pairK at h
  rw [CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.bIf_eq, if_pos h1, CFSG.KS.Raw.Orb.strictB_eq,
    CFSG.KS.Raw.Orb.bIf_eq, CFSG.KS.Raw.Orb.bAnd_eq, if_pos h2, CFSG.KS.Raw.Orb.strictB_eq,
    CFSG.KS.Raw.Orb.bIf_eq, if_neg (by rw [Nat.beq_eq]; exact h3), CFSG.KS.Raw.Orb.strictB_eq,
    CFSG.KS.Raw.Orb.strictB_eq] at h
  exact h

theorem toHat_of_k (LF : LabFacts)
    (hF6 : F6Facts zpHat y0Hat) (hcard : KCard) (hW : TOOK W P Q) : TOHat zpHat y0Hat := by
  intro s hmul hmap hinj h0 h1 h2 hM θ hθ ⟨d, hd, hdθ⟩
  have hs : SHyp zpHat s := ⟨hmul, hmap, hinj, h0, h1, h2, hM⟩
  have G := genSpec_of hW.gen
  have S := stepsSpec_of hW.steps
  have K := kSpec_of hW.codes
  have hzD : titsZ ∈ titsD := titsZ_mem_titsD
  have hex : ∀ i, ∃ j, i < 92 → j < 92 ∧ s (mE W i) = mE W j := by
    intro i
    by_cases hi : i < 92
    · obtain ⟨hm, hg⟩ := mE_mem LF hW hi
      obtain ⟨j, hj, e⟩ := mE_complete LF hW (hs.M _ hm hg)
      exact ⟨j, fun _ => ⟨hj, e.symm⟩⟩
    · exact ⟨0, fun h => absurd h hi⟩
  choose π hπ using hex
  have hπlt : ∀ i < 92, π i < 92 := fun i hi => (hπ i hi).1
  have hπs : ∀ i < 92, s (mE W i) = mE W (π i) := fun i hi => (hπ i hi).2
  have hmG : ∀ i < 92, mE W i ∈ GammaH := fun i hi => (mE_mem LF hW hi).2
  have hπinj : ∀ i < 92, ∀ j < 92, π i = π j → i = j := by
    intro i hi j hj e
    apply mE_inj hW hi hj
    apply hs.inj _ (hmG i hi) _ (hmG j hj)
    rw [hπs i hi, hπs j hj, e]
  have hπsurj : ∀ y < 92, ∃ x < 92, π x = y := by
    have himg : (Finset.range 92).image π = Finset.range 92 := by
      apply Finset.eq_of_subset_of_card_le
      · intro y hy
        rw [Finset.mem_image] at hy
        obtain ⟨x, hx, rfl⟩ := hy
        exact Finset.mem_range.2 (hπlt x (Finset.mem_range.1 hx))
      · rw [Finset.card_image_of_injOn (fun a ha b hb e =>
          hπinj a (Finset.mem_range.1 ha) b (Finset.mem_range.1 hb) e)]
    intro y hy
    have : y ∈ (Finset.range 92).image π := by
      rw [himg]
      exact Finset.mem_range.2 hy
    obtain ⟨x, hx, e⟩ := Finset.mem_image.1 this
    exact ⟨x, Finset.mem_range.1 hx, e⟩
  have hπmt : ∀ i < 92, ∀ m < 92, π (mtK W i m) = mtK W (π i) (π m) := by
    intro i hi m hm
    obtain ⟨t1, t2⟩ := mE_mt LF hW hi hm
    obtain ⟨u1, u2⟩ := mE_mt LF hW (hπlt i hi) (hπlt m hm)
    apply mE_inj hW (hπlt _ t1) u1
    rw [← hπs _ t1, t2, u2, hs.mul _ (mul_mem (hmG i hi) (hmG m hm)) _ (hmG i hi),
      hs.mul _ (hmG i hi) _ (hmG m hm), hπs i hi, hπs m hm]
  have hlam1 : lamG W 1 = titsZ := by
    obtain ⟨hD, hD0, hl⟩ := labD_spec hW (i := 1) le_rfl (by norm_num)
    rw [hl]
    have e := (LF.conj_iff hD (one_mem titsD)).2 (Fin.ext (by
      rw [hD0, show 1 - 1 = 0 from rfl, G.fz0]
      rfl))
    rw [e]
    group
  have hm1 : mE W 1 = tauH * inA titsZ := by
    unfold mE
    rw [hlam1]
  have hzp : PR P.zp zpHat := by rw [G.zp]; exact prep_wd (tprepF hW) (tprepFI hW) G.lzp
  have he := prep_wd (tprepD hW) (tprepDI hW) G.le
  have hm2 : mE W (igK W 2) = tauH * inA zpHat := by
    obtain ⟨hD, hD0, hl⟩ := labD_spec hW (i := igK W 2) S.ig2pos S.ig2
    unfold mE
    rw [hl, (LF.conj_iff hD (wordIn_titsD_mem W.ew)).2 (Fin.ext (by
      rw [hD0, S.ig2y, fin_zero_eq, ← ap_eq' he (by norm_num), G.e0])),
      conj_of_mul (mul_eq_of he (tprepZ hW) hzp he G.eZ)]
  have hzG : inA titsZ ∈ GammaH := by
    have := hmG 1 (by norm_num)
    rw [hm1] at this
    have h' := mul_mem (inv_mem tau_mem_GammaH) this
    rwa [inv_mul_cancel_left] at h'
  have hπ0 : π 0 = 1 := by
    apply mE_inj hW (hπlt 0 (by norm_num)) (by norm_num)
    rw [← hπs 0 (by norm_num), mE_zero, hm1, h0]
  have hπ1 : π 1 = 0 := by
    apply mE_inj hW (hπlt 1 (by norm_num)) (by norm_num)
    rw [← hπs 1 (by norm_num), hm1, mE_zero, hs.mul _ tau_mem_GammaH _ hzG, h0, h1, mul_assoc]
    have : inA titsZ * inA titsZ = 1 := by
      simp only [inA, Prod.mk_mul_mk, mul_one]
      rw [titsZ_sq' hW]
      rfl
    rw [this, mul_one]
  have hπ2 : π (igK W 2) = igK W 2 := by
    apply mE_inj hW (hπlt _ S.ig2) S.ig2
    rw [← hπs _ S.ig2, hm2, h2]
  have hia : ∀ l < 5, iaK W (π (igK W 3)) (π (igK W 4)) l = π (igK W l) := by
    intro l hl
    rcases l with _ | _ | _ | _ | _ | l
    · rw [S.ig0, hπ0]
      rfl
    · rw [S.ig1, hπ1]
      rfl
    · rw [hπ2]
      rfl
    · rfl
    · rfl
    · omega
  have hroot : ∀ y, bitK (rootMask W) y = true →
      y < 92 ∧ tg 7 (p0K W (π (igK W 3)) (π (igK W 4))) y = π y := by
    intro y hy
    obtain ⟨l, hl, rfl⟩ := (rootMask_iff W y).1 hy
    refine ⟨ig_lt hW l hl, ?_⟩
    have := p0_spec hW (fun l hl => by
      rw [hia l hl]
      exact lt128_of_lt92 (hπlt _ (ig_lt hW l hl))) 5 le_rfl l hl
    rw [show p0K W (π (igK W 3)) (π (igK W 4)) = Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun l ih => tsetK 7 ih (igK W l) (iaK W (π (igK W 3)) (π (igK W 4)) l)) 5 from rfl,
      this, hia l hl]
  have hst1 := stage1_inv hW hπmt hia W.steps (rootMask W) _ S.steps hroot
  have hcov : ∀ y ∈ covK W, y < 92 ∧
      tg 7 (stage1F W (π (igK W 3)) (π (igK W 4)) W.steps (p0K W (π (igK W 3)) (π (igK W 4)))) y =
        π y := by
    intro y hy
    apply hst1 y
    unfold covK at hy
    rw [mapFy_eq] at hy
    simp only [List.mem_cons] at hy
    rcases hy with h | h | h | h | h | h
    · exact Or.inl ((rootMask_iff W y).2 ⟨0, by norm_num, h⟩)
    · exact Or.inl ((rootMask_iff W y).2 ⟨1, by norm_num, h⟩)
    · exact Or.inl ((rootMask_iff W y).2 ⟨2, by norm_num, h⟩)
    · exact Or.inl ((rootMask_iff W y).2 ⟨3, by norm_num, h⟩)
    · exact Or.inl ((rootMask_iff W y).2 ⟨4, by norm_num, h⟩)
    · exact Or.inr h
  have hact1 : allK (fun x => actAt W (π (igK W 3)) (π (igK W 4))
      (stage1F W (π (igK W 3)) (π (igK W 4)) W.steps (p0K W (π (igK W 3)) (π (igK W 4)))) x)
      (covK W) = true := by
    rw [allK_iff]
    intro x hx
    unfold actAt
    rw [CFSG.KS.Raw.Orb.allN_iff]
    intro l hl
    obtain ⟨hx92, hpx⟩ := hcov x hx
    obtain ⟨-, hpy⟩ := hcov _ (S.closed x hx l hl)
    rw [Nat.beq_eq, hpy, hpx, hπmt _ (ig_lt hW l hl) _ hx92, hia l hl]
  have hpt : ∀ r ∈ W.psteps, ptK W (π (fx r)) (π (fl r)) = π (fy r) := by
    intro r hr
    obtain ⟨hy, hx, hl, hlam⟩ := S.ps r hr
    have hx92 := (hcov _ hx).1
    have hl92 := (hcov _ hl).1
    have hlamE : lamG W (fy r) = lamG W (fx r) * lamG W (fl r) := by
      apply Equiv.ext
      intro x
      apply Fin.ext
      rw [← lamK_eq hW hy, hlam x x.2, lamK_eq hW hl92 x, lamK_eq hW hx92 ⟨_, (lamG W (fl r) x).2⟩,
        Equiv.Perm.mul_apply]
    have hmE : mE W (fy r) = tauH * mE W (fx r) * mE W (fl r) := by
      unfold mE
      rw [hlamE]
      refine Prod.ext ?_ ?_
      · simp [tauH, inA]
      · simp [tauH, inA]
    have e := hπs _ hy
    rw [hmE, hs.mul _ (mul_mem tau_mem_GammaH (hmG _ hx92)) _ (hmG _ hl92),
      hs.mul _ tau_mem_GammaH _ (hmG _ hx92), h0, hπs _ hx92, hπs _ hl92] at e
    have e2 := congrArg Prod.snd e
    simp only [mE, tauH, inA, Prod.snd_mul, one_mul, mul_one] at e2
    exact pt_eq hW (hπlt _ hx92) (hπlt _ hl92) (hπlt _ hy) (by rw [← e2, mul_assoc])
  have hst2 := stage2_inv hpt (fun r hr => ⟨(S.ps r hr).2.1, (S.ps r hr).2.2.1⟩) W.psteps
    (fun r hr => hr) [] _ (fun y hy => by
      rcases hy with hy | hy
      · exact (hcov y hy).2
      · simp at hy)
  have hpall : ∀ y < 92, tg 7 (stage2F W W.psteps (stage1F W (π (igK W 3)) (π (igK W 4)) W.steps
      (p0K W (π (igK W 3)) (π (igK W 4))))) y = π y := by
    intro y hy
    apply hst2 y
    rcases S.cover y hy with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  set p := stage2F W W.psteps (stage1F W (π (igK W 3)) (π (igK W 4)) W.steps
    (p0K W (π (igK W 3)) (π (igK W 4)))) with hpdef
  have hact2 : (allN 92 (fun x => actAt W (π (igK W 3)) (π (igK W 4)) p x) && injK p) = true := by
    rw [Bool.and_eq_true]
    constructor
    · rw [CFSG.KS.Raw.Orb.allN_iff]
      intro x hx
      unfold actAt
      rw [CFSG.KS.Raw.Orb.allN_iff]
      intro l hl
      obtain ⟨t1, -⟩ := mE_mt LF hW (ig_lt hW l hl) hx
      rw [Nat.beq_eq, hpall _ t1, hpall x hx, hπmt _ (ig_lt hW l hl) _ hx, hia l hl]
    · unfold injK
      rw [CFSG.KS.Raw.Orb.allN_iff]
      intro x hx
      rw [CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true, CFSG.KS.Raw.Orb.allN_iff]
      refine ⟨by rw [hpall x hx]; exact Nat.blt_eq.mpr (hπlt x hx), fun y hy => ?_⟩
      rw [CFSG.KS.Raw.Orb.bIf_eq, if_neg]
      rw [Nat.beq_eq, hpall x hx, hpall y (by omega)]
      intro e
      have := hπinj x hx y (by omega) e
      omega
  have hsK : ∀ x ∈ KH zpHat, s x ∈ KH zpHat := fun x hx => hs.mem_KH hF6 hx
  have hKG : ∀ x ∈ KH zpHat, x ∈ GammaH := fun x hx => (Subgroup.mem_inf.1 hx).1
  obtain ⟨c5, hc5, hk5⟩ := kap_complete LF hW hcard (hsK _ (rgK_mem LF hW (j := 0) (by norm_num)))
  obtain ⟨c6, hc6, hk6⟩ := kap_complete LF hW hcard (hsK _ (rgK_mem LF hW (j := 1) (by norm_num)))
  have hR2 : RgK W 2 = mE W W.a * mE W W.b := by
    simp only [RgK, show (2 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 1 by decide, if_false,
      if_true, mE]
    refine Prod.ext ?_ ?_
    · simp [tauH, inA]
    · simp [tauH, inA]
  have hsR2 : s (RgK W 2) = inA (lamG W (π W.a) * lamG W (π W.b)) := by
    rw [hR2, hs.mul _ (hmG _ K.a) _ (hmG _ K.b), hπs _ K.a, hπs _ K.b]
    unfold mE
    refine Prod.ext ?_ ?_
    · simp [tauH, inA]
    · simp [tauH, inA]
  have hab1 : abK W (tg 7 p W.a) (tg 7 p W.b) = tg 10 W.RK (keyCm W K.b1 (s (RgK W 2))) := by
    rw [hpall _ K.a, hpall _ K.b, (tabSpec_of hW.tab).abt _ (hπlt _ K.a) _ (hπlt _ K.b),
      lamK_eq hW (hπlt _ K.b) ⟨_, K.b1⟩, lamK_eq hW (hπlt _ K.a) ⟨_, (lamG W (π W.b) _).2⟩, hsR2]
    unfold keyCm
    simp [bitOf, inA, Equiv.Perm.mul_apply]
  obtain ⟨sab, hsab, hksab⟩ := kap_complete LF hW hcard (hsK _ (rgK_mem LF hW (j := 2)
    (by norm_num)))
  have hab1' : abK W (tg 7 p W.a) (tg 7 p W.b) = sab + 1 := by
    rw [hab1, ← hksab, ← keyF_eq hW hsab, K.rk sab hsab]
  have hscan := pairK_spec (hW.search _ (hπlt _ (ig_lt hW 3 (by norm_num))) |>
    fun h => CFSG.KS.Raw.Orb.allN_iff.1 h _ (hπlt _ (ig_lt hW 4 (by norm_num)))) hact1 hact2
    (by rw [hab1']; omega)
  rw [← hpdef, hab1', Nat.add_sub_cancel] at hscan
  have hrow : ∀ {c' j : Nat}, j < 2 → c' < 512 → kap W c' = s (RgK W j) →
      W.KA.getD c' 0 = qRowK p (nthK W.KA (j + 1)) := by
    intro c' j hj hc' hk
    have hkj : kap W (j + 1) = RgK W j := by
      rcases j with _ | _ | j
      · rw [kap_of_lt (by rw [K.par1]; norm_num), K.par1, K.gen1, kap_zero, one_mul]
      · rw [kap_of_lt (by rw [K.par2]; norm_num), K.par2, K.gen2, kap_zero, one_mul]
      · omega
    obtain ⟨kc1, kc2⟩ := ka_spec LF hW c' hc'
    obtain ⟨kj1, kj2⟩ := ka_spec LF hW (j + 1) (by omega)
    have hinj' : ∀ x < 92, ∀ y < 92, tg 7 p x = tg 7 p y → x = y := fun x hx y hy e => by
      rw [hpall x hx, hpall y hy] at e
      exact hπinj x hx y hy e
    apply eq_of_rows kc1 (qRowK_shr (fun x hx => by rw [hpall x hx]; exact hπlt x hx))
    intro z hz
    obtain ⟨x, hx, rfl⟩ := hπsurj z hz
    rw [nthK_eq, ← hpall x hx, tg_qRowK hinj' hx]
    obtain ⟨a1, a2⟩ := kj2 x hx
    obtain ⟨b1, b2⟩ := kc2 _ (hπlt x hx)
    rw [hpall _ a1, hpall x hx]
    apply mE_inj hW b1 (hπlt _ a1)
    have hjK := rgK_mem LF hW (j := j) (by omega)
    rw [b2, ← hπs _ a1, a2, hkj, hk, hs.mul _ (mul_mem (hKG _ hjK) (hmG x hx)) _
      (inv_mem (hKG _ hjK)), hs.mul _ (hKG _ hjK) _ (hmG x hx), hs.inv (hKG _ hjK), hπs x hx]
  have hr5 := hrow (j := 0) (by norm_num) hc5 hk5
  have hr6 := hrow (j := 1) (by norm_num) hc6 hk6
  have hleaf := scan6_spec W.KA 0 (scan5_spec W.KA 0 hscan c5 (by rw [K.lenKA]; exact hc5) hr5)
    c6 (by rw [K.lenKA]; exact hc6) hr6
  rw [Nat.zero_add, Nat.zero_add] at hleaf
  have hθm : ∀ x ∈ KH zpHat, ∀ y ∈ KH zpHat, θ (x * y) = θ x * θ y := by
    intro x hx y hy
    rw [hθ, hθ, hθ, hs.mul _ (hKG _ hx) _ (hKG _ hy)]
    group
  have hθ1 : θ 1 = 1 := by
    rw [hθ, hs.one]
    group
  obtain ⟨mc1lt, hkmc1⟩ := kap_mc1 LF hW hcard hF6
  have hthr : ∀ j < 4, thrK W c5 c6 sab j < 512 ∧ kap W (thrK W c5 c6 sab j) = θ (RgK W j) := by
    intro j hj
    have hpick : pick4 c5 c6 sab W.mc1 j < 512 ∧ kap W (pick4 c5 c6 sab W.mc1 j) = s (RgK W j) := by
      rcases j with _ | _ | _ | _ | j
      · exact ⟨hc5, hk5⟩
      · exact ⟨hc6, hk6⟩
      · exact ⟨hsab, hksab⟩
      · refine ⟨mc1lt, ?_⟩
        rw [show pick4 c5 c6 sab W.mc1 3 = W.mc1 from rfl, hkmc1,
          show RgK W 3 = tauH by simp [RgK], h0]
      · omega
    obtain ⟨y1, y2⟩ := kap_Y LF hW hcard hF6 hpick.1
    exact ⟨y1, by rw [show thrK W c5 c6 sab j = tg 9 W.Y (pick4 c5 c6 sab W.mc1 j) from rfl, y2,
      hpick.2, hθ]⟩
  have hhom := kap_homF LF hW hcard hθm hθ1 hthr
  have hθK : ∀ x ∈ KH zpHat, θ x ∈ KH zpHat := fun x hx => hs.theta_mem_KH hF6 hθ hx
  have h3 : ∀ {t : Nat}, t < 512 → th3K W c5 c6 sab t < 512 ∧
      kap W (th3K W c5 c6 sab t) = θ (θ (θ (kap W t))) := by
    intro t ht
    obtain ⟨a1, a2⟩ := hhom 16 t ht (reach_all K ht)
    obtain ⟨b1, b2⟩ := hhom 16 _ a1 (reach_all K a1)
    obtain ⟨c1, c2⟩ := hhom 16 _ b1 (reach_all K b1)
    exact ⟨c1, by rw [show th3K W c5 c6 sab t = homF W (thrK W c5 c6 sab) 16
      (homF W (thrK W c5 c6 sab) 16 (homF W (thrK W c5 c6 sab) 16 t)) from rfl, c2, b2, a2]⟩
  obtain ⟨dc, hdc, rfl⟩ := kap_complete LF hW hcard hd
  have hmem : ∀ {t : Nat} {cl : List Nat}, t < 512 → (∀ c ∈ cl, c < 512) →
      (∀ d' < 512, ∃ c ∈ cl, mulF W 16 c d' = mulF W 16 d' t) →
      memK (th3K W c5 c6 sab t) cl = true := by
    intro t cl ht hcl hclk
    obtain ⟨c, hc, hkc⟩ := kap_cl LF hW hcard ht hcl hclk hdc
    obtain ⟨t1, t2⟩ := h3 ht
    rw [memK_iff]
    have : th3K W c5 c6 sab t = c := by
      apply kap_inj hW t1 (hcl c hc)
      rw [t2, hkc, hdθ _ (kap_mem LF hW t ht)]
    rw [this]
    exact hc
  unfold leafBadK at hleaf
  rw [hmem K.t0 K.cl0lt K.cl0, hmem K.t1 K.cl1lt K.cl1] at hleaf
  exact Bool.noConfusion hleaf

end Search

end CFSG.LocalAnalysis.EvenBN.Tits.Thm49E

end
