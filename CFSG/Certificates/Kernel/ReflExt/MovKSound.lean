module

public import Certificates.Data.Kernel.ReflExt.MovK
public import Certificates.Data.CFSGNative.DepFrame.Moving
public import CFSG.Certificates.Kernel.ReflExt.NineKSound

public section

namespace CFSG.ReflExt.MK

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG.TwoNodeSmall CFSG.TwoNodeSmall.WitK CFSG.TwoNodeSmall.ExclK CFSG.TwoNodeSmall.LaneSound
  CFSG.TwoNodeSmall.PosBK CFSG.TwoNodeSmall.PosBK.OKS CFSG.ReflExt CFSG.ReflExt.RXK CFSG.NineAll
  CFSG.DepFrame CFSG.ReflExt.NK CFSG.ReflExt.NK.NS CFSG.ReflExt.DK

open Snd (decR)

theorem partM_lt {P : Pt} {d : FDN} {i : Nat} (hi : i < 10) : partM P d i = partN P 0 d i := by
  unfold partM
  simp only [Nat.blt_eq.mpr hi, cond_true]

theorem verifyRepM_of {P0 : Pt} {cand : List Refl} {rp : NRep}
    (hw : ∀ c, rp.kind ≠ .w (.weyl c)) (h : verifyRepD P0 cand rp = true) :
    verifyRepM P0 cand rp = true := by
  unfold verifyRepM
  split
  · rename_i c heq
    exact absurd heq (hw c)
  · exact h

theorem partM_verify (P : Pt) (d : FDN) (h : ∀ i < 16, partM P d i = true) :
    ∃ T, verifyAllM P T = true := by
  have hN : ∀ i < 10, partN P 0 d i = true := fun i hi => by
    rw [← partM_lt hi]
    exact h i (by omega)
  obtain ⟨rows, bk, cd, tg, R0, R1⟩ := d
  have h0 := hN 0 (by norm_num)
  have h9 := hN 9 (by norm_num)
  have h14 := h 14 (by norm_num)
  have h15 := h 15 (by norm_num)
  unfold partN at h0 h9
  unfold partM at h14 h15
  simp only [Nat.beq_refl, cond_true, beqF (by norm_num : (9 : Nat) ≠ 0),
    bltF (by norm_num : ¬ (9 : Nat) < 9), cond_false] at h0 h9
  simp only [Nat.beq_refl, cond_true, bltF (by norm_num : ¬ (14 : Nat) < 10),
    bltF (by norm_num : ¬ (14 : Nat) < 14), bltF (by norm_num : ¬ (15 : Nat) < 10),
    bltF (by norm_num : ¬ (15 : Nat) < 14), beqF (by norm_num : (15 : Nat) ≠ 14), cond_false,
    Bool.true_and] at h14 h15
  have hmsk : ∀ k < 8, mskB (ptF P) P.D (cloE (gensK P) rows)
      (slc (Nat.succ (Nat.div bk.length 8)) k bk) = true := by
    intro k hk
    have := hN (k + 1) (by omega)
    unfold partN at this
    simp only [beqF (by omega : k + 1 ≠ 0), cond_false,
      Nat.blt_eq.mpr (by omega : k + 1 < 9), cond_true] at this
    exact this
  have htg : ∀ k < 4, all2 (tagM (ptF P) P.D (gensK P).length
      (Nat.add (gensK P).length rows.length) (pk P.D P.x) (gensK P) (cloE (gensK P) rows) R1)
      (slc (Nat.succ (Nat.div cd.length 4)) k cd) (slc (Nat.succ (Nat.div cd.length 4)) k tg) =
      true := by
    intro k hk
    have := h (k + 10) (by omega)
    unfold partM at this
    simp only [bltF (by omega : ¬ k + 10 < 10), cond_false,
      Nat.blt_eq.mpr (by omega : k + 10 < 14), cond_true, Nat.add_sub_cancel] at this
    exact this
  change (Nat.beq P.p 3 && Nat.ble 1 P.D && Nat.ble P.D 9 && allK (reflOK (fdB 3 P.D)) (gensK P) &&
      allK (fun g => Nat.beq (dotK (fdB 3 P.D) g.2 (pk P.D P.x)) 0) (gensK P) &&
      cloP (fdB 3 P.D) (gensK P).length (gensK P) rows (gensK P).length 0 (cloE (gensK P) rows) &&
      allK (fun r => Nat.beq (dotK (fdB 3 P.D) r.2 (pk P.D P.x)) 0) (cloE (gensK P) rows) &&
      bkS (Nat.pow 3 P.D) bk 0 (0, 0, true) (0, 0, true)) = true at h0
  simp only [Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq] at h0
  obtain ⟨⟨⟨⟨⟨⟨⟨hp, -⟩, hD9⟩, hrefl⟩, hGX⟩, hclo⟩, hX⟩, hbkS⟩ := h0
  have hD : P.D ≤ 10 := by omega
  have hfact : Fact P.p.Prime := ⟨by rw [hp]; norm_num⟩
  have hL := laneOK_three hp hD
  have hgk := Snd.gensK_eq hp
  change candOK (fdB 3 P.D) P.D bk cd = true at h9
  change allK (fun rp => reflOK (fdB 3 P.D) rp.1 &&
      !(Nat.beq (dotK (fdB 3 P.D) rp.1.2 (pk P.D P.x)) 0) &&
      (bif Nat.beq rp.2.1 0 then centK (fdB 3 P.D) P.D (gensK P) rp.1
       else Nat.beq rp.2.1 1 && recBad (ptX P [rp.1] P.bound) rp.2.2.1)) R1 = true at h14
  change centTags (fdB 3 P.D) P.D R1 cd tg = true at h15
  unfold ptF at hmsk htg
  rw [hgk] at hrefl hGX hclo hX hmsk htg h14
  have hrefl' := (Snd.allK_spec _ _).mp hrefl
  have hWF : P.WF := by
    intro g hg
    have := hrefl' (packR P g) (List.mem_map.mpr ⟨g, hg, rfl⟩)
    rw [Snd.packR3 hp, reflOK_pk hp hD] at this
    exact Snd.WF_of_dotv this
  have hwfP := Snd.wfCheck_of_WF hp hWF
  rw [List.length_map] at hclo
  obtain ⟨hDl, hsem⟩ := Snd.clo_spec hL rows hclo
  have hC : cloE (P.gens.map (packR P)) rows =
      ((cloD P (baseD P) rows).map fun x => decR P.D (packR P x.1)).map (packR P) := by
    refine hDl.symm.trans ?_
    rw [List.map_map]
    apply List.map_congr_left
    intro x _
    exact (Snd.packR_decR hp (Snd.canP_packR hp x.1)).symm
  have hnC : Nat.add (P.gens.map (packR P)).length rows.length =
      (cloD P (baseD P) rows).length := by
    have := congrArg List.length hDl
    simp only [List.length_map, List.length_append] at this
    rw [List.length_map]
    exact this.symm
  rw [hC] at hX hmsk htg
  rw [hnC] at htg
  set Dl := cloD P (baseD P) rows with hDl_def
  set ys := Dl.map fun x => decR P.D (packR P x.1) with hys
  have hbk : bkK (fdB 3 P.D) P.D (Nat.pow 3 P.D) (ys.map (packR P)) bk 0 (0, 0, true)
      (0, 0, true) = true := by
    apply bkK_of bk 0 _ _ hbkS
    intro b hb
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hb
    have hs : 0 < Nat.succ (Nat.div bk.length 8) := Nat.succ_pos _
    have hk : i / Nat.succ (Nat.div bk.length 8) < 8 := by
      apply (Nat.div_lt_iff_lt_mul hs).2
      change i < 8 * Nat.succ (bk.length / 8)
      omega
    have hm := hmsk _ hk
    unfold mskB at hm
    have := (Snd.allK_spec _ _).mp hm _ (mem_slc hs hi)
    rw [Bool.and_eq_true] at this
    exact this
  have hcdE : ∀ x ∈ cd, packR P (decR P.D x) = x ∧ P.dotv (decR P.D x).f (decR P.D x).h = 2 :=
    fun x hx => Snd.cd_entry hp hD h9 hx
  have htag := all2_slc (Nat.succ_pos _)
    (by change cd.length ≤ 4 * Nat.succ (cd.length / 4); omega) htg
  have hmvK : ∀ i (hi : i < cd.length), (P.dotv (decR P.D cd[i]).f P.x != 0) = true →
      dotK (fdB 3 P.D) cd[i].2 (pk P.D P.x) ≠ 0 := by
    intro i hi hmv
    obtain ⟨hpe, -⟩ := hcdE cd[i] (List.getElem_mem hi)
    rw [← hpe, dotK_packR hp hD]
    simpa using hmv
  set T : NTables := ⟨rootsD P Dl, [], [],
    (obT P.D 2 cd tg).filter (fun e => P.dotv e.e.f P.x != 0),
    (fillL (cn P.D) R1).map (NK.NS.mk1 P cd)⟩ with hT
  have hsub : ∀ ρ ∈ ys, ρ ∈ T.roots.map (·.r) := by
    intro ρ hρ
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hρ
    exact List.mem_map.mpr ⟨Snd.rt P x,
      (List.mem_flatMap.mpr ⟨x, hx, by simp⟩ : Snd.rt P x ∈ rootsD P Dl), rfl⟩
  have hcandL : ∀ c ∈ candOfN P T, decR P.D (packR P c) = c ∧ packR P c ∈ cd :=
    fun c hc => cand_mem2 hp hD hsub hbk h9 hc
  have hcanR : ∀ (i : Nat) (hi : i < cd.length) (u : List Nat) (a : Nat × Nat),
      ltAll (P.gens.map (packR P)).length u = true →
      eqPM (fdB 3 P.D) P.D a (cw (fdB 3 P.D) (P.gens.map (packR P)) u cd[i]) = true →
      canP P.D a = true ∧ realizes (withExtra P [decR P.D cd[i]])
        (u ++ [P.gens.length] ++ u.reverse) (decR P.D a) = true := by
    intro i hi u a hu heq
    obtain ⟨hpe, hde⟩ := hcdE cd[i] (List.getElem_mem hi)
    have hu' := Snd.ltAll_spec _ u hu
    rw [← hpe, Snd.cw_pack hL _ _ (gens_nth P) u hu'] at heq
    obtain ⟨hca, heq'⟩ := eqPM_canon hp heq
    refine ⟨hca, Snd.conj_real hp hD hWF _ _ hde u (by simpa using hu) ?_⟩
    rw [Snd.cw_pack hL _ _ (gens_nth P) u hu']
    exact heq'
  have hR1 : ∀ rp ∈ R1, reflOK (fdB 3 P.D) rp.1 = true ∧
      dotK (fdB 3 P.D) rp.1.2 (pk P.D P.x) ≠ 0 ∧
      (rp.2.1 = 0 → centK (fdB 3 P.D) P.D (P.gens.map (packR P)) rp.1 = true) ∧
      (rp.2.1 ≠ 0 → (rp.2.2.1.1 = 1 ∨ rp.2.2.1.1 = 2) ∧
        chkPt (ptX P [rp.1] P.bound) rp.2.2.1 = true) := by
    intro rp hrp
    have := (Snd.allK_spec _ _).mp h14 rp hrp
    rw [Bool.and_eq_true, Bool.and_eq_true] at this
    obtain ⟨⟨h1, h2⟩, h3⟩ := this
    refine ⟨h1, fun e => ?_, fun e => ?_, fun e => ?_⟩
    · rw [e] at h2
      exact absurd h2 (by decide)
    · rw [e] at h3
      exact h3
    · rw [beqF e, cond_false] at h3
      simp only [recBad, Bool.and_eq_true, Bool.or_eq_true, Nat.beq_eq] at h3
      exact h3.2
  have hv0 : vFixN P = true := by
    unfold vFixN
    rw [List.all_eq_true]
    intro g hg
    have := (Snd.allK_spec _ _).mp hGX (packR P g) (List.mem_map.mpr ⟨g, hg, rfl⟩)
    rw [beq_iff_eq]
    exact fix_of_pack hp hD this
  have hv1 : vRootsN P T = true := by
    unfold vRootsN
    rw [List.all_eq_true]
    intro ρ hρ
    have hρ' : ρ ∈ rootsD P Dl := hρ
    obtain ⟨x, hx, hρx⟩ := List.mem_flatMap.mp hρ'
    obtain ⟨hw, hr, hfx⟩ := roots_ok hp hWF (hsem x hx) ρ hρx
    have hfix : P.dotv (decR P.D (packR P x.1)).f P.x = 0 := by
      have := (Snd.allK_spec _ _).mp hX (packR P (decR P.D (packR P x.1)))
        (List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨x, hx, rfl⟩, rfl⟩)
      exact fix_of_pack hp hD this
    simp only [Bool.and_eq_true, beq_iff_eq]
    exact ⟨⟨hw, hr⟩, hfx hfix⟩
  have hv3 : vCover1 P T (candOfN P T) = true := by
    unfold vCover1 movingOf
    rw [List.all_eq_true]
    intro c hc'
    rw [List.mem_filter] at hc'
    obtain ⟨hc', hmv⟩ := hc'
    obtain ⟨hdc, hcm⟩ := hcandL c hc'
    obtain ⟨i, hi, hci⟩ := List.mem_iff_getElem.mp hcm
    obtain ⟨hi', ht⟩ := htag i hi
    have hmK : dotK (fdB 3 P.D) cd[i].2 (pk P.D P.x) ≠ 0 := by
      rw [hci, dotK_packR hp hD]
      simpa using hmv
    unfold tagM at ht
    rw [Bool.or_eq_true, Nat.beq_eq] at ht
    rcases ht with hf | ht
    · exact absurd hf hmK
    rw [List.any_eq_true]
    rcases tagN_cases ht with ⟨j, -, h0', -⟩ | ⟨j, u, -, -, hj0, -⟩ | ⟨j, u, htj, -, -⟩
    · exact absurd h0' hmK
    · exact absurd hj0 (by simp)
    · refine ⟨⟨decR P.D cd[i], u, j⟩, List.mem_filter.mpr ⟨mem_obT hi hi' htj, ?_⟩, ?_⟩
      · change (P.dotv (decR P.D cd[i]).f P.x != 0) = true
        rw [hci, hdc]
        exact hmv
      · change reqb (decR P.D cd[i]) c = true
        rw [hci, hdc]
        exact Snd.reqb_self c
  have hv6 : T.orb1.all (entry1OK P T) = true := by
    rw [List.all_eq_true]
    intro e he
    have he' : e ∈ (obT P.D 2 cd tg).filter (fun e => P.dotv e.e.f P.x != 0) := he
    obtain ⟨he', hmv⟩ := List.mem_filter.mp he'
    obtain ⟨i, hi, hi', j, u, hju, rfl⟩ := of_mem_obT he'
    have hmK := hmvK i hi hmv
    obtain ⟨hi'', ht⟩ := htag i hi
    unfold tagM at ht
    rw [Bool.or_eq_true, Nat.beq_eq] at ht
    rcases ht with hf | ht
    · exact absurd hf hmK
    rw [hju] at ht
    rcases tagN_cases ht with ⟨j', e1, -⟩ | ⟨j', u', e1, -⟩ | ⟨j', u', e1, -, hj, hu, heq⟩
    · exact absurd (List.cons.inj e1).1 (by decide)
    · exact absurd (List.cons.inj e1).1 (by decide)
    · obtain ⟨rfl, rfl⟩ := List.cons.inj (List.cons.inj e1).2
      rw [nthK_eq', List.getD_eq_getElem _ _ hj] at heq
      obtain ⟨hca, hreal⟩ := hcanR i hi u _ hu heq
      have hget : T.reps[j]? = some (NK.NS.mk1 P cd R1[j]) := by
        change ((fillL (cn P.D) R1).map (NK.NS.mk1 P cd))[j]? = _
        rw [List.getElem?_map, fill_get hj hca]
        rfl
      obtain ⟨-, hde⟩ := hcdE cd[i] (List.getElem_mem hi)
      unfold entry1OK
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨⟨Snd.wfR_of_dotv hp hde, lt_of_get hget⟩, ?_⟩
      rw [hget]
      exact hreal
  have hv7 : T.reps.all (verifyRepM P (candOfN P T)) = true := by
    rw [List.all_eq_true]
    intro rp' hrp'
    have hrp'' : rp' ∈ (fillL (cn P.D) R1).map (NK.NS.mk1 P cd) := hrp'
    obtain ⟨rp, hrp, rfl⟩ := List.mem_map.mp hrp''
    obtain ⟨hmem, hca⟩ := fill_mem hrp
    obtain ⟨hrf, hmK, hk0, hk1⟩ := hR1 rp hmem
    obtain ⟨hpr, hd2⟩ := canon_facts hp hD hca hrf
    have hbase : (wfR P (NK.NS.mk1 P cd rp).r &&
        P.dotv (NK.NS.mk1 P cd rp).r.f P.x != 0) = true := by
      rw [Bool.and_eq_true]
      refine ⟨Snd.wfR_of_dotv hp hd2, ?_⟩
      change (P.dotv (decR P.D rp.1).f P.x != 0) = true
      rw [← dotK_packR hp hD, hpr]
      simpa using hmK
    by_cases hz : rp.2.1 = 0
    · have hk : (NK.NS.mk1 P cd rp).kind = .cent := if_pos hz
      refine verifyRepM_of (by rw [hk]; intro c hc; cases hc) ?_
      unfold verifyRepD
      rw [hbase, Bool.true_and, hk]
      change centOK P (decR P.D rp.1) = true
      refine centOK_of hp hD ?_
      rw [hpr]
      exact hk0 hz
    · obtain ⟨hkk, hchk⟩ := hk1 hz
      have hk : (NK.NS.mk1 P cd rp).kind = .w (witB (ptX P [rp.1] P.bound) rp.2.2.1.1) :=
        if_neg hz
      obtain ⟨hbad, hver⟩ := witB_bad hchk hkk
      refine verifyRepM_of ?_ ?_
      · rw [hk]
        intro c hc
        injection hc with hc
        rw [hc] at hbad
        simp [isBadW] at hbad
      · unfold verifyRepD
        rw [hbase, Bool.true_and, hk]
        generalize witB (ptX P [rp.1] P.bound) rp.2.2.1.1 = w at hbad hver ⊢
        cases w <;> first | exact hver | simp [isBadW] at hbad
  have hv8 : T.orb1.all (centEntryOK P T) = true := by
    obtain ⟨-, hct⟩ := Snd.all2_spec _ cd tg h15
    rw [List.all_eq_true]
    intro e he
    have he' : e ∈ (obT P.D 2 cd tg).filter (fun e => P.dotv e.e.f P.x != 0) := he
    obtain ⟨he', hmv⟩ := List.mem_filter.mp he'
    obtain ⟨i, hi, hi', j, u, hju, rfl⟩ := of_mem_obT he'
    have hmK := hmvK i hi hmv
    obtain ⟨hi'', ht⟩ := htag i hi
    have hc := hct i hi hi'
    unfold tagM at ht
    rw [Bool.or_eq_true, Nat.beq_eq] at ht
    rcases ht with hf | ht
    · exact absurd hf hmK
    rw [hju] at ht hc
    rcases tagN_cases ht with ⟨j', e1, -⟩ | ⟨j', u', e1, -⟩ | ⟨j', u', e1, -, hj, hu, heq⟩
    · exact absurd (List.cons.inj e1).1 (by decide)
    · exact absurd (List.cons.inj e1).1 (by decide)
    · obtain ⟨rfl, rfl⟩ := List.cons.inj (List.cons.inj e1).2
      rw [nthK_eq', List.getD_eq_getElem _ _ hj] at heq
      obtain ⟨hca, -⟩ := hcanR i hi u _ hu heq
      have hget : T.reps[j]? = some (NK.NS.mk1 P cd R1[j]) := by
        change ((fillL (cn P.D) R1).map (NK.NS.mk1 P cd))[j]? = _
        rw [List.getElem?_map, fill_get hj hca]
        rfl
      have hc' : (bne (Nat.beq 2 2) true || bne (Nat.beq (nthK r10 R1 j).2.1 0) true ||
          eqPM (fdB 3 P.D) P.D cd[i] (nthK r10 R1 j).1) = true := hc
      rw [nthK_eq', List.getD_eq_getElem _ _ hj] at hc'
      unfold centEntryOK
      rw [hget]
      by_cases hz : R1[j].2.1 = 0
      · have hk : (NK.NS.mk1 P cd R1[j]).kind = .cent := if_pos hz
        obtain ⟨hrf, -, -, -⟩ := hR1 R1[j] (List.getElem_mem hj)
        obtain ⟨hr, -⟩ := canon_facts hp hD hca hrf
        rw [hz] at hc'
        have hpm : eqPM (fdB 3 P.D) P.D cd[i] R1[j].1 = true := by
          simpa [Nat.beq_refl] using hc'
        dsimp only
        rw [hk]
        change (reqb (decR P.D cd[i]) (decR P.D R1[j].1) ||
          reqb (decR P.D cd[i]) (negR P (decR P.D R1[j].1))) = true
        unfold eqPM eqP at hpm
        simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.beq_eq] at hpm
        rw [Bool.or_eq_true]
        rcases hpm with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · left
          have e : cd[i] = R1[j].1 := Prod.ext e1 e2
          rw [e]
          exact Snd.reqb_self _
        · right
          have e : cd[i] = packR P (Snd.negRf P.D (decR P.D R1[j].1)) := by
            rw [← Snd.negP_packR hp, hr]
            exact Prod.ext e1 e2
          rw [e, decR_negRf hp, negR_eq hp]
          exact Snd.reqb_self _
      · have hk : (NK.NS.mk1 P cd R1[j]).kind =
            .w (witB (ptX P [R1[j].1] P.bound) R1[j].2.2.1.1) := if_neg hz
        dsimp only
        rw [hk]
  refine ⟨T, ?_⟩
  unfold verifyAllM
  simp only [hwfP, hv0, hv1, hv3, hv6, hv7, hv8, Bool.and_self]

end CFSG.ReflExt.MK

end
