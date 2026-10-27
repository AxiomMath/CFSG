module

public import Certificates.Data.Kernel.LocalQT.CoreR
public import CFSG.Certificates.Kernel.LocalQTCoreCSnd.Core

public section

namespace CFSG.KC.LQT.M24Snd

open Equiv CFSG.KC.LQT CFSG.QuasithinUnique.A5.Kc3Cert
  CFSG.QuasithinUnique.Vol2Native.A312L.PermLat CFSG.KC.LQT.W CFSG.KC.LQT.L

private theorem aux_core_shl (x : ℕ) : Nat.shiftLeft 1 x = 2 ^ x := by
  rw [Nat.shiftLeft_eq', Nat.shiftLeft_eq, one_mul]

private theorem aux_core_or (m k i : ℕ) :
    (Nat.lor m k).testBit i = (m.testBit i || k.testBit i) :=
  Nat.testBit_or m k i

private theorem aux_core_and (m k i : ℕ) :
    (Nat.land m k).testBit i = (m.testBit i && k.testBit i) :=
  Nat.testBit_and m k i

private theorem aux_core_distinct_gen (l : List ℕ) : ∀ seen : ℕ,
    List.rec (motive := fun _ => ℕ → Bool) (fun _ => true)
      (fun x _ ih seen => CFSG.KC.LQT.P.letB (Nat.shiftLeft 1 x) fun b =>
        CFSG.KC.Ord.andB (Nat.beq (Nat.land seen b) 0) (ih (Nat.lor seen b))) l seen = true →
    l.Nodup ∧ ∀ x ∈ l, seen.testBit x = false := by
  induction l with
  | nil =>
    intro seen _
    exact ⟨List.nodup_nil, fun x hx => (List.not_mem_nil hx).elim⟩
  | cons x xs ih =>
    intro seen h
    have h' := (CFSG.KC.LQT.P.letB_eq (Nat.shiftLeft 1 x) _).symm.trans h
    obtain ⟨h1, h2⟩ := CFSG.KC.LQT.P.andB_iff.1 h'
    have e1 : Nat.land seen (Nat.shiftLeft 1 x) = 0 := CFSG.KC.LQT.P.beq_iff.1 h1
    rw [aux_core_shl] at e1
    have hx : seen.testBit x = false := by
      have e2 := congrArg (fun m => Nat.testBit m x) e1
      simpa only [aux_core_and, Nat.testBit_two_pow_self, Bool.and_true, Nat.zero_testBit] using e2
    obtain ⟨hnd, hall⟩ := ih _ h2
    have hxn : x ∉ xs := by
      intro hmem
      have e3 := hall x hmem
      rw [aux_core_or, aux_core_shl, Nat.testBit_two_pow_self] at e3
      simp at e3
    refine ⟨List.nodup_cons.2 ⟨hxn, hnd⟩, ?_⟩
    intro y hy
    rcases List.mem_cons.1 hy with rfl | hy'
    · exact hx
    · have e4 := hall y hy'
      rw [aux_core_or, aux_core_shl, Nat.testBit_two_pow] at e4
      exact (Bool.or_eq_false_iff.1 e4).1

theorem distinctR_nodup (l : List ℕ) (h : CFSG.KC.LQT.Syl.distinctR l = true) : l.Nodup := by
  unfold CFSG.KC.LQT.Syl.distinctR at h
  exact (aux_core_distinct_gen l 0 h).1

theorem orbN_sound {n : ℕ} (hn : n ≤ 32) (gs : List (Perm (Fin n))) {B : List (Perm (Fin n))}
    (h : CFSG.KC.LQT.Syl.CoreSnd.EFacts B) (rT : List ℕ) (nOrd kOrd : ℕ)
    (ho : CFSG.KC.LQT.Syl.orbN n (gs.map P.code) (B.map P.code) rT nOrd kOrd = true) :
    ((treeReps (gs.map RN.enc) (pairUp rT)).toList.map
        (imgMask (fixPts (bfsSet (B.map RN.enc) 16)))).Nodup ∧
      kOrd = (treeReps (gs.map RN.enc) (pairUp rT)).size * nOrd := by
  unfold CFSG.KC.LQT.Syl.orbN at ho
  simp only [CFSG.KC.LQT.P.andB_iff] at ho
  obtain ⟨hm, hd, hk⟩ := ho
  rw [CFSG.KC.LQT.Syl.CoreSnd.lstK_code hn B, CFSG.KC.LQT.Syl.CoreSnd.fixK_eq hn h,
    CFSG.KC.LQT.Syl.CoreSnd.repsK_eq hn gs rT hm] at hd
  rw [CFSG.KC.LQT.Syl.CoreSnd.repsK_eq hn gs rT hm, CFSG.KC.LQT.S.lenL_eq, List.length_map,
    Array.length_toList] at hk
  refine ⟨List.Nodup.of_map (CFSG.KC.LQT.Syl.rankM n) ?_, CFSG.KC.LQT.P.beq_iff.1 hk⟩
  have hnd := distinctR_nodup _ hd
  rw [List.map_map] at hnd
  rw [List.map_map]
  convert hnd using 2
  funext r
  simp only [Function.comp_apply, CFSG.KC.LQT.Syl.colexK, CFSG.KC.LQT.Syl.CoreSnd.maskK_eq hn]

open CFSG.KC.LQT.CM CFSG.KC.LQT.Syl.CoreSnd

theorem coreR_snd {n : ℕ} (gs : List (Perm (Fin n))) {G : List ℕ} (hG : gs.map codeP = G)
    (c : ECert) (kOrd : ℕ) (C : List Lvl) (W : List (List (List ℕ)))
    (hE : CFSG.KC.LQT.Syl.eK n (c.eW.map (evalWK n G)) = true) (hC : chainOK n C = true)
    (hI : CFSG.KC.LQT.L.chainInj n C = true)
    (hgc : grpC n C (chainF C) (c.nW.map (evalWK n G)) W c.depth = true)
    (hL : chainF C = c.nOrd)
    (hN : CFSG.KC.LQT.Syl.normK n (c.eW.map (evalWK n G)) (c.nW.map (evalWK n G)) = true)
    (hO : CFSG.KC.LQT.Syl.orbN n G (c.eW.map (evalWK n G)) c.rT c.nOrd kOrd = true) :
    c.coreCheckT (gs.map RN.enc) kOrd = true := by
  subst hG
  have hn : n ≤ 32 := eK_le hE
  set B : List (Perm (Fin n)) := c.eW.map (evalW gs) with hB
  set NP : List (Perm (Fin n)) := c.nW.map (evalW gs) with hNP
  have hBc : c.eW.map (evalWK n (gs.map codeP)) = B.map P.code := by
    rw [hB, List.map_map]
    exact List.map_congr_left fun w _ => CFSG.KC.LQT.LK.evalWK_code hn gs w
  have hNc : c.nW.map (evalWK n (gs.map codeP)) = NP.map P.code := by
    rw [hNP, List.map_map]
    exact List.map_congr_left fun w _ => CFSG.KC.LQT.LK.evalWK_code hn gs w
  have hBe : c.eR (gs.map RN.enc) = B.map RN.enc := by
    unfold ECert.eR
    rw [hB, List.map_map]
    exact List.map_congr_left fun w _ => (enc_evalW (rawIsEnc n) gs w).symm
  have hNe : c.nR (gs.map RN.enc) = NP.map RN.enc := by
    unfold ECert.nR
    rw [hNP, List.map_map]
    exact List.map_congr_left fun w _ => (enc_evalW (rawIsEnc n) gs w).symm
  rw [hBc] at hE hN hO
  rw [hNc] at hgc hN
  obtain ⟨-, hEF⟩ := eK_facts B hE
  have hn0 : 0 < n := hEF.pos
  have hgrp : grpC n C (chainF C) (NP.map P.code) W c.depth = true := hgc
  obtain ⟨h1, -⟩ := grpC_sound hn hC hI NP hgrp
  have hmem := mem_bfsSet_iff hn hC hI NP hgrp
  have hsz := size_bfsSet hn hC hI NP hgrp
  have hone : InC n C 1 := (h1 1).2 (Subgroup.one_mem _)
  have hmul : ∀ σ, InC n C σ → ∀ g ∈ NP, InC n C (σ * g) := fun σ hσ g hg' =>
    (h1 _).2 (Subgroup.mul_mem _ ((h1 σ).1 hσ) (Subgroup.subset_closure hg'))
  have hcN := closedH_of_grp NP c.depth (InC n C) hmem hone hmul
  have hEs : c.Es (gs.map RN.enc) = bfsSet (B.map RN.enc) 16 := by
    unfold ECert.Es
    rw [hBe]
  have hNs : c.Ns (gs.map RN.enc) = bfsSet (NP.map RN.enc) c.depth := by
    unfold ECert.Ns
    rw [hNe]
  obtain ⟨hOrb, hKO⟩ := orbN_sound hn gs hEF c.rT c.nOrd kOrd hO
  unfold ECert.coreCheckT
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, hKO⟩
  ·
    unfold ECert.eCheck
    simp only [hEs, hBe, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_map,
      forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    refine ⟨⟨⟨es_closed hEF, es_size hEF⟩, fun b hb => ?_⟩, fun b hb b' hb' => ?_⟩
    · rw [← RN.enc_mul, hEF.sq b hb, RN.enc_one]
    · rw [← RN.enc_mul, ← RN.enc_mul, hEF.comm b hb b' hb']
  ·
    unfold ECert.nCheck
    simp only [hEs, hNs, hBe, hNe, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_map,
      forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, List.any_eq_true]
    refine ⟨⟨hcN, hsz.trans hL⟩, fun g hg' b hb => ?_⟩
    obtain ⟨e', he', hge⟩ := normK_sound hn B NP hN g hg' b hb
    refine ⟨RN.enc e', Std.HashSet.mem_toList.2 ((es_mem hEF _).2 ⟨e', he', rfl⟩), ?_⟩
    rw [← RN.enc_mul, ← RN.enc_mul, hge]
  ·
    unfold ECert.orbitCheckT
    rw [hEs]
    exact decide_eq_true hOrb

end CFSG.KC.LQT.M24Snd

end
