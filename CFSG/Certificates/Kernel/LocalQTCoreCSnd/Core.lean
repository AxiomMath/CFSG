module

public import CFSG.Certificates.Kernel.LocalQTCoreCSnd.Orb
public import CFSG.Certificates.Kernel.LocalQTChainWSound

public section

namespace CFSG.KC.LQT.Syl.CoreSnd

open Equiv CFSG.KC.LQT CFSG.QuasithinUnique.A5.Kc3Cert
  CFSG.QuasithinUnique.Vol2Native.A312L.PermLat CFSG.KC.LQT.W CFSG.KC.LQT.L CFSG.KC.LQT.CM

theorem EFacts.pos {n : ℕ} {B : List (Perm (Fin n))} (h : EFacts B) : 0 < n := by
  by_contra h0
  have hn : n = 0 := by omega
  subst hn
  have := h.nodup.length_le_card
  rw [lst_length, Fintype.card_perm, Fintype.card_fin, Nat.factorial_zero] at this
  omega

theorem grpC_of_chunks {n : ℕ} (hn0 : 0 < n) {C : List Lvl} {F : ℕ} {G : List ℕ}
    {W : List (List (List ℕ))} {d : ℕ} (hg : P.allL G (inC n C F) = true)
    (hw : wordsC n C G W d = true)
    (hc : ∀ j < n, chainChunk n C
      (fun s => P.allL G fun g => inC n C F (P.mul n s g)) j = true) :
    grpC n C F G W d = true := by
  unfold grpC
  rw [P.andB_iff, P.andB_iff]
  exact ⟨hg, hw, allChain_of_chunks hn0 hc⟩

theorem coreC_snd {n : ℕ} (gs : List (Perm (Fin n))) {G : List ℕ} (hG : gs.map codeP = G)
    (c : ECert) (kOrd : ℕ) (C : List Lvl) (W : List (List (List ℕ)))
    (hE : eK n (c.eW.map (evalWK n G)) = true) (hC : chainOK n C = true)
    (hI : CFSG.KC.LQT.L.chainInj n C = true)
    (hg : CFSG.KC.LQT.P.allL (c.nW.map (evalWK n G)) (inC n C (chainF C)) = true)
    (hw : wordsC n C (c.nW.map (evalWK n G)) W c.depth = true)
    (hcl : ∀ j < n, chainChunk n C (fun s => CFSG.KC.LQT.P.allL (c.nW.map (evalWK n G))
      fun g => inC n C (chainF C) (CFSG.KC.LQT.P.mul n s g)) j = true)
    (hL : chainF C = c.nOrd)
    (hN : normK n (c.eW.map (evalWK n G)) (c.nW.map (evalWK n G)) = true)
    (hO : orbK n G (c.eW.map (evalWK n G)) c.rT c.nOrd kOrd = true) :
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
  rw [hNc] at hg hw hcl hN
  obtain ⟨-, hEF⟩ := eK_facts B hE
  have hn0 : 0 < n := hEF.pos
  have hgrp : grpC n C (chainF C) (NP.map P.code) W c.depth = true :=
    grpC_of_chunks hn0 hg hw hcl
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
  obtain ⟨hOrb, hKO⟩ := orbK_sound hn gs hEF c.rT c.nOrd kOrd hO
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

end CFSG.KC.LQT.Syl.CoreSnd

end
