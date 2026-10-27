module

public import CFSG.Certificates.Kernel.LocalQTCoreCSnd.Core
public import CFSG.Certificates.Kernel.LocalQTCoreCSnd.Hyp
import all CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListPermEnc

public section

namespace CFSG.KC.LQT.Syl.CoreSnd

open Equiv CFSG.KC.LQT CFSG.QuasithinUnique.A5.Kc3Cert
  CFSG.QuasithinUnique.Vol2Native.A312L.PermLat CFSG.KC.LQT.W CFSG.KC.LQT.L CFSG.KC.LQT.CM

theorem bfsSet_pred {n : ℕ} (G : List (Perm (Fin n))) (d : ℕ) (Q : Perm (Fin n) → Prop)
    (h1 : Q 1) (hmul : ∀ σ, Q σ → ∀ g ∈ G, Q (σ * g)) :
    ∀ r ∈ bfsSet (G.map RN.enc) d, ∃ σ, Q σ ∧ RN.enc σ = r := by
  have hP : ∀ y : RN n, (∃ x, Q x ∧ RN.enc x = y) →
      ∀ g ∈ G.map RN.enc, ∃ x, Q x ∧ RN.enc x = y * g := by
    rintro y ⟨x, hx, rfl⟩ g' hg'
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hg'
    exact ⟨x * g, hmul x hx g hg, RN.enc_mul x g⟩
  have hs1 : ∀ y ∈ ((∅ : Std.HashSet (RN n)).insert 1 : Std.HashSet (RN n)),
      ∃ x, Q x ∧ RN.enc x = y := by
    intro y hy
    rw [Std.HashSet.mem_insert] at hy
    rcases hy with hy | hy
    · have : (1 : RN n) = y := beq_iff_eq.mp hy
      exact ⟨1, h1, by rw [← this, RN.enc_one]⟩
    · have := Std.HashSet.contains_iff_mem.mpr hy
      simp [Std.HashSet.contains_empty] at this
  have hs2 : ∀ y ∈ [(1 : RN n)], ∃ x, Q x ∧ RN.enc x = y := by
    intro y hy
    rw [List.mem_singleton] at hy
    exact ⟨1, h1, by rw [hy, RN.enc_one]⟩
  exact bfsRun_sound (G.map RN.enc) _ hP d ((∅ : Std.HashSet (RN n)).insert 1, [1]) hs1 hs2

theorem mem_normalizer_of_gens {n : ℕ} {B : List (Perm (Fin n))} (h : EFacts B)
    {g : Perm (Fin n)} (hg : ∀ e ∈ B, ∃ e' ∈ lst B, g * e = e' * g) :
    g ∈ Subgroup.normalizer ((Subgroup.closure {b | b ∈ B} : Subgroup (Perm (Fin n))) :
      Set (Perm (Fin n))) := by
  have hle : Subgroup.closure {b | b ∈ B} ≤
      (Subgroup.closure {b | b ∈ B}).comap (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.closure_le]
    intro b hb
    obtain ⟨e', he', hge⟩ := hg b hb
    have : g * b * g⁻¹ = e' := by rw [hge]; group
    show (MulAut.conj g) b ∈ Subgroup.closure {b | b ∈ B}
    rw [MulAut.conj_apply, this]
    exact (mem_closure_iff_lst h e').2 he'
  exact mem_normalizer_of_conj_le fun x hx => hle hx

theorem hypAC_snd {n : ℕ} (gs : List (Perm (Fin n))) {G : List ℕ} (hG : gs.map codeP = G)
    (c : ECert) (C : List Lvl) (W : List (List (List ℕ)))
    (hE : eK n (c.eW.map (evalWK n G)) = true) (hC : chainOK n C = true)
    (hg : CFSG.KC.LQT.P.allL (c.nW.map (evalWK n G)) (inC n C (chainF C)) = true)
    (hw : wordsC n C (c.nW.map (evalWK n G)) W c.depth = true)
    (hcl : ∀ j < n, chainChunk n C (fun s => CFSG.KC.LQT.P.allL (c.nW.map (evalWK n G))
      fun g => inC n C (chainF C) (CFSG.KC.LQT.P.mul n s g)) j = true)
    (hN : normK n (c.eW.map (evalWK n G)) (c.nW.map (evalWK n G)) = true)
    (h1920 : c.nOrd % 1920 = 0)
    (hA : ∀ j < n, chainChunk n C (hypAx n (c.eW.map (evalWK n G))) j = true) :
    c.hypACheck (gs.map RN.enc) = true := by
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
  rw [hBc] at hE hN hA
  rw [hNc] at hg hcl hN
  obtain ⟨-, hEF⟩ := eK_facts B hE
  have hn0 : 0 < n := hEF.pos
  have hLvW := lvW_of_chainOK hn0 hC
  have hS1 : ∀ g ∈ NP, InC n C g := fun g hg' =>
    (inC_iff_w hn hLvW g).1 ((P.allL_map NP _).1 hg g hg')
  have hacc := allChain_of_chunks hn0 hcl
  have hS2 : ∀ σ, InC n C σ → ∀ g ∈ NP, InC n C (σ * g) := by
    intro σ hσ g hg'
    have := allChain_sound_w hn hLvW _ hacc σ hσ
    rw [P.allL_map] at this
    have := this g hg'
    rwa [P.code_mul hn, inC_iff_w hn hLvW] at this
  have hAall := allChain_of_chunks hn0 hA
  have hNorm := normK_sound hn B NP hN
  have hmemEg := mem_closure_iff_lst hEF
  have hQ := bfsSet_pred NP c.depth
    (fun σ => (σ = 1 ∨ InC n C σ) ∧ σ ∈ Subgroup.normalizer
      ((Subgroup.closure {b | b ∈ B} : Subgroup (Perm (Fin n))) : Set (Perm (Fin n))))
    ⟨Or.inl rfl, Subgroup.one_mem _⟩ (by
      rintro σ ⟨hσ, hnσ⟩ g hg'
      refine ⟨?_, Subgroup.mul_mem _ hnσ (mem_normalizer_of_gens hEF (hNorm g hg'))⟩
      rcases hσ with rfl | hσ
      · exact Or.inr (by rw [one_mul]; exact hS1 g hg')
      · exact Or.inr (hS2 σ hσ g hg'))
  have hEs : c.Es (gs.map RN.enc) = bfsSet (B.map RN.enc) 16 := by
    unfold ECert.Es
    rw [hBe]
  have hNs : c.Ns (gs.map RN.enc) = bfsSet (NP.map RN.enc) c.depth := by
    unfold ECert.Ns
    rw [hNe]
  have hfacts : ∀ σ : Perm (Fin n), ((σ = 1 ∨ InC n C σ) ∧ σ ∈ Subgroup.normalizer
      ((Subgroup.closure {b | b ∈ B} : Subgroup (Perm (Fin n))) : Set (Perm (Fin n)))) →
      (¬ ∃ u < 16, ¬ Cm B σ u ∧ ∀ y < 16, Cm B σ y ∨ Cm B σ (u ^^^ y)) ∧
        ((∀ u < 16, Cm B σ u) → σ ∈ lst B) := by
    rintro σ ⟨hσ, hnσ⟩
    have hgen : ∀ e ∈ B, ∃ e' ∈ lst B, σ * e = e' * σ := fun e he => by
      have := (Subgroup.mem_normalizer_iff.1 hnσ e).1 (Subgroup.subset_closure he)
      exact ⟨σ * e * σ⁻¹, (hmemEg _).1 this, by group⟩
    rcases hσ with rfl | hσ
    · refine ⟨?_, fun _ => one_mem_lst B⟩
      rintro ⟨u, -, hnu, -⟩
      exact hnu (by unfold Cm; rw [one_mul, mul_one])
    · have hx := allChain_sound_w hn hLvW _ hAall σ hσ
      exact hypAx_sound hn hEF σ hgen hx
  unfold ECert.hypACheck ECert.selfCentCheck
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Std.HashSet.mem_toList, hEs, hNs]
  refine ⟨⟨fun x hx => ?_, fun x hx => ?_⟩, h1920⟩
  · obtain ⟨σ, hσ, rfl⟩ := hQ x hx
    exact (selfCent_iff hEF σ).2 (hfacts σ hσ).2
  · obtain ⟨σ, hσ, rfl⟩ := hQ x hx
    have := (hfacts σ hσ).1
    rw [Bool.not_eq_true', Bool.eq_false_iff]
    intro hT
    exact this ((isTransvecB_iff hEF σ).1 hT)

end CFSG.KC.LQT.Syl.CoreSnd

end
