module

public import CFSG.Certificates.Kernel.LocalQTM24Snd.Tr
public import CFSG.Certificates.Kernel.LocalQTM24Snd.TrHash
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3Invo
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3Cert

public section

namespace CFSG.KC.LQT.M24Snd

open Equiv CFSG.QuasithinUnique.A5.Kc3Cert CFSG.QuasithinUnique.Vol2Native.A312L.PermLat
  CFSG.KC.LQT.W CFSG.KC.LQT.M24

variable {n : ℕ}

private theorem aux_isets_mem_invsK (l : List ℕ) (c : ℕ) :
    c ∈ invsK n l ↔
      c ∈ l ∧ CFSG.KC.LQT.P.mul n c c = CFSG.KC.LQT.P.one n ∧ ¬ c = CFSG.KC.LQT.P.one n := by
  simp only [invsK, List.mem_filter, CFSG.KC.LQT.P.andB_iff, CFSG.KC.LQT.P.notB_iff,
    CFSG.KC.LQT.P.beq_iff]

private theorem aux_isets_eqL_iff : ∀ l m : List ℕ, CFSG.KC.LQT.Syl.eqL l m = true ↔ l = m
  | [], [] => by simp [CFSG.KC.LQT.Syl.eqL]
  | [], _ :: _ => by simp [CFSG.KC.LQT.Syl.eqL]
  | _ :: _, [] => by simp [CFSG.KC.LQT.Syl.eqL]
  | x :: l, y :: m => by
    change CFSG.KC.Ord.andB (Nat.beq x y) (CFSG.KC.LQT.Syl.eqL l m) = true ↔ _
    rw [CFSG.KC.LQT.P.andB_iff, CFSG.KC.LQT.P.beq_iff, aux_isets_eqL_iff l m, List.cons.injEq]

private theorem aux_isets_code_sq (hn : n ≤ 32) (σ : Perm (Fin n)) :
    (CFSG.KC.LQT.P.mul n (CFSG.KC.LQT.P.code σ) (CFSG.KC.LQT.P.code σ) = CFSG.KC.LQT.P.one n ∧
      ¬ CFSG.KC.LQT.P.code σ = CFSG.KC.LQT.P.one n) ↔ (σ * σ = 1 ∧ σ ≠ 1) := by
  simp only [CFSG.KC.LQT.P.code_mul hn, CFSG.KC.LQT.P.code_one, CFSG.KC.LQT.P.code_eq_iff hn,
    ne_eq]

private theorem aux_isets_enc_sq (σ : Perm (Fin n)) :
    RN.enc σ * RN.enc σ = 1 ↔ σ * σ = 1 := by
  rw [← RN.enc_mul, ← RN.enc_one, RN.enc_inj.eq_iff]

private theorem aux_isets_enc_ne (σ : Perm (Fin n)) :
    RN.enc σ ≠ 1 ↔ σ ≠ 1 := by
  rw [← RN.enc_one]
  exact RN.enc_inj.ne_iff

theorem iset_seeds (hn : n ≤ 32) (gs : List (Perm (Fin n))) (pW : List (List ℕ)) (d : ℕ)
    (S : List ℕ) (hpre : isetPre n (gs.map codeP) pW d S = true) :
    (∀ σ : Perm (Fin n), P.code σ ∈ S ↔
      (σ ∈ ball (fun σ => (pW.map (evalW gs)).map (σ * ·)) {1} d ∧ σ * σ = 1 ∧ σ ≠ 1)) ∧
    ∀ c ∈ S, ∃ σ : Perm (Fin n), P.code σ = c := by
  have hc : gs.map codeP = gs.map P.code := rfl
  have hw : List.map (CFSG.KC.LQT.W.evalWK n (gs.map codeP)) pW =
      (pW.map (evalW gs)).map P.code := by
    rw [hc, List.map_map]
    exact List.map_congr_left fun w _ => CFSG.KC.LQT.LK.evalWK_code hn gs w
  simp only [isetPre, hw, forceN_eq, bfsC_eq] at hpre
  have hS := (aux_isets_eqL_iff _ _).1 hpre
  obtain ⟨h1, h2⟩ := rounds_code_iff hn (pW.map (evalW gs)) d
  subst hS
  refine ⟨fun σ => ?_, fun c hc' => ?_⟩
  · rw [aux_isets_mem_invsK, h1 σ, aux_isets_code_sq hn σ]
  · rw [aux_isets_mem_invsK] at hc'
    exact h2 c hc'.1

theorem mem_invSeeds_iff (gs : List (Perm (Fin n))) (pW : List (List ℕ)) (d : ℕ) (x : RN n) :
    x ∈ invSeeds (bfsSet (pW.map (evalW (gs.map RN.enc))) d) ↔
      ∃ σ : Perm (Fin n), RN.enc σ = x ∧
        σ ∈ ball (fun σ => (pW.map (evalW gs)).map (σ * ·)) {1} d ∧ σ * σ = 1 ∧ σ ≠ 1 := by
  have e : pW.map (evalW (gs.map RN.enc)) = (pW.map (evalW gs)).map RN.enc := by
    rw [List.map_map]
    exact List.map_congr_left fun w _ => (enc_evalW (rawIsEnc n) gs w).symm
  obtain ⟨hmem, hex⟩ := bfsSet_enc_iff (pW.map (evalW gs)) d
  rw [e, invSeeds, List.mem_filter, Std.HashSet.mem_toList]
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq]
  constructor
  · rintro ⟨hx, hsq, hne⟩
    obtain ⟨σ, rfl⟩ := hex _ hx
    exact ⟨σ, rfl, (hmem σ).1 hx, (aux_isets_enc_sq σ).1 hsq, (aux_isets_enc_ne σ).1 hne⟩
  · rintro ⟨σ, rfl, hσ, h1, h2⟩
    exact ⟨(hmem σ).2 hσ, (aux_isets_enc_sq σ).2 h1, (aux_isets_enc_ne σ).2 h2⟩

end CFSG.KC.LQT.M24Snd

end
