module

public import CFSG.Certificates.Kernel.LocalQTM24Snd.SortSorted
public import CFSG.Certificates.Kernel.LocalQTM24Snd.DiffDedup
public import CFSG.Certificates.Kernel.LocalQTM24Snd.Tr
public import CFSG.Certificates.Kernel.LocalQTM24Snd.TrHash
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3Invo
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3Cert

public section

namespace CFSG.KC.LQT.M24Snd

open Equiv CFSG.QuasithinUnique.A5.Kc3Cert CFSG.QuasithinUnique.Vol2Native.A312L.PermLat
  CFSG.KC.LQT.W CFSG.KC.LQT.M24 CFSG.KC.LQT.T2 CFSG.KC.LQT.Syl

private theorem aux_sub_length_rounds (f : ℕ → List ℕ) (r : ℕ) :
    ∀ S F : List ℕ, S.length ≤ (rounds f r S F).1.length := by
  induction r with
  | zero => intro S F; exact Nat.le_refl _
  | succ r ih =>
    intro S F
    rw [rounds_succ]
    refine le_trans ?_ (ih _ _)
    rw [(mergeK_permT S (newK f S F)).length_eq, List.length_append]
    omega

private theorem aux_sub_strict_of_le_nodup {l : List ℕ} (h : l.Pairwise (· ≤ ·)) (hn : l.Nodup) :
    l.Pairwise (· < ·) :=
  (h.and hn).imp fun {_ _} ⟨h1, h2⟩ => lt_of_le_of_ne h1 h2

theorem rounds_sorted (PG : List ℕ) (n : ℕ) (r : ℕ) :
    ∀ (S F : List ℕ), S.Pairwise (· < ·) → F.length ≤ S.length →
      (rounds (fun x => PG.map (CFSG.KC.LQT.P.mul n x)) r S F).1.length * PG.length ≤ 131072 →
      (rounds (fun x => PG.map (CFSG.KC.LQT.P.mul n x)) r S F).1.Pairwise (· < ·) := by
  induction r with
  | zero => intro S F hS _ _; exact hS
  | succ r ih =>
    intro S F hS hF hB
    rw [rounds_succ] at hB ⊢
    set f : ℕ → List ℕ := fun x => PG.map (CFSG.KC.LQT.P.mul n x) with hf
    set l : List ℕ := List.flatten (List.map f F) with hl
    have hlen : l.length = F.length * PG.length := by
      simp [hl, hf, List.length_flatten, List.map_map, Function.comp_def]
    have h1 := aux_sub_length_rounds f r (mergeK S (newK f S F)) (newK f S F)
    have h2 : S.length ≤ (mergeK S (newK f S F)).length := by
      rw [(mergeK_permT S (newK f S F)).length_eq, List.length_append]
      omega
    have hle : l.length ≤ 131072 := by
      calc l.length = F.length * PG.length := hlen
        _ ≤ S.length * PG.length := Nat.mul_le_mul_right _ hF
        _ ≤ (rounds f r (mergeK S (newK f S F)) (newK f S F)).1.length * PG.length :=
          Nat.mul_le_mul_right _ (h2.trans h1)
        _ ≤ 131072 := hB
    have hxs := dedupS_strict (sortN_sorted l hle)
    have hNw : newK f S F = (dedupS (sortN l)).filter (fun x => decide (x ∉ S)) := by
      unfold newK
      exact diffS_eq_filter hxs hS
    have hNws : (newK f S F).Pairwise (· < ·) := by
      rw [hNw]
      exact hxs.filter _
    have hdisj : ∀ x ∈ newK f S F, x ∉ S := by
      intro x hx
      rw [hNw] at hx
      simpa using (List.mem_filter.1 hx).2
    have hnd : (S ++ newK f S F).Nodup := by
      refine List.nodup_append.2 ⟨hS.imp fun {a b} h => ne_of_lt h,
        hNws.imp fun {a b} h => ne_of_lt h, ?_⟩
      intro a ha b hb heq
      exact hdisj b hb (heq ▸ ha)
    have hmerge : (mergeK S (newK f S F)).Pairwise (· < ·) :=
      aux_sub_strict_of_le_nodup
        (mergeK_sorted (hS.imp fun {a b} h => le_of_lt h) (hNws.imp fun {a b} h => le_of_lt h))
        ((mergeK_permT S (newK f S F)).nodup_iff.2 hnd)
    refine ih _ _ hmerge ?_ hB
    rw [(mergeK_permT S (newK f S F)).length_eq, List.length_append]
    omega

theorem list_length_eq_card {α β : Type} [DecidableEq β] (B : Finset α) (φ : α → β)
    (hφ : Function.Injective φ) (l : List β) (hnd : l.Nodup)
    (h : ∀ y, y ∈ l ↔ ∃ a ∈ B, φ a = y) : l.length = B.card := by
  rw [← List.toFinset_card_of_nodup hnd, ← Finset.card_image_of_injective B hφ]
  congr 1
  ext y
  rw [List.mem_toFinset, Finset.mem_image, h]

theorem sub_snd {n : ℕ} (hn : n ≤ 32) (gs : List (Perm (Fin n))) (pW : List (List ℕ))
    (d size : ℕ) (h : subK n (gs.map codeP) pW d size = true)
    (hb : size * pW.length ≤ 131072) :
    subgroupCheck (gs.map RN.enc) pW d size = true := by
  classical
  have hcP : (codeP : Perm (Fin n) → ℕ) = CFSG.KC.LQT.P.code := rfl
  set L : List (Perm (Fin n)) := pW.map (evalW gs) with hL
  have hw : List.map (evalWK n (gs.map codeP)) pW = L.map CFSG.KC.LQT.P.code := by
    rw [hcP, hL, List.map_map]
    exact List.map_congr_left fun w _ => CFSG.KC.LQT.LK.evalWK_code hn gs w
  have he : pW.map (evalW (gs.map RN.enc)) = L.map RN.enc := by
    rw [hL, List.map_map]
    exact List.map_congr_left fun w _ => (enc_evalW (rawIsEnc n) gs w).symm
  unfold subK at h
  simp only [hw, forceN_eq, bfsC_eq] at h
  obtain ⟨hcl, hlen⟩ := CFSG.KC.LQT.P.andB_iff.1 h
  set S : List ℕ := (rounds (fun x => (L.map CFSG.KC.LQT.P.code).map (CFSG.KC.LQT.P.mul n x)) d
    [CFSG.KC.LQT.P.one n] [CFSG.KC.LQT.P.one n]).1 with hSdef
  have hlen' : S.length = size := by
    have := CFSG.KC.LQT.P.beq_iff.1 hlen
    rwa [CFSG.KC.LQT.S.lenL_eq] at this
  have hsorted : S.Pairwise (· < ·) := by
    refine rounds_sorted (L.map CFSG.KC.LQT.P.code) n d _ _ (List.pairwise_singleton _ _)
      (Nat.le_refl _) ?_
    rw [← hSdef, hlen', List.length_map, hL, List.length_map]
    exact hb
  have hndS : S.Nodup := hsorted.imp fun {a b} h => ne_of_lt h
  have hS := rounds_code_iff hn L d
  have hH := bfsSet_enc_iff L d
  have hclo := closedK_spec n (L.map CFSG.KC.LQT.P.code) S hcl
  have hclosedH : closedH (L.map RN.enc) (bfsSet (L.map RN.enc) d) = true := by
    refine CFSG.KC.LQT.CM.closedH_of_grp L d
      (fun σ => σ ∈ ball (fun σ => L.map (σ * ·)) {1} d) (fun r => ?_)
      (mem_ball_zero rfl |> fun h => ball_mono (Nat.zero_le d) h) (fun σ hσ g hg => ?_)
    · constructor
      · intro hr
        obtain ⟨σ, rfl⟩ := hH.2 r hr
        exact ⟨σ, (hH.1 σ).1 hr, rfl⟩
      · rintro ⟨σ, hσ, rfl⟩
        exact (hH.1 σ).2 hσ
    · have h1 : CFSG.KC.LQT.P.code σ ∈ S := (hS.1 σ).2 hσ
      have h2 := hclo _ h1 (CFSG.KC.LQT.P.code g) (List.mem_map_of_mem hg)
      rw [CFSG.KC.LQT.P.code_mul hn] at h2
      exact (hS.1 (σ * g)).1 h2
  obtain ⟨B, hB⟩ : ∃ B : Finset (Perm (Fin n)),
      ∀ σ, σ ∈ B ↔ σ ∈ ball (fun σ => L.map (σ * ·)) {1} d :=
    ⟨Finset.univ.filter fun σ => σ ∈ ball (fun σ => L.map (σ * ·)) {1} d, by simp⟩
  have hScard : S.length = B.card :=
    list_length_eq_card B CFSG.KC.LQT.P.code (fun a b hab => CFSG.KC.LQT.P.code_inj hn hab) S
      hndS fun c => by
        constructor
        · intro hc
          obtain ⟨σ, rfl⟩ := hS.2 c hc
          exact ⟨σ, (hB σ).2 ((hS.1 σ).1 hc), rfl⟩
        · rintro ⟨σ, hσ, rfl⟩
          exact (hS.1 σ).2 ((hB σ).1 hσ)
  have hHcard : (bfsSet (L.map RN.enc) d).size = B.card := by
    rw [← Std.HashSet.length_toList]
    refine list_length_eq_card B RN.enc RN.enc_inj _ (CFSG.KC.LQT.L.toList_nodup _) fun x => ?_
    rw [Std.HashSet.mem_toList]
    constructor
    · intro hx
      obtain ⟨σ, rfl⟩ := hH.2 x hx
      exact ⟨σ, (hB σ).2 ((hH.1 σ).1 hx), rfl⟩
    · rintro ⟨σ, hσ, rfl⟩
      exact (hH.1 σ).2 ((hB σ).1 hσ)
  unfold subgroupCheck
  rw [he, Bool.and_eq_true, beq_iff_eq]
  exact ⟨hclosedH, hHcard.trans (hScard.symm.trans hlen')⟩

end CFSG.KC.LQT.M24Snd

end
