module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6gStd
public import CFSG.ClassicalInvolution.Q3.TL3T52
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6gNorm
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPfMembers

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6g

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr CFSG.ClassicalInvolution.Q3.TL4
open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6e
  (aeBar8 vq vq_mul vq_eq_iff conj_vq vq_mem_aeBar8 vq_compl vq_empty vq_mul_self zBar_eq_vq)
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf (memBar_le_e29)
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.A6h1
  (conjSub_ofPerm_memBar conjSub_ofPerm_ae6AE8 mkQ_ofPerm_inv natCard_conjSub)

theorem tl_mem_e29Sub (b : Fin 3 → ZMod 2) : tl b ∈ e29Sub :=
  mkQ_ofPerm_mem_aeBarOver (aperm_mem_agl32 1 b)
    (Equiv.Perm.mem_alternatingGroup.mpr (agl32_sign _ (aperm_mem_agl32 1 b)))

theorem E8_mem_e29Sub {f : Fin 8 → ZMod 2} (hf : EvF f) (b : Fin 3 → ZMod 2) : E8 f b ∈ e29Sub :=
  e29Sub.mul_mem (vbar_mem_aeBarOver hf) (tl_mem_e29Sub b)

theorem AT_le_e29Sub : AT ≤ e29Sub := by
  intro x hx
  obtain ⟨f, b, hf, rfl⟩ := mem_AT.mp hx
  exact E8_mem_e29Sub hf.even b

theorem AD_le_e29Sub : AD ≤ e29Sub := by
  intro x hx
  obtain ⟨f, b, hf, rfl⟩ := mem_AD.mp hx
  have h : EvF f := by
    have h1 := hf.even.add (dd_even b)
    rwa [pi_add_cancel] at h1
  exact E8_mem_e29Sub h b

theorem vq_α₀_mem_E3p : vq α₀ ∈ E3p := by
  rw [← zBar_eq_vq α₀ card_α₀]
  exact zBar_mem_E3p (by decide) card_α₀

theorem vq_β₀_mem_E3p : vq β₀ ∈ E3p := by
  rw [← zBar_eq_vq β₀ card_β₀]
  exact zBar_mem_E3p (by decide) card_β₀

@[expose] noncomputable def memSpan (X : Subgroup (AEQ 8)) : Subgroup (AEQ 8) :=
  ⨆ (δ : Finset (Fin 8)) (h : δ.card = 4) (c : Bool) (_ : memBar δ h c ≤ X), memBar δ h c

theorem memBar_le_memSpan {X : Subgroup (AEQ 8)} {δ : Finset (Fin 8)} {h : δ.card = 4} {c : Bool}
    (hc : memBar δ h c ≤ X) : memBar δ h c ≤ memSpan X :=
  le_iSup_of_le δ (le_iSup_of_le h (le_iSup_of_le c (le_iSup_of_le hc le_rfl)))

theorem memSpan_le (X : Subgroup (AEQ 8)) : memSpan X ≤ X :=
  iSup_le fun _ => iSup_le fun _ => iSup_le fun _ => iSup_le fun hc => hc

theorem conjSub_memSpan_le (w : Wr 8) (X : Subgroup (AEQ 8)) :
    conjSub (mkQ 8 w) (memSpan X) ≤ memSpan (conjSub (mkQ 8 w) X) := by
  refine Subgroup.map_le_iff_le_comap.mpr
    (iSup_le fun δ => iSup_le fun h => iSup_le fun c => iSup_le fun hc => ?_)
  refine Subgroup.map_le_iff_le_comap.mp ?_
  show conjSub (mkQ 8 w) (memBar δ h c) ≤ memSpan (conjSub (mkQ 8 w) X)
  obtain ⟨c', hc'⟩ := exists_conj_memBar_map w δ h c
  have h1 : conjSub (mkQ 8 w) (memBar δ h c) ≤ conjSub (mkQ 8 w) X := conjSub_mono hc
  rw [hc'] at h1 ⊢
  exact memBar_le_memSpan h1

theorem e29Sub_gen : e29Sub ≤ memSpan e29Sub := by
  set G₀ := memSpan e29Sub with hG₀
  have hle : G₀ ≤ e29Sub := memSpan_le _
  have hnorm : ∀ x ∈ e29Sub, ∀ y ∈ G₀, x * y * x⁻¹ ∈ G₀ := by
    intro x hx y hy
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective x
    have hx' : mkQ 8 w ∈ e29Sub := hx
    have h1 := conjSub_memSpan_le w e29Sub
    rw [conjSub_eq_self_of_mem hx'] at h1
    exact h1 (conj_mem_conjSub hy)
  rcases e29_normal G₀ hle hnorm with h2 | heq
  · exfalso
    have hN : G₀ ≤ nBar := le_nBar_of_normal hle hnorm h2
    have hmem : memBar α₀ card_α₀ true ≤ G₀ :=
      memBar_le_memSpan (memBar_le_e29 α₀ (six_planes α₀ (by simp [six])) card_α₀ true)
    have hsub : ((memBar α₀ card_α₀ true : Subgroup (AEQ 8)) : Set (AEQ 8)) ⊆
        {1, zBar α₀ card_α₀} := fun g hg => by
      have := memBar_inf_nBar hg (hN (hmem hg)).2
      simpa using this
    have hc1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    have hc2 : ({1, zBar α₀ card_α₀} : Set (AEQ 8)).ncard ≤ 2 := by
      refine (Set.ncard_insert_le _ _).trans ?_
      rw [Set.ncard_singleton]
    have hc3 : Nat.card (memBar α₀ card_α₀ true) = 8 := natCard_memBar (by norm_num) _ _ _
    rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq] at hc3
    omega
  · exact heq.ge

structure GoodPair (X E : Subgroup (AEQ 8)) (y : AEQ 8) : Prop where
  X_le : X ≤ aeBar8
  card_X : Nat.card X = 86016
  six_le : ∀ δ ∈ six, ∀ h : δ.card = 4, ∀ c, memBar δ h c ≤ X
  gen : X ≤ memSpan X
  E_le : E ≤ X
  E_norm : ∀ g ∈ X, ∀ a ∈ E, g * a * g⁻¹ ∈ E
  E_sq : ∀ a ∈ E, a * a = 1
  card_E : Nat.card E = 64
  y_mem : y ∈ E
  α_mem : vq α₀ ∈ E
  β_mem : vq β₀ ∈ E
  norm_le : ∀ g ∈ aeBar8, (∀ a, a ∈ E ↔ g * a * g⁻¹ ∈ E) → g ∈ X
  far : ∃ g ∈ X, g * vq α₀ * g⁻¹ ∉ ({1, vq α₀, vq β₀, vq α₀ * vq β₀} : Set (AEQ 8))

@[expose] def farPerm : Equiv.Perm (Fin 8) := Equiv.swap 1 4 * Equiv.swap 3 6

theorem farPerm_mem : farPerm ∈ agl32 := mem_agl32_of_dec (by unfold farPerm; decide +kernel)

theorem vq_ne_of {T S : Finset (Fin 8)} (h1 : S ≠ T) (h2 : S ≠ Tᶜ) : vq T ≠ vq S := fun h =>
  (vq_eq_iff.mp h).elim h1 h2

theorem far_e29 : ∃ g ∈ e29Sub, g * vq α₀ * g⁻¹ ∉
    ({1, vq α₀, vq β₀, vq α₀ * vq β₀} : Set (AEQ 8)) := by
  refine ⟨mkQ 8 (ofPerm farPerm), mkQ_ofPerm_mem_aeBarOver farPerm_mem
    (Equiv.Perm.mem_alternatingGroup.mpr (agl32_sign _ farPerm_mem)), ?_⟩
  rw [conj_vq, show permQ 8 (mkQ 8 (ofPerm farPerm)) = farPerm from rfl, vq_α₀_mul_β₀]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← vq_empty]
    exact vq_ne_of (by decide +kernel) (by decide +kernel)
  · exact vq_ne_of (by decide +kernel) (by decide +kernel)
  · exact vq_ne_of (by decide +kernel) (by decide +kernel)
  · exact vq_ne_of (by decide +kernel) (by decide +kernel)

theorem goodPair_e29 {E : Subgroup (AEQ 8)} (hEle : E ≤ e29Sub)
    (hEn : ∀ g ∈ e29Sub, ∀ a ∈ E, g * a * g⁻¹ ∈ E) (hsq : ∀ a ∈ E, a * a = 1)
    (hcard : Nat.card E = 64) {y : AEQ 8} (hy : y ∈ E) (hα : vq α₀ ∈ E) (hβ : vq β₀ ∈ E)
    (hnorm : ∀ g ∈ aeBar8, (∀ a, a ∈ E ↔ g * a * g⁻¹ ∈ E) → g ∈ e29Sub) :
    GoodPair e29Sub E y where
  X_le := e29Sub_le_aeBar8
  card_X := card_e29Sub
  six_le := fun δ hδ h c => memBar_le_e29 δ (six_planes δ hδ) h c
  gen := e29Sub_gen
  E_le := hEle
  E_norm := hEn
  E_sq := hsq
  card_E := hcard
  y_mem := hy
  α_mem := hα
  β_mem := hβ
  norm_le := hnorm
  far := far_e29

theorem goodPair_X2 {y : AEQ 8} (hy : y ∈ aeBar8) (hp : permQ 8 y = σ₀) (hsq : y * y = 1) :
    ∃ E, GoodPair e29Sub E y := by
  rcases x_class hy hp hsq with h | h
  · exact ⟨AT, goodPair_e29 AT_le_e29Sub (fun g hg a ha => normal_AT hg a ha) AT_sq card_AT h
      (E3p_le_AT vq_α₀_mem_E3p) (E3p_le_AT vq_β₀_mem_E3p) fun g hg hn => normalizer_AT_le hg hn⟩
  · exact ⟨AD, goodPair_e29 AD_le_e29Sub (fun g hg a ha => normal_AD hg a ha) AD_sq card_AD h
      (E3p_le_AD vq_α₀_mem_E3p) (E3p_le_AD vq_β₀_mem_E3p) fun g hg hn => normalizer_AD_le hg hn⟩

theorem sQ_vq_α₀ : sQ⁻¹ * vq α₀ * sQ = vq α₀ := by
  have h := sQ_conj_vq_α₀
  rw [sQ_inv] at h ⊢
  exact h

theorem sQ_vq_β₀ : sQ⁻¹ * vq β₀ * sQ = vq β₀ := by
  have h := sQ_conj_vq_β₀
  rw [sQ_inv] at h ⊢
  exact h

theorem sQ_vq_αβ : sQ⁻¹ * (vq α₀ * vq β₀) * sQ = vq α₀ * vq β₀ := by
  calc sQ⁻¹ * (vq α₀ * vq β₀) * sQ = (sQ⁻¹ * vq α₀ * sQ) * (sQ⁻¹ * vq β₀ * sQ) := by group
    _ = vq α₀ * vq β₀ := by rw [sQ_vq_α₀, sQ_vq_β₀]

theorem GoodPair.conj_sQ {X E : Subgroup (AEQ 8)} {y : AEQ 8} (hG : GoodPair X E y) :
    GoodPair (conjSub sQ X) (conjSub sQ E) (sQ * y * sQ⁻¹) where
  X_le := by
    rw [← conjSub_sQ_aeBar8]
    exact conjSub_mono hG.X_le
  card_X := by rw [natCard_conjSub, hG.card_X]
  six_le := by
    intro δ hδ h c
    obtain ⟨c', hc'⟩ := conjSub_ofPerm_memBar sw⁻¹ h c
    have e : mkQ 8 (ofPerm sw⁻¹) = sQ⁻¹ := (mkQ_ofPerm_inv sw).symm
    rw [e] at hc'
    have hmap : δ.map sw⁻¹.toEmbedding = δ := by rw [sw_inv]; exact sw_map_six δ hδ
    have key : ∀ (δ' : Finset (Fin 8)) (hδ' : δ' = δ) (h' : δ'.card = 4),
        memBar δ' h' c' ≤ X := by
      intro δ' hδ' h'
      subst hδ'
      exact hG.six_le δ' hδ h' c'
    have h1 : conjSub sQ⁻¹ (memBar δ h c) ≤ X := by
      rw [hc']
      exact key _ hmap _
    calc memBar δ h c = conjSub sQ (conjSub sQ⁻¹ (memBar δ h c)) := (conjSub_conjSub_inv _ _).symm
      _ ≤ conjSub sQ X := conjSub_mono h1
  gen := (conjSub_mono hG.gen).trans (conjSub_memSpan_le (ofPerm sw) X)
  E_le := conjSub_mono hG.E_le
  E_norm := by
    intro g hg a ha
    have hg' : sQ⁻¹ * g * sQ ∈ X := mem_conjSub_iff.mp hg
    have ha' : sQ⁻¹ * a * sQ ∈ E := mem_conjSub_iff.mp ha
    have h1 := hG.E_norm _ hg' _ ha'
    rw [mem_conjSub_iff]
    convert h1 using 1
    group
  E_sq := by
    intro a ha
    have ha' : sQ⁻¹ * a * sQ ∈ E := mem_conjSub_iff.mp ha
    have h1 := hG.E_sq _ ha'
    calc a * a = sQ * ((sQ⁻¹ * a * sQ) * (sQ⁻¹ * a * sQ)) * sQ⁻¹ := by group
      _ = 1 := by rw [h1]; group
  card_E := by rw [natCard_conjSub, hG.card_E]
  y_mem := conj_mem_conjSub hG.y_mem
  α_mem := by
    rw [mem_conjSub_iff, sQ_vq_α₀]
    exact hG.α_mem
  β_mem := by
    rw [mem_conjSub_iff, sQ_vq_β₀]
    exact hG.β_mem
  norm_le := by
    intro g hg hn
    have hg₀ : sQ⁻¹ * g * sQ ∈ aeBar8 := by
      have h1 := conj_mem_conjSub (n := sQ) hg
      rw [conjSub_sQ_aeBar8] at h1
      rw [sQ_inv] at h1 ⊢
      exact h1
    have h2 := hG.norm_le _ hg₀ (fun a => by
      have e1 : sQ⁻¹ * (sQ * a * sQ⁻¹) * sQ = a := by group
      have e2 : sQ⁻¹ * (g * (sQ * a * sQ⁻¹) * g⁻¹) * sQ =
          (sQ⁻¹ * g * sQ) * a * (sQ⁻¹ * g * sQ)⁻¹ := by group
      have h3 := hn (sQ * a * sQ⁻¹)
      rw [mem_conjSub_iff, mem_conjSub_iff, e1, e2] at h3
      exact h3)
    exact mem_conjSub_iff.mpr h2
  far := by
    obtain ⟨g, hg, hfar⟩ := hG.far
    refine ⟨sQ * g * sQ⁻¹, conj_mem_conjSub hg, fun hmem => hfar ?_⟩
    have e : sQ * g * sQ⁻¹ * vq α₀ * (sQ * g * sQ⁻¹)⁻¹ = sQ * (g * vq α₀ * g⁻¹) * sQ⁻¹ := by
      calc _ = sQ * g * (sQ⁻¹ * vq α₀ * sQ) * g⁻¹ * sQ⁻¹ := by group
        _ = sQ * g * vq α₀ * g⁻¹ * sQ⁻¹ := by rw [sQ_vq_α₀]
        _ = _ := by group
    rw [e] at hmem
    set w := g * vq α₀ * g⁻¹ with hw
    have hw' : w = sQ⁻¹ * (sQ * w * sQ⁻¹) * sQ := by group
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem ⊢
    rcases hmem with h | h | h | h
    · left; rw [hw', h]; group
    · right; left; rw [hw', h, sQ_vq_α₀]
    · right; right; left; rw [hw', h, sQ_vq_β₀]
    · right; right; right; rw [hw', h, sQ_vq_αβ]

theorem goodPair_X3 {y : AEQ 8} (hy : y ∈ aeBar8) (hp : permQ 8 y = σ₀) (hsq : y * y = 1) :
    ∃ E, GoodPair X3 E y := by
  have hy₀ : sQ⁻¹ * y * sQ ∈ aeBar8 := by
    have h1 := conj_mem_conjSub (n := sQ) hy
    rw [conjSub_sQ_aeBar8] at h1
    rw [sQ_inv] at h1 ⊢
    exact h1
  have hp₀ : permQ 8 (sQ⁻¹ * y * sQ) = σ₀ := by
    rw [map_mul, map_mul, map_inv, hp, permQ_sQ]
    have h := sw_comm_σ₀
    rw [sw_inv] at h ⊢
    exact h
  have hsq₀ : (sQ⁻¹ * y * sQ) * (sQ⁻¹ * y * sQ) = 1 := by
    calc (sQ⁻¹ * y * sQ) * (sQ⁻¹ * y * sQ) = sQ⁻¹ * (y * y) * sQ := by group
      _ = 1 := by rw [hsq]; group
  obtain ⟨E, hE⟩ := goodPair_X2 hy₀ hp₀ hsq₀
  refine ⟨conjSub sQ E, ?_⟩
  have h := hE.conj_sQ
  have e : sQ * (sQ⁻¹ * y * sQ) * sQ⁻¹ = y := by group
  rw [e] at h
  exact h

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6g
