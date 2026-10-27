module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylNormE

public noncomputable section

namespace CFSG.EvenSmallLie.OmegaEight.Weyl

open Subgroup CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.RankThree.Native

theorem closure_frameGens_le_realized : closure frameGens ≤ frameRealizedW := by
  rw [closure_le]
  rintro τ (rfl | rfl)
  · exact frameSinger_mem_realized
  · exact frameFlip_mem_realized

theorem frameAut_realized {σ : Equiv.Perm (Fin 8)} (hσ : σ ∈ frameAut) :
    ∃ w ∈ wPlus, ∀ v, w * frameElt v * w⁻¹ = frameElt (permVec σ v) := by
  have h : σ ∈ frameAutSub := hσ
  rw [frameAutSub_eq] at h
  exact closure_frameGens_le_realized h

theorem perm_eq_of_frameElt {σ τ : Equiv.Perm (Fin 8)}
    (h : ∀ v, frameElt (permVec σ v) = frameElt (permVec τ v)) : σ = τ := by
  ext i
  have h1 := frameElt_injective (h (frameE i))
  rw [permVec_frameE, permVec_frameE] at h1
  exact congrArg Fin.val (frameE_injective h1)

theorem e1Sub_comm {e f : Equiv.Perm (Fin 240)} (he : e ∈ e1Sub) (hf : f ∈ e1Sub) :
    e * f = f * e := by
  obtain ⟨v, rfl⟩ := mem_e1Sub.1 he
  obtain ⟨u, rfl⟩ := mem_e1Sub.1 hf
  exact frameElt_comm v u

theorem mem_normalizer_e1Sub_of_action {w : Equiv.Perm (Fin 240)} {σ : Equiv.Perm (Fin 8)}
    (h : ∀ v, w * frameElt v * w⁻¹ = frameElt (permVec σ v)) :
    w ∈ normalizer (e1Sub : Set (Equiv.Perm (Fin 240))) := by
  rw [mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    obtain ⟨v, rfl⟩ := mem_e1Sub.1 hg
    rw [h v]
    exact mem_e1Sub.2 ⟨_, rfl⟩
  · intro hg
    obtain ⟨u, hu⟩ := mem_e1Sub.1 hg
    have h1 := h (permVec σ⁻¹ u)
    rw [permVec_permVec_inv, hu] at h1
    have h2 : g = frameElt (permVec σ⁻¹ u) := mul_left_cancel (mul_right_cancel h1.symm)
    rw [h2]
    exact mem_e1Sub.2 ⟨_, rfl⟩

@[expose] def frameReal (σ : frameAutSub) : Equiv.Perm (Fin 240) :=
  Classical.choose (frameAut_realized σ.2)

theorem frameReal_mem (σ : frameAutSub) : frameReal σ ∈ wPlus :=
  (Classical.choose_spec (frameAut_realized σ.2)).1

theorem frameReal_conj (σ : frameAutSub) (v : FrameVec) :
    frameReal σ * frameElt v * (frameReal σ)⁻¹ = frameElt (permVec σ v) :=
  (Classical.choose_spec (frameAut_realized σ.2)).2 v

theorem conj_mem_e1Sub_of_e1PlusSub {w : Equiv.Perm (Fin 240)} (hw : w ∈ wE8)
    (hn : w ∈ normalizer (e1PlusSub : Set (Equiv.Perm (Fin 240)))) {g : Equiv.Perm (Fin 240)}
    (hg : g ∈ e1Sub) : w * g * w⁻¹ ∈ e1Sub := by
  refine centralizer_e1PlusSub (mul_mem (mul_mem hw (e1Sub_le_wE8 hg)) (inv_mem hw))
    fun e he => ?_
  have he' : w⁻¹ * e * w⁻¹⁻¹ ∈ e1PlusSub := (mem_normalizer_iff.1 (inv_mem hn) e).1 he
  rw [inv_inv] at he'
  have hc := e1Sub_comm hg ((e1PlusSub_eq ▸ he' : _ ∈ e1Sub ⊓ wPlus).1)
  calc w * g * w⁻¹ * e = w * (g * (w⁻¹ * e * w)) * w⁻¹ := by group
    _ = w * ((w⁻¹ * e * w) * g) * w⁻¹ := by rw [hc]
    _ = e * (w * g * w⁻¹) := by group

theorem normalizer_e1PlusSub_iff {w : Equiv.Perm (Fin 240)} (hw : w ∈ wE8) :
    w ∈ normalizer (e1PlusSub : Set (Equiv.Perm (Fin 240))) ↔
      w ∈ normalizer (e1Sub : Set (Equiv.Perm (Fin 240))) := by
  constructor
  · intro hn
    rw [mem_normalizer_iff]
    intro g
    refine ⟨conj_mem_e1Sub_of_e1PlusSub hw hn, fun hg => ?_⟩
    have h := conj_mem_e1Sub_of_e1PlusSub (inv_mem hw) (inv_mem hn) hg
    rwa [inv_inv, show w⁻¹ * (w * g * w⁻¹) * w = g by group] at h
  · intro hn
    rw [mem_normalizer_iff]
    intro g
    rw [e1PlusSub_eq, mem_inf, mem_inf, mem_normalizer_iff.1 hn g, mem_wPlus_iff, mem_wPlus_iff]
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, mul_mem (mul_mem hw h2) (inv_mem hw), ?_⟩
      rw [map_mul, map_mul, map_inv, h3, mul_one, mul_inv_cancel]
    · rintro ⟨h1, h2, h3⟩
      have h2' : g ∈ wE8 := by
        have := mul_mem (mul_mem (inv_mem hw) h2) hw
        rwa [show w⁻¹ * (w * g * w⁻¹) * w = g by group] at this
      refine ⟨h1, h2', ?_⟩
      rw [map_mul, map_mul, map_inv, mul_comm, ← mul_assoc, inv_mul_cancel, one_mul] at h3
      exact h3

theorem card_e1Sub : Nat.card e1Sub = 2 ^ 8 := by
  have e : FrameVec ≃ e1Sub :=
    Equiv.ofBijective (fun v => ⟨frameElt v, mem_e1Sub.2 ⟨v, rfl⟩⟩)
      ⟨fun v w h => frameElt_injective (congrArg Subtype.val h), fun g => by
        obtain ⟨v, h⟩ := mem_e1Sub.1 g.2
        exact ⟨v, Subtype.ext h⟩⟩
  rw [← Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card,
    Fintype.card_fin]

theorem card_e1PlusSub : Nat.card e1PlusSub = 2 ^ 7 := by
  have e : evenSub ≃ e1PlusSub :=
    Equiv.ofBijective (fun v => ⟨frameElt v, mem_e1PlusSub.2 ⟨v, v.2, rfl⟩⟩)
      ⟨fun v w h => Subtype.ext (frameElt_injective (congrArg Subtype.val h)), fun g => by
        obtain ⟨v, hv, h⟩ := mem_e1PlusSub.1 g.2
        exact ⟨⟨v, hv⟩, Subtype.ext h⟩⟩
  rw [← Nat.card_congr e, Nat.card_congr evenSubEquiv.toEquiv, Nat.card_eq_fintype_card,
    Fintype.card_fun, ZMod.card, Fintype.card_fin]

theorem frameReal_mem_normalizer (σ : frameAutSub) :
    frameReal σ ∈ normalizer (e1Sub : Set (Equiv.Perm (Fin 240))) :=
  mem_normalizer_e1Sub_of_action (frameReal_conj σ)

theorem e1Sub_conj_frameElt {e : Equiv.Perm (Fin 240)} (he : e ∈ e1Sub) (v : FrameVec) :
    e * frameElt v * e⁻¹ = frameElt v := by
  rw [e1Sub_comm he (mem_e1Sub.2 ⟨v, rfl⟩), mul_inv_cancel_right]

theorem frameReal_decomp_inj {e e' : Equiv.Perm (Fin 240)} (he : e ∈ e1Sub) (he' : e' ∈ e1Sub)
    {σ σ' : frameAutSub} (h : e * frameReal σ = e' * frameReal σ') : e = e' ∧ σ = σ' := by
  have hσ : σ = σ' := by
    refine Subtype.ext (perm_eq_of_frameElt fun v => ?_)
    have key : ∀ f ∈ e1Sub, ∀ τ : frameAutSub,
        frameElt (permVec τ v) = (f * frameReal τ) * frameElt v * (f * frameReal τ)⁻¹ := by
      intro f hf τ
      rw [show (f * frameReal τ) * frameElt v * (f * frameReal τ)⁻¹ =
        f * (frameReal τ * frameElt v * (frameReal τ)⁻¹) * f⁻¹ by group, frameReal_conj τ,
        e1Sub_conj_frameElt hf]
    rw [key e he σ, key e' he' σ', h]
  subst hσ
  exact ⟨mul_right_cancel h, rfl⟩

theorem exists_frameReal_decomp {w : Equiv.Perm (Fin 240)} (hw : w ∈ wE8)
    (hn : w ∈ normalizer (e1Sub : Set (Equiv.Perm (Fin 240)))) :
    ∃ σ : frameAutSub, w * (frameReal σ)⁻¹ ∈ e1Sub := by
  obtain ⟨σ, hσ, hact⟩ := normalizer_e1Sub_action hw hn
  refine ⟨⟨σ, hσ⟩, centralizer_e1Sub (mul_mem hw (inv_mem (wPlus_le (frameReal_mem _))))
    fun e he => ?_⟩
  obtain ⟨v, rfl⟩ := mem_e1Sub.1 he
  have h1 := frameReal_conj ⟨σ, hσ⟩ (permVec σ⁻¹ v)
  rw [permVec_permVec_inv] at h1
  have h2 := hact (permVec σ⁻¹ v)
  rw [permVec_permVec_inv] at h2
  have h3 : (frameReal ⟨σ, hσ⟩)⁻¹ * frameElt v = frameElt (permVec σ⁻¹ v) *
      (frameReal ⟨σ, hσ⟩)⁻¹ := by
    rw [← h1]
    group
  calc w * (frameReal ⟨σ, hσ⟩)⁻¹ * frameElt v
      = w * frameElt (permVec σ⁻¹ v) * (frameReal ⟨σ, hσ⟩)⁻¹ := by rw [mul_assoc, h3, mul_assoc]
    _ = w * frameElt (permVec σ⁻¹ v) * w⁻¹ * (w * (frameReal ⟨σ, hσ⟩)⁻¹) := by group
    _ = frameElt v * (w * (frameReal ⟨σ, hσ⟩)⁻¹) := by rw [h2]

@[expose] def n1Decomp (p : e1Sub × frameAutSub) :
    (wE8 ⊓ normalizer (e1Sub : Set (Equiv.Perm (Fin 240))) : Subgroup (Equiv.Perm (Fin 240))) :=
  ⟨p.1 * frameReal p.2, mem_inf.2 ⟨mul_mem (e1Sub_le_wE8 p.1.2) (wPlus_le (frameReal_mem _)),
    mul_mem (le_normalizer p.1.2) (frameReal_mem_normalizer _)⟩⟩

theorem n1Decomp_bijective : Function.Bijective n1Decomp := by
  refine ⟨fun p q h => ?_, fun w => ?_⟩
  · have h1 := frameReal_decomp_inj p.1.2 q.1.2 (congrArg Subtype.val h)
    exact Prod.ext (Subtype.ext h1.1) h1.2
  · obtain ⟨σ, he⟩ := exists_frameReal_decomp (mem_inf.1 w.2).1 (mem_inf.1 w.2).2
    exact ⟨(⟨_, he⟩, σ), Subtype.ext (inv_mul_cancel_right _ _)⟩

theorem card_normalizer_e1Sub : Nat.card (wE8 ⊓ normalizer (e1Sub : Set (Equiv.Perm (Fin 240))) :
    Subgroup (Equiv.Perm (Fin 240))) = 2 ^ 8 * 1344 := by
  rw [← Nat.card_congr (Equiv.ofBijective _ n1Decomp_bijective), Nat.card_prod, card_e1Sub,
    card_frameAutSub]

@[expose] def n1DecompPlus (p : e1PlusSub × frameAutSub) :
    (wPlus ⊓ normalizer (e1Sub : Set (Equiv.Perm (Fin 240))) : Subgroup (Equiv.Perm (Fin 240))) :=
  ⟨p.1 * frameReal p.2, by
    have hp : (p.1 : Equiv.Perm (Fin 240)) ∈ e1Sub ⊓ wPlus := e1PlusSub_eq ▸ p.1.2
    exact mem_inf.2 ⟨mul_mem hp.2 (frameReal_mem _),
      mul_mem (le_normalizer hp.1) (frameReal_mem_normalizer _)⟩⟩

theorem n1DecompPlus_bijective : Function.Bijective n1DecompPlus := by
  refine ⟨fun p q h => ?_, fun w => ?_⟩
  · have hp : (p.1 : Equiv.Perm (Fin 240)) ∈ e1Sub ⊓ wPlus := e1PlusSub_eq ▸ p.1.2
    have hq : (q.1 : Equiv.Perm (Fin 240)) ∈ e1Sub ⊓ wPlus := e1PlusSub_eq ▸ q.1.2
    have h1 := frameReal_decomp_inj hp.1 hq.1 (congrArg Subtype.val h)
    exact Prod.ext (Subtype.ext h1.1) h1.2
  · have hw := mem_inf.1 w.2
    obtain ⟨σ, he⟩ := exists_frameReal_decomp (wPlus_le hw.1) hw.2
    have he' : w * (frameReal σ)⁻¹ ∈ e1PlusSub := by
      rw [e1PlusSub_eq]
      exact mem_inf.2 ⟨he, mul_mem hw.1 (inv_mem (frameReal_mem σ))⟩
    exact ⟨(⟨_, he'⟩, σ), Subtype.ext (inv_mul_cancel_right _ _)⟩

theorem card_normalizer_e1Sub_plus : Nat.card (wPlus ⊓
    normalizer (e1Sub : Set (Equiv.Perm (Fin 240))) : Subgroup (Equiv.Perm (Fin 240))) =
      2 ^ 7 * 1344 := by
  rw [← Nat.card_congr (Equiv.ofBijective _ n1DecompPlus_bijective), Nat.card_prod,
    card_e1PlusSub, card_frameAutSub]

theorem blockVec_0123 : blockVec ({0, 1, 2, 3} : Finset (Fin 8)) = vec2 0 1 + vec2 2 3 := by
  decide

theorem signPerm_vec2_01 : signPerm (vec2 0 1) = frameElt (vec2 0 1) := signPerm_pair 0 (by decide)

theorem signPerm_vec2_23 : signPerm (vec2 2 3) = frameElt (vec2 2 3) := signPerm_pair 2 (by decide)

theorem signPerm_vec2_45 : signPerm (vec2 4 5) = frameElt (vec2 4 5) := signPerm_pair 4 (by decide)

theorem xPlane_eq_frameElt : xPlane = frameElt (blockVec {0, 1, 2, 3}) := by
  rw [blockVec_0123, frameElt_add, ← signPerm_vec2_01, ← signPerm_vec2_23,
    ← signPerm_add (vec2_mem_evenSub 0 1 (by decide)) (vec2_mem_evenSub 2 3 (by decide))]
  rfl

@[expose] def planeWords : List (List (Fin 2)) :=
  [[], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0], [0], [0, 0, 0, 0, 0], [0, 0], [0, 0, 0], [1, 0, 0],
    [1, 0, 0, 0], [1, 0], [0, 0, 0, 1, 0], [0, 1, 0, 0], [0, 1, 0], [0, 0, 1, 0]]

theorem plane_words : ∀ B ∈ frameBlocks, ∃ w ∈ planeWords,
    ({0, 1, 2, 3} : Finset (Fin 8)).image (frameWord w) = B := by
  decide +kernel

theorem exists_conj_plane {B : Finset (Fin 8)} (hB : B ∈ frameBlocks) :
    ∃ g ∈ wPlus, g * frameElt (blockVec B) * g⁻¹ = xPlane := by
  obtain ⟨w, -, hw⟩ := plane_words B hB
  obtain ⟨g, hg, hact⟩ := closure_frameGens_le_realized (frameWord_mem_closure w)
  refine ⟨g⁻¹, inv_mem hg, ?_⟩
  have h1 := hact (blockVec {0, 1, 2, 3})
  rw [permVec_blockVec, hw] at h1
  rw [← h1, xPlane_eq_frameElt]
  group

theorem frameClass_two : ∀ n < 256, framePop n = 2 → frameClass n = 2 := by decide +kernel

theorem frameClass_six : ∀ n < 256, framePop n = 6 → frameClass n = 7 := by decide +kernel

theorem frame_conj_eSub_spec {v : FrameVec}
    (h : frameWt v = 2 ∨ frameWt v = 6 ∨ ∃ B ∈ frameBlocks, v = blockVec B) :
    ∃ g ∈ wPlus, ∃ u ∈ evenSub, u ≠ frameZ ∧ g * frameElt v * g⁻¹ = signPerm u := by
  set Y : Set FrameVec := {v | ∃ g ∈ wPlus, ∃ u ∈ evenSub, u ≠ frameZ ∧
    g * frameElt v * g⁻¹ = signPerm u} with hYdef
  have hY : ∀ σ ∈ closure frameGens, ∀ v ∈ Y, permVec σ v ∈ Y := by
    rintro σ hσ v ⟨g, hg, u, hu, hne, he⟩
    obtain ⟨w, hw, hact⟩ := closure_frameGens_le_realized hσ
    refine ⟨g * w⁻¹, mul_mem hg (inv_mem hw), u, hu, hne, ?_⟩
    rw [← hact v, ← he]
    group
  have h01 : vec2 0 1 ∈ evenSub := vec2_mem_evenSub 0 1 (by decide)
  have h23 : vec2 2 3 ∈ evenSub := vec2_mem_evenSub 2 3 (by decide)
  have h45 : vec2 4 5 ∈ evenSub := vec2_mem_evenSub 4 5 (by decide)
  rcases h with h2 | h6 | ⟨B, hB, rfl⟩
  · have hr : vec2 0 1 ∈ Y := ⟨1, one_mem _, vec2 0 1, h01, by decide, by
      rw [one_mul, inv_one, mul_one, signPerm_vec2_01]⟩
    have hc : frameCls (vec2 0 1) = frameCls v := by
      rw [frameWt_eq] at h2
      rw [frameCls, frameCls, frameClass_two _ (frameEncode_lt v) h2]
      decide
    exact mem_of_frameCls_eq hY hc (by decide) (by decide) (by decide) hr
  · set r := vec2 0 1 + vec2 2 3 + vec2 4 5
    have hr : r ∈ Y := ⟨1, one_mem _, r, add_mem (add_mem h01 h23) h45, by decide, by
      rw [one_mul, inv_one, mul_one, frameElt_add, frameElt_add, ← signPerm_vec2_01,
        ← signPerm_vec2_23, ← signPerm_vec2_45, signPerm_add (add_mem h01 h23) h45,
        signPerm_add h01 h23]⟩
    have hc : frameCls r = frameCls v := by
      rw [frameWt_eq] at h6
      rw [frameCls, frameCls, frameClass_six _ (frameEncode_lt v) h6]
      decide
    exact mem_of_frameCls_eq hY hc (by decide) (by decide) (by decide) hr
  · obtain ⟨g, hg, he⟩ := exists_conj_plane hB
    exact ⟨g, hg, vec2 0 1 + vec2 2 3, add_mem h01 h23, by decide, he⟩

end CFSG.EvenSmallLie.OmegaEight.Weyl
