module

public import Certificates.Data.Kernel.L5.EngOne
public import CFSG.Certificates.Kernel.L5.EngRec

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5.Fus

open Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2

variable {n : Nat} [Group (Idx n)]

theorem homGo_of_path {ctx : HomCtx n} {ci : Array Nat} {ld : List Nat} {tp : Idx n} :
    ∀ (d j : Nat) (cs ps : List (Idx n)), pathGo ctx ci ld tp d j cs ps = true →
      homGo ctx ci ld ((elemsI n).filter fun c => decide (c * tp = tp * c)) d j cs = true
  | 0, _, _, _, h => h
  | _ + 1, _, _, [], h => by simp [pathGo] at h
  | d + 1, j, cs, c :: ps, h => by
    simp only [pathGo, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    simp only [homGo, Bool.and_eq_true, List.any_eq_true]
    exact ⟨h1, c, List.mem_filter.2 ⟨mem_elemsI c, decide_eq_true h2⟩,
      homGo_of_path d (j + 1) (cs ++ [c]) ps h3⟩

theorem homExists_of_path {ctx : HomCtx n} {ci : Array Nat} {ld : List Nat} {tp : Idx n}
    {ps : List (Idx n)} (h : hexPath ctx ci ld tp ps = true) : homExists ctx ci ld tp = true :=
  homGo_of_path _ _ _ _ h

theorem mkHomCtx_eq_ctxF (t : Idx n) : mkHomCtx t = ctxF (mkHomCtx t).gens := rfl

theorem ctxs_eq {e : Eng n} {Rs : List (List (Idx n))}
    (hctx : ∀ k < e.reps.length, e.ctxs.getD k default = mkHomCtx (e.reps.getD k 1))
    (hx : ctxGensChk e.reps Rs = true) {k : Nat} (hk : k < e.reps.length) :
    e.ctxs.getD k default = ctxF (e.reps.getD k 1 :: Rs.getD k []) := by
  rw [hctx k hk, mkHomCtx_eq_ctxF, ctxGens_of hx hk]

section Ctx

variable {e : Eng n} {Rs : List (List (Idx n))}
  (hctx : ∀ k < e.reps.length, e.ctxs.getD k default = mkHomCtx (e.reps.getD k 1))
  (hx : ctxGensChk e.reps Rs = true)
include hctx hx

theorem scpOK_of_path {ld : List Nat} {Ps : List (List (Idx n))}
    (h : scpPath e Rs ld Ps = true) : scpOK e ld = true := by
  simp only [scpPath, List.all_eq_true, List.mem_range] at h
  simp only [scpOK, List.all_eq_true, List.mem_range]
  intro k hk
  rw [ctxs_eq hctx hx hk]
  exact homExists_of_path (h k hk)

theorem feasible_of_survChk {ld : List Nat} {Ps : List (List (Idx n))}
    (h : survChk e Rs ld Ps = true) : feasible e ld = true := by
  simp only [survChk, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  simp only [feasible, Bool.and_eq_true]
  exact ⟨⟨h1, h2⟩, scpOK_of_path hctx hx h3⟩

theorem scpOK_false_direct {ld : List Nat} {k : Nat} (h : scpDirect e Rs ld k = true) :
    scpOK e ld = false := by
  simp only [scpDirect, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  obtain ⟨hk, hf⟩ := h
  rw [Bool.eq_false_iff]
  intro hs
  simp only [scpOK, List.all_eq_true, List.mem_range] at hs
  have h2 := hs k hk
  rw [ctxs_eq hctx hx hk, hf] at h2
  exact Bool.false_ne_true h2

theorem witOK1_sound {ld₀ ld w : List Nat} (h : witOK1 e Rs ld₀ ld w = true) :
    ld = ld₀ ∨ feasible e ld = false := by
  unfold witOK1 at h
  split_ifs at h
  · exact Or.inl (of_decide_eq_true h)
  · right
    unfold feasible
    rw [scpOK_false_direct hctx hx h, Bool.and_false]
  · exact Or.inr (feasible_false_of_witOK hctx h)

theorem survivors_one {ld₀ : List Nat} {Ps : List (List (Idx n))} {ws : List (List Nat)}
    (hs : survChk e Rs ld₀ Ps = true) (hw : allWit1 e Rs ld₀ ws = true) :
    survivors e = [ld₀] := by
  simp only [allWit1, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hw
  obtain ⟨⟨hlen, hcnt⟩, hall⟩ := hw
  have hf₀ := feasible_of_survChk hctx hx hs
  have key : ∀ ld ∈ leaders e.reps.length, feasible e ld = decide (ld = ld₀) := by
    intro ld hld
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hld
    have hz : ((leaders e.reps.length)[j], ws[j]'(by omega)) ∈ (leaders e.reps.length).zip ws := by
      rw [List.mem_iff_getElem]
      exact ⟨j, by simp only [List.length_zip]; omega, by simp only [List.getElem_zip]⟩
    rcases witOK1_sound hctx hx (hall _ hz) with h | h
    · dsimp only at h
      rw [h, hf₀]
      exact (decide_eq_true rfl).symm
    · dsimp only at h
      rw [h]
      refine (decide_eq_false fun he => ?_).symm
      rw [he, hf₀] at h
      exact absurd h (by decide)
  unfold survivors
  rw [List.filter_congr key]
  have h1 : (leaders e.reps.length).filter (fun ld => decide (ld = ld₀)) = List.replicate 1 ld₀ :=
    List.eq_replicate_iff.2 ⟨hcnt, fun b hb => of_decide_eq_true (List.mem_filter.1 hb).2⟩
  rw [h1]
  rfl

end Ctx

theorem survChk_congr {e e' : Eng n} (hr : e.reps = e'.reps) (hc : e.ciA = e'.ciA)
    (hs : e.cszA = e'.cszA) (hi : e.invs = e'.invs) (hm : e.maxSubs = e'.maxSubs)
    (hx : e.x = e'.x) (Rs : List (List (Idx n))) (ld : List Nat) (Ps : List (List (Idx n))) :
    survChk e Rs ld Ps = survChk e' Rs ld Ps := by
  cases e
  cases e'
  simp only at hr hc hs hi hm hx
  subst hr hc hs hi hm hx
  rfl

theorem allWit1_congr {e e' : Eng n} (hr : e.reps = e'.reps) (hc : e.ciA = e'.ciA)
    (hs : e.cszA = e'.cszA) (hi : e.invs = e'.invs) (hm : e.maxSubs = e'.maxSubs)
    (hx : e.x = e'.x) (Rs : List (List (Idx n))) (ld₀ : List Nat) (ws : List (List Nat)) :
    allWit1 e Rs ld₀ ws = allWit1 e' Rs ld₀ ws := by
  cases e
  cases e'
  simp only at hr hc hs hi hm hx
  subst hr hc hs hi hm hx
  rfl

theorem engChk_of1
    {emb : ↥T5 →* Idx n} (d : Eng n) (mg : List (Idx n)) (Rs : List (List (Idx n)))
    (ld₀ : List Nat) (Ps : List (List (Idx n))) (ws : List (List Nat))
    (hf : fusChk emb d.reps d.ciA d.invs d.x = true) (hc : cszChk (n := n) d.cszA = true)
    (hg : genChk (elemsI n) [] mg = true) (hm : mgChk mg d.maxSubs = true)
    (hx : ctxGensChk d.reps Rs = true) (hR : ctxChk d.reps Rs = true)
    (hs : survChk d Rs ld₀ Ps = true) (hw : allWit1 d Rs ld₀ ws = true) :
    (engOK (mkEng emb) && decide (survivors (mkEng emb) = [ld₀])) = true := by
  simp only [fusChk, Bool.and_eq_true, decide_eq_true_eq] at hf
  obtain ⟨⟨⟨⟨⟨⟨⟨hi, hr⟩, hci⟩, hxe⟩, h1⟩, h2⟩, h3⟩, h7⟩ := hf
  simp only [cszChk, decide_eq_true_eq] at hc
  simp only [mgChk, Bool.and_eq_true, decide_eq_true_eq] at hm
  have hgg : greedyGens (elemsI n) [] = mg := greedyGens_of_genChk hg
  have er : (mkEng emb).reps = d.reps := hr
  have ec : (mkEng emb).ciA = d.ciA := hci
  have ei : (mkEng emb).invs = d.invs := hi
  have ex : (mkEng emb).x = d.x := hxe
  have es : (mkEng emb).cszA = d.cszA := hc
  have emg : (mkEng emb).mgens = mg := hgg
  have ems : (mkEng emb).maxSubs = d.maxSubs := by
    change maxSubsOf (mkEng emb).mgens (wordArrOf (mkEng emb).mgens) = _
    rw [emg]
    exact hm.1
  have hctx : ∀ k < (mkEng emb).reps.length,
      (mkEng emb).ctxs.getD k default = mkHomCtx ((mkEng emb).reps.getD k 1) :=
    fun k hk => getD_map_mkHomCtx hk
  have hx' : ctxGensChk (mkEng emb).reps Rs = true := by
    rw [er]
    exact hx
  have hsurv : survivors (mkEng emb) = [ld₀] := by
    refine survivors_one hctx hx' (Ps := Ps) (ws := ws) ?_ ?_
    · rw [survChk_congr er ec es ei ems ex]
      exact hs
    · rw [allWit1_congr er ec es ei ems ex]
      exact hw
  rw [hsurv, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨?_, rfl⟩
  simp only [engOK, Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [er]
    exact h1
  · rw [er, ec]
    exact h2
  · rw [ei, ec, er]
    exact h3
  · rw [List.all_eq_true]
    intro a _
    rw [decide_eq_true_eq]
    exact getD_toArray_map_elemsI cszI a
  · change (elemsI n).all (fun m => decide (evW (mkEng emb).mgens
      ((wordArrOf (mkEng emb).mgens).getD m.v []) = m)) = true
    rw [emg]
    exact hm.2
  · simp only [ctxChk, List.all_eq_true, List.mem_range] at hR
    rw [List.all_eq_true]
    intro k hk
    rw [List.mem_range] at hk
    have hk' : k < d.reps.length := by
      rw [← er]
      exact hk
    rw [hctx k hk, ctxOK_mkHomCtx, er, ctxGens_of hx hk']
    exact hR k hk'
  · rw [ex]
    exact h7

end CFSG.GH74.GLS.C3.Layer2.L5.Fus

end
