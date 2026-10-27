module

public import Certificates.Data.Kernel.L5.EngRec
public import CFSG.Certificates.Kernel.L5.EngWit

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5.Fus

open Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2

variable {n : Nat} [Group (Idx n)]

theorem getD_toArray_map_elemsI (f : Idx n → Nat) (a : Idx n) :
    ((elemsI n).map f).toArray.getD a.v 0 = f a := by
  have ha : a.v < (List.finRange n).length := by
    rw [List.length_finRange]
    exact Idx.v_lt a
  have h1 : (List.finRange n)[a.v]? = some a.i := by
    rw [List.getElem?_eq_getElem ha, Option.some.injEq]
    exact Fin.ext (by simp [Idx.v])
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map, elemsI,
    List.getElem?_map, h1]
  rfl

theorem getD_map_mkHomCtx {reps : List (Idx n)} {k : Nat} (hk : k < reps.length) :
    (reps.map mkHomCtx).getD k default = mkHomCtx (reps.getD k 1) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hk,
    Option.map_some, Option.getD_some]

theorem ctxOK_mkHomCtx (t : Idx n) : ctxOK t (mkHomCtx t) = ctxOK t (ctxR (mkHomCtx t).gens) :=
  rfl

theorem engChk_of
    {emb : ↥T5 →* Idx n} (d : Eng n) (mg : List (Idx n)) (Rs : List (List (Idx n)))
    (ws : List (List Nat)) (hf : fusChk emb d.reps d.ciA d.invs d.x = true)
    (hc : cszChk (n := n) d.cszA = true) (hg : genChk (elemsI n) [] mg = true)
    (hm : mgChk mg d.maxSubs = true) (hx : ctxGensChk d.reps Rs = true)
    (hR : ctxChk d.reps Rs = true) (hw : allWit d ws = true) :
    (engOK (mkEng emb) && decide (survivors (mkEng emb) = [])) = true := by
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
  have hsurv : survivors (mkEng emb) = [] := by
    refine survivors_nil hctx (ws := ws) ?_
    rw [allWit_congr er ec es ei ems ex]
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
