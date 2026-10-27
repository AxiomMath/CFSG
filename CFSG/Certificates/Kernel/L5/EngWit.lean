module

public import Certificates.Data.Kernel.L5.EngWit
public import CFSG.Certificates.Kernel.L5.Words
public import CFSG.Certificates.Kernel.L5.EngScp

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5.Fus

open Subgroup

variable {n : Nat} [Group (Idx n)]

theorem greedyGens_cons (s : Idx n) (S init : List (Idx n)) : greedyGens (s :: S) init =
    greedyGens S (if (wordsOf init).any (fun p => decide (p.1 = s)) then init else init ++ [s]) :=
  rfl

theorem mem_closure_greedyGens :
    ∀ (S init : List (Idx n)), ∀ s ∈ S, s ∈ closure {g | g ∈ greedyGens S init}
  | [], _, s, hs => absurd hs List.not_mem_nil
  | a :: S, init, s, hs => by
    rw [greedyGens_cons]
    rcases List.mem_cons.1 hs with rfl | hs
    · split_ifs with h
      · exact closure_mono (fun x hx => mem_greedyGens S init x hx) ((any_wordsOf_iff init s).1 h)
      · exact subset_closure
          (mem_greedyGens S _ s (List.mem_append_right _ (List.mem_singleton_self s)))
    · exact mem_closure_greedyGens S _ s hs

theorem getD_map_fst (L : List (List (Idx n × List Nat))) (j : Nat) :
    (L.map fun W => W.map Prod.fst).getD j [] = (L.getD j []).map Prod.fst := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases L[j]? <;> rfl

theorem greedyGens_of_genChk {S init R : List (Idx n)} (h : genChk S init R = true) :
    greedyGens S init = init ++ R := by
  simp only [genChk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  refine greedyGens_eq S init R _ (fun j hj x => ?_) h.2
  rw [getD_map_fst]
  exact mem_of_subChk _ _ (h.1 j (by omega)) x

theorem mkHomCtx_gens (t : Idx n) : (mkHomCtx t).gens = greedyGens (centL t) [t] := rfl

theorem ctxGens_of {reps : List (Idx n)} {Rs : List (List (Idx n))} (h : ctxGensChk reps Rs = true)
    {k : Nat} (hk : k < reps.length) :
    (mkHomCtx (reps.getD k 1)).gens = reps.getD k 1 :: Rs.getD k [] := by
  simp only [ctxGensChk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  rw [mkHomCtx_gens, greedyGens_of_genChk (h.2 k hk)]
  rfl

theorem xOK_false {e : Eng n} {ld : List Nat} {i : Idx n} (h : xWit e ld i = true) :
    xOK e ld = false := by
  simp only [xWit, Bool.and_eq_true, List.contains_iff_mem, decide_eq_true_eq] at h
  obtain ⟨⟨hi, hb⟩, hc⟩ := h
  rw [Bool.eq_false_iff]
  intro hx
  simp only [xOK, List.all_eq_true] at hx
  have h2 := hx i hi
  simp only [hb, decide_true, Bool.not_true, Bool.false_or, decide_eq_true_eq] at h2
  omega

theorem thompsonOK_false {e : Eng n} {ld : List Nat} {h : Nat} {u : Idx n}
    (hw : thWit e ld h u = true) : thompsonOK e ld = false := by
  simp only [thWit, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
    List.contains_iff_mem] at hw
  obtain ⟨⟨⟨hh, hu⟩, hH⟩, hany⟩ := hw
  rw [Bool.eq_false_iff]
  intro ht
  simp only [thompsonOK, List.all_eq_true] at ht
  have hmem : e.maxSubs.getD h #[] ∈ e.maxSubs := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hh, Option.getD_some]
    exact List.getElem_mem hh
  have h2 := ht _ hmem u hu
  rw [hH, hany] at h2
  exact Bool.false_ne_true h2

theorem scpOK_false {e : Eng n} {ld : List Nat} {k : Nat} {τ₀ : Nat × Nat × Nat × Nat}
    (hctx : e.ctxs.getD k default = mkHomCtx (e.reps.getD k 1)) (h : scpWit e ld k τ₀ = true) :
    scpOK e ld = false := by
  simp only [scpWit, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hk, hr⟩ := h
  have hLS : ∀ x ∈ centL (e.reps.getD k 1),
      x ∈ closure {g | g ∈ (mkHomCtx (e.reps.getD k 1)).gens} := fun x hx => by
    rw [mkHomCtx_gens]
    exact mem_closure_greedyGens _ _ x hx
  have hf := homExists_false _ ((nodup_elemsI n).filter _) hLS τ₀ hr
  rw [Bool.eq_false_iff]
  intro hs
  simp only [scpOK, List.all_eq_true, List.mem_range] at hs
  have h2 := hs k hk
  rw [hctx, hf] at h2
  exact Bool.false_ne_true h2

theorem feasible_false_of_witOK {e : Eng n}
    (hctx : ∀ k < e.reps.length, e.ctxs.getD k default = mkHomCtx (e.reps.getD k 1))
    {ld w : List Nat} (h : witOK e ld w = true) : feasible e ld = false := by
  unfold witOK at h
  unfold feasible
  split_ifs at h
  · rw [xOK_false h, Bool.false_and, Bool.false_and]
  · rw [thompsonOK_false h, Bool.and_false, Bool.false_and]
  · have hk : w.getD 1 0 < e.reps.length := by
      simp only [scpWit, Bool.and_eq_true, decide_eq_true_eq] at h
      exact h.1
    rw [scpOK_false (hctx _ hk) h, Bool.and_false]

theorem survivors_nil {e : Eng n}
    (hctx : ∀ k < e.reps.length, e.ctxs.getD k default = mkHomCtx (e.reps.getD k 1))
    {ws : List (List Nat)} (h : allWit e ws = true) : survivors e = [] := by
  simp only [allWit, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨hlen, hall⟩ := h
  unfold survivors
  rw [List.filter_eq_nil_iff]
  intro ld hld
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hld
  have hz : ((leaders e.reps.length)[j], ws[j]'(by omega)) ∈ (leaders e.reps.length).zip ws := by
    rw [List.mem_iff_getElem]
    exact ⟨j, by simp only [List.length_zip]; omega, by simp only [List.getElem_zip]⟩
  rw [feasible_false_of_witOK hctx (hall _ hz)]
  exact Bool.false_ne_true

theorem allWit_congr {e e' : Eng n} (hr : e.reps = e'.reps) (hc : e.ciA = e'.ciA)
    (hs : e.cszA = e'.cszA) (hi : e.invs = e'.invs) (hm : e.maxSubs = e'.maxSubs)
    (hx : e.x = e'.x) (ws : List (List Nat)) : allWit e ws = allWit e' ws := by
  cases e
  cases e'
  simp only at hr hc hs hi hm hx
  subst hr hc hs hi hm hx
  rfl

end CFSG.GH74.GLS.C3.Layer2.L5.Fus

end
