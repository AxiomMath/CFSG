module

public import Certificates.Data.Kernel.Misc.MergeT
public import CFSG.Quasithin.Recognition.CertMergeTargets
public import CFSG.Certificates.Kernel.Spor.RawDefs
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.BfsPinAlg

public section

namespace CFSG.KC.MergeT

open CFSG.KC.Enum CFSG.KS.Raw CFSG.Certificates.Native CFSG.Monster.B.Co2.Native
open CFSG.KS (mask)
open CFSG.KC.YModel (lget)

theorem lget_eq : ∀ (L : List Nat) (i : Nat), lget L i = L.getD i 0
  | [], i => by cases i <;> rfl
  | a :: L, 0 => rfl
  | a :: L, i + 1 => by
    rw [List.getD_cons_succ, ← lget_eq L i]
    rfl

theorem blt_dec (a b : Nat) : Nat.blt a b = decide (a < b) := by
  rw [Bool.eq_iff_iff, Nat.blt_eq, decide_eq_true_iff]

theorem strictL_eq (y : Nat) (k : Nat → List Nat) : strictL y k = k y := by
  cases y <;> rfl

theorem mapE_eq (f : Nat → Nat) : ∀ L : List Nat, mapE f L = L.map f
  | [] => rfl
  | a :: L => by
    change strictL (f a) (fun v => v :: mapE f L) = _
    rw [strictL_eq, mapE_eq f L]
    rfl

theorem arr_get (a : Array Nat) (k : Nat) : a[k]! = a.toList.getD k 0 := by
  by_cases hk : k < a.size
  · rw [getElem!_pos a k hk, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using hk)]
    simp
  · rw [getElem!_neg a k hk, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simpa using hk)]
    rfl

@[expose] def Rel (s : Bool × Array Nat) (s' : Bool × List Nat) : Prop :=
  s.1 = s'.1 ∧ (s.1 = true → s.2.toList = s'.2)

section

variable {n w kG : Nat} {GP : Nat → Nat} {G : Array (Array Nat)}
  (hG : G.size = kG ∧ ∀ i < kG, G[i]! = unpack n w (GP i))
include hG

theorem rel_step {s : Bool × Array Nat} {s' : Bool × List Nat} (hr : Rel s s')
    (t : Nat × Nat × Nat) : Rel (mergeStep n G s t) (mergeStepK n w GP kG s' t) := by
  obtain ⟨h1, h2⟩ := hr
  obtain ⟨i, u, v⟩ := t
  unfold mergeStep mergeStepK
  dsimp only
  cases hs : s.1
  · rw [hs] at h1
    rw [← h1]
    exact ⟨rfl, fun h => absurd h (by simp)⟩
  · have hl := h2 hs
    rw [hs] at h1
    rw [← h1]
    simp only [CFSG.KS.Raw.Orb.bAnd_eq, Bool.true_and]
    have hflag : (decide (i < G.size) && decide (u < n) && decide (v < n) && s.2[u]! == s.2[v]!) =
        (Nat.blt i kG && (Nat.blt u n && (Nat.blt v n && Nat.beq (lget s'.2 u) (lget s'.2 v)))) := by
      rw [hG.1, arr_get, arr_get, hl, lget_eq, lget_eq, blt_dec, blt_dec, blt_dec]
      simp only [Bool.and_assoc]
      rfl
    refine ⟨hflag, fun hf => ?_⟩
    rw [hflag] at hf
    simp only [Bool.and_eq_true, Nat.blt_eq] at hf
    obtain ⟨hi, hu, hv, -⟩ := hf
    rw [hG.2 i hi, CFSG.KC.BfsPin.unpack_getElem!, CFSG.KC.BfsPin.unpack_getElem!]
    simp only [hu, hv, ↓reduceIte]
    unfold relabel relabelL
    rw [strictL_eq, strictL_eq, mapE_eq, Array.toList_map, arr_get, arr_get,
      hl, ← lget_eq, ← lget_eq]
    congr 1
    funext l
    rw [CFSG.KS.Raw.Orb.nIf_eq]
    simp [Nat.beq_eq_true_eq]

theorem rel_fold : ∀ (L : List (Nat × Nat × Nat)) {s : Bool × Array Nat} {s' : Bool × List Nat},
    Rel s s' → Rel (L.foldl (mergeStep n G) s) (L.foldl (mergeStepK n w GP kG) s')
  | [], _, _, hr => hr
  | t :: L, _, _, hr => rel_fold L (rel_step hG hr t)

omit hG in
theorem rel_init (b x : Nat) : Rel (true, mergeInit n b x) (true, initL n b x) := by
  refine ⟨rfl, fun _ => ?_⟩
  apply List.ext_getElem
  · simp [mergeInit, initL]
  · intro i h1 h2
    simp only [mergeInit, initL, Array.toList_ofFn, List.getElem_ofFn, List.getElem_map,
      List.getElem_range]
    rw [CFSG.KS.Raw.Orb.nIf_eq]
    simp

theorem mergeTargetsOK_of_mergeTK {b x : Nat} {L : List (Nat × Nat × Nat)} {ts : List Nat}
    (h : mergeTK n w GP kG b x L ts = true) : CFSG.Quasithin.mergeTargetsOK n G b x L ts = true := by
  unfold mergeTK at h
  simp only [CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true, Nat.blt_eq] at h
  obtain ⟨hb, hx, hf, ht⟩ := h
  obtain ⟨r1, r2⟩ := rel_fold hG L (rel_init b x)
  unfold CFSG.Quasithin.mergeTargetsOK
  dsimp only
  have hf' : (L.foldl (mergeStep n G) (true, mergeInit n b x)).1 = true := r1.trans hf
  have hl := r2 hf'
  simp only [hb, hx, hf', decide_true, Bool.true_and, List.all_eq_true, Bool.and_eq_true,
    decide_eq_true_eq, beq_iff_eq]
  intro t htm
  have := List.all_eq_true.1 ht t htm
  simp only [Bool.and_eq_true, Nat.blt_eq] at this
  refine ⟨this.1, ?_⟩
  have e := this.2
  rw [lget_eq, lget_eq, ← hl] at e
  rw [arr_get, arr_get]
  simpa using e

end

end CFSG.KC.MergeT

end
