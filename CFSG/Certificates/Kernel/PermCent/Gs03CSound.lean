module

public import Certificates.Data.Kernel.PermCent.Gs03C
public import CFSG.Certificates.Kernel.PermCent.CVSound
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2Gs03Check

public section

namespace CFSG.Certificates.Kernel.PkCV.Gs03

open CFSG.Certificates CFSG.LocalAnalysis.WeakClosure81 CFSG.GH74.KGroups

variable {n : Nat} [Small n]

theorem getD_map_ev (cs : List (CV n)) (l : ℕ) : (cs.map ev).getD l 1 = ev (cs.getD l 1) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases cs[l]? <;> simp [ev_one]

theorem ev_wEvC (cs : List (CV n)) (w : List ℕ) :
    ev (wEvC cs w) = gs03WordEval (cs.map ev) w := by
  induction w with
  | nil => exact ev_one
  | cons l w ih => rw [wEvC, gs03WordEval, ev_mul, ih, getD_map_ev]

theorem map_ev_cOf (L : List (Equiv.Perm (Fin n))) : (L.map cOf).map ev = L := by
  rw [List.map_map]
  conv_rhs => rw [← List.map_id L]
  exact List.map_congr_left fun σ _ => ev_cOf σ

theorem clsC_eq (QP : RawSchreierDatum n) (gens : List (CV n)) (k : ℕ) (r : CV n)
    (ss : List (CV n)) (ws : List (List ℕ)) :
    clsC QP gens k r ss ws = gs03ClassCheck QP (gens.map ev) k (ev r) (ss.map ev) ws := by
  have hc : (ss.map ev).map (fun x => x⁻¹ * ev r * x) =
      (ss.map fun x => x⁻¹ * r * x).map ev := by
    rw [List.map_map, List.map_map]
    exact List.map_congr_left fun x _ => by simp only [Function.comp_apply, ev_mul, ev_inv]
  have hs : (ss.map ev).all (fun x => QP.sift x 0) = ss.all fun x => siftC QP x 0 := by
    rw [List.all_map]
    exact congrArg ss.all (funext fun x => sift_ev QP x 0)
  have hz : ((gens.map ev).zip ws).all (fun gw =>
        decide (gs03WordEval ((ss.map ev).map fun x => x⁻¹ * ev r * x) gw.2 = gw.1)) =
      (gens.zip ws).all fun gw => decide (wEvC (ss.map fun x => x⁻¹ * r * x) gw.2 = gw.1) := by
    rw [List.zip_map_left, List.all_map, hc]
    refine congrArg (gens.zip ws).all (funext fun gw => ?_)
    simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd, id_eq, ← ev_wEvC]
    exact decide_ev_eq _ _
  unfold clsC gs03ClassCheck
  rw [hs, hz, List.length_map, List.length_map]

theorem clsesC_eq (QP : RawSchreierDatum n) (gens : List (CV n)) (k : ℕ)
    (cls : List (CV n × List (CV n) × List (List ℕ))) :
    clsesC QP gens k cls = gs03ClassesCheck QP (gens.map ev) k (cls.map evCls) := by
  unfold clsesC gs03ClassesCheck
  rw [List.all_map]
  exact congrArg cls.all (funext fun c => clsC_eq QP gens k c.1 c.2.1 c.2.2)

theorem gs03ClassesCheck_of_C (QP : RawSchreierDatum n) (gens : List (Equiv.Perm (Fin n)))
    (k : ℕ) (cls : List (Equiv.Perm (Fin n) × List (Equiv.Perm (Fin n)) × List (List ℕ)))
    (h : clsesC QP (gens.map cOf) k (cls.map cOfCls) = true) :
    gs03ClassesCheck QP gens k cls = true := by
  have hcls : (cls.map cOfCls).map evCls = cls := by
    rw [List.map_map]
    conv_rhs => rw [← List.map_id cls]
    exact List.map_congr_left fun c _ => by
      simp only [Function.comp_apply, evCls, cOfCls, ev_cOf, map_ev_cOf, id_eq]
  rw [clsesC_eq, map_ev_cOf, hcls] at h
  exact h

theorem covWC_sound (L R : List (CV n)) (wit : List (ℕ × ℕ)) (h : covWC L R wit = true) :
    gs03CoverCheck (L.map ev) (R.map ev) = true := by
  unfold covWC at h
  rw [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨hlen, hall⟩ := h
  unfold gs03CoverCheck
  rw [List.all_eq_true]
  intro g' hg'
  obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hg'
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hg
  have hk' : k < wit.length := hlen ▸ hk
  have hmem : (L[k], wit[k]) ∈ L.zip wit := by
    have hz : k < (L.zip wit).length := by simp [List.length_zip, hk, hk']
    have := List.getElem_mem hz
    simpa [List.getElem_zip] using this
  have hc := hall _ hmem
  simp only [covAt] at hc
  rw [Bool.or_eq_true]
  by_cases hi : wit[k].1 < R.length
  · simp only [hi, decide_true, cond_true, Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨hj, he⟩ := hc
    rw [eq22C_eq, decide_eq_true_eq, List.getD_eq_getElem _ _ hj,
      List.getD_eq_getElem _ _ hi] at he
    right
    rw [List.any_eq_true]
    refine ⟨ev R[wit[k].1], List.mem_map_of_mem (List.getElem_mem hi), ?_⟩
    rw [List.any_eq_true]
    refine ⟨ev L[wit[k].2], List.mem_map_of_mem (List.getElem_mem hj), ?_⟩
    rw [decide_eq_true_eq, ev_inv', ev_mul', ev_mul', ev_eq_iff, he, mul_inv_cancel_right]
  · simp only [hi, decide_false, cond_false, Bool.not_eq_true', Bool.and_eq_false_iff,
      Bool.not_eq_false', decide_eq_true_eq, powOneC_eq, decide_eq_false_iff_not] at hc
    left
    rw [Bool.not_eq_true', decide_eq_false_iff_not, not_and, not_not, ev_mul', one_eq_ev,
      ev_eq_iff, ev_eq_iff, ← pow_two]
    rcases hc with hc | hc
    · exact fun h2 => absurd h2 hc
    · exact fun _ => hc

theorem gs03CoverCheck_of_C (Q : RawSchreierDatum n) (reps : List (Equiv.Perm (Fin n)))
    (wit : List (ℕ × ℕ)) (h : covWC (elemsC Q) (reps.map cOf) wit = true) :
    gs03CoverCheck (elemsT Q) reps = true := by
  rw [elemsT_eq_elemsC, ← map_ev_cOf reps]
  exact covWC_sound _ _ wit h

theorem cOf_injective : Function.Injective (cOf : Equiv.Perm (Fin n) → CV n) := fun a b h => by
  rw [← ev_cOf a, ← ev_cOf b, h]

theorem decide_map_cOf (L M : List (Equiv.Perm (Fin n))) (h : L.map cOf = M.map cOf) :
    decide (L = M) = true :=
  decide_eq_true ((List.map_injective_iff.2 cOf_injective) h)

end CFSG.Certificates.Kernel.PkCV.Gs03

end
