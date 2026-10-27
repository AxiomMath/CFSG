module

public import Certificates.Data.Kernel.L5.WBfs
public import CFSG.Certificates.Kernel.L5.Fast
public import CFSG.GH74.GLS.C3.Layer2.L5C3bInputs

public section

namespace CFSG.Certificates.Kernel.PkCV

open Equiv Perm CFSG.GH74.GLS.C3.Layer2.L5 CFSG.KD.L5

@[expose] noncomputable def evP (e : CV 16 × List ℕ) : Perm (Fin 16) × List ℕ := (ev e.1, e.2)

theorem getD_map_ev {n : ℕ} [Small n] (L : List (CV n)) (i : ℕ) :
    (L.map ev).getD i 1 = ev (L.getD i 1) := by
  rw [one_eq_ev, List.getD_map]

theorem wval_map_ev {n : ℕ} [Small n] (L : List (CV n)) (w : List ℕ) :
    wval (L.map ev) w = ev (wval L w) := by
  unfold wval
  have e : (fun i => (L.map ev).getD i 1) = fun i => ev (L.getD i 1) := funext (getD_map_ev L)
  rw [e]
  induction w with
  | nil => exact ev_one.symm
  | cons i w ih =>
    rw [List.map_cons, List.prod_cons, ih, List.map_cons, List.prod_cons]
    exact (ev_mul (n := n) _ _).symm

theorem decide_ev_eq' (a b : CV 16) (inst : Decidable (ev a = ev b)) :
    @decide (ev a = ev b) inst = decide (a = b) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff, ev_eq_iff]

theorem wval_eq_of_getD {M : Type*} [Monoid M] {L L' : List M} {w : List ℕ}
    (h : ∀ i ∈ w, L.getD i 1 = L'.getD i 1) : wval L w = wval L' w := by
  unfold wval
  rw [List.map_congr_left h]

theorem wBfsRound_map_ev (gs : List (CV 16)) (tab : List (CV 16 × List ℕ)) :
    wBfsRound (gs.map ev) (tab.map evP) = (wBfsRoundG gs tab).map evP := by
  unfold wBfsRound wBfsRoundG
  rw [List.foldl_map]
  refine List.foldl_hom (List.map evP) fun acc pw => ?_
  beta_reduce
  have hm : (gs.map ev).mapIdx (fun i g => (nrm ((evP pw).1 * g), (evP pw).2 ++ [i])) =
      (gs.mapIdx fun i g => (pw.1 * g, pw.2 ++ [i])).map evP := by
    apply List.ext_getElem (by simp)
    intro k _ _
    simp only [List.getElem_mapIdx, List.getElem_map, evP, nrm_eq, ev_mul']
  rw [hm, List.foldl_map]
  refine List.foldl_hom (List.map evP) fun acc2 qw => ?_
  beta_reduce
  simp only [List.any_map, Function.comp_def, evP, beq_ev, beq_cv]
  cases acc2.any (fun e => decide (e.1 = qw.1)) <;> simp [evP]

theorem wBfsTab_map_ev (gs : List (CV 16)) (k : ℕ) :
    wBfsTab (gs.map ev) k = (wBfsTabG gs k).map evP := by
  induction k with
  | zero => simp [wBfsTab, wBfsTabG, evP, ev_one]
  | succ k ih => simp only [wBfsTab, wBfsTabG, ih, wBfsRound_map_ev]

theorem homTab_eq_false {tab : List (Perm (Fin 16) × List ℕ)} {images : List (Perm (Fin 16))}
    (hnd : (tab.map Prod.fst).Nodup) {a b c : Perm (Fin 16) × List ℕ} (ha : a ∈ tab)
    (hb : b ∈ tab) (hc : c ∈ tab) (hp : c.1 = a.1 * b.1)
    (hne : wval images c.2 ≠ wval images a.2 * wval images b.2) : homTab tab images = false := by
  unfold homTab
  simp only [map_nrm, nrm_eq]
  rw [Bool.eq_false_iff]
  intro h
  let f : Perm (Fin 16) × List ℕ → Perm (Fin 16) × Perm (Fin 16) := fun e => (e.1, wval images e.2)
  have h1 := List.all_eq_true.1 (List.all_eq_true.1 h _ (List.mem_map_of_mem (f := f) ha)) _
    (List.mem_map_of_mem (f := f) hb)
  obtain ⟨e₃, he₃, hq⟩ := List.any_eq_true.1 h1
  obtain ⟨d, hd, rfl⟩ := List.mem_map.1 he₃
  simp only [f, Bool.and_eq_true, beq_iff_eq] at hq
  have hdc : d = c := List.inj_on_of_nodup_map hnd hd hc (hq.1.trans hp.symm)
  subst hdc
  exact hne hq.2

end CFSG.Certificates.Kernel.PkCV

end
