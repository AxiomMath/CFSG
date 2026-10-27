module

public import Certificates.Data.Kernel.Census.PackedE16
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoL3FourE16Tests
import CFSG.Certificates.Kernel.Census.XsProof

public section

namespace CFSG.KC.Census

open CFSG.ComponentClassification.RankTwoL3Four.HypII CFSG.ComponentClassification.RankTwoSporadic.Cert

theorem pe16OK_eq {inSP : Nat → Bool} {inS : Array Nat → Bool} {L : List Nat}
    (hL : L.all (canon1 42 6) = true) (hLv : L.all (pvalid 42 6) = true)
    (hin : ∀ P, canon1 42 6 P = true → pvalid 42 6 P = true → inSP P = inS (unpackP 42 6 P)) :
    pe16OK 42 6 inSP (L.filter (pisInv 42 6)) =
      e16OKW inS ((L.map (unpackP 42 6)).filter isInvA) := by
  obtain ⟨e1, e2⟩ := SP.pid_good_of_le (n := 42) (w := 6) (by norm_num) (by norm_num)
  have G : SP.Good 42 6 := ⟨by norm_num, by norm_num, e1, e2⟩
  have hc : ∀ P ∈ L, canon1 42 6 P = true := List.all_eq_true.1 hL
  have hv : ∀ P ∈ L, pvalid 42 6 P = true := List.all_eq_true.1 hLv
  have hpc := SP.pc_canon G
  have hpc_eq := fun {p : Nat} (hp : canon1 42 6 p = true) (q : Nat) => SP.pc_eq G (q := q) hp
  have hinv : ∀ P ∈ L, isInvA (unpackP 42 6 P) = pisInv 42 6 P := fun P hP => by
    rw [isInvA, pisInv, ← SP.pc_eq G (hc P hP), SP.eqA_pid G (hpc _ _), SP.eqA_pid G (hc P hP)]
  have hfil : (L.map (unpackP 42 6)).filter isInvA = (L.filter (pisInv 42 6)).map (unpackP 42 6) := by
    rw [List.filter_map, List.map_inj_left.2 (fun _ _ => rfl)]
    congr 1
    exact List.filter_congr fun P hP => by rw [Function.comp_apply, hinv P hP]
  rw [hfil]
  set I := L.filter (pisInv 42 6)
  have hI : ∀ P ∈ I, canon1 42 6 P = true ∧ pvalid 42 6 P = true := fun P hP =>
    have hP := (List.mem_filter.1 hP).1
    ⟨hc P hP, hv P hP⟩
  have allc : ∀ {f g : Nat → Bool}, (∀ P ∈ I, f P = g P) → I.all f = I.all g := fun h =>
    Bool.eq_iff_iff.2 (by simp only [List.all_eq_true]; exact forall₂_congr fun P hP => by rw [h P hP])
  have cm := fun {p q} (hp : p ∈ I) (hq : q ∈ I) => SP.commA_eq G (hI _ hp).1 (hI _ hq).1
  have eq := fun {p q : Nat} (hp : canon1 42 6 p = true) (hq : canon1 42 6 q = true) =>
    SP.eqA_unpack hp hq
  unfold pe16OK e16OKW
  rw [List.all_map]
  refine allc fun u hu => ?_
  have cu := (hI u hu).1
  rw [Function.comp_apply, pe16At, ← hin u cu (hI u hu).2, List.all_map]
  congr 1
  refine allc fun v hv' => ?_
  have cv := (hI v hv').1
  rw [Function.comp_apply, List.all_map, cm hu hv', eq cv cu]
  congr 1
  refine allc fun x hx => ?_
  have cx := (hI x hx).1
  rw [Function.comp_apply, List.all_map, cm hu hx, cm hv' hx, eq cx cu, eq cx cv, ← hpc_eq cu,
    eq cx (hpc _ _)]
  congr 1
  refine allc fun t ht => ?_
  have ct := (hI t ht).1
  rw [Function.comp_apply, cm ht hu, cm ht hv', cm ht hx, inSpan3, pinSpan3]
  congr 1
  simp only [List.any_cons, List.any_nil, ← e1, ← hpc_eq cv, ← hpc_eq cu, eq ct e2, eq ct cu, eq ct cv, eq ct cx,
    eq ct (hpc _ _)]

theorem all_drop_chunk {α : Type} {f : α → Bool} {l : List α} {a B : Nat}
    (h1 : ((l.drop a).take B).all f = true) (h2 : (l.drop (a + B)).all f = true) :
    (l.drop a).all f = true := by
  rw [← List.take_append_drop B (l.drop a), List.all_append, h1, Bool.true_and, List.drop_drop]
  exact h2

end CFSG.KC.Census
