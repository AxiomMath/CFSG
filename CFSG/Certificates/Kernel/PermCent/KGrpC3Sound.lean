module

public import Certificates.Data.Kernel.PermCent.KGrpC3
public import CFSG.Certificates.Kernel.PermCent.CVSound
public import CFSG.GH74.E2.Q8C2Check
public import CFSG.ClassicalInvolution.Q3.ONanTA3SmallCheck

public section

namespace CFSG.Certificates.Kernel.PkCV.KGrp

open CFSG.GH74.E2 CFSG.ClassicalInvolution.Q3.TA3.Check

section Q8C2

variable {n : Nat} [Small n]

theorem q8c2at_C (c : CV n) (C : List (CV n)) :
    q8c2at (ev c) (C.map ev) = q8c2atC c C := by
  unfold q8c2at q8c2atC
  simp only [List.all_map, Function.comp_def, ne_eq, decide_not, ev_mul', ev_inv', ev_pow',
    one_eq_ev, decide_ev_eq, pow_fast, conj_fast]

theorem q8c2free_C (L : List (CV n)) : q8c2free (L.map ev) = q8c2freeC L := by
  unfold q8c2free q8c2freeC
  simp only [List.filter_map, List.all_map, Function.comp_def, q8c2at_C, ne_eq, decide_not,
    ev_mul', ev_pow', one_eq_ev, decide_ev_eq, pow_fast, comm_fast]

end Q8C2

section Good

variable {M N : Type*} [Group M] [DecidableEq M] [Group N] [DecidableEq N] (f : M →* N)
  (hf : Function.Injective f)
include hf

theorem ordAux_map (o : M) (fuel k : ℕ) : ordAux (f o) fuel k = ordAux o fuel k := by
  induction fuel generalizing k with
  | zero => rfl
  | succ fuel ih =>
    have h : f o ^ k = 1 ↔ o ^ k = 1 := by rw [← map_pow, ← map_one f, hf.eq_iff]
    simp only [ordAux, h, ih]

theorem ordB_map (B : ℕ) (o : M) : ordB B (f o) = ordB B o := ordAux_map f hf o B 1

theorem memB_map (l : List M) (x : M) : memB (l.map f) (f x) = memB l x := by
  simp only [memB, List.any_map, Function.comp_def, hf.eq_iff]

theorem centB_map (L : List M) (t : M) : centB (L.map f) (f t) = (centB L t).map f := by
  simp only [centB, List.filter_map, Function.comp_def, ← map_mul, hf.eq_iff]

theorem noOddB_map (B : ℕ) (C : List M) : noOddB B (C.map f) = noOddB B C := by
  simp only [noOddB, List.all_map, List.any_map, Function.comp_def, ← map_inv, ← map_mul,
    ordB_map f hf, ← map_one f, hf.eq_iff]

theorem q8B_map (t a b : M) : q8B (f t) (f a) (f b) = (q8B t a b).map f := by
  simp only [q8B, List.map_cons, List.map_nil, map_mul, map_one]

theorem pairsB_map (t : M) (C : List M) : pairsB (f t) (C.map f) = pairsB t C := by
  simp only [pairsB, List.filter_map, List.all_map, List.any_map, Function.comp_def, ← map_mul,
    ← map_inv, ← map_pow, ← map_one f, hf.eq_iff, q8B_map f hf, memB_map f hf]

theorem goodCheck_map (B : ℕ) (L : List M) : goodCheck B (L.map f) = goodCheck B L := by
  simp only [goodCheck, List.all_map, Function.comp_def, ne_eq, ← map_mul, ← map_one f, hf.eq_iff,
    centB_map f hf, noOddB_map f hf, pairsB_map f hf]

end Good

theorem goodCheck_ev {n : Nat} [Small n] (B : ℕ) (L : List (CV n)) :
    goodCheck B (L.map ev) = goodCheck B L :=
  goodCheck_map (evHom n) ev_injective B L

end CFSG.Certificates.Kernel.PkCV.KGrp

end
