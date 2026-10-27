module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpSmSMCheck
public import Certificates.Data.GH74.PSp43NoQ8
public import Certificates.Data.TL4MF163U3Inv
public import Certificates.Data.TL4LieZ2Inv
public import Certificates.Data.Kernel.ONanSmall.P43Gen

public section

namespace CFSG.Certificates.Kernel.ONanSmall

open CFSG.ClassicalInvolution.Q3.TA3.Check

variable {M N : Type*} [Group M] [DecidableEq M] [Group N] [DecidableEq N]
  (f : M →* N) (hf : Function.Injective f)

include hf

theorem memB_map (l : List M) (x : M) : memB (l.map f) (f x) = memB l x := by
  simp only [memB, List.any_map, Function.comp_def, hf.eq_iff]

theorem q8B_map (t a b : M) : q8B (f t) (f a) (f b) = (q8B t a b).map f := by
  simp [q8B, map_mul]

theorem centB_map (L : List M) (t : M) : centB (L.map f) (f t) = (centB L t).map f := by
  simp only [centB, List.filter_map, Function.comp_def, ← map_mul, hf.eq_iff]

theorem ordAux_map (o : M) : ∀ fuel k, ordAux (f o) fuel k = ordAux o fuel k
  | 0, _ => rfl
  | fuel + 1, k => by
    simp only [ordAux, ← map_pow, map_eq_one_iff f hf, ordAux_map o fuel]

theorem ordB_map (B : ℕ) (o : M) : ordB B (f o) = ordB B o := ordAux_map f hf o B 1

theorem noOddB_map (B : ℕ) (C : List M) : noOddB B (C.map f) = noOddB B C := by
  simp only [noOddB, List.all_map, List.any_map, Function.comp_def, ← map_mul, ← map_inv,
    ordB_map f hf, map_eq_one_iff f hf]

theorem noOddB3_map (B : ℕ) (C : List M) : noOddB3 B (C.map f) = noOddB3 B C := by
  simp only [noOddB3, List.all_map, List.any_map, Function.comp_def, ← map_mul, ← map_inv,
    ordB_map f hf, map_eq_one_iff f hf]

theorem edgelessB_map (L : List M) (t a b : M) :
    edgelessB (L.map f) (f t) (f a) (f b) = edgelessB L t a b := by
  simp only [edgelessB, q8B_map f hf, List.all_map, List.any_map, Function.comp_def, ← map_mul,
    ← map_inv, hf.eq_iff]

theorem noActs3B_map (B : ℕ) (C : List M) (a b : M) :
    noActs3B B (C.map f) (f a) (f b) = noActs3B B C a b := by
  simp only [noActs3B, List.all_map, Function.comp_def, ← map_mul, ordB_map f hf, hf.eq_iff]

theorem filter_sq_map (C : List M) (t : M) :
    (C.map f).filter (fun a => decide (a * a = f t)) =
      (C.filter fun a => decide (a * a = t)).map f := by
  simp only [List.filter_map, Function.comp_def, ← map_mul, hf.eq_iff]

theorem pairsV_map (B : ℕ) (LN L : List M) (e3b : Bool) (t : M) (C : List M) :
    pairsV B (LN.map f) (L.map f) e3b (f t) (C.map f) = pairsV B LN L e3b t C := by
  simp only [pairsV, filter_sq_map f hf, List.all_map, List.any_map, Function.comp_def, ← map_mul,
    ← map_inv, ← map_pow, q8B_map f hf, memB_map f hf, edgelessB_map f hf, noActs3B_map f hf,
    hf.eq_iff, map_eq_one_iff f hf]

theorem isCovered_map (L reps : List M) (t : M) :
    isCovered (L.map f) (reps.map f) (f t) = isCovered L reps t := by
  simp only [isCovered, List.any_map, Function.comp_def, ← map_mul, ← map_inv, hf.eq_iff]

theorem coverB_map (reps L : List M) : coverB (reps.map f) (L.map f) = coverB reps L := by
  simp only [coverB, List.all_map, Function.comp_def, ← map_mul, isCovered_map f hf, ne_eq,
    map_eq_one_iff f hf]

theorem pickReps_map (L : List M) : pickReps (L.map f) = (pickReps L).map f := by
  unfold pickReps
  have key : ∀ (L' : List M) (R : List M),
      (L'.map f).foldl (fun reps t => if decide (t * t = 1 ∧ t ≠ 1) &&
          !isCovered (L.map f) reps t then reps ++ [t] else reps) (R.map f) =
        (L'.foldl (fun reps t => if decide (t * t = 1 ∧ t ≠ 1) && !isCovered L reps t
          then reps ++ [t] else reps) R).map f := by
    intro L'
    induction L' with
    | nil => intro R; rfl
    | cons x L' ih =>
      intro R
      simp only [List.map_cons, List.foldl_cons]
      rw [← ih]
      congr 1
      simp only [isCovered_map f hf, ← map_mul, ne_eq, map_eq_one_iff f hf]
      split <;> simp
  simpa using key L []

theorem verdictCheck_map (B : ℕ) (LN L : List M) (e3b : Bool) (reps : List M) :
    verdictCheck B (LN.map f) (L.map f) e3b (reps.map f) = verdictCheck B LN L e3b reps := by
  simp only [verdictCheck, coverB_map f hf, List.all_map, Function.comp_def, centB_map f hf,
    noOddB3_map f hf, pairsV_map f hf]

open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small.SM in
theorem nqCheck_map (inX : N → Bool) (L reps : List M) :
    nqCheck inX (L.map f) (reps.map f) = nqCheck (fun x => inX (f x)) L reps := by
  simp only [nqCheck, nqAt, coverB_map f hf, List.all_map, Function.comp_def, centB_map f hf,
    filter_sq_map f hf, ← map_mul, ← map_inv, q8B_map f hf, memB_map f hf, hf.eq_iff]

theorem noQ8Check_map (L reps : List M) :
    Certificates.PSp43NoQ8.noQ8Check (L.map f) (reps.map f) =
      Certificates.PSp43NoQ8.noQ8Check L reps := by
  simp only [Certificates.PSp43NoQ8.noQ8Check, Certificates.PSp43NoQ8.noQ8PairsB, List.all_map,
    Function.comp_def, centB_map f hf, filter_sq_map f hf, ← map_mul, ← map_inv, q8B_map f hf,
    memB_map f hf, hf.eq_iff]

theorem centInvCheck_map (LN L reps : List M) :
    Certificates.TL4MF163U3Inv.centInvCheck (LN.map f) (L.map f) (reps.map f) =
      Certificates.TL4MF163U3Inv.centInvCheck LN L reps := by
  simp only [Certificates.TL4MF163U3Inv.centInvCheck, Certificates.TL4MF163U3Inv.centInvAt,
    List.all_map, Function.comp_def, centB_map f hf, filter_sq_map f hf, ← map_mul, ← map_inv,
    ← map_pow, q8B_map f hf, memB_map f hf, hf.eq_iff, map_eq_one_iff f hf]

theorem q8InvCheck_map (LP LA reps : List M) :
    Certificates.TL4LieZ2Inv.q8InvCheck (LP.map f) (LA.map f) (reps.map f) =
      Certificates.TL4LieZ2Inv.q8InvCheck LP LA reps := by
  simp only [Certificates.TL4LieZ2Inv.q8InvCheck, Certificates.TL4LieZ2Inv.q8InvAt,
    coverB_map f hf, List.all_map, Function.comp_def, centB_map f hf, filter_sq_map f hf, ← map_mul,
    hf.eq_iff, map_eq_one_iff f hf]

theorem p43_checkG_map (L0 LA : List M) (tA tB t36 t540 a1 b1 a2 b2 x1 x2 : M) :
    Certificates.P43Gen.checkG (L0.map f) (LA.map f) (f tA) (f tB) (f t36) (f t540) (f a1) (f b1)
      (f a2) (f b2) (f x1) (f x2) =
      Certificates.P43Gen.checkG L0 LA tA tB t36 t540 a1 b1 a2 b2 x1 x2 := by
  have hc : ∀ (L Q : List M), Certificates.P43Gen.centQG (L.map f) (Q.map f) =
      (Certificates.P43Gen.centQG L Q).map f := fun L Q => by
    simp only [Certificates.P43Gen.centQG, List.filter_map, List.all_map, Function.comp_def,
      ← map_mul, hf.eq_iff]
  have hs : ∀ l m : List M, Certificates.P43Gen.setEqG (l.map f) (m.map f) =
      Certificates.P43Gen.setEqG l m := fun l m => by
    simp only [Certificates.P43Gen.setEqG, List.all_map, Function.comp_def, memB_map f hf]
  have h2 : [f tA, f tB] = [tA, tB].map f := rfl
  have h4 : [f tA, f tB, f t36, f t540] = [tA, tB, t36, t540].map f := rfl
  simp only [Certificates.P43Gen.checkG, Certificates.P43Gen.localChkG,
    Certificates.P43Gen.pairChkG, Certificates.P43Gen.pairOKG, Certificates.P43Gen.sigmaChkG,
    q8B_map f hf, h2, h4, coverB_map f hf, List.all_map, Function.comp_def, centB_map f hf,
    noOddB_map f hf, filter_sq_map f hf, ← map_mul, ← map_inv, ← map_pow, hs, hc,
    ← List.map_append, memB_map f hf, List.length_map, hf.eq_iff, map_eq_one_iff f hf,
    ordB_map f hf]
  rfl

end CFSG.Certificates.Kernel.ONanSmall
