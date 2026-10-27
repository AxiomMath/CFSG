module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.SmallQ3Check
public import CFSG.Certificates.Kernel.ONanSmall.MapSound
public import CFSG.Certificates.Kernel.ONanSmall.CoverSound

public section

namespace CFSG.Certificates.Kernel.ONanSmall

open CFSG.ClassicalInvolution.Q3.TA3.Check CFSG.CGT.PushingUpLit.SolKNA.R4.Check

section Map

variable {M N : Type*} [Group M] [DecidableEq M] [Group N] [DecidableEq N]
  (f : M →* N) (hf : Function.Injective f)

include hf

theorem q16At_map (t : M) (C : List M) : q16At (f t) (C.map f) = q16At t C := by
  simp only [q16At, List.filter_map, List.all_map, Function.comp_def, ← map_pow, ← map_mul,
    ← map_inv, hf.eq_iff]

theorem noQ16Check_map (L reps : List M) :
    noQ16Check (L.map f) (reps.map f) = noQ16Check L reps := by
  simp only [noQ16Check, coverB_map f hf, List.all_map, Function.comp_def, centB_map f hf,
    q16At_map f hf]

end Map

theorem noQ16Check_pickReps {M : Type*} [Group M] [DecidableEq M] {L : List M}
    (h1 : (1 : M) ∈ L) :
    noQ16Check L (pickReps L) = (pickReps L).all fun t => q16At t (centB L t) := by
  rw [noQ16Check, coverB_pickReps h1, Bool.true_and]

end CFSG.Certificates.Kernel.ONanSmall

end
