module

public import Certificates.Data.Kernel.PermCent.SmallF3Twin
public import CFSG.Certificates.Kernel.PermCent.CVSound
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GXC6Chk
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FHChk
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoL33Check
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbC414Defs

public section

namespace CFSG.Certificates.Kernel.PkCV.SmallF3T

open CFSG.OddStandard.SmallF3.Omega CFSG.ComponentClassification.RankTwoL33
  CFSG.OddStandard.SmallF3.HarrisU33.S4B

variable {n : Nat} [Small n]

theorem c6free_C (LA LP : List (CV n)) : c6free (LA.map ev) (LP.map ev) = c6freeC LA LP := by
  unfold c6free c6freeC
  simp only [List.filter_map, List.all_map, Function.comp_def, ev_pow', ev_mul', one_eq_ev,
    decide_ev_eq, pow_fast, comm_fast, ne_eq, decide_not]

theorem fhO3Chk_C (LA LP : List (CV n)) : fhO3Chk (LA.map ev) (LP.map ev) = fhO3C LA LP := by
  unfold fhO3Chk fhO3C
  simp only [List.filter_map, List.all_map, List.any_map, Function.comp_def, ev_pow', ev_mul',
    ev_inv', one_eq_ev, decide_ev_eq, pow_fast, comm_fast, ne_eq, decide_not]

theorem fourGenCheck_C (LA LP : List (CV n)) :
    fourGenCheck (LA.map ev) (LP.map ev) = fourGenC LA LP := by
  unfold fourGenCheck cent48Check order13Check order13Pair
    CFSG.ComponentClassification.RankTwoL33.centList invList fourGenC
    cent48C
    order13C order13PairC centListC invListC
  simp only [List.filter_map, List.all_map, List.any_map, List.length_map, Function.comp_def,
    ev_pow', ev_mul', one_eq_ev, decide_ev_eq, pow_fast, comm_fast, ne_eq, decide_not]

theorem allFin_cube {m : Nat} (σ : Equiv.Perm (Fin m)) :
    (List.finRange m).all (fun i => σ (σ (σ i)) == i) = decide (σ * σ * σ = 1) :=
  allFin_id (σ * σ * σ)

theorem cent3OddAll_C (LA LP : List (CV 28)) :
    cent3OddAll (LA.map ev) (LP.map ev) = cent3OddAllC LA LP := by
  unfold cent3OddAll cent3OddB order3B cubeOneB isOneB sqOneB
    CFSG.OddStandard.SmallF3.HarrisU33.S4B.centList commB cent3OddAllC
  simp only [List.filter_map, List.all_map, List.length_map, Function.comp_def, allFin_cube,
    allFin_sq, allFin_comm, allFin_id, ev_mul', one_eq_ev, decide_ev_eq, sift_ev, sq_fast,
    comm_fast]

end CFSG.Certificates.Kernel.PkCV.SmallF3T

end
