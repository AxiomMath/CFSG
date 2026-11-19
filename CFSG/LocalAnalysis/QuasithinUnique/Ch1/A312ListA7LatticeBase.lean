
module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListA7Enc
public meta import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListA7Enc
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListA7LatticeInputs

@[expose] public section

namespace CFSG.QuasithinUnique.Vol2Native.A312L.Seven

open Equiv CFSG.QuasithinUnique.Unc25K1.Six

def D7 : Subgroup P7 := Subgroup.closure {g | g ∈ dGens}

theorem setEq_spec {a b : Std.HashSet R7} (h : setEq a b = true) : ∀ x, x ∈ a ↔ x ∈ b := by
  simp only [setEq, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  intro x
  constructor
  · intro hx
    exact Std.HashSet.contains_iff_mem.mp (h.1.2 x (Std.HashSet.mem_toList.mpr hx))
  · intro hx
    exact Std.HashSet.contains_iff_mem.mp (h.2 x (Std.HashSet.mem_toList.mpr hx))

def IsLat (H : Subgroup P7) : Prop :=
  ∃ G ∈ latGens, H = Subgroup.closure {g | g ∈ G}

theorem D7_le_closure (l : List P7) : D7 ≤ Subgroup.closure {g | g ∈ dGens ++ l} :=
  Subgroup.closure_mono fun _ hg => List.mem_append_left _ hg

theorem dGens_mem_lat : dGens ∈ latGens := by
  simp [latGens]

end CFSG.QuasithinUnique.Vol2Native.A312L.Seven
