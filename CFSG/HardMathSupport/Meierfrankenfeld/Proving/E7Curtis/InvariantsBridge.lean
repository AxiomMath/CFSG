module

public import Mathlib.RepresentationTheory.Invariants
public import CFSG.HardMathSupport.Meierfrankenfeld.Proving.E7Curtis.FixBaseChange

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.Proving.E7Curtis

theorem invariants_eq_iInf_ker {k G V : Type*} [CommRing k] [Group G] [AddCommGroup V]
    [Module k V] (ρ : Representation k G V) :
    Representation.invariants ρ = ⨅ g : G, LinearMap.ker (ρ g - 1) := by
  ext v
  rw [Representation.mem_invariants, Submodule.mem_iInf]
  refine forall_congr' fun g => ?_
  rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]

theorem finrank_invariants_le_of_matrix {K k : Type*} [Field K] [Field k] (ι : K →+* k)
    {G : Type*} [Group G] [Finite G] {m : ℕ}
    (ρ : Representation k G (Fin m → k)) (N : G → Matrix (Fin m) (Fin m) K)
    (hN : ∀ g, ρ g = Matrix.toLin' ((N g).map ι)) :
    Module.finrank k ↥(Representation.invariants ρ) ≤
      Module.finrank K ↥(⨅ g : G, LinearMap.ker (Matrix.toLin' (N g) - 1)) := by
  have h : (⨅ g : G, LinearMap.ker (ρ g - 1)) =
      ⨅ g : G, LinearMap.ker (Matrix.toLin' ((N g).map ι) - 1) :=
    iInf_congr fun g => by rw [hN g]
  rw [invariants_eq_iInf_ker, h]
  exact finrank_fix_map_le ι N

end CFSG.HardMathSupport.Meierfrankenfeld.Proving.E7Curtis
