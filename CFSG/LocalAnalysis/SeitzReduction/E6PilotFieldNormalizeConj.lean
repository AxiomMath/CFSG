module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotFieldNormalizeExists

public section

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Quasithin (perfectCore)

section Conj

variable (K : Type) [Field K]

theorem map_conj_rep_levi_high (N : E6Neighbour) :
    (E6Neighbour.high.levi K).map (MulAut.conj (N.rep K)).toMonoidHom = N.levi K := by
  rw [E6Neighbour.levi_high]
  exact map_conj_rep_a5Levi N

@[expose] noncomputable def highLeviConjEquiv (N : E6Neighbour) :
    ↥(E6Neighbour.high.levi K) ≃* ↥(N.levi K) :=
  ((MulAut.conj (N.rep K)).subgroupMap (E6Neighbour.high.levi K)).trans
    (MulEquiv.subgroupCongr (map_conj_rep_levi_high K N))

variable {K}

theorem coe_highLeviConjEquiv (N : E6Neighbour) (g : E6Neighbour.high.levi K) :
    (((highLeviConjEquiv K N g : N.levi K) : adjointGroup .E6 K) : ModGL .E6 K) =
      (N.rep K : ModGL .E6 K) * ((g : adjointGroup .E6 K) : ModGL .E6 K) *
        (N.rep K : ModGL .E6 K)⁻¹ :=
  rfl

theorem leviBaseChange_highLeviConjEquiv {k : Type} [Field k] (ι : k →+* K) (N : E6Neighbour)
    (x : E6Neighbour.high.levi k) :
    leviBaseChange ι N (highLeviConjEquiv k N x) =
      highLeviConjEquiv K N (leviBaseChange ι .high x) := by
  refine Subtype.ext (Subtype.ext ?_)
  rw [coe_leviBaseChange, coe_highLeviConjEquiv, coe_highLeviConjEquiv, map_mul, map_mul, map_inv,
    baseChangeGL_rep, coe_leviBaseChange]

variable {σ : K ≃+* K} {G : Type} [Group G] [Finite G] {L : Subgroup G}
  {e : L ≃* adjointGroup .E6 (fixSubfield σ)}

variable (e) in
@[expose] noncomputable def neighbourCoreConjEquiv (N : E6Neighbour) :
    ↥(neighbourCore e .high) ≃* ↥(neighbourCore e N) :=
  ((MulAut.conj ((e.symm (N.rep (fixSubfield σ)) : L) : G)).subgroupMap
    (neighbourCore e .high)).trans (MulEquiv.subgroupCongr (neighbourCore_eq_map_conj e N).symm)

end Conj

end CFSG.SeitzReduction.E6Pilot
