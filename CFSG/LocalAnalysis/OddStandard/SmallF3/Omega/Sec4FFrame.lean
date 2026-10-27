module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FOrder
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Conj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Struct

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec4_frame_lemma [Finite G] (h39 : Asc82Lemma39) (hk6 : Asc82FactK6) {t : G}
    {L S : Subgroup G} {z : G} (hctx : Sec4Ctx G t L S z) {g : G}
    (hg6 : InducesTypeSome L (g⁻¹ * t * g) 7 1 6 1) {v : G} (hvL : v ∈ L)
    (hvL' : v ∈ CFSG.conjugate L g) (hv2 : orderOf v = 2)
    (h6 : InducesTypeSome L v 7 1 6 (-1))
    (h6' : InducesTypeSome (CFSG.conjugate L g) v 7 1 6 (-1)) : False := by
  have hL : IsOmega7Group L := sec4_isOmega7Group hctx.toSec4Setting
  have hL' : IsOmega7Group (CFSG.conjugate L g) :=
    sec4_isOmega7Group (hctx.conjugate g).toSec4Setting
  obtain ⟨K, hKcomp, hvK, hKU⟩ := hk6 G L hL v hvL hv2 h6
  obtain ⟨K', hK'comp, hvK', hK'U⟩ := hk6 G (CFSG.conjugate L g) hL' v hvL' hv2 h6'
  obtain ⟨hKcent, hKF, huniq⟩ :=
    h39 G t L hctx.toSec3SettingLB v K hv2 hvL hvK hKcomp hKU
  obtain ⟨hK'cent, hK'F, -⟩ :=
    h39 G (g⁻¹ * t * g) (CFSG.conjugate L g) (hctx.conjugate g).toSec3SettingLB
      v K' hv2 hvL' hvK' hK'comp hK'U
  have hK'eqK : K' = K := huniq K' hK'cent hK'F
  have hKL : K ≤ L := hKcomp.le.trans inf_le_left
  have hKleL' : K ≤ CFSG.conjugate L g := by
    rw [← hK'eqK]
    exact hK'comp.le.trans inf_le_left
  have hKs : K ≤ centralizer ({g⁻¹ * t * g} : Set G) := by
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact (Subgroup.mem_centralizer_iff.mp
      (sec4_t_mem_centralizer (hctx.conjugate g).toSec3Setting) k (hKleL' hk)).symm
  exact sec4F_no_twoU43_cent hL hg6 hKcomp.isQuasisimple hKL hKs hKU

end CFSG.OddStandard.SmallF3.Omega
