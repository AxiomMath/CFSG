module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FLemmaP
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FTri
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4ZStar

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec4F_tu_conj [Finite G] (I : Sec4FInputs) {t : G} {L S : Subgroup G} {z : G}
    (hctx : Sec4Ctx G t L S z) (hnot : ¬ ∃ h : G, h⁻¹ * t * h = t * z) {u : G} (huL : u ∈ L)
    (hu2 : orderOf u = 2) (hu6 : InducesTypeSome L u 7 1 6 (-1)) :
    ∃ h : G, t * u = h⁻¹ * t * h := by
  obtain ⟨s, hs, hsc, hst⟩ := sec4_exists_conj_commuting hctx.simple
    (sec4_nonabelian hctx.toSec3Setting) hctx.involution
  rcases sec4_conj_tri I.h36 I.h39 I.h42 I.h43 I.hf43c I.hf214 I.hin6 I.hk6 hctx hs hsc hst with
    hz | ⟨u₀, hu₀L, hu₀2, hu₀6, hsu⟩ | hs6
  · exact absurd hz hnot
  · obtain ⟨l, hl, hlu⟩ := I.hf6 G L (sec4_isOmega7Group hctx.toSec4Setting) u₀ u hu₀L huL
      hu₀2 hu2 hu₀6 hu6
    obtain ⟨h, hh⟩ := hs
    have htC : t * l = l * t :=
      (Subgroup.mem_centralizer_iff.mp (sec4_t_mem_centralizer
        hctx.toSec4Setting.toSec3SettingLB.toSec3Setting) l hl).symm
    refine ⟨h * l⁻¹, ?_⟩
    have h1 : t * u = l * (t * u₀) * l⁻¹ := by
      rw [hlu]
      calc t * (l * u₀ * l⁻¹) = (t * l) * u₀ * l⁻¹ := by group
        _ = (l * t) * u₀ * l⁻¹ := by rw [htC]
        _ = l * (t * u₀) * l⁻¹ := by group
    rw [h1, ← hsu, hh]
    group
  · exact sec4_lemmaP I.h36 I.h39 I.hk6 I.hf6 I.hD I.hABC hctx hs hsc hs6 huL hu2 hu6

end CFSG.OddStandard.SmallF3.Omega
