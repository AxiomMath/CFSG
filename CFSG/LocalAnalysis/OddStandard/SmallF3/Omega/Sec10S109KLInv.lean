module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10S109Ce
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10S109KL

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec10C_kl_L [Finite G] (hKL : Asc82StepKL) (h3 : Asc82Sec3Res10) (h : Asc82Res10a)
    (hf : Asc82Facts10) (hb : Asc82Basic10) {t : G} {L S : Subgroup G} {z : G}
    {K1 K2 : Subgroup G} {g : G} (hctx : Sec109Ctx G t L S z K1 K2 g) {u : G} (hu : u ∈ L)
    (hty : InducesTypeSome L u 5 1 2 (-1)) : ¬ ∃ k : G, k⁻¹ * t * k = t * u := by
  obtain ⟨hpsp, htC, -⟩ := hb G t L S z hctx.toSec10Z
  obtain ⟨z', u0, -, -, -, -, hu0B, hu02, hu0ty, hu0z, -⟩ := sec10C_Zdata h3 h hf hb hctx
  obtain ⟨l, hl, hlu⟩ := hf.factsC.i2m G L hpsp u0 u (secB_le_L S L hu0B) hu hu0ty hty
  rintro ⟨k, hk⟩
  have hlt : l * t = t * l := Subgroup.mem_centralizer_iff.mp htC l hl
  refine hKL G t L S z K1 K2 g hctx u0 hu0B hu02 hu0ty hu0z ⟨k * l⁻¹, ?_⟩
  rw [← hlu] at hk
  calc (k * l⁻¹)⁻¹ * t * (k * l⁻¹) = l * (k⁻¹ * t * k) * l⁻¹ := by group
    _ = l * (t * (l⁻¹ * u0 * l)) * l⁻¹ := by rw [hk]
    _ = (l * t) * l⁻¹ * u0 := by group
    _ = (t * l) * l⁻¹ * u0 := by rw [hlt]
    _ = t * u0 := by group

end CFSG.OddStandard.SmallF3.Omega
