module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.Sec217Global
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.PerfectCore

public section

open scoped commutatorElement

namespace CFSG.AGLEmbeddingD2.Wilson.Proving

open Subgroup CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

theorem perfCore_map_of_greatest {G H : Type} [Group G] [Group H]
    (ι : H →* G) (hι : Function.Injective ι) (C I : Subgroup H) (hI : I ≤ C)
    (hperf : ⁅I, I⁆ = I)
    (hmax : ∀ P : Subgroup H, P ≤ C → ⁅P, P⁆ = P → P ≤ I) :
    perfCore (C.map ι) = I.map ι := by
  apply le_antisymm
  · unfold perfCore
    refine sSup_le fun P hP => ?_
    obtain ⟨hPC, hPp⟩ := hP
    have hPrange : P ≤ ι.range := hPC.trans (Subgroup.map_le_range ι C)
    have hmapP : (P.comap ι).map ι = P := Subgroup.map_comap_eq_self hPrange
    have hP'C : P.comap ι ≤ C := by
      intro x hx
      have h1 : ι x ∈ C.map ι := hPC hx
      obtain ⟨c, hc, hcx⟩ := Subgroup.mem_map.mp h1
      rw [← hι hcx]
      exact hc
    have hP'perf : ⁅P.comap ι, P.comap ι⁆ = P.comap ι := by
      apply Subgroup.map_injective hι
      rw [Subgroup.map_commutator, hmapP, hPp]
    have hP'I : P.comap ι ≤ I := hmax _ hP'C hP'perf
    calc P = (P.comap ι).map ι := hmapP.symm
      _ ≤ I.map ι := Subgroup.map_mono hP'I
  · unfold perfCore
    apply le_sSup
    refine ⟨Subgroup.map_mono hI, ?_⟩
    rw [← Subgroup.map_commutator, hperf]

end CFSG.AGLEmbeddingD2.Wilson.Proving

end
