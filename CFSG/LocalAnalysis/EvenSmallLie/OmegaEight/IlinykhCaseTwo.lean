module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.IlinykhStars
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.IlinykhNine

public section

namespace CFSG.EvenSmallLie.OmegaEight

theorem normalizer_fixes_frameZ {N : Type*} [Group N] [MulAction N FrameVec]
    (hadd : ∀ (n : N) (x y : FrameVec), n • (x + y) = n • x + n • y)
    (hup : ∀ n : N, n • frameZ = frameZ → ∃ σ ∈ frameAut, ∀ v, n • v = permVec σ v)
    (hgen : ∀ σ ∈ frameGens, ∃ n : N, ∀ v, n • v = permVec σ v)
    (hplane : ∀ n : N, ∀ B ∈ frameBlocks, n • frameZ ≠ blockVec B) :
    ∀ n : N, n • frameZ = frameZ := by
  intro n
  rcases orbit_frameZ_cases hadd hgen hplane with h | h | h | h
  · have hn : n • frameZ ∈ MulAction.orbit N frameZ := MulAction.mem_orbit _ n
    rw [h] at hn
    exact hn
  · exact absurd h (orbit_ne_frameNine hup hgen)
  · exact absurd h (orbit_ne_frameNine' hup hgen)
  · exact absurd h (orbit_ne_frameFortyFive hadd hup)

end CFSG.EvenSmallLie.OmegaEight
