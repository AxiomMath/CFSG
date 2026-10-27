module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD309Cfg

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD309L

open Subgroup CFSG.Open
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD309
open scoped commutatorElement

variable {Y Y' : Type} [Group Y] [Group Y']

theorem conjSub_map (f : Y →* Y') (n : Y) (P : Subgroup Y) :
    conjSub (f n) (P.map f) = (conjSub n P).map f := by
  ext x
  rw [mem_conjSub, Subgroup.mem_map]
  constructor
  · rintro ⟨p', ⟨p, hp, rfl⟩, rfl⟩
    exact ⟨n * p * n⁻¹, mem_conjSub.mpr ⟨p, hp, rfl⟩, by simp⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨p, hp, rfl⟩ := mem_conjSub.mp hy
    exact ⟨f p, Subgroup.mem_map_of_mem f hp, by simp⟩

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD309L
