module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P3S14D
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P3S14C

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits.N

open Subgroup CFSG.Open CFSG.Sporadic.Schreier.Tits

section S14E

variable {G : Type} [Group G] [Finite G] {d : Data G} {z₀ : G}


theorem node14 (h49 : d.Thm49Statement) (hd : d.Hyp) (h10 : Node10 d z₀) (h11 : Node11 d z₀)
    (h12 : Node12 d z₀) (h13 : Node13 d) : Node14 d := by
  refine ⟨fun s hs hsH => six_five hd h10 h12 h13 hs hsH, ?_, ?_⟩
  ·
    obtain ⟨g, -, hg⟩ := exists_P1_conj_t_mul_pv7 h13
    have hs : d.t * d.pv 7 ∈ d.tG := ⟨g, hg⟩
    have hsH : d.t * d.pv 7 ∈ Hg d :=
      M_le_Hg h49 hd (mul_mem t_mem_M (pv7_mem_M hd))
    rcases six_five hd h10 h12 h13 hs hsH with h | ⟨hP1a, -, k, hkt, hDB, hVP⟩
    · exact h
    · exact (six_six_false h49 hd h11 h13 hP1a hkt hDB hVP).elim
  ·
    have hs : d.t * d.pv 2 ∈ d.tG := t_mul_pv2_mem_tG hd
    have hsH : d.t * d.pv 2 ∈ Hg d :=
      M_le_Hg h49 hd (mul_mem t_mem_M (pv2_mem_M hd))
    rcases six_five hd h10 h12 h13 hs hsH with h | ⟨hP1a, -, k, hkt, hDB, hVP⟩
    · exact h
    · exact (six_seven_false h49 hd h11 h13 hP1a hkt hDB hVP).elim

theorem step14_holds : Step14 := by
  intro G _ _ d z₀ h49 hd hz h10 h11 h12 h13
  exact node14 h49 hd h10 h11 h12 h13

end S14E

end CFSG.LocalAnalysis.EvenBN.Tits.N
