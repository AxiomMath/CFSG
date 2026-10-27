module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P6bA6
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P6bE25

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P6b

open Subgroup CFSG.Sporadic.Schreier.Tits CFSG.LocalAnalysis.EvenBN.Tits CFSG.Open

section Assembly

variable {G : Type} [Group G] [Finite G] {d : Data G} {z₀ : G}


theorem node23b_of_cores (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀)
    (hinv : d.S56Z0Inv) (h10 : Node10 d z₀) (h14 : Node14 d) (h17 : Node17 d z₀)
    (h19 : Node19 d z₀) (h23a : Node23a d z₀) (a6 : A6CoreStmt) (e25 : E25CoreStmt) :
    Node23b d z₀ := by
  obtain ⟨-, hVel, hcard, -⟩ := h10
  obtain ⟨-, -, -, hconj⟩ := h14
  obtain ⟨hCU, -⟩ := h17
  obtain ⟨-, -, -, -, hWimg, hUW, hWel, hWcard⟩ := h19
  obtain ⟨-, ⟨hWnorm, -⟩, ⟨hZW, hZH⟩, -, -, hWJ, hN, hcases⟩ := h23a
  have hc : ∀ a b : ↥d.s56V, a * b = b * a := fun a b => hVel.1.is_comm.comm a b
  have hs : ∀ a : ↥d.s56V, a * a = 1 := fun a => by
    have := hVel.2 a a.2
    exact Subtype.ext (by simpa [pow_two] using this)
  haveI : Fact (∀ a b : ↥d.s56V, a * b = b * a) := ⟨hc⟩
  haveI : Fact (∀ a : ↥d.s56V, a * a = 1) := ⟨hs⟩
  haveI := hN
  obtain ⟨h₀, hh₀, hh⟩ := hconj
  have hcomm := comm_VW_mem_Z h49 hd hz hinv hVel hcard hZH ⟨h₀, hh₀, hh⟩ hWimg hWnorm hWel
  refine (node23b_iff).2 ⟨commutator_eq_Z h49 hd hz hinv hVel hcard hZH ⟨h₀, hh₀, hh⟩ hWimg hWnorm
    hWel hZW hCU hUW hWcard, ?_⟩
  rcases hcases with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · exact Or.inl (node23b_A6 h49 hd hz hinv hcard hZH hh₀ hh hWimg hWnorm hWel hWJ hcomm e a6)
  · exact Or.inr (node23b_E25 h49 hd hz hinv hcard hZH hh₀ hh hWimg hWnorm hWel hWJ e e25)

end Assembly

end CFSG.LocalAnalysis.EvenBN.Tits.N.P6b
