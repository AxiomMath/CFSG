module

public import CFSG.GH74.GLS.Bg.Iii2.ExtE

public section

namespace CFSG.GH74.GLS.Bg.Iii2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec6

theorem extP_of (hPU : PU) (hCM : CM) (h43d : II4_43d) (hquat : II4_4_quat) : ExtP := by
  intro G _ _ hG h3 hex
  obtain ⟨x₀, K₀, h₀⟩ := hex
  have hX : ({x : G | orderOf x = 2 ∧ ∃ K, IsRigidRankOneComp x K} : Set G).Nonempty :=
    ⟨x₀, rr_ord h₀, K₀, h₀⟩
  obtain ⟨x, ⟨hx, hne⟩, hext⟩ := exists_lex_max hX rrNum cLog rrMem
  obtain ⟨T, hT⟩ := ext_of_max hPU hCM h43d hquat hG h3 hx hne
    (fun y hy hJ => (hext y ⟨hy, hJ⟩).1)
    (fun y hy hJ h => ((hext y ⟨hy, hJ⟩).2 h).1)
    (fun y hy hJ h h' => ((hext y ⟨hy, hJ⟩).2 h).2 h')
  exact ⟨x, T, hT⟩

end CFSG.GH74.GLS.Bg.Iii2
