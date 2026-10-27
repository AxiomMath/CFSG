module

public import CFSG.GF2Type.CenterFour.CaseACount
public import CFSG.GF2Type.CenterFour.CaseBOne
public import CFSG.GF2Type.CenterFour.CaseBTwo
public import CFSG.GF2Type.CenterFour.CaseBPsi

public section

namespace CFSG.GF2Type.CenterFour

open Subgroup

variable {G : Type} [Group G] [Finite G] {z : G} {n : ℕ}

theorem Config.false (hC : Config z n) : False := by
  by_cases hA : CaseA z
  · exact CaseA.false hC hA
  · have hA' : ∃ w : G, Fused z w ∧ w ∈ centralizer ({z} : Set G) ∧
        w ∉ centralizer (centerAt z : Set G) := by
      by_contra hcon
      apply hA
      intro w hw hwH
      by_contra hwK
      exact hcon ⟨w, hw, hwH, hwK⟩
    obtain ⟨w, ⟨g, rfl⟩, hH, hK⟩ := hA'
    rcases CaseB.dichotomy hC hH hK with hall | ⟨hq, hJ⟩
    · exact CaseB.false_of_forall_mem hC hH hK hall
    · exact CaseB.false_of_exists_not_mem hC hH hK hq hJ

end CFSG.GF2Type.CenterFour
