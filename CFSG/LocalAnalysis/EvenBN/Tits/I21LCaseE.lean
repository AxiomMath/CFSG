module

public import CFSG.LocalAnalysis.EvenBN.Tits.I21LCaseER
public import CFSG.LocalAnalysis.EvenBN.Tits.I21LCaseES
public import CFSG.LocalAnalysis.EvenBN.Tits.I21LThmDefs

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.I21L

open Module Subgroup CFSG.Open

section CaseE

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {Y : Type*} [Group Y] [Finite Y]
  {ρ : Y →* (V ≃ₗ[ZMod 2] V)} {t u x h : Y}

theorem case_E25 (H : HypYW ρ t u x h) (hxO : x ∈ standardComponentOddCore Y) :
    Nonempty (normalClosure ({x} : Set Y) ≃* Multiplicative (ZMod 5) × Multiplicative (ZMod 5)) ∧
      Thm107P ρ t := by
  have hsh : E25Shape ρ x t := E25Shape.of_hypM H.toHypM (e25_abelian H hxO)
  obtain ⟨hZ, hP3, hE1, hE2⟩ := e25_struct H hsh
  obtain ⟨hP1, hP2⟩ := e25_ranks H hsh
  exact ⟨hZ, hP1, hP2, hP3, hE1, hE2⟩

end CaseE

end CFSG.LocalAnalysis.EvenBN.Tits.I21L
