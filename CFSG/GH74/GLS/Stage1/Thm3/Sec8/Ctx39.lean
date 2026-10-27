module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic9
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Closed

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8

theorem y34_E : Y34_E := by
  intro G _ _ Y U hY hUY hU4 hUN
  obtain ⟨e⟩ := hY
  obtain ⟨E₁, E₂, h1, h2, hc1, hs1, hc2, hs2, hcard1, hcard2, hint, hprod, hinv, hcomm⟩ :=
    Basic.exists_E_of_equiv e hUY hU4.2 hUN
  have hinv' : ∀ y ∈ Y, orderOf y = 2 → y ∈ E₁ ∨ y ∈ E₂ := fun y hy hy2 => by
    apply hinv y hy
    have := pow_orderOf_eq_one y
    rwa [hy2, pow_two] at this
  refine ⟨E₁, E₂, ⟨h1, h2, ⟨hc1, fun a ha => ?_⟩, ⟨hc2, fun a ha => ?_⟩, hcard1, hcard2, hint, hprod,
    hinv', hcomm⟩⟩
  · rw [pow_two]
    exact hs1 a ha
  · rw [pow_two]
    exact hs2 a ha

end CFSG.GH74.GLS.Stage1.Thm3.Sec8
