module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellJ.Defs
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellJ.Seven6
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellDouble

public section

namespace CFSG.QuasithinUnique.Setup.CampbellJ

open CFSG.QuasithinUnique.Setup.Campbell

variable {G : Type*} [Group G] [Finite G] {k : Type*} [Field k] [Finite k] {S : Sylow 2 G}
  {ρ : G →* Matrix.SpecialLinearGroup (Fin 2) k} {ψ : Ecore G →* Multiplicative (Fin 2 → k)}

theorem theoremA_J (h : IsSeed S ρ (Ecore G) ψ)
    {Λ : Subgroup (MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G)))} (hΛ : LamHyp S Λ)
    {α : MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))} (hα : α ∈ Λ) :
    ⁅Hone S, aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)⁆ ≤ Fcore G := by
  by_contra hcon
  obtain ⟨A, hA, hAQ, g, hgH, hgM, hg2⟩ := h.exists_A_g
  exact DoubleSetupJ.absurd
    (⟨h, hΛ, hα, hcon, hA, hAQ, hgH, hgM, hg2⟩ : DoubleSetupJ S ρ ψ Λ α A g)

end CFSG.QuasithinUnique.Setup.CampbellJ

end
