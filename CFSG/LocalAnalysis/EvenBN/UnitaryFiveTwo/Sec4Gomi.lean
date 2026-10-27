module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec5KNine

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Open

@[expose] def GomiU42Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (d : Data G), d.Hyp →
    d.K ⊓ d.H = d.K₃ ∧
      (CFSG.Blueprint.LieModel d.K .PSL 4 2 2 ∨
        ∃ K₀ : Subgroup G, CFSG.Blueprint.LieModel K₀ .PSU 4 2 1 ∧
          d.K = K₀ ⊔ K₀.map (MulAut.conj d.t).toMonoidHom ∧
          ⁅K₀, K₀.map (MulAut.conj d.t).toMonoidHom⁆ = ⊥ ∧
          K₀ ⊓ K₀.map (MulAut.conj d.t).toMonoidHom = ⊥)

structure Data.KUnitary {G : Type} [Group G] (d : Data G) : Prop where
  centralizer_eq : d.K ⊓ d.H = d.K₃
  swap : ∃ K₀ : Subgroup G, CFSG.Blueprint.LieModel K₀ .PSU 4 2 1 ∧
    d.K = K₀ ⊔ K₀.map (MulAut.conj d.t).toMonoidHom ∧
    ⁅K₀, K₀.map (MulAut.conj d.t).toMonoidHom⁆ = ⊥ ∧
    K₀ ⊓ K₀.map (MulAut.conj d.t).toMonoidHom = ⊥

namespace Data.Hyp

variable {G : Type} [Group G] [Finite G] {d : Data G}

theorem kLinear_or_kUnitary (hG : GomiU42Input) (h : d.Hyp) : d.KLinear ∨ d.KUnitary := by
  obtain ⟨hC, hm | hu⟩ := hG G d h
  · exact Or.inl (h.kLinear_of_lieModel hC hm)
  · exact Or.inr ⟨hC, hu⟩

end Data.Hyp

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
