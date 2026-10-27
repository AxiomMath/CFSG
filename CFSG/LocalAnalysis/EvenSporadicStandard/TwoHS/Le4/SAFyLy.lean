module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFyNorm

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup

@[expose] def Sect8InputLy : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (f s y : G) (S₀ : Subgroup G) (n : G),
    Sect7Hyps G L f s y S₀ n → ∀ w : G, w * f ^ 2 = f ^ 2 * w → w ∉ L ⊔ zpowers f →
      (∃ g : G, w = g⁻¹ * f ^ 2 * g) → ∃ m : G, m * f ^ 2 = f ^ 2 * m ∧ w = m * y * m⁻¹

theorem sect8InputFy_of_ly (hLy : Sect8InputLy) : Sect8InputFy := by
  intro G _ _ L f s y S₀ n hH w hw hwy hwf g hg
  obtain ⟨m, hm, hwm⟩ := hLy G L f s y S₀ n hH w hw hwf ⟨g, hg⟩
  apply hwy
  rw [hwm]
  exact (hH.normalizes_y hm y).1 (Subgroup.mem_sup_right (mem_zpowers y))

end CFSG.EvenSporadicStandard.TwoHS
