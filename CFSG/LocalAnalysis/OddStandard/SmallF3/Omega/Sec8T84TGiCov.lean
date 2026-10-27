module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2OutLayer
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFShapesAux

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem sec8t84t_gi_of_cover {C : Type} [Group C] {B : Type} [Group B] {ρ : C →* B}
    (hρ : OddCentralCover ρ) (E : Subgroup B) [E.Normal] (hE : IsSimpleGroup ↥E)
    (hnc : ∃ a b : ↥E, a * b ≠ b * a)
    (hcent : ∀ c : B, (∀ e ∈ E, c * e = e * c) → c = 1)
    (hinv : ∀ b : B, b * b = 1 → b ∈ E) {l : C}
    (hl : ∀ y ∈ CFSG.layer C, l * l * y = y * (l * l)) :
    ∃ y ∈ CFSG.layer C, l * y⁻¹ ∈ ρ.ker := by
  have hEl : E ≤ CFSG.layer B := by
    have hlay : CFSG.layer B = sSup {K : Subgroup B | CFSG.IsComponent K} := rfl
    rw [hlay]
    exact le_sSup ⟨ff_isQuasisimple_of_simple hE hnc, Subgroup.Normal.isSubnormal ‹_›⟩
  have hEmap : E ≤ (CFSG.layer C).map ρ := hEl.trans hρ.layer_le_map_layer
  have hsq : ρ l * ρ l = 1 := by
    apply hcent
    intro e he
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp (hEmap he)
    have h := congrArg ρ (hl y hy)
    simpa only [map_mul] using h
  have hρlE : ρ l ∈ E := hinv (ρ l) hsq
  obtain ⟨y, hy, hyl⟩ := Subgroup.mem_map.mp (hEmap hρlE)
  refine ⟨y, hy, ?_⟩
  rw [MonoidHom.mem_ker, map_mul, map_inv, hyl, mul_inv_cancel]

end CFSG.OddStandard.SmallF3.Omega
