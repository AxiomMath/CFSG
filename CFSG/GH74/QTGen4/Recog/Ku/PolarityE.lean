module

public import CFSG.GH74.QTGen4.Recog.Ku.PolarityD
public import CFSG.GH74.QTGen4.Recog.Ku.PolarityC

public section

namespace CFSG.GH74.QTGen4.Ku

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13

variable {G : Type} [Group G]

namespace KuHyp

variable [Finite G] {T M H P : Subgroup G} {z : G}

theorem kuPolar_mul_left [KuLeaf LeafCardKuA] [KuLeaf LeafIsMulCommutativeKuA]
    [KuLeaf LeafHInfCentralizerKuA] [KuLeaf LeafEqKuAOfElemAbelian]
    [KuLeaf LeafTInfCentralizerKuWLeKuA] [KuLeaf LeafKuV2LeKuW]
    (h : KuHyp G T M H P z) {x₁ x₂ : G} (hx₁ : x₁ ∈ kuA P H)
    (hx₂ : x₂ ∈ kuA P H) {y : G} (hy : y ∈ kuA P H) :
    kuPolar P H z (x₁ * x₂) y = kuPolar P H z x₁ y + kuPolar P H z x₂ y := by
  rw [h.kuPolar_symm (Subgroup.mul_mem _ hx₁ hx₂) hy, h.kuPolar_mul hx₁ hx₂ y,
    h.kuPolar_symm hx₁ hy, h.kuPolar_symm hx₂ hy]

theorem exists_kuPolar_ne_zero_right [KuLeaf LeafCardKuA] [KuLeaf LeafIsMulCommutativeKuA]
    [KuLeaf LeafHInfCentralizerKuA] [KuLeaf LeafEqKuAOfElemAbelian]
    [KuLeaf LeafTInfCentralizerKuWLeKuA] [KuLeaf LeafKuV2LeKuW]
    (h : KuHyp G T M H P z) {x : G} (hx : x ∈ kuA P H)
    (hx1 : x ≠ 1) : ∃ y ∈ kuA P H, kuPolar P H z x y ≠ 0 := by
  obtain ⟨y, hy, hne⟩ := h.exists_kuPolar_ne_zero hx hx1
  refine ⟨y, hy, ?_⟩
  rw [h.kuPolar_symm hx hy]
  exact hne

end KuHyp

end CFSG.GH74.QTGen4.Ku

end
