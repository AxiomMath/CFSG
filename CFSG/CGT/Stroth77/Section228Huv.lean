module

public import CFSG.CGT.Stroth77.Section228Hu

public section

namespace CFSG.CGT.Stroth77

variable {G : Type} [Group G] [Finite G]

namespace StrothFrame.IsD

variable {F : StrothFrame G} {D : Subgroup G} {τ : StrothTypeIndex}
  {dD : StrothWeakTypeData D τ}

theorem stroth_2_28_frame_of_huv (h : F.IsD D dD)
    (hnotall : ∃ x : G, x ∈ omegaIn 1 D ∧ orderOf x = 2 ∧
      ∃ y : G, y ∈ omegaIn 1 D ∧ orderOf y = 2 ∧ ∀ g : G, y ≠ g * x * g⁻¹)
    (huv : ¬ ((∃ m, τ = .t200 m) ∨ (∃ m, τ = .t201 m) ∨ (∃ m, τ = .t100 m) ∨
        (∃ s, τ = .t101 s) ∨ ∃ n, τ = .t300 n) →
      IsConj F.dA.uv (F.dA.toConfig.x * F.dA.toConfig.y * F.dA.uv)) :
    (∃ m, τ = .t200 m) ∨ (∃ m, τ = .t201 m) ∨ (∃ m, τ = .t100 m) ∨
      (∃ s, τ = .t101 s) ∨ ∃ n, τ = .t300 n :=
  h.stroth_2_28_frame_of_inputs hnotall h.isConj_u_w_mul_u_of_not_five huv

end StrothFrame.IsD

end CFSG.CGT.Stroth77
