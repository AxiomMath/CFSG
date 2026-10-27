module

public import CFSG.Dihedral.DisconnectedInvolutionGraph.SylowNormalizerControl

public section

namespace CFSG.DisconnectedInvolutionGraph.Helpers

open scoped Pointwise

variable {G : Type*} [Group G] {α : Type*} [MulAction G α]

theorem sylow_smul_subgroup_eq_map (prime : ℕ) (sylow : Sylow prime G) (element : G) :
    ((element • sylow : Sylow prime G) : Subgroup G) =
      (sylow : Subgroup G).map (MulAut.conj element).toMonoidHom := by
  rfl

end CFSG.DisconnectedInvolutionGraph.Helpers
