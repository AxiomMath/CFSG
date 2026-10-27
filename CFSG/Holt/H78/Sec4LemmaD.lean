module

public import CFSG.LocalAnalysis.ComponentInitial.GroupAlternatingCover

public section

namespace CFSG.Holt.H78

open Equiv Equiv.Perm Subgroup CFSG.LocalAnalysis.ComponentInitial

section LemmaD

variable {M : Type*} [Group M] [Finite M] {Ψ : Type*} [Fintype Ψ] [DecidableEq Ψ]

theorem card_ker_le_two_of_alternatingGroup [Group.IsPerfect M] (h5 : 5 ≤ Fintype.card Ψ)
    (η : M →* alternatingGroup Ψ) (hη : Function.Surjective η) (hK : η.ker ≤ center M)
    (hK2 : IsPGroup 2 η.ker) : Nat.card η.ker ≤ 2 := by
  let e : Ψ ≃ Fin (Fintype.card Ψ) := Fintype.equivFin Ψ
  let η' : M →* alternatingGroup (Fin (Fintype.card Ψ)) := e.altCongrHom.toMonoidHom.comp η
  have hker : η'.ker = η.ker := by
    ext g
    simp only [MonoidHom.mem_ker, η', MonoidHom.coe_comp, Function.comp_apply,
      MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]
  have := alternating_perfect_central_two_kernel_order_at_most_two h5 η'
    (e.altCongrHom.surjective.comp hη) (hker ▸ hK) (hker ▸ hK2)
  rwa [hker] at this

end LemmaD

end CFSG.Holt.H78
