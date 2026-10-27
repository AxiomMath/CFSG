module

public import CFSG.LocalAnalysis.ComponentInitial.NonsplitOrthogonalCoverModel

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.NonsplitOrthogonalCover

open OrthogonalTail CFSG.ClassicalGroups.Orthogonal

theorem ker_eq_bot_of_binShape_of_five_le {K : Type*} [Field K] [CharP K 2] [Finite K]
    (hK : Nat.card K = 2) {r : ℕ} (hr : 5 ≤ r) {E : Type*} [Group E] [Finite E]
    [Group.IsPerfect E] (θ : E →* orthElementaryGroup (quadTail r (minusTailForm K 1 1)))
    (hθ : Function.Surjective θ) (hC : θ.ker ≤ Subgroup.center E) (h2 : IsPGroup 2 θ.ker) :
    θ.ker = ⊥ := by
  have hr3 : 3 ≤ r := by omega
  refine UnitaryOddCover.ker_eq_bot_of_sq_reduction (fun θ' hθ' hC' hsq' => ?_) θ hθ hC h2
  have h2' : IsPGroup 2 θ'.ker := fun k => ⟨1, Subtype.ext (by
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one, pow_one]
    exact hsq' _ k.2)⟩
  obtain ⟨U, hU, hUsurj, hUinj⟩ :=
    Shape.exists_lift_of_five_le (S := binShape K r hK hr3) hθ' hC' hr h2'
  exact Shape.ker_eq_bot_of_lift hθ' hC' hr3 hsq' U hU hUsurj hUinj

end CFSG.LocalAnalysis.ComponentInitial.NonsplitOrthogonalCover

namespace CFSG.LocalAnalysis.ComponentInitial

open NonsplitOrthogonalCover

theorem even_higher_nonsplit_orthogonal_prime_field_central_two_cover_trivial {E : Type*}
    {J : Type} [Group E] [Group J] [Finite E] [Finite J] [Group.IsPerfect E] (η : E →* J)
    (hη : Function.Surjective η) (hC : η.ker ≤ Subgroup.center E) (h2 : IsPGroup 2 η.ker)
    {n : ℕ} (hn : 6 ≤ n) (hJ : CFSG.Blueprint.LieModel J .POmegaMinus n 2 1) :
    η.ker = ⊥ ∧ Function.Bijective η := by
  obtain ⟨K, _, _, _, hK, -, ⟨e⟩⟩ := exists_mulEquiv_of_lieModel hJ
  set η' := e.toMonoidHom.comp η with hη'
  have hker' : η'.ker = η.ker := by
    ext z
    exact e.map_eq_one_iff
  have hbot := ker_eq_bot_of_binShape_of_five_le hK (r := n - 1) (by omega) η'
    (e.surjective.comp hη) (hker' ▸ hC) (hker' ▸ h2)
  rw [hker'] at hbot
  exact ⟨hbot, (MonoidHom.ker_eq_bot_iff η).mp hbot, hη⟩

end CFSG.LocalAnalysis.ComponentInitial
