module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL410Surj

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33

namespace Fz410Set

variable {G : Type} [Group G] [Finite G] {t : G} {L S T : Subgroup G}
  {x₁ x₂ lam rho tau s : G} {Z E W Q R P : Subgroup G}
  (D : Fz410Set t L S T x₁ x₂ lam rho tau s Z E W Q R P)

include D

theorem main : ∃ M : Subgroup G, R ≤ M ∧ M ≤ normalizer (R : Set G) ∧
    M.relIndex (normalizer (R : Set G)) ≤ 2 ∧
      ∃ f : ↥M →* FzSigma4, Function.Surjective f ∧ f.ker = R.subgroupOf M := by
  obtain ⟨Φ, hΦ⟩ := D.exists_act
  have hcard : Nat.card (Fz410Om E P Q) = 4 := D.card_Om
  haveI : Finite (Fz410Om E P Q) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  let e : Fz410Om E P Q ≃ Fin 4 := Finite.equivFinOfCardEq hcard
  refine ⟨fz410M R E, D.R_le_M, D.M_le_N3, D.relIndex_M,
    e.permCongrHom.toMonoidHom.comp Φ, ?_, ?_⟩
  · exact e.permCongrHom.surjective.comp (D.act_surjective Φ hΦ)
  · ext n
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have h1 : Φ n = 1 := by
        have h2 : e.permCongrHom (Φ n) = 1 := h
        exact (MulEquiv.map_eq_one_iff _).mp h2
      exact D.ker_le Φ hΦ n h1
    · intro hn
      have h1 : Φ n = 1 := D.act_R Φ hΦ n hn
      show e.permCongrHom (Φ n) = 1
      rw [h1, map_one]

end Fz410Set

end CFSG.OddStandard.SmallF3.FritzII
