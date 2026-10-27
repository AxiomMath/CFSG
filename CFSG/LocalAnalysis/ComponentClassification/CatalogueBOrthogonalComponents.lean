module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDerived
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBFixedCentralQuotientComponents

public section

namespace CFSG.ComponentClassification.CatalogueBOrthogonal

noncomputable section

open QuadraticMap CFSG.ClassicalGroups.Orthogonal

theorem pComponent_eq_derived_of_quasisimple {G : Type*} [Group G] [Finite G]
    (hderived : CFSG.IsQuasisimple (commutator G)) (p : ℕ) (hp : p.Prime)
    (L : Subgroup G) (hL : CFSG.IsPComponent p L) :
    L = commutator G ∧ CFSG.IsQuasisimple L := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨hle, hrestricted⟩ :=
    CatalogueBFixedCentralQuotient.pComponent_in_normal_of_solvable_quotient
      p (commutator G) L hL
  let J := L.subgroupOf (commutator G)
  let : Group.IsPerfect J := CatalogueBAlternating.pComponent_perfect hrestricted
  let : Nontrivial J := CatalogueBAlternating.pComponent_nontrivial hrestricted
  have htop : J = ⊤ :=
    (Quasisimple.perfect_subnormal_eq_bot_or_eq_top
      (CatalogueBAlternating.quasisimple_iff_native.mp hderived) J
      (Components.chain_of_mathlib_subnormal hrestricted.choose_spec.2.1)).resolve_left
        (J.nontrivial_iff_ne_bot.mp inferInstance)
  have heq : L = commutator G :=
    le_antisymm hle (Subgroup.subgroupOf_eq_top.mp htop)
  refine ⟨heq, ?_⟩
  rw [heq]
  exact hderived

instance orthogonalFinite (K V : Type*) [Field K] [Finite K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (Q : QuadraticForm K V) : Finite (TauCeti.QuadraticMap.orthogonalGroup Q) := by
  let : Finite V := Module.finite_of_finite K
  apply Finite.of_injective (fun g : TauCeti.QuadraticMap.orthogonalGroup Q =>
    fun x : V => g.val x)
  intro g h heq
  exact Subtype.ext (LinearEquiv.ext (congrFun heq))

theorem high_Witt_orthogonal_p_components
    {K V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (Q : QuadraticForm K V)
    (h2 : (2 : K) ≠ 0) (hQ : (polarBilin Q).Nondegenerate)
    {T : Submodule K V} (hT : 3 ≤ Module.finrank K T)
    (hTQ : ∀ x ∈ T, Q x = 0) :
    CFSG.IsQuasisimple (commutator (TauCeti.QuadraticMap.orthogonalGroup Q)) ∧
      ∀ p : ℕ, p.Prime →
        ∀ L : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q),
          CFSG.IsPComponent p L →
            L = commutator (TauCeti.QuadraticMap.orthogonalGroup Q) ∧ CFSG.IsQuasisimple L := by
  have hderived := derived_quasisimple Q h2 hQ hT hTQ
  exact ⟨hderived, pComponent_eq_derived_of_quasisimple hderived⟩

end

end CFSG.ComponentClassification.CatalogueBOrthogonal
