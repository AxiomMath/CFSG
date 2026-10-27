module

public import CFSG.LieType.SemisimpleCentralizers.HeldCompTrivSU

public section

namespace CFSG.LieType.SemisimpleCentralizers.Held

open CFSG.Open CFSG.Open.StatedAPI Matrix
open CFSG.LieType.Steinberg
open scoped MatrixGroups

variable {p k Q : ℕ} {M : Type} [Field M] [Finite M] {τ : M ≃+* M} {hτ : ∀ x, τ (τ x) = x}

theorem nonempty_heldSU_two_mulEquiv_statedSL [Fact p.Prime] [CharP M p]
    (hQ : Q = p ^ k) (hcard : Nat.card M = Q ^ 2) (hτQ : ∀ x, τ x = x ^ Q) :
    Nonempty (↥(heldSU 2 M τ hτ) ≃* StatedSL 2 (fixedSubfield M p k)) := by
  have hcard' : Nat.card M = (p ^ k) ^ 2 := by
    rw [← hQ]
    exact hcard
  obtain ⟨e⟩ := CFSG.RankThree.SubgroupLists.nonempty_sl2_mulEquiv_statedSU_two (K := M) (r := p) (f := k) hcard'
  have hEq : StatedSU 2 (p ^ k) M = heldSU 2 M τ hτ := by
    rw [← hQ]
    exact (hct_heldSU_eq_statedSU (a := 2) (Q := Q) hτQ).symm
  exact ⟨(e.trans (MulEquiv.subgroupCongr hEq)).symm.trans
    (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 (fixedSubfield M p k))⟩

theorem nonempty_quotientCenter_heldSU_two_equiv_statedProj [Fact p.Prime] [CharP M p]
    (hQ : Q = p ^ k) (hcard : Nat.card M = Q ^ 2) (hτQ : ∀ x, τ x = x ^ Q) :
    Nonempty (↥(heldSU 2 M τ hτ) ⧸ Subgroup.center ↥(heldSU 2 M τ hτ) ≃*
      StatedProj (StatedSL 2 (fixedSubfield M p k))) := by
  obtain ⟨e⟩ := nonempty_heldSU_two_mulEquiv_statedSL (hτ := hτ) hQ hcard hτQ
  exact nonempty_quotientCenter_equiv_statedProj e

theorem isComponentOf_subgroupOf_top_of {G : Type*} [Group G] {L K : Subgroup G}
    (hL : IsComponentOf L K) : IsComponentOf (L.subgroupOf K) ⊤ := by
  refine ⟨le_top, ?_, ?_⟩
  · exact CFSG.Open.IsSubnormal.of_mathlib
      ((CFSG.Open.IsSubnormal.iff_subgroupOf hL.1).mp hL.2.1)
  · exact CFSG.Open.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hL.1) hL.2.2

end CFSG.LieType.SemisimpleCentralizers.Held

end
