module

public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.LieType.BorelTits

open CFSG.Open

private theorem le_of_normalizer_subgroupOf_le_radp {X : Type*} [Group X] [Finite X] {r : ℕ}
    [Fact r.Prime] {Q R : Subgroup X} (hQ : IsPGroup r Q) (hRQ : R ≤ Q)
    (hle : (Subgroup.normalizer (R : Set X)).subgroupOf Q ≤ R.subgroupOf Q) : Q ≤ R := by
  by_contra hnot
  have hlt : R.subgroupOf Q < ⊤ := by
    rw [lt_top_iff_ne_top]
    exact fun htop => hnot (Subgroup.subgroupOf_eq_top.mp htop)
  have hnc : NormalizerCondition ↥Q :=
    normalizerCondition_of_isNilpotent (G := ↥Q) (h := IsPGroup.isNilpotent hQ)
  have hlt' := hnc (R.subgroupOf Q) hlt
  have hle' : Subgroup.normalizer (R.subgroupOf Q) ≤ R.subgroupOf Q := by
    rw [← Subgroup.subgroupOf_normalizer_eq hRQ]
    exact hle
  exact absurd hle' (not_le_of_gt hlt')

theorem Holds.exists_sylow_normalizer_le_normalizer {X : Type*} [Group X] [Finite X] {r : ℕ}
    [Fact r.Prime] (h : Holds X r) {R : Subgroup X}
    (hrad : pCoreOf r (Subgroup.normalizer (R : Set X)) = R) :
    ∃ S : Sylow r X,
      Subgroup.normalizer ((S : Subgroup X) : Set X) ≤ Subgroup.normalizer (R : Set X) := by
  have hR : IsPGroup r R := by
    rw [← hrad]
    exact pCoreOf_isPGroup r _
  by_cases hbot : R = ⊥
  · refine ⟨default, ?_⟩
    rw [hbot, Subgroup.normalizer_eq_top (H := ⊥)]
    exact le_top
  · obtain ⟨S, P, -, hN, hcore, hRle, hS⟩ := h R hbot hR
    have hQp : IsPGroup r (pCoreOf r P) := pCoreOf_isPGroup r P
    have hRleQ : R ≤ pCoreOf r P := by
      rw [← hrad]
      exact hcore
    have hQN : pCoreOf r P ⊓ Subgroup.normalizer (R : Set X) ≤ R := by
      have hle : pCoreOf r P ⊓ Subgroup.normalizer (R : Set X) ≤
          Subgroup.normalizer (R : Set X) := inf_le_right
      have hnorm : Subgroup.normalizer (R : Set X) ≤ Subgroup.normalizer
          ((pCoreOf r P ⊓ Subgroup.normalizer (R : Set X) : Subgroup X) : Set X) := by
        refine (le_inf ?_ Subgroup.le_normalizer).trans
          Subgroup.inf_normalizer_le_normalizer_inf
        exact hN.trans (le_normalizer_pCoreOf r P)
      have hp : IsPGroup r ↥(pCoreOf r P ⊓ Subgroup.normalizer (R : Set X) : Subgroup X) :=
        hQp.to_le inf_le_left
      have hcore' := le_pCoreOf_of_le_normalizer r hle hnorm hp
      rwa [hrad] at hcore'
    have hQR : pCoreOf r P ≤ R := by
      refine le_of_normalizer_subgroupOf_le_radp hQp hRleQ ?_
      intro q hq
      rw [Subgroup.mem_subgroupOf] at hq ⊢
      exact hQN ⟨q.2, hq⟩
    have hPeq : R = pCoreOf r P := le_antisymm hRleQ hQR
    refine ⟨S, ?_⟩
    refine hS.trans ?_
    rw [hPeq]
    exact le_normalizer_pCoreOf r P

end CFSG.LieType.BorelTits
