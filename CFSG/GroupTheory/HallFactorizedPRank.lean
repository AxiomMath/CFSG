module

public import CFSG.GroupTheory.SolvableFactorizedHall
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

open scoped Pointwise

namespace CFSG

universe u

variable {G : Type u} [Group G] [Finite G]

theorem exists_isHallSubgroup_eq_sup_inf_of_le_pRank (hG : Group.IsSolvable G)
    {A B : Subgroup G} (hAB : (A : Set G) * (B : Set G) = Set.univ) {π : Set Nat.Primes}
    {Hc : Subgroup G} (hHc : IsPiSubgroup π Hc) {q : ℕ} (hq : q.Prime)
    (hqπ : (⟨q, hq⟩ : Nat.Primes) ∈ π) (h3 : 3 ≤ CFSG.Open.pRank q Hc) :
    ∃ H : Subgroup G, IsHallSubgroup π H ∧ H = H ⊓ A ⊔ H ⊓ B ∧
      3 ≤ CFSG.Open.pRank q H := by
  obtain ⟨H', hH', hHcH'⟩ := CFSG.SolvableHall.solvable_hall_containment hG π Hc hHc
  obtain ⟨H, hH, hfac⟩ := exists_isHallSubgroup_eq_sup_inf hG hAB π
  obtain ⟨g, hg⟩ := exists_conj_eq_of_isHallSubgroup_of_solvable hG hH hH'
  refine ⟨H, hH, hfac, ?_⟩
  have hconj : CFSG.Open.pRank q (H.map (MulAut.conj g).toMonoidHom) ≤ CFSG.Open.pRank q H := by
    have hmap : (H.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = H := by
      rw [Subgroup.map_map]
      have hcomp : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom
          = MonoidHom.id G := by
        ext x
        change MulAut.conj g⁻¹ (MulAut.conj g x) = x
        rw [MulAut.conj_apply, MulAut.conj_apply]
        group
      rw [hcomp, Subgroup.map_id]
    calc CFSG.Open.pRank q (H.map (MulAut.conj g).toMonoidHom)
        ≤ CFSG.Open.pRank q
            ((H.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom) :=
          CFSG.SectionRank.pRank_le_map (p := q) hq.one_lt _ (MulAut.conj g⁻¹).injective _
      _ = CFSG.Open.pRank q H := by rw [hmap]
  have h3' : 3 ≤ CFSG.Open.pRank q (H.map (MulAut.conj g).toMonoidHom) := by
    rw [← hg]
    exact h3.trans (CFSG.SectionRank.pRank_mono hq.one_lt hHcH')
  exact h3'.trans hconj

end CFSG
