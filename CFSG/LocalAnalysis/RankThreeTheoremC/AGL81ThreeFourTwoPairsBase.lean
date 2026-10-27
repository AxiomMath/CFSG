module

public import CFSG.Assembly.Subnormal

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open CFSG.Open

variable {G : Type*} [Group G]

theorem eq_bot_of_perfect_of_le_isSolvable {J S : Subgroup G} (hJS : J ≤ S)
    (hS : Group.IsSolvable S) (hJ : ⁅J, J⁆ = J) : J = ⊥ := by
  haveI : Group.IsSolvable J :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hJS)
  haveI : Group.IsPerfect J := Subgroup.isPerfect_iff.mpr hJ
  by_contra hne
  haveI : Nontrivial J := (Subgroup.nontrivial_iff_ne_bot J).mpr hne
  exact Group.IsPerfect.not_isSolvable J inferInstance

theorem le_of_perfect_of_card_eq_two_mul [Finite G] {J L M : Subgroup G} (hLM : L ≤ M)
    (hcard : Nat.card M = 2 * Nat.card L) (hJM : J ≤ M) (hJ : ⁅J, J⁆ = J) : J ≤ L := by
  set L' : Subgroup M := L.subgroupOf M
  have hL' : Nat.card L' = Nat.card L := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLM).toEquiv
  have hidx : L'.index = 2 := by
    have h := L'.card_mul_index
    rw [hL', hcard] at h
    have hpos : 0 < Nat.card L := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hpos (h.trans (mul_comm 2 _))
  have hLn : L'.Normal := Subgroup.normal_of_index_eq_two hidx
  have hcardQ : Nat.card (M ⧸ L') = 2 := by rw [← Subgroup.index_eq_card]; exact hidx
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : IsCyclic (M ⧸ L') := isCyclic_of_prime_card hcardQ
  have hker := Abelianization.commutator_subset_ker (QuotientGroup.mk' L')
  rw [QuotientGroup.ker_mk'] at hker
  have hMM : ⁅M, M⁆ ≤ L := by
    have e : ⁅M, M⁆ = (commutator M).map M.subtype := by
      rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype]
    rw [e]
    rintro _ ⟨x, hx, rfl⟩
    exact Subgroup.mem_subgroupOf.mp (hker hx)
  rw [← hJ]
  exact (Subgroup.commutator_mono hJM hJM).trans hMM

theorem eq_of_perfect_of_isSubnormal_of_card_eq_two_mul [Finite G] {J L Y M : Subgroup G}
    (hLY : L ≤ Y) (hYM : Y ≤ M) (hcard : Nat.card M = 2 * Nat.card L) (hL : IsSimpleGroup L)
    (hJY : J ≤ Y) (hJ1 : J ≠ ⊥) (hJp : ⁅J, J⁆ = J) (hJs : IsSubnormal J Y) : J = L := by
  have hJL : J ≤ L := le_of_perfect_of_card_eq_two_mul (hLY.trans hYM) hcard (hJY.trans hYM) hJp
  have hJsL : IsSubnormal J L := by
    have h := hJs.inf_of_le hLY
    rwa [inf_eq_left.mpr hJL] at h
  exact (hJsL.eq_bot_or_eq_of_isSimpleGroup hL).resolve_left hJ1

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
