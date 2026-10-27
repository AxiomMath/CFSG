module

public import CFSG.Dihedral.DisconnectedInvolutionGraph.CyclicTwoSquareRoot
public import CFSG.Dihedral.DisconnectedInvolutionGraph.RankOneCentralCoset
public import CFSG.Dihedral.DisconnectedInvolutionGraph.RankOneCommutingOrders

public section

namespace CFSG.DisconnectedInvolutionGraph.Helpers

variable {G : Type*} [Group G] [Finite G]

theorem rank_one_two_exists_noncommuting_equal_squares
    (hpgroup : IsPGroup 2 G) (hrank : NoCommutingDistinctInvolutions G)
    (hnonabelian : ∃ first second : G, first * second ≠ second * first) :
    ∃ first second : G,
      QuotientGroup.mk' (Subgroup.center G) first ∈ Subgroup.center (G ⧸ Subgroup.center G) ∧
      orderOf (QuotientGroup.mk' (Subgroup.center G) first) = 2 ∧
      first ^ 2 = second ^ 2 ∧ Subgroup.zpowers (first ^ 2) = Subgroup.center G ∧
      first * second ≠ second * first := by
  classical
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨first, hcosetCentral, hcosetOrder, hcenter⟩ :=
    rank_one_two_exists_central_order_two_coset hpgroup hrank hnonabelian
  have hfirstNoncentral : first ∉ Subgroup.center G := by
    intro hmem
    have hone := (QuotientGroup.eq_one_iff first).mpr hmem
    change QuotientGroup.mk' (Subgroup.center G) first = 1 at hone
    rw [hone, orderOf_one] at hcosetOrder
    omega
  have hfirstNonidentity : first ≠ 1 :=
    fun heq => hfirstNoncentral (heq ▸ (Subgroup.center G).one_mem)
  have hnontrivial : Nontrivial G := ⟨⟨first, 1, hfirstNonidentity⟩⟩
  let _ := hnontrivial
  have hfirstSquareNe : first ^ 2 ≠ 1 := by
    intro hsquare
    let involution : Involution G := ⟨first, orderOf_eq_prime hsquare hfirstNonidentity⟩
    obtain ⟨central, hcentral, hunique⟩ := rank_one_two_group_unique_involution hpgroup hrank
    have heq : first = (central : G) := congrArg Subtype.val (hunique involution)
    exact hfirstNoncentral (heq ▸ hcentral)
  obtain ⟨original, hnoncommute⟩ : ∃ original : G, first * original ≠ original * first := by
    by_contra hmissing
    push Not at hmissing
    apply hfirstNoncentral
    exact Subgroup.mem_center_iff.mpr (fun other => (hmissing other).symm)
  have horiginalNoncentral : original ∉ Subgroup.center G :=
    fun hmem => hnoncommute (Subgroup.mem_center_iff.mp hmem first)
  have hcenterLe : Subgroup.center G < Subgroup.zpowers original :=
    rank_one_two_center_lt_zpowers hpgroup hrank original horiginalNoncentral
  have hcenterProper : (Subgroup.center G).subgroupOf (Subgroup.zpowers original) < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    intro htop
    apply hcenterLe.ne
    apply le_antisymm hcenterLe.le
    intro element hmem
    have hwithin : (⟨element, hmem⟩ : Subgroup.zpowers original) ∈
        (Subgroup.center G).subgroupOf (Subgroup.zpowers original) := by
      rw [htop]
      trivial
    exact hwithin
  have hfirstSquareCentral : first ^ 2 ∈ Subgroup.center G := by
    rw [← hcenter]
    exact Subgroup.mem_zpowers _
  let squareWithin : (Subgroup.center G).subgroupOf (Subgroup.zpowers original) :=
    ⟨⟨first ^ 2, hcenterLe.le hfirstSquareCentral⟩, hfirstSquareCentral⟩
  obtain ⟨secondInside, hsecondSquare⟩ := cyclic_two_pgroup_square_root
    (hpgroup.to_subgroup (Subgroup.zpowers original)) _ hcenterProper squareWithin
  let second : G := secondInside.val
  have hsecondSquareAmbient : second ^ 2 = first ^ 2 :=
    congrArg (fun element : Subgroup.zpowers original => element.val) hsecondSquare
  have hsecondNe : second ≠ 1 := by
    intro hone
    apply hfirstSquareNe
    rw [← hsecondSquareAmbient, hone, one_pow]
  have hfirstDiv : 2 ∣ orderOf first := hpgroup.dvd_orderOf hfirstNonidentity
  have hsecondDiv : 2 ∣ orderOf second := hpgroup.dvd_orderOf hsecondNe
  have horderEq : orderOf first = orderOf second := by
    have hhalf : orderOf first / 2 = orderOf second / 2 := by
      rw [← orderOf_pow_of_dvd (by decide : 2 ≠ 0) hfirstDiv,
        ← orderOf_pow_of_dvd (by decide : 2 ≠ 0) hsecondDiv, hsecondSquareAmbient]
    calc
      orderOf first = orderOf first / 2 * 2 := (Nat.div_mul_cancel hfirstDiv).symm
      _ = orderOf second / 2 * 2 := by rw [hhalf]
      _ = orderOf second := Nat.div_mul_cancel hsecondDiv
  refine ⟨first, second, hcosetCentral, hcosetOrder, hsecondSquareAmbient.symm, hcenter, ?_⟩
  intro hcommute
  have hcyclicEq := rank_one_two_commuting_equal_order_zpowers hpgroup hrank first second
    hcommute horderEq
  have hfirstIn : first ∈ Subgroup.zpowers original := by
    have hfirstIn : first ∈ Subgroup.zpowers second := hcyclicEq ▸ Subgroup.mem_zpowers first
    exact (Subgroup.zpowers_le.mpr secondInside.property) hfirstIn
  obtain ⟨exponent, hexponent⟩ := Subgroup.mem_zpowers_iff.mp hfirstIn
  apply hnoncommute
  rw [← hexponent]
  exact (Commute.refl original).zpow_left exponent

end CFSG.DisconnectedInvolutionGraph.Helpers
