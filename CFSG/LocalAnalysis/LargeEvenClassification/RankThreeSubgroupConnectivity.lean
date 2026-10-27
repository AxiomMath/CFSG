module

public import CFSG.LocalAnalysis.LargeEvenClassification.RankThreeSubgroupConnectivityCore
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.NormalFourExistence
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.NormalFourGeometry

public section

namespace CFSG.LargeEvenClassification.Helpers

open CFSG.Open CFSG.LargeEvenClassification CFSG.ProperTwoGeneratedCore

universe u

variable {G : Type u} [Group G] [Finite G]

theorem rankThree_path_to_normal_four_vertex (htwo : IsPGroup 2 G)
    (V : Subgroup G) [V.Normal] (hV : IsElemAbelian 2 V) (hVcard : Nat.card V = 4)
    (E : Subgroup G) (hE : E ∈ E3 G) (hVE : V ≤ E)
    (A : Subgroup G) (hA : A ∈ E3 G) : RankThreeSubgroupPath A E := by
  let C := Subgroup.centralizer (V : Set G)
  let R := A ⊓ C
  let U := R ⊔ V
  obtain ⟨hRlarge, hUC, hVU, hU, hUlarge, _⟩ :=
    normal_four_centralizer_rank_three htwo V hV hVcard A hA.1 hA.2
  have happroach : ∃ EA : Subgroup G,
      EA ≤ U ∧ EA ∈ E3 G ∧ RankThreeSubgroupPath A EA := by
    rcases rankThree_subgroup_card_four_or_eight A R hA inf_le_left hRlarge with
      hRfour | hReight
    · obtain ⟨EA, hREA, hEAU, hEA⟩ :=
        rankThree_extend_four_in_elementary U R hU hUlarge le_sup_left hRfour
      have hintersection : A ⊓ EA = R := by
        apply le_antisymm
        · exact le_inf inf_le_left (inf_le_right.trans (hEAU.trans hUC))
        · exact le_inf inf_le_left hREA
      exact ⟨EA, hEAU, hEA, rankThree_path_of_intersection_four A EA hA hEA
        (hintersection ▸ hRfour)⟩
    · have hRA : R = A := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hReight, hA.2])
      have hAU : A ≤ U := hRA ▸ (le_sup_left : R ≤ U)
      exact ⟨A, hAU, hA, rankThree_path_refl A hA⟩
  obtain ⟨EA, hEAU, hEA, hAEA⟩ := happroach
  obtain ⟨EV, hVEV, hEVU, hEV⟩ :=
    rankThree_extend_four_in_elementary U V hU hUlarge hVU hVcard
  have hinside : RankThreeSubgroupPath EA EV :=
    rankThree_path_in_elementary U EA EV hU hEA hEV hEAU hEVU
  have hfinal : RankThreeSubgroupPath EV E :=
    rankThree_path_of_common_four EV E V hEV hE hVcard hVEV hVE
  exact rankThree_path_trans (rankThree_path_trans hAEA hinside) hfinal

theorem rankThree_normal_four_common_vertex (htwo : IsPGroup 2 G)
    (V : Subgroup G) [V.Normal] (hV : IsElemAbelian 2 V) (hVcard : Nat.card V = 4)
    (A : Subgroup G) (hA : A ∈ E3 G) :
    ∃ E : Subgroup G, V ≤ E ∧ E ∈ E3 G ∧
      E ≤ Subgroup.centralizer (V : Set G) ∧
      ∀ B : Subgroup G, B ∈ E3 G → RankThreeSubgroupPath B E := by
  let C := Subgroup.centralizer (V : Set G)
  let U := (A ⊓ C) ⊔ V
  obtain ⟨_, hUC, hVU, hU, hUlarge, _⟩ :=
    normal_four_centralizer_rank_three htwo V hV hVcard A hA.1 hA.2
  obtain ⟨E, hVE, hEU, hE⟩ :=
    rankThree_extend_four_in_elementary U V hU hUlarge hVU hVcard
  exact ⟨E, hVE, hE, hEU.trans hUC,
    fun B hB => rankThree_path_to_normal_four_vertex htwo V hV hVcard E hE hVE B hB⟩

theorem rank_three_elementary_subgroup_path (S : Type u) [Group S] [Finite S]
    (htwo : IsPGroup 2 S) (hrank : 3 ≤ twoRank S)
    (A B : Subgroup S) (hA : IsElemAbelian 2 A) (hAcard : Nat.card A = 8)
    (hB : IsElemAbelian 2 B) (hBcard : Nat.card B = 8) :
    RankThreeSubgroupPath A B := by
  obtain ⟨V, hVnormal, hV, hVcard⟩ := high_two_rank_normal_four S htwo hrank
  let : V.Normal := hVnormal
  obtain ⟨E, _, _, _, hpaths⟩ :=
    rankThree_normal_four_common_vertex htwo V hV hVcard A ⟨hA, hAcard⟩
  exact rankThree_path_trans (hpaths A ⟨hA, hAcard⟩)
    (rankThree_path_symm (hpaths B ⟨hB, hBcard⟩))

theorem rank_three_elementary_subgroup_connectivity (S : Type u) [Group S] [Finite S]
    (htwo : IsPGroup 2 S) (hrank : 3 ≤ twoRank S)
    (A B : Subgroup S) (hA : IsElemAbelian 2 A) (hAcard : Nat.card A = 8)
    (hB : IsElemAbelian 2 B) (hBcard : Nat.card B = 8) :
    ∃ n : ℕ, ∃ path : Fin (n + 1) → Subgroup S,
      path 0 = A ∧ path (Fin.last n) = B ∧
      (∀ i, IsElemAbelian 2 (path i) ∧ Nat.card (path i) = 8) ∧
      ∀ i : Fin n, Nat.card (path i.castSucc ⊓ path i.succ : Subgroup S) = 4 :=
  (rankThree_path_iff_subgroup_sequence A B).mp
    (rank_three_elementary_subgroup_path S htwo hrank A B hA hAcard hB hBcard)

theorem rank_three_conn3 (S : Type u) [Group S] [Finite S]
    (htwo : IsPGroup 2 S) (hrank : 3 ≤ twoRank S) : Conn3 S := by
  refine ⟨rankThree_vertices_nonempty_of_twoRank hrank, ?_⟩
  intro A B
  exact rank_three_elementary_subgroup_path S htwo hrank A.val B.val
    A.property.1 A.property.2 B.property.1 B.property.2

theorem rank_three_subgroup_graph_connected (S : Type u) [Group S] [Finite S]
    (htwo : IsPGroup 2 S) (hrank : 3 ≤ twoRank S) :
    (RankThreeSubgroupGraph S).Connected :=
  conn3_iff_graph_connected.mp (rank_three_conn3 S htwo hrank)

end CFSG.LargeEvenClassification.Helpers
