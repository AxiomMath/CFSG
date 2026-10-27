module

public import CFSG.LocalAnalysis.LargeEvenClassification.RankThreeSubgroupGraph
public import CFSG.LocalAnalysis.LargeEvenClassification.ElementarySubgroupPaths

public section

namespace CFSG.LargeEvenClassification.Helpers

open CFSG.Open CFSG.LargeEvenClassification

universe u

variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
theorem rankThree_elementary_isPGroup (U : Subgroup G) (hU : IsElemAbelian 2 U) :
    IsPGroup 2 U := by
  apply isPGroup_iff_pow_pow_eq_one.mpr
  intro x
  exact ⟨1, by simpa using (Subtype.ext (hU.2 x x.property) : x ^ 2 = 1)⟩

omit [Finite G] in
theorem rankThree_card_subgroupOf_eq (A U : Subgroup G) (hAU : A ≤ U) :
    Nat.card (A.subgroupOf U) = Nat.card A := by
  rw [← Subgroup.card_subtype U (A.subgroupOf U),
    Subgroup.map_subgroupOf_eq_of_le hAU]

theorem rankThree_extend_in_elementary (U R : Subgroup G)
    (hU : IsElemAbelian 2 U) (hUcard : 8 ≤ Nat.card U)
    (hRU : R ≤ U) (hRdiv : Nat.card R ∣ 8) :
    ∃ E : Subgroup G, R ≤ E ∧ E ≤ U ∧ E ∈ E3 G := by
  obtain ⟨rank, hcard⟩ := (rankThree_elementary_isPGroup U hU).exists_card_eq
  have hrank : 3 ≤ rank := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    simpa only [← hcard] using hUcard
  have hdiv : 2 ^ 3 ∣ Nat.card U := by
    rw [hcard]
    exact Nat.pow_dvd_pow 2 hrank
  obtain ⟨E, hEcard, hRE, hEU⟩ :=
    Sylow.exists_subgroup_card_pow_prime_le_le Nat.prime_two (n := 3)
      (H := R) (L := U) (by simpa using hRdiv) hdiv hRU
  exact ⟨E, hRE, hEU, elementary_subgroup_of_le U E hU hEU,
    by simpa using hEcard⟩

theorem rankThree_extend_four_in_elementary (U R : Subgroup G)
    (hU : IsElemAbelian 2 U) (hUcard : 8 ≤ Nat.card U)
    (hRU : R ≤ U) (hRcard : Nat.card R = 4) :
    ∃ E : Subgroup G, R ≤ E ∧ E ≤ U ∧ E ∈ E3 G :=
  rankThree_extend_in_elementary U R hU hUcard hRU (by rw [hRcard]; norm_num)

theorem rankThree_vertex_in_elementary (U : Subgroup G)
    (hU : IsElemAbelian 2 U) (hUcard : 8 ≤ Nat.card U) :
    ∃ E : Subgroup G, E ≤ U ∧ E ∈ E3 G := by
  obtain ⟨E, _, hEU, hE⟩ := rankThree_extend_in_elementary U ⊥ hU hUcard bot_le
    (by simp)
  exact ⟨E, hEU, hE⟩

theorem rankThree_vertices_nonempty_of_twoRank (hrank : 3 ≤ twoRank G) :
    (E3 G).Nonempty := by
  obtain ⟨U, _, hU, hcard⟩ := pRank_witness (by decide : 1 < 2) (⊤ : Subgroup G)
  have hUcard : 8 ≤ Nat.card U := by
    rw [hcard]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) hrank
  obtain ⟨E, _, hE⟩ := rankThree_vertex_in_elementary U hU hUcard
  exact ⟨E, hE⟩

theorem rankThree_subgroup_card_four_or_eight (A R : Subgroup G)
    (hA : A ∈ E3 G) (hRA : R ≤ A) (hRcard : 4 ≤ Nat.card R) :
    Nat.card R = 4 ∨ Nat.card R = 8 := by
  obtain ⟨rank, hcard⟩ :=
    (rankThree_elementary_isPGroup R (elementary_subgroup_of_le A R hA.1 hRA)).exists_card_eq
  have hupper : Nat.card R ≤ 8 := hA.2 ▸ Subgroup.card_le_of_le hRA
  have hrankLower : 2 ≤ rank := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    simpa only [← hcard] using hRcard
  have hrankUpper : rank ≤ 3 := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    simpa only [← hcard] using hupper
  have hrankCases : rank = 2 ∨ rank = 3 := by omega
  rcases hrankCases with htwo | hthree
  · exact Or.inl (by rw [hcard, htwo]; norm_num)
  · exact Or.inr (by rw [hcard, hthree]; norm_num)

theorem rankThree_bounded_path_in_elementary (U A B : Subgroup G)
    (hU : IsElemAbelian 2 U) (hAU : A ≤ U) (hBU : B ≤ U)
    (hAcard : Nat.card A = 8) (hBcard : Nat.card B = 8)
    {d : ℕ} (hJcard : Nat.card (A ⊓ B : Subgroup G) = 2 ^ d) :
    ∃ n : ℕ, n ≤ 3 - d ∧ ∃ path : Fin (n + 1) → Subgroup G,
      path 0 = A ∧ path (Fin.last n) = B ∧
      (∀ i, path i ≤ U ∧ IsElemAbelian 2 (path i) ∧ Nat.card (path i) = 8) ∧
      ∀ i : Fin n, Nat.card (path i.castSucc ⊓ path i.succ : Subgroup G) = 4 := by
  let : CommGroup U := { U.toGroup with mul_comm := @mul_comm' U _ hU.1 }
  let X := A.subgroupOf U
  let Y := B.subgroupOf U
  have hXcard : Nat.card X = 2 ^ 3 := by
    simpa using (rankThree_card_subgroupOf_eq A U hAU).trans hAcard
  have hYcard : Nat.card Y = 2 ^ 3 := by
    simpa using (rankThree_card_subgroupOf_eq B U hBU).trans hBcard
  have hJinternal : Nat.card (X ⊓ Y : Subgroup U) = 2 ^ d := by
    rw [← Subgroup.card_subtype U (X ⊓ Y),
      Subgroup.map_inf X Y U.subtype Subtype.val_injective,
      Subgroup.map_subgroupOf_eq_of_le hAU,
      Subgroup.map_subgroupOf_eq_of_le hBU]
    exact hJcard
  obtain ⟨n, hn, path, hfirst, hlast, hcards, hsteps⟩ :=
    elementary_equal_rank_subgroup_path Nat.prime_two
      (fun x : U => Subtype.ext (hU.2 x x.property)) (by decide : 1 ≤ 3)
      X Y hXcard hYcard hJinternal
  refine ⟨n, hn, fun i => (path i).map U.subtype, ?_, ?_, ?_, ?_⟩
  · exact (congrArg (fun X => X.map U.subtype) hfirst).trans
      (Subgroup.map_subgroupOf_eq_of_le hAU)
  · exact (congrArg (fun X => X.map U.subtype) hlast).trans
      (Subgroup.map_subgroupOf_eq_of_le hBU)
  · intro i
    have hle : (path i).map U.subtype ≤ U := Subgroup.map_subtype_le _
    exact ⟨hle, elementary_subgroup_of_le U _ hU hle,
      (Subgroup.card_subtype U (path i)).trans (by simpa using hcards i)⟩
  · intro i
    rw [← Subgroup.map_inf _ _ U.subtype Subtype.val_injective,
      Subgroup.card_subtype]
    simpa using hsteps i

theorem rankThree_path_in_elementary (U A B : Subgroup G)
    (hU : IsElemAbelian 2 U) (hA : A ∈ E3 G) (hB : B ∈ E3 G)
    (hAU : A ≤ U) (hBU : B ≤ U) : RankThreeSubgroupPath A B := by
  obtain ⟨d, hJcard⟩ :=
    (rankThree_elementary_isPGroup (A ⊓ B) (elementary_subgroup_of_le A (A ⊓ B) hA.1
      inf_le_left)).exists_card_eq
  obtain ⟨n, _, path, hfirst, hlast, hvertices, hsteps⟩ :=
    rankThree_bounded_path_in_elementary U A B hU hAU hBU hA.2 hB.2 hJcard
  exact (rankThree_path_iff_subgroup_sequence A B).mpr
    ⟨n, path, hfirst, hlast, fun i => (hvertices i).2, hsteps⟩

theorem rankThree_common_four_eq_or_adj (A B V : Subgroup G)
    (hA : A ∈ E3 G) (hB : B ∈ E3 G) (hVcard : Nat.card V = 4)
    (hVA : V ≤ A) (hVB : V ≤ B) :
    A = B ∨ Nat.card (A ⊓ B : Subgroup G) = 4 := by
  have hJlarge : 4 ≤ Nat.card (A ⊓ B : Subgroup G) :=
    hVcard ▸ Subgroup.card_le_of_le (le_inf hVA hVB)
  rcases rankThree_subgroup_card_four_or_eight A (A ⊓ B) hA inf_le_left hJlarge with
    hfour | height
  · exact Or.inr hfour
  · have hJA : A ⊓ B = A := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [height, hA.2])
    have hJB : A ⊓ B = B := Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [height, hB.2])
    exact Or.inl (hJA.symm.trans hJB)

theorem rankThree_path_of_common_four (A B V : Subgroup G)
    (hA : A ∈ E3 G) (hB : B ∈ E3 G) (hVcard : Nat.card V = 4)
    (hVA : V ≤ A) (hVB : V ≤ B) : RankThreeSubgroupPath A B := by
  rcases rankThree_common_four_eq_or_adj A B V hA hB hVcard hVA hVB with heq | hadj
  · subst B
    exact rankThree_path_refl A hA
  · exact rankThree_path_of_intersection_four A B hA hB hadj

end CFSG.LargeEvenClassification.Helpers
