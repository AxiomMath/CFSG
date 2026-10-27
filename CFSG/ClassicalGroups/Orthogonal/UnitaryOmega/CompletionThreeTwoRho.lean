module

public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.CompletionThreeTwoPhi
public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.QTwoBlockGen
import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.BlockGeneration

public section

namespace CFSG.ClassicalGroups.Orthogonal.UnitaryOmega

open CFSG.LieType.Universal.Spin CFSG.LieType.CurtisTits
open CFSG.ClassicalInvolution.PhanDn CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial CFSG.Timmesfeld.ClassicalOrders

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Finite K] [CharP K 2] {f : ℕ}
  (E : QuadExt F K (unitaryInvolution K 2 f)) {ω : K} (hω : IsTraceNormOne E ω)
  {H : Type} [Group H]

@[expose] noncomputable def qTwoRho (t : Equiv.Perm (Fin 4) →* H) (κ : normOmega E 3 →* H)
    (k : Fin 5) : rankOne (plusRootGroup 5 F (by norm_num)) k →* H :=
  if hk : (k : ℕ) < 2 then
    (deletionPhiThree E t κ {0, 1} (pair_ne_univ_four 0 1)).comp
      (((qTwoLambda E hω).symm.toMonoidHom.comp
        (rankOne (plusRootGroup 5 F (by norm_num)) k).subtype).codRestrict _
        fun x => map_rankOne_le_normBlock_zero_one E hω hk (Subgroup.mem_map_of_mem _ x.2))
  else
    (deletionPhiThree E t κ {2, 3} (pair_ne_univ_four 2 3)).comp
      (((qTwoLambda E hω).symm.toMonoidHom.comp
        (rankOne (plusRootGroup 5 F (by norm_num)) k).subtype).codRestrict _
        fun x => map_rankOne_le_normBlock_two_three E hω (by omega)
          (Subgroup.mem_map_of_mem _ x.2))

variable {t : Equiv.Perm (Fin 4) →* H} {κ : normOmega E 3 →* H}

theorem qTwoRho_of_lt_two {k : Fin 5} (hk : (k : ℕ) < 2)
    (x : rankOne (plusRootGroup 5 F (by norm_num)) k) :
    qTwoRho E hω t κ k x = deletionPhiThree E t κ {0, 1} (pair_ne_univ_four 0 1)
      ⟨(qTwoLambda E hω).symm x,
        map_rankOne_le_normBlock_zero_one E hω hk (Subgroup.mem_map_of_mem _ x.2)⟩ := by
  simp only [qTwoRho, dif_pos hk]
  rfl

theorem qTwoRho_of_two_le {k : Fin 5} (hk : 2 ≤ (k : ℕ))
    (x : rankOne (plusRootGroup 5 F (by norm_num)) k) :
    qTwoRho E hω t κ k x = deletionPhiThree E t κ {2, 3} (pair_ne_univ_four 2 3)
      ⟨(qTwoLambda E hω).symm x,
        map_rankOne_le_normBlock_two_three E hω hk (Subgroup.mem_map_of_mem _ x.2)⟩ := by
  simp only [qTwoRho, dif_neg (show ¬(k : ℕ) < 2 by omega)]
  rfl

private lemma eq_top_of_singleton_le
    {E : QuadExt F K (unitaryInvolution K 2 f)} {i j : Fin 4}
    (P : Subgroup (normBlock E 4 ({i, j} : Finset (Fin 4))))
    (hi : ∀ g : normBlock E 4 {i},
      (⟨(g : normOmega E 4), normBlock_mono E 4 (by simp) g.2⟩ :
        normBlock E 4 ({i, j} : Finset (Fin 4))) ∈ P)
    (hj : ∀ g : normBlock E 4 {j},
      (⟨(g : normOmega E 4), normBlock_mono E 4 (by simp) g.2⟩ :
        normBlock E 4 ({i, j} : Finset (Fin 4))) ∈ P) :
    P = ⊤ := by
  rw [Subgroup.eq_top_iff']
  intro x
  have hle : normBlock E 4 ({i, j} : Finset (Fin 4)) ≤
      P.map (normBlock E 4 ({i, j} : Finset (Fin 4))).subtype := by
    conv_lhs => rw [← normBlock_singleton_sup_singleton E i j]
    refine sup_le ?_ ?_
    · intro g hg
      exact Subgroup.mem_map.mpr
        ⟨⟨g, normBlock_mono E 4 (by simp) hg⟩, hi ⟨g, hg⟩, rfl⟩
    · intro g hg
      exact Subgroup.mem_map.mpr
        ⟨⟨g, normBlock_mono E 4 (by simp) hg⟩, hj ⟨g, hg⟩, rfl⟩
  obtain ⟨p, hp, hpx⟩ := Subgroup.mem_map.mp (hle x.2)
  rwa [show p = x from Subtype.ext hpx] at hp

private theorem commute_deletionPhiThree_singleton_of_mem_rankOne_zero
    (hT1 : t.comp (Equiv.Perm.viaEmbeddingHom Fin.castSuccEmb) = κ.comp (normPerm E le_rfl))
    (hC : ∀ y ∈ (anchorBlock E (by norm_num : 2 ≤ 3)).map κ, Commute (t (Equiv.swap 2 3)) y)
    {x : normOmega E 4} (hx01 : x ∈ normBlock E 4 ({0, 1} : Finset (Fin 4)))
    (hxL : x ∈ (rankOne (plusRootGroup 5 F (by norm_num)) (0 : Fin 5)).map
      (qTwoLambda E hω).symm.toMonoidHom)
    {j : Fin 4} (hj : j ∈ ({2, 3} : Finset (Fin 4)))
    (g : normBlock E 4 ({j} : Finset (Fin 4))) :
    Commute
      (deletionPhiThree E t κ ({2, 3} : Finset (Fin 4)) (pair_ne_univ_four 2 3)
        ⟨(g : normOmega E 4), normBlock_mono E 4 (Finset.singleton_subset_iff.mpr hj) g.2⟩)
      (deletionPhiThree E t κ ({0, 1} : Finset (Fin 4)) (pair_ne_univ_four 0 1)
        ⟨x, hx01⟩) := by
  have hj' : j = 2 ∨ j = 3 := by simpa using hj
  have hge : 2 ≤ (j : ℕ) := by rcases hj' with rfl | rfl <;> norm_num
  have hR : ({j} : Finset (Fin 4)) ≠ Finset.univ :=
    (Finset.card_lt_iff_ne_univ _).mp (by simp)
  have hunion : (({0, 1} : Finset (Fin 4)) ∪ {j}) ≠ Finset.univ := by
    refine (Finset.card_lt_iff_ne_univ _).mp ?_
    calc (({0, 1} : Finset (Fin 4)) ∪ {j}).card
        ≤ ({0, 1} : Finset (Fin 4)).card + ({j} : Finset (Fin 4)).card :=
          Finset.card_union_le _ _
      _ = 3 := by simp
      _ < 4 := by norm_num
  have hsub : deletionPhiThree E t κ ({2, 3} : Finset (Fin 4)) (pair_ne_univ_four 2 3)
        ⟨(g : normOmega E 4), normBlock_mono E 4 (Finset.singleton_subset_iff.mpr hj) g.2⟩ =
      deletionPhiThree E t κ ({j} : Finset (Fin 4)) hR ⟨(g : normOmega E 4), g.2⟩ :=
    deletionPhiThree_of_subset hT1 hC hR (pair_ne_univ_four 2 3)
      (Finset.singleton_subset_iff.mpr hj) g.2
  rw [hsub]
  exact (commute_deletionPhiThree hT1 hC (pair_ne_univ_four 0 1) hR hunion hx01 g.2
    (commute_map_rankOne_zero E hω (k := j) hge x hxL (g : normOmega E 4) g.2)).symm

private theorem commute_deletionPhiThree_pair_of_mem_rankOne_zero
    (hT1 : t.comp (Equiv.Perm.viaEmbeddingHom Fin.castSuccEmb) = κ.comp (normPerm E le_rfl))
    (hC : ∀ y ∈ (anchorBlock E (by norm_num : 2 ≤ 3)).map κ, Commute (t (Equiv.swap 2 3)) y)
    {x : normOmega E 4} (hx01 : x ∈ normBlock E 4 ({0, 1} : Finset (Fin 4)))
    (hxL : x ∈ (rankOne (plusRootGroup 5 F (by norm_num)) (0 : Fin 5)).map
      (qTwoLambda E hω).symm.toMonoidHom)
    {y : normOmega E 4} (hy23 : y ∈ normBlock E 4 ({2, 3} : Finset (Fin 4))) :
    Commute
      (deletionPhiThree E t κ ({0, 1} : Finset (Fin 4)) (pair_ne_univ_four 0 1) ⟨x, hx01⟩)
      (deletionPhiThree E t κ ({2, 3} : Finset (Fin 4)) (pair_ne_univ_four 2 3) ⟨y, hy23⟩) := by
  let P : Subgroup (normBlock E 4 ({2, 3} : Finset (Fin 4))) :=
    (Subgroup.centralizer
      ({(deletionPhiThree E t κ ({0, 1} : Finset (Fin 4)) (pair_ne_univ_four 0 1))
          ⟨x, hx01⟩} : Set H)).comap
      (deletionPhiThree E t κ ({2, 3} : Finset (Fin 4)) (pair_ne_univ_four 2 3))
  have h2 : ∀ g : normBlock E 4 ({2} : Finset (Fin 4)),
      (⟨(g : normOmega E 4), normBlock_mono E 4 (by simp) g.2⟩ :
        normBlock E 4 ({2, 3} : Finset (Fin 4))) ∈ P := by
    intro g
    dsimp only [P]
    rw [Subgroup.mem_comap]
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (commute_deletionPhiThree_singleton_of_mem_rankOne_zero E hω hT1 hC hx01 hxL
        (j := 2) (by simp) g)
  have h3 : ∀ g : normBlock E 4 ({3} : Finset (Fin 4)),
      (⟨(g : normOmega E 4), normBlock_mono E 4 (by simp) g.2⟩ :
        normBlock E 4 ({2, 3} : Finset (Fin 4))) ∈ P := by
    intro g
    dsimp only [P]
    rw [Subgroup.mem_comap]
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (commute_deletionPhiThree_singleton_of_mem_rankOne_zero E hω hT1 hC hx01 hxL
        (j := 3) (by simp) g)
  have hP : P = ⊤ := eq_top_of_singleton_le (i := 2) (j := 3) P h2 h3
  have hz : (⟨y, hy23⟩ : normBlock E 4 ({2, 3} : Finset (Fin 4))) ∈ P := by
    rw [hP]
    exact Subgroup.mem_top _
  exact (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_comap.mp hz)).symm

private theorem commute_deletionPhiThree_singleton_of_mem_rankOne_of_three_le
    (hT1 : t.comp (Equiv.Perm.viaEmbeddingHom Fin.castSuccEmb) = κ.comp (normPerm E le_rfl))
    (hC : ∀ y ∈ (anchorBlock E (by norm_num : 2 ≤ 3)).map κ, Commute (t (Equiv.swap 2 3)) y)
    {y : normOmega E 4} (hy23 : y ∈ normBlock E 4 ({2, 3} : Finset (Fin 4)))
    {l : Fin 5} (hl : 3 ≤ (l : ℕ))
    (hyL : y ∈ (rankOne (plusRootGroup 5 F (by norm_num)) l).map
      (qTwoLambda E hω).symm.toMonoidHom)
    {j : Fin 4} (hj : j ∈ ({0, 1} : Finset (Fin 4)))
    (g : normBlock E 4 ({j} : Finset (Fin 4))) :
    Commute
      (deletionPhiThree E t κ ({0, 1} : Finset (Fin 4)) (pair_ne_univ_four 0 1)
        ⟨(g : normOmega E 4), normBlock_mono E 4 (Finset.singleton_subset_iff.mpr hj) g.2⟩)
      (deletionPhiThree E t κ ({2, 3} : Finset (Fin 4)) (pair_ne_univ_four 2 3)
        ⟨y, hy23⟩) := by
  have hj' : j = 0 ∨ j = 1 := by simpa using hj
  have hlt : (j : ℕ) < 2 := by rcases hj' with rfl | rfl <;> norm_num
  have hR : ({j} : Finset (Fin 4)) ≠ Finset.univ :=
    (Finset.card_lt_iff_ne_univ _).mp (by simp)
  have hunion : (({2, 3} : Finset (Fin 4)) ∪ {j}) ≠ Finset.univ := by
    refine (Finset.card_lt_iff_ne_univ _).mp ?_
    calc (({2, 3} : Finset (Fin 4)) ∪ {j}).card
        ≤ ({2, 3} : Finset (Fin 4)).card + ({j} : Finset (Fin 4)).card :=
          Finset.card_union_le _ _
      _ = 3 := by simp
      _ < 4 := by norm_num
  have hsub : deletionPhiThree E t κ ({0, 1} : Finset (Fin 4)) (pair_ne_univ_four 0 1)
        ⟨(g : normOmega E 4), normBlock_mono E 4 (Finset.singleton_subset_iff.mpr hj) g.2⟩ =
      deletionPhiThree E t κ ({j} : Finset (Fin 4)) hR ⟨(g : normOmega E 4), g.2⟩ :=
    deletionPhiThree_of_subset hT1 hC hR (pair_ne_univ_four 0 1)
      (Finset.singleton_subset_iff.mpr hj) g.2
  rw [hsub]
  exact (commute_deletionPhiThree hT1 hC (pair_ne_univ_four 2 3) hR hunion hy23 g.2
    (commute_map_rankOne_of_three_le E hω (j := l) hl (k := j) hlt y hyL
      (g : normOmega E 4) g.2)).symm

private theorem commute_deletionPhiThree_pair_of_mem_rankOne_of_three_le
    (hT1 : t.comp (Equiv.Perm.viaEmbeddingHom Fin.castSuccEmb) = κ.comp (normPerm E le_rfl))
    (hC : ∀ y ∈ (anchorBlock E (by norm_num : 2 ≤ 3)).map κ, Commute (t (Equiv.swap 2 3)) y)
    {y : normOmega E 4} (hy23 : y ∈ normBlock E 4 ({2, 3} : Finset (Fin 4)))
    {l : Fin 5} (hl : 3 ≤ (l : ℕ))
    (hyL : y ∈ (rankOne (plusRootGroup 5 F (by norm_num)) l).map
      (qTwoLambda E hω).symm.toMonoidHom)
    {x : normOmega E 4} (hx01 : x ∈ normBlock E 4 ({0, 1} : Finset (Fin 4))) :
    Commute
      (deletionPhiThree E t κ ({0, 1} : Finset (Fin 4)) (pair_ne_univ_four 0 1) ⟨x, hx01⟩)
      (deletionPhiThree E t κ ({2, 3} : Finset (Fin 4)) (pair_ne_univ_four 2 3) ⟨y, hy23⟩) := by
  let P : Subgroup (normBlock E 4 ({0, 1} : Finset (Fin 4))) :=
    (Subgroup.centralizer
      ({(deletionPhiThree E t κ ({2, 3} : Finset (Fin 4)) (pair_ne_univ_four 2 3))
          ⟨y, hy23⟩} : Set H)).comap
      (deletionPhiThree E t κ ({0, 1} : Finset (Fin 4)) (pair_ne_univ_four 0 1))
  have h0 : ∀ g : normBlock E 4 ({0} : Finset (Fin 4)),
      (⟨(g : normOmega E 4), normBlock_mono E 4 (by simp) g.2⟩ :
        normBlock E 4 ({0, 1} : Finset (Fin 4))) ∈ P := by
    intro g
    dsimp only [P]
    rw [Subgroup.mem_comap]
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (commute_deletionPhiThree_singleton_of_mem_rankOne_of_three_le E hω hT1 hC hy23 hl hyL
        (j := 0) (by simp) g)
  have h1 : ∀ g : normBlock E 4 ({1} : Finset (Fin 4)),
      (⟨(g : normOmega E 4), normBlock_mono E 4 (by simp) g.2⟩ :
        normBlock E 4 ({0, 1} : Finset (Fin 4))) ∈ P := by
    intro g
    dsimp only [P]
    rw [Subgroup.mem_comap]
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (commute_deletionPhiThree_singleton_of_mem_rankOne_of_three_le E hω hT1 hC hy23 hl hyL
        (j := 1) (by simp) g)
  have hP : P = ⊤ := eq_top_of_singleton_le (i := 0) (j := 1) P h0 h1
  have hx : (⟨x, hx01⟩ : normBlock E 4 ({0, 1} : Finset (Fin 4))) ∈ P := by
    rw [hP]
    exact Subgroup.mem_top _
  exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_comap.mp hx)

theorem commute_qTwoRho_cross
    (hT1 : t.comp (Equiv.Perm.viaEmbeddingHom Fin.castSuccEmb) = κ.comp (normPerm E le_rfl))
    (hC : ∀ y ∈ (anchorBlock E (by norm_num : 2 ≤ 3)).map κ, Commute (t (Equiv.swap 2 3)) y)
    {k l : Fin 5} (hk : (k : ℕ) < 2) (hl : 2 ≤ (l : ℕ)) (hkl : ¬((k : ℕ) = 1 ∧ (l : ℕ) = 2))
    (a : rankOne (plusRootGroup 5 F (by norm_num)) k)
    (b : rankOne (plusRootGroup 5 F (by norm_num)) l) :
    Commute (qTwoRho E hω t κ k a) (qTwoRho E hω t κ l b) := by
  have hk01 : (k : ℕ) = 0 ∨ (k : ℕ) = 1 := by omega
  rcases hk01 with hk0 | hk1
  · have hk_eq : k = 0 := Fin.ext hk0
    subst hk_eq
    rw [qTwoRho_of_lt_two E hω hk a, qTwoRho_of_two_le E hω hl b]
    exact commute_deletionPhiThree_pair_of_mem_rankOne_zero E hω hT1 hC
      (map_rankOne_le_normBlock_zero_one E hω hk (Subgroup.mem_map_of_mem _ a.2))
      (Subgroup.mem_map_of_mem _ a.2)
      (map_rankOne_le_normBlock_two_three E hω hl (Subgroup.mem_map_of_mem _ b.2))
  · have hk_eq : k = 1 := Fin.ext hk1
    have hl2 : (l : ℕ) ≠ 2 := fun h => hkl ⟨hk1, h⟩
    have hl3 : 3 ≤ (l : ℕ) := by omega
    subst hk_eq
    rw [qTwoRho_of_lt_two E hω hk a, qTwoRho_of_two_le E hω hl b]
    exact commute_deletionPhiThree_pair_of_mem_rankOne_of_three_le E hω hT1 hC
      (map_rankOne_le_normBlock_two_three E hω hl (Subgroup.mem_map_of_mem _ b.2))
      hl3 (Subgroup.mem_map_of_mem _ b.2)
      (map_rankOne_le_normBlock_zero_one E hω hk (Subgroup.mem_map_of_mem _ a.2))

end CFSG.ClassicalGroups.Orthogonal.UnitaryOmega
