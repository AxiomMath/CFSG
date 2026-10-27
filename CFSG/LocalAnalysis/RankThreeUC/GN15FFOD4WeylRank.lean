module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.IndepRank
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.WordsG

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.D4

open CFSG.Quasithin.SmithCurtis CFSG.Quasithin.SmithCurtis.Chev CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc

@[expose] def invWord : Fin 5 → List (Fin 4) :=
  ![[0], [1, 3], [0, 1], [0, 3], [0, 1, 3, 2, 0, 1, 3, 2, 0, 1, 3, 2]]

@[expose] def vEnds : Fin 4 → ℤ := ![1, 1, 2, 1]

@[expose] def vCE : Fin 4 → Fin 4 → ℤ :=
  ![![2, 3, 4, 3], ![3, 2, 4, 3], ![1, 1, 2, 1], ![3, 3, 4, 2]]

@[expose] def caseVec : Fin 4 → Fin Tag.D4.rank → ℤ :=
  ![(vEnds : Fin Tag.D4.rank → ℤ), (vCE 0 : Fin Tag.D4.rank → ℤ),
    (vCE 1 : Fin Tag.D4.rank → ℤ), (vCE 3 : Fin Tag.D4.rank → ℤ)]

private theorem reflectLG_vEnds : ∀ j ∈ ({0, 1, 3} : Finset (Fin 4)),
    reflectLG .D4 j (List.ofFn (vEnds : Fin Tag.D4.rank → ℤ)) =
      List.ofFn (vEnds : Fin Tag.D4.rank → ℤ) := by
  decide +kernel

private theorem reflectLG_vCE : ∀ e ∈ ({0, 1, 3} : Finset (Fin 4)),
    ∀ j ∈ ({2, e} : Finset (Fin 4)),
      reflectLG .D4 j (List.ofFn (vCE e : Fin Tag.D4.rank → ℤ)) =
        List.ofFn (vCE e : Fin Tag.D4.rank → ℤ) := by
  decide +kernel

theorem reflect_vEnds : ∀ j ∈ ({0, 1, 3} : Finset (Fin 4)),
    reflect .D4 j vEnds = vEnds := by
  intro j hj
  have h := ofFn_reflectG (τ := .D4) j (vEnds : Fin Tag.D4.rank → ℤ)
  have hl := reflectLG_vEnds j hj
  exact List.ofFn_injective (h.trans hl)

theorem reflect_vCE : ∀ e ∈ ({0, 1, 3} : Finset (Fin 4)),
    ∀ j ∈ ({2, e} : Finset (Fin 4)), reflect .D4 j (vCE e) = vCE e := by
  intro e he j hj
  have h := ofFn_reflectG (τ := .D4) j (vCE e : Fin Tag.D4.rank → ℤ)
  have hl := reflectLG_vCE e he j hj
  exact List.ofFn_injective (h.trans hl)

theorem invWord_four_smul
    (α : Fin Tag.D4.rank → ℤ) : (coxeterSystem .D4).wordProd (invWord 4) • α = -α :=
  wordProd_smul_neg_of_single (τ := .D4) (l := invWord 4) (by decide +kernel) α

private theorem wordProd_smul_D4
    (l : List (Fin 4)) (v : Fin Tag.D4.rank → ℤ) :
    (coxeterSystem .D4).wordProd l • v = l.foldr (reflect .D4) v :=
  wordProd_smul' (τ := .D4) l v

private theorem ofFn_foldr_reflectG_D4 (l : List (Fin 4)) (v : Fin Tag.D4.rank → ℤ) :
    List.ofFn (l.foldr (reflect .D4) v) = l.foldr (reflectLG .D4) (List.ofFn v) :=
  ofFn_foldr_reflectG (τ := .D4) l v

private theorem wordProd_append_D4 (l l' : List (Fin 4)) :
    (coxeterSystem .D4).wordProd (l ++ l') =
      (coxeterSystem .D4).wordProd l * (coxeterSystem .D4).wordProd l' :=
  CoxeterSystem.wordProd_append (cs := coxeterSystem .D4) l l'

theorem subset_ends_or_subset_center_end {J : Finset (Fin Tag.D4.rank)} (hJu : J ≠ Finset.univ)
    (hJe : ∀ e ∈ ({0, 1, 3} : Finset (Fin 4)), J ≠ Finset.univ.erase e) :
    J ⊆ ({0, 1, 3} : Finset (Fin 4)) ∨
      ∃ e ∈ ({0, 1, 3} : Finset (Fin 4)), J ⊆ ({2, e} : Finset (Fin 4)) := by
  have h : ∀ J : Finset (Fin 4), J ≠ Finset.univ →
      (∀ e ∈ ({0, 1, 3} : Finset (Fin 4)), J ≠ Finset.univ.erase e) →
      J ⊆ ({0, 1, 3} : Finset (Fin 4)) ∨
        ∃ e ∈ ({0, 1, 3} : Finset (Fin 4)), J ⊆ ({2, e} : Finset (Fin 4)) := by
    decide +kernel
  exact h J hJu hJe

@[expose] def pairWords : Fin 4 → Fin 5 → Fin 9 → List (Fin 4) :=
  ![
    ![
      ![[2], [1, 2], [3, 2], [3, 1, 2], [2, 3, 1, 2], [2, 3, 1, 0, 2], [2, 3, 2, 1, 0, 2],
        [1, 2, 3, 1, 0, 2], [1, 2, 3, 2, 1, 0, 2]],
      ![[2], [0, 2], [1, 2], [1, 0, 2], [2, 1, 0, 2], [2, 3, 0, 2], [2, 3, 1, 0, 2],
        [2, 3, 2, 1, 0, 2], [0, 2, 3, 1, 0, 2]],
      ![[2], [0, 2], [3, 2], [3, 0, 2], [2, 3, 0, 2], [2, 3, 1, 2], [2, 3, 1, 0, 2],
        [2, 3, 2, 1, 0, 2], [0, 2, 3, 1, 0, 2]],
      ![[2], [0, 2], [1, 2], [1, 0, 2], [2, 1, 0, 2], [2, 3, 1, 2], [2, 3, 1, 0, 2],
        [2, 3, 2, 1, 0, 2], [1, 2, 3, 1, 0, 2]],
      ![[], [2], [0, 2], [1, 2], [3, 2], [1, 0, 2], [3, 0, 2], [3, 1, 2], [2, 1, 0, 2]]
    ],
    ![
      ![[2, 1], [2, 3], [3, 2, 1], [2, 3, 1], [1, 2, 3], [2, 3, 2, 1], [1, 2, 3, 1],
        [2, 3, 0, 2, 1], [1, 2, 3, 2, 1]],
      ![[], [1], [2, 1], [2, 3], [0, 2, 1], [2, 3, 1], [0, 2, 3], [2, 3, 2, 1], [0, 2, 3, 1]],
      ![[], [3], [2, 1], [2, 3], [3, 2, 1], [2, 3, 1], [0, 2, 3], [2, 3, 2, 1], [0, 2, 3, 1]],
      ![[], [1], [2, 1], [2, 3], [0, 2, 1], [2, 3, 1], [1, 2, 3], [2, 3, 2, 1], [1, 2, 3, 1]],
      ![[], [1], [3], [2, 1], [3, 1], [2, 3], [0, 2, 1], [3, 2, 1], [2, 3, 1]]
    ],
    ![
      ![[], [3], [2, 3], [2, 3, 0], [1, 2, 3], [2, 3, 2, 0], [1, 2, 3, 0], [2, 3, 1, 2, 0],
        [1, 2, 3, 2, 0]],
      ![[], [0], [2, 0], [2, 3], [1, 2, 0], [2, 3, 0], [0, 2, 3], [2, 3, 2, 0], [0, 2, 3, 0]],
      ![[], [3], [2, 0], [2, 3], [3, 2, 0], [2, 3, 0], [0, 2, 3], [2, 3, 2, 0], [0, 2, 3, 0]],
      ![[], [0], [2, 0], [2, 3], [1, 2, 0], [2, 3, 0], [1, 2, 3], [2, 3, 2, 0], [1, 2, 3, 0]],
      ![[], [0], [3], [2, 0], [3, 0], [2, 3], [1, 2, 0], [3, 2, 0], [2, 3, 0]]
    ],
    ![
      ![[], [1], [2, 1], [2, 1, 0], [3, 2, 1], [1, 2, 1, 0], [3, 2, 1, 0], [3, 1, 2, 1, 0],
        [2, 3, 1, 2, 0]],
      ![[], [0], [2, 0], [2, 1], [2, 1, 0], [1, 2, 0], [0, 2, 1], [0, 2, 1, 0], [1, 2, 1, 0]],
      ![[], [0], [2, 0], [2, 1], [2, 1, 0], [3, 2, 0], [3, 2, 1], [0, 2, 1, 0], [3, 2, 1, 0]],
      ![[], [1], [2, 0], [2, 1], [2, 1, 0], [1, 2, 0], [0, 2, 1], [0, 2, 1, 0], [1, 2, 1, 0]],
      ![[], [0], [1], [1, 0], [2, 0], [2, 1], [2, 1, 0], [1, 2, 0], [3, 2, 0]]
    ]
  ]

@[expose] def caseVecAt (c : Fin 4) (x : Fin 5) (k : Fin 9) : List ℤ :=
  (pairWords c x k).foldr (reflectLG .D4) (List.ofFn (caseVec c))

@[expose] def caseVecAt' (c : Fin 4) (x : Fin 5) (k : Fin 9) : List ℤ :=
  (invWord x ++ pairWords c x k).foldr (reflectLG .D4) (List.ofFn (caseVec c))

theorem pairWords_check : ∀ (c : Fin 4) (x : Fin 5),
    (∀ a b : Fin 9, a ≠ b → caseVecAt c x a ≠ caseVecAt c x b) ∧
      (∀ a b : Fin 9, a ≠ b → caseVecAt' c x a ≠ caseVecAt' c x b) ∧
        ∀ a b : Fin 9, caseVecAt c x a ≠ caseVecAt' c x b := by
  decide +kernel

section Chev


variable {K : Type} [Field K] [Finite K] [CharP K 2]
  {hw : ∃ w₁ : WeylGroup Tag.D4, ∀ α : Fin Tag.D4.rank → ℤ, w₁ • α = -α}
  {k V : Type*} [Field k] [Algebra K k] [CharP k 2] [AddCommGroup V] [Module k V]
  [Module.Finite k V] {ρ : Representation k (adjointGroup .D4 K) V} {y : V}
  {χ : adjointGroup .D4 K → k} {J : Finset (Fin Tag.D4.rank)}

private theorem nine_le_of_case (hρ : IsSimpleRep ρ)
    (ht : IsChevType .D4 K 2 hw ρ y χ J) (c : Fin 4) (x : Fin 5)
    (hv : ∀ j ∈ J, reflect .D4 j (caseVec c) = caseVec c) :
    9 ≤ Module.finrank k (LinearMap.range
      (ρ ((chevDatum .D4 K 2 hw).nW ((coxeterSystem .D4).wordProd (invWord x))) - 1)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcheck := pairWords_check c x
  refine le_finrank_range_sub_one_of_isChevType (p := 2) hρ ht hv
    ((coxeterSystem .D4).wordProd (invWord x)) (m := 9)
    (fun a => (coxeterSystem .D4).wordProd (pairWords c x a)) ?_ ?_
  · intro a b hab h
    refine hcheck.1 a b hab ?_
    have h1 : (pairWords c x a).foldr (reflect .D4) (caseVec c) =
        (pairWords c x b).foldr (reflect .D4) (caseVec c) := by
      simpa only [wordProd_smul_D4] using h
    have h2 := congrArg List.ofFn h1
    rw [ofFn_foldr_reflectG_D4, ofFn_foldr_reflectG_D4] at h2
    simpa [caseVecAt] using h2
  · intro a b h
    refine hcheck.2.2 a b ?_
    have h1 : (pairWords c x a).foldr (reflect .D4) (caseVec c) =
        (invWord x ++ pairWords c x b).foldr (reflect .D4) (caseVec c) := by
      rw [← wordProd_append_D4] at h
      simpa only [wordProd_smul_D4] using h
    have h2 := congrArg List.ofFn h1
    rw [ofFn_foldr_reflectG_D4, ofFn_foldr_reflectG_D4] at h2
    simpa [caseVecAt, caseVecAt'] using h2

theorem nine_le_finrank_range_of_subset_ends (hρ : IsSimpleRep ρ)
    (ht : IsChevType .D4 K 2 hw ρ y χ J) (hJ : J ⊆ ({0, 1, 3} : Finset (Fin 4))) (i : Fin 5) :
    9 ≤ Module.finrank k (LinearMap.range
      (ρ ((chevDatum .D4 K 2 hw).nW ((coxeterSystem .D4).wordProd (invWord i))) - 1)) :=
  nine_le_of_case (c := 0) (x := i) hρ ht fun j hj => reflect_vEnds j (hJ hj)

theorem nine_le_finrank_range_of_subset_center_end (hρ : IsSimpleRep ρ)
    (ht : IsChevType .D4 K 2 hw ρ y χ J) {e : Fin 4}
    (he : e ∈ ({0, 1, 3} : Finset (Fin 4))) (hJ : J ⊆ ({2, e} : Finset (Fin 4))) (i : Fin 5) :
    9 ≤ Module.finrank k (LinearMap.range
      (ρ ((chevDatum .D4 K 2 hw).nW ((coxeterSystem .D4).wordProd (invWord i))) - 1)) := by
  have he' : e = 0 ∨ e = 1 ∨ e = 3 := by simpa using he
  rcases he' with rfl | rfl | rfl
  · exact nine_le_of_case (c := 1) (x := i) hρ ht fun j hj =>
      reflect_vCE 0 (by decide) j (hJ hj)
  · exact nine_le_of_case (c := 2) (x := i) hρ ht fun j hj =>
      reflect_vCE 1 (by decide) j (hJ hj)
  · exact nine_le_of_case (c := 3) (x := i) hρ ht fun j hj =>
      reflect_vCE 3 (by decide) j (hJ hj)

theorem nine_le_finrank_range_of_not_natural (hρ : IsSimpleRep ρ)
    (ht : IsChevType .D4 K 2 hw ρ y χ J) (hJu : J ≠ Finset.univ)
    (hJe : ∀ e ∈ ({0, 1, 3} : Finset (Fin 4)), J ≠ Finset.univ.erase e) (i : Fin 5) :
    9 ≤ Module.finrank k (LinearMap.range
      (ρ ((chevDatum .D4 K 2 hw).nW ((coxeterSystem .D4).wordProd (invWord i))) - 1)) := by
  rcases subset_ends_or_subset_center_end hJu hJe with hJ | ⟨e, he, hJ⟩
  · exact nine_le_finrank_range_of_subset_ends hρ ht hJ i
  · exact nine_le_finrank_range_of_subset_center_end hρ ht he hJ i

end Chev

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.D4
