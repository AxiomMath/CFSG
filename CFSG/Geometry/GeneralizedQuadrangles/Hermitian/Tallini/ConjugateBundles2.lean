module

public import CFSG.Geometry.GeneralizedQuadrangles.Hermitian.Tallini.ConjugateBundles

public section

namespace CFSG.Geometry.GeneralizedQuadrangles

open SimpleGraph CFSG.Geometry.GeneralizedPolygons

universe u

variable {V : Type u}

section ConjugateBundles2

variable {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj]

private theorem isNonabsPlane_of_isConjPlane_of_ne_ptPerp (hP : IsGeneralizedPolygon Γ 4)
    (hT : IsThick Γ) (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hreg : ∀ x, c x = 0 → IsRegularVertex Γ x) {Y W : Set V} {x : V}
    (hY : IsNonabsPlane Γ c Y) (hxY : x ∈ Y) (hW : IsStarPlane Γ c W) (hxW : x ∈ W)
    (hYW : IsConjPlane Γ c Y W) (hWx : W ≠ ptPerp Γ c {x}) : IsNonabsPlane Γ c W := by
  classical
  rcases isStarPlane_cases hP hT c hdeg hreg hW with habs | hnon
  · obtain ⟨w, hw0, hWw⟩ := habs
    exfalso
    have hwY : w ∈ Y := by
      have hmem : ptPerp Γ c {w} ∈ conjNet Γ c Y := by
        rw [← hWw]
        exact ⟨hW, hYW⟩
      exact (ptPerp_mem_conjNet_iff hP hT c hdeg hreg hY.1 hw0).mp hmem
    have hxw : x ∈ ptPerp Γ c {w} := by rw [← hWw]; exact hxW
    have hle : Γ.dist w x ≤ 2 := by
      have h := (mem_ptPerp.mp hxw).2 w (by simp)
      rwa [SimpleGraph.dist_comm] at h
    have hwx : w = x := by
      by_contra hne
      have h4 : Γ.dist w x = 4 := dist_eq_four_of_mem_of_isOvoid hP hT hY.2 hwY hxY hne
      omega
    exact hWx (by rw [hwx] at hWw; exact hWw)
  · exact hnon

private theorem conjPlaneSet_eq_tangentBundle (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hreg : ∀ x, c x = 0 → IsRegularVertex Γ x) (hst : s ≠ t) (hii : TalliniCond Γ c)
    {X Y : Set V} {x : V} (hX : IsNonabsPlane Γ c X) (hx : x ∈ X)
    (hY : IsNonabsPlane Γ c Y) (hxY : x ∈ Y) (hXY : IsConjPlane Γ c X Y) :
    {W : Set V | IsStarPlane Γ c W ∧ x ∈ W ∧ IsConjPlane Γ c Y W} = tangentBundle Γ c X x := by
  classical
  have hii' : TalliniCondPrime Γ c := talliniCondPrime_of_talliniCond hP hT c hdeg hreg hii
  have hx0 : c x = 0 := hX.1.1.1.1 x hx
  have hYstar : IsStarPlane Γ c Y := hY.1
  have hYne : Y ≠ ptPerp Γ c {x} := ne_ptPerp_of_isNonabsPlane hP hT c hdeg hY hxY
  have hxperpPlane : IsStarPlane Γ c (ptPerp Γ c {x}) :=
    isStarPlane_ptPerp_singleton hP hT c hdeg hx0
  have hXint : X ∩ ptPerp Γ c {x} = {x} :=
    inter_ptPerp_eq_singleton_of_isNonabsPlane hP hT hX hx
  have hYX : IsConjPlane Γ c Y X := (isConjPlane_comm hP hT c hdeg hreg).mp hXY
  have hCsub : {W : Set V | IsStarPlane Γ c W ∧ x ∈ W ∧ IsConjPlane Γ c Y W} ⊆
      tangentBundle Γ c X x := by
    rintro W ⟨hWplane, hxW, hYW⟩
    by_cases hWx : W = ptPerp Γ c {x}
    · rw [hWx]
      exact ⟨hxperpPlane, Or.inr hXint⟩
    · have hWnon : IsNonabsPlane Γ c W :=
        isNonabsPlane_of_isConjPlane_of_ne_ptPerp hP hT c hdeg hreg hY hxY hWplane hxW hYW hWx
      rcases eq_or_inter_eq_singleton_of_isConjPlane hP hT c hdeg hreg hst hii
        hY hX hWnon hxY hx hxW hYX hYW with hXW | hXW
      · rw [← hXW]
        exact ⟨hX.1, Or.inl rfl⟩
      · exact ⟨hWplane, Or.inr hXW⟩
  let Cf : Finset (Set V) :=
    Finset.univ.filter (fun W => IsStarPlane Γ c W ∧ x ∈ W ∧ IsConjPlane Γ c Y W)
  have hCfmem : ∀ W : Set V, W ∈ Cf ↔ IsStarPlane Γ c W ∧ x ∈ W ∧ IsConjPlane Γ c Y W := by
    intro W
    simp only [Cf, Finset.mem_filter, Finset.mem_univ, true_and]
  have hCfcoe : (Cf : Set (Set V)) = {W | IsStarPlane Γ c W ∧ x ∈ W ∧ IsConjPlane Γ c Y W} := by
    ext W
    rw [Finset.mem_coe, hCfmem]
    rfl
  have hxperpCf : ptPerp Γ c {x} ∈ Cf := by
    rw [hCfmem]
    refine ⟨hxperpPlane, ?_, ?_⟩
    · rw [mem_ptPerp]
      exact ⟨hx0, by intro z hz; rw [Set.mem_singleton_iff] at hz; rw [hz]; simp⟩
    · exact ((ptPerp_mem_conjNet_iff hP hT c hdeg hreg hYstar hx0).mpr hxY).2
  have hc_le : Cf.card ≤ s + 1 := by
    have hβcard : (tangentBundle Γ c X x).ncard = s + 1 :=
      ncard_of_isPlaneBundle hP hT c hdeg hreg hst hii'
        (Or.inr ⟨X, x, hX, hx, rfl⟩)
    have hsub : (Cf : Set (Set V)) ⊆ tangentBundle Γ c X x := by
      intro W hW
      rw [hCfcoe] at hW
      exact hCsub ⟨hW.1, hW.2.1, hW.2.2⟩
    calc Cf.card = (Cf : Set (Set V)).ncard := by rw [Set.ncard_coe_finset]
      _ ≤ (tangentBundle Γ c X x).ncard := Set.ncard_le_ncard hsub
      _ = s + 1 := hβcard
  let Lall : Finset (Set V) := Finset.univ.filter (fun ℓ => IsHypLine Γ c ℓ ∧ x ∈ ℓ)
  let LY : Finset (Set V) := Finset.univ.filter (fun ℓ => IsHypLine Γ c ℓ ∧ x ∈ ℓ ∧ ℓ ⊆ Y)
  let Lf : Finset (Set V) := Finset.univ.filter (fun ℓ => IsHypLine Γ c ℓ ∧ x ∈ ℓ ∧ ¬ ℓ ⊆ Y)
  have hLfmem : ∀ ℓ : Set V, ℓ ∈ Lf ↔ IsHypLine Γ c ℓ ∧ x ∈ ℓ ∧ ¬ ℓ ⊆ Y := by
    intro ℓ
    simp only [Lf, Finset.mem_filter, Finset.mem_univ, true_and]
  have hLallcard : Lall.card = s ^ 2 := by
    have hcoe : (Lall : Set (Set V)) = {ℓ | IsHypLine Γ c ℓ ∧ x ∈ ℓ} := by
      ext ℓ
      simp only [Lall, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_coe,
        Set.mem_setOf_eq]
    rw [← Set.ncard_coe_finset, hcoe]
    exact ncard_hypLines_through hP hT c hdeg hreg hx0
  have hLYcard : LY.card = s := by
    have hcoe : (LY : Set (Set V)) = {ℓ | IsHypLine Γ c ℓ ∧ x ∈ ℓ ∧ ℓ ⊆ Y} := by
      ext ℓ
      simp only [LY, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_coe,
        Set.mem_setOf_eq]
    rw [← Set.ncard_coe_finset, hcoe]
    exact ncard_hypLines_through_subset hP hT c hdeg hreg hYstar hxY hYne
  have hLfcard : Lf.card = s ^ 2 - s := by
    have hunion : Lall = LY ∪ Lf := by
      ext ℓ
      simp only [Lall, LY, Lf, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
        true_and]
      tauto
    have hdisj : Disjoint LY Lf := by
      rw [Finset.disjoint_left]
      intro ℓ hℓY hℓf
      simp only [LY, Finset.mem_filter, Finset.mem_univ, true_and] at hℓY
      simp only [Lf, Finset.mem_filter, Finset.mem_univ, true_and] at hℓf
      exact hℓf.2.2 hℓY.2.2
    have hcard : Lall.card = LY.card + Lf.card := by
      rw [hunion, Finset.card_union_of_disjoint hdisj]
    have hs : 2 ≤ s := two_le_s hP hT c hdeg
    have hsle : s ≤ s ^ 2 := by nlinarith
    omega
  let Wf : Set V → Set V := fun ℓ =>
    if h : ∃ W, IsStarPlane Γ c W ∧ ℓ ⊆ W ∧ IsConjPlane Γ c Y W then Classical.choose h else ∅
  have hWf_spec : ∀ ℓ : Set V, IsHypLine Γ c ℓ → ¬ ℓ ⊆ Y → ¬ ptPerp Γ c ℓ ⊆ Y →
      IsStarPlane Γ c (Wf ℓ) ∧ ℓ ⊆ Wf ℓ ∧ IsConjPlane Γ c Y (Wf ℓ) := by
    intro ℓ hℓ hℓY hℓperp
    have hex : ∃ W, IsStarPlane Γ c W ∧ ℓ ⊆ W ∧ IsConjPlane Γ c Y W :=
      (existsUnique_conjPlane_superset hP hT c hdeg hreg hii hYstar
        (IsHypLine.isStarLine hP hℓ) hℓY hℓperp).exists
    show IsStarPlane Γ c (if h : ∃ W, IsStarPlane Γ c W ∧ ℓ ⊆ W ∧ IsConjPlane Γ c Y W
        then Classical.choose h else ∅) ∧
      ℓ ⊆ (if h : ∃ W, IsStarPlane Γ c W ∧ ℓ ⊆ W ∧ IsConjPlane Γ c Y W
        then Classical.choose h else ∅) ∧
      IsConjPlane Γ c Y (if h : ∃ W, IsStarPlane Γ c W ∧ ℓ ⊆ W ∧ IsConjPlane Γ c Y W
        then Classical.choose h else ∅)
    rw [dif_pos hex]
    exact Classical.choose_spec hex
  have hWf_unique : ∀ ℓ : Set V, IsHypLine Γ c ℓ → ¬ ℓ ⊆ Y → ¬ ptPerp Γ c ℓ ⊆ Y →
      ∀ W : Set V, IsStarPlane Γ c W → ℓ ⊆ W → IsConjPlane Γ c Y W → Wf ℓ = W := by
    intro ℓ hℓ hℓY hℓperp W hWplane hℓW hYW
    obtain ⟨W₀, hW₀, huniq⟩ := existsUnique_conjPlane_superset hP hT c hdeg hreg hii hYstar
      (IsHypLine.isStarLine hP hℓ) hℓY hℓperp
    obtain ⟨h1, h2, h3⟩ := hWf_spec ℓ hℓ hℓY hℓperp
    exact (huniq (Wf ℓ) ⟨h1, h2, h3⟩).trans (huniq W ⟨hWplane, hℓW, hYW⟩).symm
  have hℓperpNot : ∀ ℓ : Set V, IsHypLine Γ c ℓ → x ∈ ℓ → ¬ ptPerp Γ c ℓ ⊆ Y := by
    intro ℓ hℓ hxℓ hsub
    have hdisj := disjoint_of_ptPerp_subset hP hT c hdeg hreg hY
      (IsHypLine.isStarLine hP hℓ) hsub
    exact (Set.disjoint_left.mp hdisj) hxℓ hxY
  have hWfmem : ∀ ℓ ∈ Lf, Wf ℓ ∈ Cf := by
    intro ℓ hℓ
    obtain ⟨hℓhyp, hxℓ, hℓY⟩ := (hLfmem ℓ).mp hℓ
    obtain ⟨h1, h2, h3⟩ := hWf_spec ℓ hℓhyp hℓY (hℓperpNot ℓ hℓhyp hxℓ)
    rw [hCfmem]
    exact ⟨h1, h2 hxℓ, h3⟩
  have hfiber_eq : ∀ W : Set V, W ∈ Cf → W ≠ ptPerp Γ c {x} →
      (Lf.filter (fun ℓ => Wf ℓ = W)) =
        (Finset.univ.filter (fun ℓ => IsHypLine Γ c ℓ ∧ x ∈ ℓ ∧ ℓ ⊆ W)) \
          (Finset.univ.filter (fun ℓ => IsHypLine Γ c ℓ ∧ x ∈ ℓ ∧ ℓ ⊆ W ∩ Y)) := by
    intro W hW hWne
    obtain ⟨hWplane, hxW, hYW⟩ := (hCfmem W).mp hW
    ext ℓ
    simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and, hLfmem]
    constructor
    · rintro ⟨⟨hℓhyp, hxℓ, hℓY⟩, hℓW⟩
      have hℓW' : ℓ ⊆ W := by
        rw [← hℓW]
        exact (hWf_spec ℓ hℓhyp hℓY (hℓperpNot ℓ hℓhyp hxℓ)).2.1
      refine ⟨⟨hℓhyp, hxℓ, hℓW'⟩, ?_⟩
      rintro ⟨-, -, hsub⟩
      exact hℓY (fun z hz => (hsub hz).2)
    · rintro ⟨⟨hℓhyp, hxℓ, hℓW⟩, hnotB⟩
      have hℓY : ¬ ℓ ⊆ Y := by
        intro hℓsubY
        exact hnotB ⟨hℓhyp, hxℓ, fun z hz => ⟨hℓW hz, hℓsubY hz⟩⟩
      exact ⟨⟨hℓhyp, hxℓ, hℓY⟩,
        hWf_unique ℓ hℓhyp hℓY (hℓperpNot ℓ hℓhyp hxℓ) W hWplane hℓW hYW⟩
  have hBsubA : ∀ W : Set V,
      (Finset.univ.filter (fun ℓ => IsHypLine Γ c ℓ ∧ x ∈ ℓ ∧ ℓ ⊆ W ∩ Y)) ⊆
        (Finset.univ.filter (fun ℓ => IsHypLine Γ c ℓ ∧ x ∈ ℓ ∧ ℓ ⊆ W)) := by
    intro W ℓ hℓ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hℓ ⊢
    exact ⟨hℓ.1, hℓ.2.1, fun z hz => (hℓ.2.2 hz).1⟩
  have hAcard : ∀ W : Set V, W ∈ Cf → W ≠ ptPerp Γ c {x} →
      (Finset.univ.filter (fun ℓ => IsHypLine Γ c ℓ ∧ x ∈ ℓ ∧ ℓ ⊆ W)).card = s := by
    intro W hW hWne
    obtain ⟨hWplane, hxW, -⟩ := (hCfmem W).mp hW
    have hcoe : (Finset.univ.filter (fun ℓ => IsHypLine Γ c ℓ ∧ x ∈ ℓ ∧ ℓ ⊆ W) :
        Set (Set V)) = {ℓ | IsHypLine Γ c ℓ ∧ x ∈ ℓ ∧ ℓ ⊆ W} := by
      ext ℓ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_coe, Set.mem_setOf_eq]
    rw [← Set.ncard_coe_finset, hcoe]
    exact ncard_hypLines_through_subset hP hT c hdeg hreg hWplane hxW hWne
  have hBcard_line : ∀ W : Set V, W ∈ Cf → IsStarLine Γ c (W ∩ Y) →
      (Finset.univ.filter (fun ℓ => IsHypLine Γ c ℓ ∧ x ∈ ℓ ∧ ℓ ⊆ W ∩ Y)).card = 1 := by
    intro W hW hWY
    obtain ⟨hWplane, hxW, -⟩ := (hCfmem W).mp hW
    have hWhyp : IsHypLine Γ c (W ∩ Y) :=
      isHypLine_of_isStarLine_subset_of_isNonabsPlane hP hT hY hWY Set.inter_subset_right
    have hset : (Finset.univ.filter (fun ℓ => IsHypLine Γ c ℓ ∧ x ∈ ℓ ∧ ℓ ⊆ W ∩ Y)) =
        ({W ∩ Y} : Finset (Set V)) := by
      ext ℓ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · rintro ⟨hℓhyp, hxℓ, hℓsub⟩
        exact eq_of_isStarLine_subset hP hT (IsHypLine.isStarLine hP hℓhyp) hWY hℓsub
      · rintro rfl
        exact ⟨hWhyp, ⟨hxW, hxY⟩, fun z hz => hz⟩
    rw [hset, Finset.card_singleton]
  have hBcard_pt : ∀ W : Set V, W ∈ Cf → ¬ IsStarLine Γ c (W ∩ Y) →
      (Finset.univ.filter (fun ℓ => IsHypLine Γ c ℓ ∧ x ∈ ℓ ∧ ℓ ⊆ W ∩ Y)).card = 0 := by
    intro W hW hWnot
    obtain ⟨hWplane, hxW, hYW⟩ := (hCfmem W).mp hW
    have hWYne : W ≠ Y := by
      intro h
      have hYY : IsConjPlane Γ c Y Y := by rwa [h] at hYW
      exact not_isNonabsPlane_of_isAbsPlane hP hT c hdeg
        ((isConjPlane_self_iff hP hT c hdeg hreg hYstar).mp hYY) hY
    have hWY : W ∩ Y = {x} := by
      rcases inter_cases hP hT c hdeg hreg hWplane hYstar hWYne with hemp | hsingle | hline
      · have hne : (W ∩ Y).Nonempty :=
          inter_nonempty hP hT c hdeg hreg hst hii' hWplane hYstar
        rw [hemp] at hne
        exact absurd hne (by simp)
      · obtain ⟨z, hz⟩ := hsingle
        rw [hz]
        have hxz : x = z := by
          have hmem : x ∈ ({z} : Set V) := by rw [← hz]; exact ⟨hxW, hxY⟩
          simpa using hmem
        rw [hxz]
      · exact absurd hline hWnot
    have hempty : (Finset.univ.filter (fun ℓ => IsHypLine Γ c ℓ ∧ x ∈ ℓ ∧ ℓ ⊆ W ∩ Y)) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro ℓ hℓ hp
      obtain ⟨hℓhyp, hxℓ, hℓsub⟩ := hp
      have hℓcard : ℓ.ncard = t + 1 := IsHypLine.ncard hP hT c hdeg hreg hℓhyp
      have hsub' : ℓ ⊆ ({x} : Set V) := by rw [← hWY]; exact hℓsub
      have hle : ℓ.ncard ≤ 1 := by
        have := Set.ncard_le_ncard hsub'
        simpa using this
      have ht : 2 ≤ t := two_le_t hP hT c hdeg
      omega
    rw [hempty, Finset.card_empty]
  let Cf' : Finset (Set V) := Cf.erase (ptPerp Γ c {x})
  let CfA : Finset (Set V) := Cf'.filter (fun W => IsStarLine Γ c (W ∩ Y))
  let CfB : Finset (Set V) := Cf'.filter (fun W => ¬ IsStarLine Γ c (W ∩ Y))
  have hCf'mem : ∀ W ∈ Cf', W ∈ Cf ∧ W ≠ ptPerp Γ c {x} := by
    intro W hW
    simp only [Cf', Finset.mem_erase] at hW
    exact ⟨hW.2, hW.1⟩
  have hCf'split : Cf' = CfA ∪ CfB := by
    simp only [CfA, CfB]
    exact (Finset.filter_union_filter_not_eq (p := fun W => IsStarLine Γ c (W ∩ Y)) Cf').symm
  have hCf'disj : Disjoint CfA CfB := by
    rw [Finset.disjoint_left]
    intro W hA hB
    simp only [CfA, CfB, Finset.mem_filter] at hA hB
    exact hB.2 hA.2
  have hfiberA : ∀ W ∈ CfA, (Lf.filter (fun ℓ => Wf ℓ = W)).card = s - 1 := by
    intro W hW
    have hW' : W ∈ Cf' := (Finset.mem_filter.mp hW).1
    have hWY : IsStarLine Γ c (W ∩ Y) := (Finset.mem_filter.mp hW).2
    obtain ⟨hWcf, hWne⟩ := hCf'mem W hW'
    rw [hfiber_eq W hWcf hWne, Finset.card_sdiff_of_subset (hBsubA W),
      hAcard W hWcf hWne, hBcard_line W hWcf hWY]
  have hfiberB : ∀ W ∈ CfB, (Lf.filter (fun ℓ => Wf ℓ = W)).card = s := by
    intro W hW
    have hW' : W ∈ Cf' := (Finset.mem_filter.mp hW).1
    have hWY : ¬ IsStarLine Γ c (W ∩ Y) := (Finset.mem_filter.mp hW).2
    obtain ⟨hWcf, hWne⟩ := hCf'mem W hW'
    rw [hfiber_eq W hWcf hWne, Finset.card_sdiff_of_subset (hBsubA W),
      hAcard W hWcf hWne, hBcard_pt W hWcf hWY, Nat.sub_zero]
  have hsumA : ∑ W ∈ CfA, (Lf.filter (fun ℓ => Wf ℓ = W)).card = CfA.card * (s - 1) := by
    calc
      ∑ W ∈ CfA, (Lf.filter (fun ℓ => Wf ℓ = W)).card =
          ∑ W ∈ CfA, (s - 1) := Finset.sum_congr rfl hfiberA
      _ = CfA.card * (s - 1) := by rw [Finset.sum_const, smul_eq_mul]
  have hsumB : ∑ W ∈ CfB, (Lf.filter (fun ℓ => Wf ℓ = W)).card = CfB.card * s := by
    calc
      ∑ W ∈ CfB, (Lf.filter (fun ℓ => Wf ℓ = W)).card =
          ∑ W ∈ CfB, s := Finset.sum_congr rfl hfiberB
      _ = CfB.card * s := by rw [Finset.sum_const, smul_eq_mul]
  have hfiberZero : (Lf.filter (fun ℓ => Wf ℓ = ptPerp Γ c {x})).card = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro ℓ hℓ hℓW
    obtain ⟨hℓhyp, hxℓ, hℓY⟩ := (hLfmem ℓ).mp hℓ
    have hsub : ℓ ⊆ ptPerp Γ c {x} := by
      rw [← hℓW]
      exact (hWf_spec ℓ hℓhyp hℓY (hℓperpNot ℓ hℓhyp hxℓ)).2.1
    exact not_subset_ptPerp_singleton_of_isHypLine hP hT hx0 hℓhyp hxℓ hsub
  have hsum : Lf.card = CfA.card * (s - 1) + CfB.card * s := by
    have hfiberwise : Lf.card = ∑ W ∈ Cf, (Lf.filter (fun ℓ => Wf ℓ = W)).card :=
      Finset.card_eq_sum_card_fiberwise (fun ℓ hℓ => hWfmem ℓ hℓ)
    calc
      Lf.card = ∑ W ∈ Cf, (Lf.filter (fun ℓ => Wf ℓ = W)).card := hfiberwise
      _ = (Lf.filter (fun ℓ => Wf ℓ = ptPerp Γ c {x})).card +
            ∑ W ∈ Cf.erase (ptPerp Γ c {x}), (Lf.filter (fun ℓ => Wf ℓ = W)).card :=
          (Finset.add_sum_erase Cf (fun W => (Lf.filter fun ℓ => Wf ℓ = W).card) hxperpCf).symm
      _ = 0 + ∑ W ∈ Cf', (Lf.filter (fun ℓ => Wf ℓ = W)).card := by
          rw [hfiberZero]
      _ = ∑ W ∈ CfA, (Lf.filter (fun ℓ => Wf ℓ = W)).card +
            ∑ W ∈ CfB, (Lf.filter (fun ℓ => Wf ℓ = W)).card := by
          rw [hCf'split, Finset.sum_union hCf'disj, Nat.zero_add]
      _ = CfA.card * (s - 1) + CfB.card * s := by rw [hsumA, hsumB]
  have hLf' : Lf.card = s * (s - 1) := by
    rw [hLfcard]
    have hmul : s * (s - 1) = s * s - s := by rw [Nat.mul_sub_left_distrib]; simp
    rw [show s ^ 2 = s * s by ring, hmul]
  have hsum' : s * (s - 1) = CfA.card * (s - 1) + CfB.card * s := by
    rw [← hLf']
    exact hsum
  have hAB : CfA.card + CfB.card = Cf.card - 1 := by
    have h1 : Cf'.card = CfA.card + CfB.card := by
      rw [hCf'split, Finset.card_union_of_disjoint hCf'disj]
    have h2 : Cf'.card = Cf.card - 1 := by
      simp only [Cf']
      rw [Finset.card_erase_of_mem hxperpCf]
    omega
  have ha_le : CfA.card ≤ s := by
    have hmaps : ∀ W ∈ CfA, W ∩ Y ∈ LY := by
      intro W hW
      have hW' : W ∈ Cf' := (Finset.mem_filter.mp hW).1
      have hstar : IsStarLine Γ c (W ∩ Y) := (Finset.mem_filter.mp hW).2
      obtain ⟨hWcf, hWne⟩ := hCf'mem W hW'
      obtain ⟨-, hxW, -⟩ := (hCfmem W).mp hWcf
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_, ?_, ?_⟩
      · exact isHypLine_of_isStarLine_subset_of_isNonabsPlane hP hT hY hstar Set.inter_subset_right
      · exact ⟨hxW, hxY⟩
      · exact fun z hz => hz.2
    have hinj : ∀ W₁ ∈ CfA, ∀ W₂ ∈ CfA, W₁ ∩ Y = W₂ ∩ Y → W₁ = W₂ := by
      intro W₁ hW₁ W₂ hW₂ heq
      have hW₁' : W₁ ∈ Cf' := (Finset.mem_filter.mp hW₁).1
      have hW₂' : W₂ ∈ Cf' := (Finset.mem_filter.mp hW₂).1
      have hstar : IsStarLine Γ c (W₁ ∩ Y) := (Finset.mem_filter.mp hW₁).2
      obtain ⟨hW₁cf, hW₁ne⟩ := hCf'mem W₁ hW₁'
      obtain ⟨hW₂cf, hW₂ne⟩ := hCf'mem W₂ hW₂'
      obtain ⟨hW₁plane, hxW₁, hYW₁⟩ := (hCfmem W₁).mp hW₁cf
      obtain ⟨hW₂plane, hxW₂, hYW₂⟩ := (hCfmem W₂).mp hW₂cf
      by_contra hne
      have hW₁non : IsNonabsPlane Γ c W₁ :=
        isNonabsPlane_of_isConjPlane_of_ne_ptPerp hP hT c hdeg hreg hY hxY hW₁plane hxW₁
          hYW₁ hW₁ne
      have hW₂non : IsNonabsPlane Γ c W₂ :=
        isNonabsPlane_of_isConjPlane_of_ne_ptPerp hP hT c hdeg hreg hY hxY hW₂plane hxW₂
          hYW₂ hW₂ne
      rcases eq_or_inter_eq_singleton_of_isConjPlane hP hT c hdeg hreg hst hii
        hY hW₁non hW₂non hxY hxW₁ hxW₂ hYW₁ hYW₂ with h | h
      · exact hne h
      · obtain ⟨a, b, ha, hb, hab, hEq⟩ := hstar
        have ha₁ : a ∈ W₁ ∩ Y := by rw [hEq]; exact mem_starLine_left ha
        have hb₁ : b ∈ W₁ ∩ Y := by rw [hEq]; exact mem_starLine_right hb
        have ha₂ : a ∈ W₂ ∩ Y := by rw [← heq]; exact ha₁
        have hb₂ : b ∈ W₂ ∩ Y := by rw [← heq]; exact hb₁
        have ha' : a ∈ W₁ ∩ W₂ := ⟨ha₁.1, ha₂.1⟩
        have hb' : b ∈ W₁ ∩ W₂ := ⟨hb₁.1, hb₂.1⟩
        rw [h] at ha' hb'
        have hax : a = x := by simpa using ha'
        have hbx : b = x := by simpa using hb'
        exact hab (hax.trans hbx.symm)
    have hcard := Finset.card_le_card_of_injOn (fun W => W ∩ Y) hmaps hinj
    rwa [hLYcard] at hcard
  have ha_ge : 1 ≤ CfA.card := by
    have hXCf : X ∈ Cf := by
      rw [hCfmem]
      exact ⟨hX.1, hx, hYX⟩
    have hXne : X ≠ ptPerp Γ c {x} := by
      intro h
      exact not_isNonabsPlane_of_isAbsPlane hP hT c hdeg ⟨x, hx0, h⟩ hX
    have hXstar : IsStarLine Γ c (X ∩ Y) :=
      IsHypLine.isStarLine hP
        (isHypLine_inter_of_isConjPlane hP hT c hdeg hreg hst hii hX hY hXY)
    have hXmem : X ∈ Cf' := by
      simp only [Cf', Finset.mem_erase]
      exact ⟨hXne, hXCf⟩
    have hXmemA : X ∈ CfA := by
      simp only [CfA, Finset.mem_filter]
      exact ⟨hXmem, hXstar⟩
    exact Nat.succ_le_of_lt (Finset.card_pos.mpr ⟨X, hXmemA⟩)
  have hc_eq : Cf.card = s + 1 := by
    have hs : 2 ≤ s := two_le_s hP hT c hdeg
    have hkey : (CfA.card + CfB.card) * s = s * (s - 1) + CfA.card := by
      have ha_mul : CfA.card * (s - 1) = CfA.card * s - CfA.card := by
        rw [Nat.mul_sub_left_distrib]; simp
      have ha_add : CfA.card * (s - 1) + CfA.card = CfA.card * s := by
        rw [ha_mul]
        exact Nat.sub_add_cancel (by
          have : CfA.card * 1 ≤ CfA.card * s := Nat.mul_le_mul_left _ (by omega)
          simpa using this)
      calc
        (CfA.card + CfB.card) * s = CfA.card * s + CfB.card * s := Nat.add_mul _ _ _
        _ = (CfA.card * (s - 1) + CfA.card) + CfB.card * s := by rw [ha_add]
        _ = (CfA.card * (s - 1) + CfB.card * s) + CfA.card := by omega
        _ = s * (s - 1) + CfA.card := by rw [← hsum']
    have hk_le : CfA.card + CfB.card ≤ s := by
      have hle : (CfA.card + CfB.card) * s ≤ s * s := by
        rw [hkey]
        have h1 : s * (s - 1) + CfA.card ≤ s * (s - 1) + s := Nat.add_le_add_left ha_le _
        have h2 : s * (s - 1) + s = s * s := by
          have hmul : s * (s - 1) = s * s - s := by rw [Nat.mul_sub_left_distrib]; simp
          have hle' : s ≤ s * s := by nlinarith
          omega
        omega
      rw [Nat.mul_comm (CfA.card + CfB.card) s] at hle
      exact Nat.le_of_mul_le_mul_left hle (by omega)
    have hk_ge : s ≤ CfA.card + CfB.card := by
      by_contra hlt
      have hle : CfA.card + CfB.card ≤ s - 1 := by omega
      have h1 : (CfA.card + CfB.card) * s ≤ (s - 1) * s := Nat.mul_le_mul_right s hle
      have h2 : s * (s - 1) + 1 ≤ s * (s - 1) + CfA.card := Nat.add_le_add_left ha_ge _
      have h3 : (s - 1) * s = s * (s - 1) := Nat.mul_comm _ _
      rw [hkey, h3] at h1
      omega
    have hk : CfA.card + CfB.card = s := le_antisymm hk_le hk_ge
    have hcpos : 0 < Cf.card := Finset.card_pos.mpr ⟨_, hxperpCf⟩
    omega
  have hCfcard : {W : Set V | IsStarPlane Γ c W ∧ x ∈ W ∧ IsConjPlane Γ c Y W}.ncard =
      Cf.card := by
    rw [← Set.ncard_coe_finset, hCfcoe]
  have hβcard : (tangentBundle Γ c X x).ncard = s + 1 :=
    ncard_of_isPlaneBundle hP hT c hdeg hreg hst hii'
      (Or.inr ⟨X, x, hX, hx, rfl⟩)
  exact Set.eq_of_subset_of_ncard_le hCsub (by rw [hCfcard, hc_eq, hβcard])

theorem conjBundle_tangentBundle (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hreg : ∀ x, c x = 0 → IsRegularVertex Γ x) (hst : s ≠ t) (hii : TalliniCond Γ c)
    {X : Set V} {x : V} (hX : IsNonabsPlane Γ c X) (hx : x ∈ X) :
    conjBundle Γ c (tangentBundle Γ c X x) =
        {Y | IsStarPlane Γ c Y ∧ x ∈ Y ∧ IsConjPlane Γ c X Y} ∧
      ∃ X', IsNonabsPlane Γ c X' ∧ x ∈ X' ∧
        conjBundle Γ c (tangentBundle Γ c X x) = tangentBundle Γ c X' x := by
  classical
  have hx0 : c x = 0 := hX.1.1.1.1 x hx
  have hmain : conjBundle Γ c (tangentBundle Γ c X x) =
      {Y | IsStarPlane Γ c Y ∧ x ∈ Y ∧ IsConjPlane Γ c X Y} := by
    ext Y
    constructor
    · rintro ⟨hYplane, hYall⟩
      have hxperpβ : ptPerp Γ c {x} ∈ tangentBundle Γ c X x :=
        ⟨isStarPlane_ptPerp_singleton hP hT c hdeg hx0,
          Or.inr (inter_ptPerp_eq_singleton_of_isNonabsPlane hP hT hX hx)⟩
      have hconj : IsConjPlane Γ c Y (ptPerp Γ c {x}) := hYall _ hxperpβ
      refine ⟨hYplane, ?_, ?_⟩
      · exact (ptPerp_mem_conjNet_iff hP hT c hdeg hreg hYplane hx0).mp
          ⟨isStarPlane_ptPerp_singleton hP hT c hdeg hx0, hconj⟩
      · exact (isConjPlane_comm hP hT c hdeg hreg).mp (hYall X ⟨hX.1, Or.inl rfl⟩)
    · rintro ⟨hYplane, hxY, hXY⟩
      refine ⟨hYplane, ?_⟩
      intro Z hZ
      rcases hZ with ⟨hZplane, hZX | hZXint⟩
      · rw [hZX]
        exact (isConjPlane_comm hP hT c hdeg hreg).mp hXY
      · have hxZ : x ∈ Z := by
          have hmem : x ∈ X ∩ Z := by rw [hZXint]; simp
          exact hmem.2
        by_cases hYabs : IsAbsPlane Γ c Y
        · obtain ⟨w, hw0, hYw⟩ := hYabs
          have hwX : w ∈ X := by
            have hmem : ptPerp Γ c {w} ∈ conjNet Γ c X := by
              rw [← hYw]
              exact ⟨hYplane, hXY⟩
            exact (ptPerp_mem_conjNet_iff hP hT c hdeg hreg hX.1 hw0).mp hmem
          have hxw : x ∈ ptPerp Γ c {w} := by rw [← hYw]; exact hxY
          have hle : Γ.dist w x ≤ 2 := by
            have h := (mem_ptPerp.mp hxw).2 w (by simp)
            rwa [SimpleGraph.dist_comm] at h
          have hwx : w = x := by
            by_contra hne
            have h4 : Γ.dist w x = 4 := dist_eq_four_of_mem_of_isOvoid hP hT hX.2 hwX hx hne
            omega
          have hYx : Y = ptPerp Γ c {x} := by rw [hwx] at hYw; exact hYw
          rw [hYx]
          have hmem : Z ∈ conjNet Γ c (ptPerp Γ c {x}) := by
            rw [conjNet_ptPerp hP hT c hdeg hreg hx0]
            exact ⟨hZplane, hxZ⟩
          exact hmem.2
        · have hYnon : IsNonabsPlane Γ c Y := by
            rcases isStarPlane_cases hP hT c hdeg hreg hYplane with h | h
            · exact absurd h hYabs
            · exact h
          have heq := conjPlaneSet_eq_tangentBundle hP hT c hdeg hreg hst hii hX hx hYnon hxY hXY
          have hZC : Z ∈ {W : Set V | IsStarPlane Γ c W ∧ x ∈ W ∧ IsConjPlane Γ c Y W} := by
            rw [heq]
            exact ⟨hZplane, Or.inr hZXint⟩
          exact hZC.2.2
  refine ⟨hmain, ?_⟩
  have hXne : X ≠ ptPerp Γ c {x} := ne_ptPerp_of_isNonabsPlane hP hT c hdeg hX hx
  have hex : ∃ R : Set V, IsHypLine Γ c R ∧ x ∈ R ∧ ¬ R ⊆ X := by
    by_contra h
    push Not at h
    have hset : {ℓ : Set V | IsHypLine Γ c ℓ ∧ x ∈ ℓ} =
        {ℓ : Set V | IsHypLine Γ c ℓ ∧ x ∈ ℓ ∧ ℓ ⊆ X} := by
      ext ℓ
      exact ⟨fun hℓ => ⟨hℓ.1, hℓ.2, h ℓ hℓ.1 hℓ.2⟩, fun hℓ => ⟨hℓ.1, hℓ.2.1⟩⟩
    have h1 := ncard_hypLines_through hP hT c hdeg hreg hx0
    have h2 := ncard_hypLines_through_subset hP hT c hdeg hreg hX.1 hx hXne
    rw [hset, h2] at h1
    have hs : 2 ≤ s := two_le_s hP hT c hdeg
    nlinarith
  obtain ⟨R, hRhyp, hxR, hRX⟩ := hex
  have hRstar : IsStarLine Γ c R := IsHypLine.isStarLine hP hRhyp
  have hRperp : ¬ ptPerp Γ c R ⊆ X := by
    intro hsub
    have hdisj := disjoint_of_ptPerp_subset hP hT c hdeg hreg hX hRstar hsub
    exact (Set.disjoint_left.mp hdisj) hxR hx
  obtain ⟨X', ⟨hX'plane, hRX', hXX'⟩, -⟩ :=
    existsUnique_conjPlane_superset hP hT c hdeg hreg hii hX.1 hRstar hRX hRperp
  have hxX' : x ∈ X' := hRX' hxR
  have hX'non : IsNonabsPlane Γ c X' := by
    by_contra hnon
    rcases isStarPlane_cases hP hT c hdeg hreg hX'plane with h | h
    · obtain ⟨w, hw0, hX'w⟩ := h
      have hwX : w ∈ X := by
        have hmem : ptPerp Γ c {w} ∈ conjNet Γ c X := by
          rw [← hX'w]
          exact ⟨hX'plane, hXX'⟩
        exact (ptPerp_mem_conjNet_iff hP hT c hdeg hreg hX.1 hw0).mp hmem
      have hxw : x ∈ ptPerp Γ c {w} := by rw [← hX'w]; exact hxX'
      have hle : Γ.dist w x ≤ 2 := by
        have h' := (mem_ptPerp.mp hxw).2 w (by simp)
        rwa [SimpleGraph.dist_comm] at h'
      have hwx : w = x := by
        by_contra hne
        have h4 : Γ.dist w x = 4 := dist_eq_four_of_mem_of_isOvoid hP hT hX.2 hwX hx hne
        omega
      have hsub : R ⊆ ptPerp Γ c {x} := by rw [← hwx, ← hX'w]; exact hRX'
      exact not_subset_ptPerp_singleton_of_isHypLine hP hT hx0 hRhyp hxR hsub
    · exact absurd h hnon
  exact ⟨X', hX'non, hxX', by
    rw [hmain]
    exact conjPlaneSet_eq_tangentBundle hP hT c hdeg hreg hst hii hX'non hxX' hX hx
      ((isConjPlane_comm hP hT c hdeg hreg).mp hXX')⟩

theorem conjBundle_conjBundle (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hreg : ∀ x, c x = 0 → IsRegularVertex Γ x) (hst : s ≠ t) (hii : TalliniCond Γ c)
    {β : Set (Set V)} (hβ : IsPlaneBundle Γ c β) :
    IsPlaneBundle Γ c (conjBundle Γ c β) ∧ conjBundle Γ c (conjBundle Γ c β) = β := by
  classical
  rcases hβ with ⟨L, hL, rfl⟩ | ⟨X, x, hX, hx, rfl⟩
  · have hLperp : IsStarLine Γ c (ptPerp Γ c L) :=
      (ptPerp_ptPerp_starLine hP hT c hdeg hreg hL).1
    have hLL : ptPerp Γ c (ptPerp Γ c L) = L :=
      (ptPerp_ptPerp_starLine hP hT c hdeg hreg hL).2
    refine ⟨Or.inl ⟨ptPerp Γ c L, hLperp, conjBundle_axisBundle hP hT c hdeg hreg hL⟩, ?_⟩
    rw [conjBundle_axisBundle hP hT c hdeg hreg hL,
      conjBundle_axisBundle hP hT c hdeg hreg hLperp, hLL]
  · obtain ⟨hmain, X', hX', hx', heq⟩ :=
      conjBundle_tangentBundle hP hT c hdeg hreg hst hii hX hx
    refine ⟨Or.inr ⟨X', x, hX', hx', heq⟩, ?_⟩
    have hX'β : X' ∈ conjBundle Γ c (tangentBundle Γ c X x) := by
      rw [heq]
      exact ⟨hX'.1, Or.inl rfl⟩
    have hX'X : IsConjPlane Γ c X' X := hX'β.2 X ⟨hX.1, Or.inl rfl⟩
    obtain ⟨hmain', X'', hX'', hx'', heq'⟩ :=
      conjBundle_tangentBundle hP hT c hdeg hreg hst hii hX' hx'
    have hXin : X ∈ conjBundle Γ c (tangentBundle Γ c X' x) := by
      rw [hmain']
      exact ⟨hX.1, hx, hX'X⟩
    have hXmem : X ∈ tangentBundle Γ c X'' x := by
      rw [← heq']
      exact hXin
    have hc3 : tangentBundle Γ c X x = tangentBundle Γ c X'' x :=
      tangentBundle_eq hP hT c hdeg hreg
        (talliniCondPrime_of_talliniCond hP hT c hdeg hreg hii) hX'' hx'' hXmem hX
    calc conjBundle Γ c (conjBundle Γ c (tangentBundle Γ c X x))
        = conjBundle Γ c (tangentBundle Γ c X' x) := by rw [heq]
      _ = tangentBundle Γ c X'' x := heq'
      _ = tangentBundle Γ c X x := hc3.symm

end ConjugateBundles2

end CFSG.Geometry.GeneralizedQuadrangles
