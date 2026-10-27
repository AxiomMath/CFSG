module

public import CFSG.Geometry.GeneralizedQuadrangles.Hermitian.Tallini.PlanesThrough

public section

namespace CFSG.Geometry.GeneralizedQuadrangles

open SimpleGraph CFSG.Geometry.GeneralizedPolygons

universe u

variable {V : Type u}

private theorem ncard_setOf_eq_card_filter {α : Type*} [Fintype α] (p : α → Prop)
    [DecidablePred p] : {x | p x}.ncard = (Finset.univ.filter p).card := by
  rw [← Set.ncard_coe_finset]
  congr 1
  ext x
  simp

section TangentNonabs

variable {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj]

theorem ncard_inter_ovoid_ptPerp (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1) {X : Set V}
    (hO : IsOvoid Γ c X) {y : V} (hy : c y = 0) (hyX : y ∉ X) :
    (X ∩ ptPerp Γ c {y}).ncard = t + 1 := by
  classical
  let Lines : Finset V := Γ.neighborFinset y
  let S : Finset V := Finset.univ.filter fun z => z ∈ X ∧ z ∈ ptPerp Γ c {y}
  have hLines : ∀ L : V, L ∈ Lines ↔ Γ.Adj y L := fun L => by simp [Lines]
  let f : ∀ L ∈ Lines, V := fun L hL =>
    Classical.choose (Set.ncard_eq_one.mp (hO.2 L
      (color_eq_one_of_adj_of_color_eq_zero hy ((hLines L).mp hL))))
  have hfspec : ∀ (L : V) (hL : L ∈ Lines), Γ.neighborSet L ∩ X = {f L hL} := by
    intro L hL
    exact Classical.choose_spec (Set.ncard_eq_one.mp (hO.2 L
      (color_eq_one_of_adj_of_color_eq_zero hy ((hLines L).mp hL))))
  have hfmem : ∀ (L : V) (hL : L ∈ Lines), f L hL ∈ S := by
    intro L hL
    have hL1 : c L = 1 := color_eq_one_of_adj_of_color_eq_zero hy ((hLines L).mp hL)
    have hLadj : Γ.Adj y L := (hLines L).mp hL
    have hmem : f L hL ∈ Γ.neighborSet L ∩ X := by
      rw [hfspec L hL]
      simp
    have hsub : Γ.neighborSet L ⊆ ptPerp Γ c {y} := neighborSet_subset_ptPerp hP hL1 hLadj
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hmem.2, hsub hmem.1⟩
  have hfinj : ∀ (L₁ : V) (hL₁ : L₁ ∈ Lines) (L₂ : V) (hL₂ : L₂ ∈ Lines),
      f L₁ hL₁ = f L₂ hL₂ → L₁ = L₂ := by
    intro L₁ hL₁ L₂ hL₂ heq
    have hz1 : f L₁ hL₁ ∈ Γ.neighborSet L₁ ∩ X := by
      rw [hfspec L₁ hL₁]
      simp
    have hz2 : f L₁ hL₁ ∈ Γ.neighborSet L₂ ∩ X := by
      rw [heq]
      rw [hfspec L₂ hL₂]
      simp
    have hL₁adj : Γ.Adj y L₁ := (hLines L₁).mp hL₁
    have hL₂adj : Γ.Adj y L₂ := (hLines L₂).mp hL₂
    have hzy : f L₁ hL₁ ≠ y := fun h => hyX (h ▸ hz1.2)
    have h2 : Γ.dist (f L₁ hL₁) y = 2 :=
      dist_eq_two_of_adj_of_adj_of_ne hP hz1.1.symm hL₁adj.symm hzy
    exact (existsUnique_commonNeighbor hP h2).unique
      ⟨hz1.1.symm, hL₁adj⟩ ⟨hz2.1.symm, hL₂adj⟩
  have hfsurj : ∀ z ∈ S, ∃ (L : V) (hL : L ∈ Lines), f L hL = z := by
    intro z hz
    rw [Finset.mem_filter] at hz
    obtain ⟨-, hzX, hzperp⟩ := hz
    have hz0 : c z = 0 := (mem_ptPerp.1 hzperp).1
    have hzy_le : Γ.dist z y ≤ 2 := (mem_ptPerp.1 hzperp).2 y (by simp)
    have hzy : z ≠ y := fun h => hyX (h ▸ hzX)
    have heven : Even (Γ.dist z y) := (hP.eq_iff_even_dist c z y).1 (hz0.trans hy.symm)
    have hne0 : Γ.dist z y ≠ 0 := fun h => hzy ((hP.connected.dist_eq_zero_iff).mp h)
    have h2 : Γ.dist z y = 2 := by
      obtain ⟨k, hk⟩ := heven
      omega
    let L := commonNeighbor hP h2
    have hLmem : L ∈ Lines := (hLines L).mpr (commonNeighbor_adj_right hP h2)
    refine ⟨L, hLmem, ?_⟩
    have hzint : z ∈ Γ.neighborSet L ∩ X :=
      ⟨(commonNeighbor_adj_left hP h2).symm, hzX⟩
    have hset := hfspec L hLmem
    rw [hset] at hzint
    have hzf : z = f L hLmem := by simpa using hzint
    exact hzf.symm
  have hcard : S.card = t + 1 := by
    rw [← Finset.card_bij f hfmem hfinj hfsurj]
    rw [show Lines = Γ.neighborFinset y from rfl, card_neighborFinset_eq_degree, hdeg y, if_pos hy]
  have hcoe : ((S : Set V)) = X ∩ ptPerp Γ c {y} := by
    ext z
    change z ∈ S ↔ z ∈ X ∩ ptPerp Γ c {y}
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_inter_iff,
      mem_ptPerp, Set.mem_singleton_iff]
  rw [← hcoe, Set.ncard_coe_finset, hcard]

theorem isNonabsPlane_of_inter_eq_singleton (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hreg : ∀ x, c x = 0 → IsRegularVertex Γ x) {X Y : Set V} (hX : IsNonabsPlane Γ c X)
    (hY : IsStarPlane Γ c Y) {w : V} (hXY : X ∩ Y = {w}) (hYw : Y ≠ ptPerp Γ c {w}) :
    IsNonabsPlane Γ c Y := by
  classical
  have hwXY : w ∈ X ∩ Y := by rw [hXY]; simp
  have hwX : w ∈ X := hwXY.1
  have hwY : w ∈ Y := hwXY.2
  by_cases habs : IsAbsPlane Γ c Y
  · exfalso
    obtain ⟨y, hy, rfl⟩ := habs
    have hyw : y ≠ w := by
      intro h
      exact hYw (by rw [h])
    have hyY : y ∈ ptPerp Γ c {y} := by
      rw [mem_ptPerp]
      exact ⟨hy, by intro z hz; rw [Set.mem_singleton_iff] at hz; rw [hz]; simp⟩
    have hyX : y ∉ X := by
      intro hyX
      have : y ∈ X ∩ ptPerp Γ c {y} := ⟨hyX, hyY⟩
      rw [hXY] at this
      exact hyw (by simpa using this)
    have hcount : (X ∩ ptPerp Γ c {y}).ncard = t + 1 :=
      ncard_inter_ovoid_ptPerp hP hT c hdeg hX.2 hy hyX
    rw [hXY] at hcount
    have ht : 2 ≤ t := two_le_t hP hT c hdeg
    simp at hcount
    omega
  · rcases isStarPlane_cases hP hT c hdeg hreg hY with h | h
    · exact absurd h habs
    · exact h

end TangentNonabs

section Tangent

variable {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj]

theorem existsUnique_tangent (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hreg : ∀ x, c x = 0 → IsRegularVertex Γ x) (hii : TalliniCondPrime Γ c) {X : Set V}
    (hX : IsNonabsPlane Γ c X) {w : V} (hw : w ∈ X) {ℓ : Set V} (hℓ : IsHypLine Γ c ℓ)
    (hwℓ : w ∈ ℓ) (hℓX : ¬ ℓ ⊆ X) :
    ∃! Y, IsStarPlane Γ c Y ∧ ℓ ⊆ Y ∧ X ∩ Y = {w} := by
  classical
  have hXstar : IsStarPlane Γ c X := hX.1
  have hXlin : IsLinearVariety Γ c X := hX.1.1.1
  have hXov : IsOvoid Γ c X := hX.2
  have hw0 : c w = 0 := hXlin.1 w hw
  have hℓstar : IsStarLine Γ c ℓ := IsHypLine.isStarLine hP hℓ
  have ht : 2 ≤ t := two_le_t hP hT c hdeg
  have hℓcard : ℓ.ncard = t + 1 := IsHypLine.ncard hP hT c hdeg hreg hℓ
  have hℓtwo : 1 < ℓ.ncard := by rw [hℓcard]; omega
  have hinterℓX : ℓ ∩ X = {w} := by
    refine Set.Subset.antisymm ?_ ?_
    · intro z hz
      obtain ⟨hzℓ, hzX⟩ := hz
      by_contra hzw
      have hzw' : z ≠ w := hzw
      have hℓeq : starLine Γ c w z = ℓ :=
        (starLine_eq_of_isStarLine_of_mem hP hT hℓstar hwℓ hzℓ (Ne.symm hzw')).symm
      have hsub : starLine Γ c w z ⊆ X := hXlin.2 w hw z hzX (Ne.symm hzw')
      rw [hℓeq] at hsub
      exact hℓX hsub
    · rintro z hz
      rw [Set.mem_singleton_iff] at hz
      rw [hz]
      exact ⟨hwℓ, hw⟩
  let M : Finset (Set V) := Finset.univ.filter fun m => IsHypLine Γ c m ∧ w ∈ m ∧ m ⊆ X
  have hMcard : M.card = s := by
    rw [← Set.ncard_coe_finset]
    have hcoe : ((M : Set (Set V))) = {m | IsHypLine Γ c m ∧ w ∈ m ∧ m ⊆ X} := by
      ext m
      simp [M]
    rw [hcoe]
    exact ncard_hypLines_through_subset hP hT c hdeg hreg hXstar hw
      (ne_ptPerp_of_isNonabsPlane hP hT c hdeg hX hw)
  have hexists : ∀ m ∈ M, ∃ Y, IsStarPlane Γ c Y ∧ ℓ ⊆ Y ∧ m ⊆ Y := by
    intro m hmM
    have hm := Finset.mem_filter.mp hmM
    obtain ⟨-, hmhyp, hwm, hmX⟩ := hm
    have hmcard : m.ncard = t + 1 := IsHypLine.ncard hP hT c hdeg hreg hmhyp
    have hmtwo : 1 < m.ncard := by rw [hmcard]; omega
    obtain ⟨a, haℓ, haw⟩ := Set.exists_ne_of_one_lt_ncard hℓtwo w
    obtain ⟨b, hbm, hbw⟩ := Set.exists_ne_of_one_lt_ncard hmtwo w
    have ha0 : c a = 0 := IsHypLine.color hP hT hℓ haℓ
    have hb0 : c b = 0 := IsHypLine.color hP hT hmhyp hbm
    have hnc : ¬ IsStarCollinear Γ c w a b := by
      rintro ⟨Z, hZ, hwZ, haZ, hbZ⟩
      have hZeq : starLine Γ c w a = Z :=
        (starLine_eq_of_isStarLine_of_mem hP hT hZ hwZ haZ (Ne.symm haw)).symm
      have hbZ' : b ∈ starLine Γ c w a := by rw [hZeq]; exact hbZ
      have hℓeq : starLine Γ c w a = ℓ :=
        (starLine_eq_of_isStarLine_of_mem hP hT hℓstar hwℓ haℓ (Ne.symm haw)).symm
      have hbℓ : b ∈ ℓ := by rw [hℓeq] at hbZ'; exact hbZ'
      have hbint : b ∈ ℓ ∩ X := ⟨hbℓ, hmX hbm⟩
      rw [hinterℓX] at hbint
      exact hbw (by simpa using hbint)
    obtain ⟨Y, hYstar, hwY, haY, hbY⟩ := hii w a b hw0 ha0 hb0 hnc
    have hYlin : IsLinearVariety Γ c Y := hYstar.1.1
    refine ⟨Y, hYstar, ?_, ?_⟩
    · have hℓeq : starLine Γ c w a = ℓ :=
        (starLine_eq_of_isStarLine_of_mem hP hT hℓstar hwℓ haℓ (Ne.symm haw)).symm
      have hsub : starLine Γ c w a ⊆ Y := hYlin.2 w hwY a haY (Ne.symm haw)
      rw [hℓeq] at hsub
      exact hsub
    · have hmeq : starLine Γ c w b = m :=
        (starLine_eq_of_isStarLine_of_mem hP hT (IsHypLine.isStarLine hP hmhyp) hwm hbm
          (Ne.symm hbw)).symm
      have hsub : starLine Γ c w b ⊆ Y := hYlin.2 w hwY b hbY (Ne.symm hbw)
      rw [hmeq] at hsub
      exact hsub
  let Y : Set V → Set V := fun m =>
    if hm : m ∈ M then Classical.choose (hexists m hm) else X
  have hY : ∀ m ∈ M, IsStarPlane Γ c (Y m) ∧ ℓ ⊆ Y m ∧ m ⊆ Y m := by
    intro m hm
    have hYm : Y m = Classical.choose (hexists m hm) := by
      simp [Y, hm]
    rw [hYm]
    exact Classical.choose_spec (hexists m hm)
  have hYinj : ∀ m ∈ M, ∀ m' ∈ M, m ≠ m' → Y m ≠ Y m' := by
    intro m hmM m' hm'M hmm' heq
    have hm := Finset.mem_filter.mp hmM
    have hm' := Finset.mem_filter.mp hm'M
    obtain ⟨-, hmhyp, hwm, hmX⟩ := hm
    obtain ⟨-, hm'hyp, hwm', hm'X⟩ := hm'
    have hYstar : IsStarPlane Γ c (Y m) := (hY m hmM).1
    have hℓYm : ℓ ⊆ Y m := (hY m hmM).2.1
    have hmYm : m ⊆ Y m := (hY m hmM).2.2
    have hm'Ym : m' ⊆ Y m' := (hY m' hm'M).2.2
    have hXY : X ≠ Y m := by
      intro h
      exact hℓX (by rw [h]; exact hℓYm)
    have hZm : m ⊆ X ∩ Y m := fun z hz => ⟨hmX hz, hmYm hz⟩
    have hmcard : m.ncard = t + 1 := IsHypLine.ncard hP hT c hdeg hreg hmhyp
    have hmlarge : 1 < m.ncard := by rw [hmcard]; omega
    have hZline : IsStarLine Γ c (X ∩ Y m) := by
      rcases inter_cases hP hT c hdeg hreg hXstar hYstar hXY with hemp | hsingle | hline
      · obtain ⟨a, ha, b, hb, -⟩ := (Set.one_lt_ncard (s := m)).mp hmlarge
        have haz : a ∈ X ∩ Y m := hZm ha
        rw [hemp] at haz
        exact absurd haz (by simp)
      · obtain ⟨x, hx⟩ := hsingle
        obtain ⟨a, ha, b, hb, hab⟩ := (Set.one_lt_ncard (s := m)).mp hmlarge
        have haz : a ∈ X ∩ Y m := hZm ha
        have hbz : b ∈ X ∩ Y m := hZm hb
        rw [hx] at haz hbz
        simp only [Set.mem_singleton_iff] at haz hbz
        exact absurd (haz.trans hbz.symm) hab
      · exact hline
    have hZeq : X ∩ Y m = m := by
      obtain ⟨a, ha, b, hb, hab⟩ := (Set.one_lt_ncard (s := m)).mp hmlarge
      have hZeqm : starLine Γ c a b = X ∩ Y m :=
        (starLine_eq_of_isStarLine_of_mem hP hT hZline (hZm ha) (hZm hb) hab).symm
      have hmeq : starLine Γ c a b = m :=
        (starLine_eq_of_isStarLine_of_mem hP hT (IsHypLine.isStarLine hP hmhyp) ha hb hab).symm
      rw [← hZeqm, hmeq]
    have hm'sub : m' ⊆ m := by
      intro z hz
      have hzYm : z ∈ Y m := by
        have hz' : z ∈ Y m' := hm'Ym hz
        rwa [← heq] at hz'
      have hzZ : z ∈ X ∩ Y m := ⟨hm'X hz, hzYm⟩
      rwa [hZeq] at hzZ
    have hm'card : m'.ncard = t + 1 := IsHypLine.ncard hP hT c hdeg hreg hm'hyp
    have hEq : m' = m :=
      Set.eq_of_subset_of_ncard_le hm'sub (by rw [hmcard, hm'card])
    exact hmm' hEq.symm
  let P : Finset (Set V) := Finset.univ.filter fun Y' => IsStarPlane Γ c Y' ∧ ℓ ⊆ Y'
  have hPcard : P.card = s + 1 := by
    rw [← Set.ncard_coe_finset]
    have hcoe : ((P : Set (Set V))) = {Y' | IsStarPlane Γ c Y' ∧ ℓ ⊆ Y'} := by
      ext Y'
      simp [P]
    rw [hcoe]
    exact (ncard_planes_superset_hypLine hP hT c hdeg hreg hii hℓ).1
  have himage_sub : M.image Y ⊆ P := by
    intro Z hZ
    rw [Finset.mem_image] at hZ
    obtain ⟨m, hmM, rfl⟩ := hZ
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hY m hmM).1, (hY m hmM).2.1⟩
  have himage_card : (M.image Y).card = M.card := by
    apply Finset.card_image_of_injOn
    intro m hmM m' hm'M heq
    by_contra hne
    exact hYinj m hmM m' hm'M hne heq
  have hcompl_card : (P \ M.image Y).card = 1 := by
    rw [Finset.card_sdiff_of_subset himage_sub, hPcard, himage_card, hMcard]
    omega
  obtain ⟨Y0, hY0eq⟩ := Finset.card_eq_one.mp hcompl_card
  have hY0mem : Y0 ∈ P \ M.image Y := by rw [hY0eq]; simp
  have hY0P : Y0 ∈ P := (Finset.mem_sdiff.mp hY0mem).1
  have hY0not : Y0 ∉ M.image Y := (Finset.mem_sdiff.mp hY0mem).2
  have hY0star : IsStarPlane Γ c Y0 := (Finset.mem_filter.mp hY0P).2.1
  have hY0ℓ : ℓ ⊆ Y0 := (Finset.mem_filter.mp hY0P).2.2
  have hwY0 : w ∈ Y0 := hY0ℓ hwℓ
  have hinterY0 : X ∩ Y0 = {w} := by
    refine Set.Subset.antisymm ?_ ?_
    · intro z hz
      obtain ⟨hzX, hzY0⟩ := hz
      by_contra hzw
      have hzw' : z ≠ w := hzw
      have hznotℓ : z ∉ ℓ := by
        intro hzℓ
        have hℓeq : starLine Γ c w z = ℓ :=
          (starLine_eq_of_isStarLine_of_mem hP hT hℓstar hwℓ hzℓ (Ne.symm hzw')).symm
        have hsub : starLine Γ c w z ⊆ X := hXlin.2 w hw z hzX (Ne.symm hzw')
        rw [hℓeq] at hsub
        exact hℓX hsub
      have hdist : Γ.dist w z = 4 :=
        dist_eq_four_of_mem_of_isOvoid hP hT hXov hw hzX (Ne.symm hzw')
      let m : Set V := starLine Γ c w z
      have hmhyp : IsHypLine Γ c m := ⟨w, z, hw0, hdist, rfl⟩
      have hwm : w ∈ m := mem_starLine_left hw0
      have hmX : m ⊆ X := hXlin.2 w hw z hzX (Ne.symm hzw')
      have hmM : m ∈ M :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmhyp, hwm, hmX⟩
      have hmY0 : m ⊆ Y0 := (hY0star.1.1.2) w hwY0 z hzY0 (Ne.symm hzw')
      have hmcard : m.ncard = t + 1 := IsHypLine.ncard hP hT c hdeg hreg hmhyp
      have hmtwo : 1 < m.ncard := by rw [hmcard]; omega
      obtain ⟨a, haℓ, haw⟩ := Set.exists_ne_of_one_lt_ncard hℓtwo w
      obtain ⟨b, hbm, hbw⟩ := Set.exists_ne_of_one_lt_ncard hmtwo w
      have hnc : ¬ IsStarCollinear Γ c w a b := by
        rintro ⟨Z, hZ, hwZ, haZ, hbZ⟩
        have hZeq : starLine Γ c w a = Z :=
          (starLine_eq_of_isStarLine_of_mem hP hT hZ hwZ haZ (Ne.symm haw)).symm
        have hbZ' : b ∈ starLine Γ c w a := by rw [hZeq]; exact hbZ
        have hℓeq : starLine Γ c w a = ℓ :=
          (starLine_eq_of_isStarLine_of_mem hP hT hℓstar hwℓ haℓ (Ne.symm haw)).symm
        have hbℓ : b ∈ ℓ := by rw [hℓeq] at hbZ'; exact hbZ'
        have hbint : b ∈ ℓ ∩ X := ⟨hbℓ, hmX hbm⟩
        rw [hinterℓX] at hbint
        exact hbw (by simpa using hbint)
      have hY0eqm : Y0 = Y m :=
        eq_of_isStarPlane hP hT c hdeg hreg hY0star (hY m hmM).1
          ⟨hwY0, (hY m hmM).2.1 hwℓ⟩
          ⟨hY0ℓ haℓ, (hY m hmM).2.1 haℓ⟩
          ⟨hmY0 hbm, (hY m hmM).2.2 hbm⟩ hnc
      exact hY0not (Finset.mem_image.mpr ⟨m, hmM, hY0eqm.symm⟩)
    · rintro z hz
      rw [Set.mem_singleton_iff] at hz
      rw [hz]
      exact ⟨hw, hwY0⟩
  refine ⟨Y0, ⟨hY0star, hY0ℓ, hinterY0⟩, ?_⟩
  intro Y' hY'
  obtain ⟨hY'star, hY'ℓ, hY'inter⟩ := hY'
  have hY'P : Y' ∈ P :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hY'star, hY'ℓ⟩
  have hY'not : Y' ∉ M.image Y := by
    intro hmem
    rw [Finset.mem_image] at hmem
    obtain ⟨m, hmM, hYm⟩ := hmem
    have hm := Finset.mem_filter.mp hmM
    obtain ⟨-, hmhyp, hwm, hmX⟩ := hm
    have hmYm : m ⊆ Y m := (hY m hmM).2.2
    have hmsub : m ⊆ X ∩ Y' := fun z hz => ⟨hmX hz, hYm ▸ hmYm hz⟩
    have hmcard : m.ncard = t + 1 := IsHypLine.ncard hP hT c hdeg hreg hmhyp
    have hmlarge : 1 < m.ncard := by rw [hmcard]; omega
    have : 1 < (X ∩ Y').ncard := by
      rw [Set.one_lt_ncard]
      obtain ⟨a, ha, b, hb, hab⟩ := (Set.one_lt_ncard (s := m)).mp hmlarge
      exact ⟨a, hmsub ha, b, hmsub hb, hab⟩
    rw [hY'inter] at this
    simp at this
  have hmem : Y' ∈ P \ M.image Y := Finset.mem_sdiff.mpr ⟨hY'P, hY'not⟩
  rw [hY0eq] at hmem
  simpa using hmem

end Tangent


section OvoidCounts

variable {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj]

theorem ncard_of_isStarLine_subset_isOvoid (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hreg : ∀ x, c x = 0 → IsRegularVertex Γ x) {X Z : Set V} (hO : IsOvoid Γ c X)
    (hZ : IsStarLine Γ c Z) (hZX : Z ⊆ X) : Z.ncard = t + 1 := by
  obtain ⟨x, y, hx, hy, hxy, rfl⟩ := hZ
  have hxX : x ∈ X := hZX (mem_starLine_left hx)
  have hyX : y ∈ X := hZX (mem_starLine_right hy)
  have h4 : Γ.dist x y = 4 := dist_eq_four_of_mem_of_isOvoid hP hT hO hxX hyX hxy
  exact ncard_starLine_of_dist_four hP hT c hdeg hreg hx h4

theorem ncard_opposite_mem_of_isOvoid (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1) {X : Set V}
    (hO : IsOvoid Γ c X) {x : V} (hx : c x = 0) (hxX : x ∉ X) :
    {w | w ∈ X ∧ Γ.dist x w = 4}.ncard = s * t - t := by
  classical
  have hw0 : ∀ w, w ∈ X → c w = 0 := hO.1
  have hinter : (X ∩ ptPerp Γ c {x}).ncard = t + 1 :=
    ncard_inter_ovoid_ptPerp hP hT c hdeg hO hx hxX
  have hXc : X.ncard = s * t + 1 := ncard_of_isOvoid hP hT c hdeg hO
  have hsub : X ∩ ptPerp Γ c {x} ⊆ X := Set.inter_subset_left
  have hYeq : {w | w ∈ X ∧ Γ.dist x w = 4} = X \ (X ∩ ptPerp Γ c {x}) := by
    ext w
    constructor
    · rintro ⟨hwX, hw4⟩
      refine ⟨hwX, ?_⟩
      intro hmem
      have hle : Γ.dist x w ≤ 2 := by
        rw [SimpleGraph.dist_comm]
        exact (mem_ptPerp.1 hmem.2).2 x (by simp)
      omega
    · rintro ⟨hwX, hwnot⟩
      refine ⟨hwX, ?_⟩
      have hw0' : c w = 0 := hw0 w hwX
      have hxw : x ≠ w := fun h => hxX (h ▸ hwX)
      have heven : Even (Γ.dist x w) := (hP.eq_iff_even_dist c x w).1 (hx.trans hw0'.symm)
      have hle4 : Γ.dist x w ≤ 4 := hP.dist_le (by norm_num) x w
      have hne0 : Γ.dist x w ≠ 0 := fun h => hxw ((hP.connected.dist_eq_zero_iff).mp h)
      by_contra h4
      have h2 : Γ.dist x w = 2 := by
        obtain ⟨k, hk⟩ := heven
        omega
      have hmem : w ∈ X ∩ ptPerp Γ c {x} := by
        refine ⟨hwX, ?_⟩
        rw [mem_ptPerp]
        refine ⟨hw0', ?_⟩
        intro z hz
        rw [Set.mem_singleton_iff] at hz
        rw [hz, SimpleGraph.dist_comm]
        omega
      exact hwnot hmem
  rw [hYeq, Set.ncard_sdiff (s := X ∩ ptPerp Γ c {x}) (t := X) hsub, hXc, hinter]
  omega

end OvoidCounts

section TangentCount

variable {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj]

theorem ncard_nonabs_planes_inter_singleton (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hreg : ∀ x, c x = 0 → IsRegularVertex Γ x) (hii : TalliniCondPrime Γ c) {X : Set V}
    (hX : IsNonabsPlane Γ c X) {x : V} (hx : c x = 0) (hxX : x ∉ X) :
    {Y | IsNonabsPlane Γ c Y ∧ x ∈ Y ∧ (X ∩ Y).ncard = 1}.ncard = s * t - t := by
  classical
  let W : Set V := {w | w ∈ X ∧ Γ.dist x w = 4}
  have ht : 2 ≤ t := two_le_t hP hT c hdeg
  have htangent : ∀ w ∈ W, ∃! Y, IsStarPlane Γ c Y ∧ starLine Γ c x w ⊆ Y ∧ X ∩ Y = {w} := by
    intro w hw
    obtain ⟨hwX, hwx4⟩ := hw
    have hw0 : c w = 0 := hX.2.1 w hwX
    have hℓhyp : IsHypLine Γ c (starLine Γ c x w) := ⟨x, w, hx, hwx4, rfl⟩
    have hwℓ : w ∈ starLine Γ c x w := mem_starLine_right hw0
    have hxℓ : x ∈ starLine Γ c x w := mem_starLine_left hx
    have hℓX : ¬ starLine Γ c x w ⊆ X := fun h => hxX (h hxℓ)
    exact existsUnique_tangent hP hT c hdeg hreg hii hX hwX hℓhyp hwℓ hℓX
  let g : V → Set V := fun w =>
    if hw : w ∈ W then Classical.choose (htangent w hw) else X
  have hgspec : ∀ (w : V) (hw : w ∈ W),
      IsStarPlane Γ c (g w) ∧ starLine Γ c x w ⊆ g w ∧ X ∩ g w = {w} := by
    intro w hw
    have hgw : g w = Classical.choose (htangent w hw) := by simp [g, hw]
    rw [hgw]
    exact (Classical.choose_spec (htangent w hw)).1
  have hgA1 : ∀ w ∈ W, g w ∈ {Y | IsNonabsPlane Γ c Y ∧ x ∈ Y ∧ (X ∩ Y).ncard = 1} := by
    intro w hw
    have hwW : w ∈ W := hw
    obtain ⟨hwX, hwx4⟩ := hw
    have hw0 : c w = 0 := hX.2.1 w hwX
    have hspec := hgspec w hwW
    have hℓhyp : IsHypLine Γ c (starLine Γ c x w) := ⟨x, w, hx, hwx4, rfl⟩
    have hwℓ : w ∈ starLine Γ c x w := mem_starLine_right hw0
    have hℓcard : (starLine Γ c x w).ncard = t + 1 :=
      IsHypLine.ncard hP hT c hdeg hreg hℓhyp
    have hℓtwo : 1 < (starLine Γ c x w).ncard := by rw [hℓcard]; omega
    have hYw : g w ≠ ptPerp Γ c {w} := by
      obtain ⟨y, hyℓ, hyw⟩ := Set.exists_ne_of_one_lt_ncard hℓtwo w
      have hy4 : Γ.dist w y = 4 :=
        IsHypLine.dist_eq_four hP hT hℓhyp hwℓ hyℓ (Ne.symm hyw)
      have hynot : y ∉ ptPerp Γ c {w} := by
        intro hyp
        have hle : Γ.dist w y ≤ 2 := by
          rw [SimpleGraph.dist_comm]
          exact (mem_ptPerp.1 hyp).2 w (by simp)
        omega
      intro heq
      exact hynot (by rw [← heq]; exact hspec.2.1 hyℓ)
    have hnonabs : IsNonabsPlane Γ c (g w) :=
      isNonabsPlane_of_inter_eq_singleton hP hT c hdeg hreg hX hspec.1 hspec.2.2 hYw
    exact ⟨hnonabs, hspec.2.1 (mem_starLine_left hx), by rw [hspec.2.2]; simp⟩
  have hginj : ∀ w ∈ W, ∀ w' ∈ W, g w = g w' → w = w' := by
    intro w hw w' hw' heq
    have h1 : X ∩ g w = {w} := (hgspec w hw).2.2
    have h2 : X ∩ g w' = {w'} := (hgspec w' hw').2.2
    have hsets : ({w} : Set V) = {w'} := by rw [← h1, ← h2, heq]
    have hmem : w ∈ ({w'} : Set V) := by rw [← hsets]; simp
    simpa using hmem
  have hgsurj : ∀ Y ∈ {Y | IsNonabsPlane Γ c Y ∧ x ∈ Y ∧ (X ∩ Y).ncard = 1},
      ∃ w ∈ W, g w = Y := by
    intro Y hY
    obtain ⟨hYnon, hxY, hYcard⟩ := hY
    have hYstar : IsStarPlane Γ c Y := hYnon.1
    have hYlin : IsLinearVariety Γ c Y := hYnon.1.1.1
    obtain ⟨z, hz⟩ := Set.ncard_eq_one.mp hYcard
    have hzint : z ∈ X ∩ Y := by rw [hz]; simp
    have hzX : z ∈ X := hzint.1
    have hzY : z ∈ Y := hzint.2
    have hxz : x ≠ z := fun h => hxX (h ▸ hzX)
    have hzw4 : Γ.dist x z = 4 :=
      dist_eq_four_of_mem_of_isOvoid hP hT hYnon.2 hxY hzY hxz
    have hzW : z ∈ W := ⟨hzX, hzw4⟩
    refine ⟨z, hzW, ?_⟩
    have hgz := hgspec z hzW
    have hYprop : IsStarPlane Γ c Y ∧ starLine Γ c x z ⊆ Y ∧ X ∩ Y = {z} :=
      ⟨hYstar, hYlin.2 x hxY z hzY hxz, hz⟩
    exact (htangent z hzW).unique hgz hYprop
  have hWcard : W.ncard = s * t - t :=
    ncard_opposite_mem_of_isOvoid hP hT c hdeg hX.2 hx hxX
  have hbij : W.ncard = {Y | IsNonabsPlane Γ c Y ∧ x ∈ Y ∧ (X ∩ Y).ncard = 1}.ncard :=
    Set.ncard_congr (fun w _ => g w) hgA1
      (fun a b ha hb heq => hginj a ha b hb heq)
      (fun Y hY => by
        obtain ⟨w, hw, hgw⟩ := hgsurj Y hY
        exact ⟨w, hw, hgw⟩)
  rw [← hbij, hWcard]

end TangentCount

section SumIntersections

variable {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj]

theorem sum_ncard_inter_eq (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hreg : ∀ x, c x = 0 → IsRegularVertex Γ x) (hii : TalliniCondPrime Γ c) {X : Set V}
    (hX : IsNonabsPlane Γ c X) {x : V} (hx : c x = 0) (hxX : x ∉ X)
    [DecidablePred (fun Y : Set V => IsNonabsPlane Γ c Y ∧ x ∈ Y)] :
    (∑ Y ∈ Finset.univ.filter (fun Y : Set V => IsNonabsPlane Γ c Y ∧ x ∈ Y),
        (X ∩ Y).ncard) = (s * t - t) * (s - t) := by
  classical
  let N : Finset (Set V) := Finset.univ.filter fun Y => IsNonabsPlane Γ c Y ∧ x ∈ Y
  let W : Finset V := Finset.univ.filter fun w => w ∈ X ∧ Γ.dist x w = 4
  have hWcard : W.card = s * t - t := by
    rw [← Set.ncard_coe_finset]
    have hcoe : ((W : Set V)) = {w | w ∈ X ∧ Γ.dist x w = 4} := by
      ext w
      simp [W]
    rw [hcoe, ncard_opposite_mem_of_isOvoid hP hT c hdeg hX.2 hx hxX]
  have hrow : ∀ w ∈ W, (N.filter fun Y => w ∈ Y).card = s - t := by
    intro w hw
    rw [Finset.mem_filter] at hw
    obtain ⟨-, hwX, hwx4⟩ := hw
    have hw0 : c w = 0 := hX.2.1 w hwX
    have hℓhyp : IsHypLine Γ c (starLine Γ c x w) := ⟨x, w, hx, hwx4, rfl⟩
    have hxℓ : x ∈ starLine Γ c x w := mem_starLine_left hx
    have hwℓ : w ∈ starLine Γ c x w := mem_starLine_right hw0
    have hxw : x ≠ w := fun h => hxX (h ▸ hwX)
    have hset : (N.filter fun Y => w ∈ Y) =
        Finset.univ.filter (fun Y : Set V =>
          IsNonabsPlane Γ c Y ∧ starLine Γ c x w ⊆ Y) := by
      ext Y
      simp only [N, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨hYnon, hxY⟩, hwY⟩
        exact ⟨hYnon, hYnon.1.1.1.2 x hxY w hwY hxw⟩
      · rintro ⟨hYnon, hℓY⟩
        exact ⟨⟨hYnon, hℓY hxℓ⟩, hℓY hwℓ⟩
    rw [hset, ← Set.ncard_coe_finset]
    have hcoe : ((Finset.univ.filter (fun Y : Set V =>
        IsNonabsPlane Γ c Y ∧ starLine Γ c x w ⊆ Y) : Finset (Set V)) : Set (Set V)) =
        {Y | IsNonabsPlane Γ c Y ∧ starLine Γ c x w ⊆ Y} := by
      ext Y
      simp
    rw [hcoe]
    exact (ncard_planes_superset_hypLine hP hT c hdeg hreg hii hℓhyp).2.2
  have hcol : ∀ Y ∈ N, (W.filter fun w => w ∈ Y).card = (X ∩ Y).ncard := by
    intro Y hY
    rw [Finset.mem_filter] at hY
    obtain ⟨-, hYnon, hxY⟩ := hY
    have hset : (W.filter fun w => w ∈ Y) = Finset.univ.filter (fun w => w ∈ X ∧ w ∈ Y) := by
      ext w
      simp only [W, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨hwX, -⟩, hwY⟩
        exact ⟨hwX, hwY⟩
      · rintro ⟨hwX, hwY⟩
        refine ⟨⟨hwX, ?_⟩, hwY⟩
        exact dist_eq_four_of_mem_of_isOvoid hP hT hYnon.2 hxY hwY
          (fun h => hxX (h ▸ hwX))
    rw [hset, ← Set.ncard_coe_finset]
    have hcoe : ((Finset.univ.filter (fun w => w ∈ X ∧ w ∈ Y) : Finset V) : Set V) = X ∩ Y := by
      ext w
      simp
    rw [hcoe]
  let Pairs : Finset (V × Set V) := (W ×ˢ N).filter fun p => p.1 ∈ p.2
  have hrowSum : Pairs.card = ∑ w ∈ W, (N.filter fun Y => w ∈ Y).card := by
    rw [Finset.card_filter, Finset.sum_product]
    apply Finset.sum_congr rfl
    intro w hw
    rw [← Finset.card_filter]
  have hcolSum : Pairs.card = ∑ Y ∈ N, (W.filter fun w => w ∈ Y).card := by
    rw [Finset.card_filter, Finset.sum_product, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro Y hY
    rw [← Finset.card_filter]
  have hrow' : Pairs.card = (s * t - t) * (s - t) := by
    rw [hrowSum, Finset.sum_congr rfl hrow, Finset.sum_const, smul_eq_mul, hWcard]
  have hcol' : Pairs.card = ∑ Y ∈ N, (X ∩ Y).ncard := by
    rw [hcolSum]
    exact Finset.sum_congr rfl hcol
  rw [← hcol', hrow']

end SumIntersections

section UnitalCount

variable {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj]

theorem card_mul_nonabs_disjoint (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hreg : ∀ x, c x = 0 → IsRegularVertex Γ x) (hii : TalliniCondPrime Γ c) {X : Set V}
    (hX : IsNonabsPlane Γ c X) {x : V} (hx : c x = 0) (hxX : x ∉ X) :
    ((t : ℤ) + 1) * ({Y | IsNonabsPlane Γ c Y ∧ x ∈ Y ∧ Disjoint X Y}.ncard : ℤ) =
      (s : ℤ) * ((s : ℤ) - (t : ℤ) ^ 2) := by
  classical
  let N : Finset (Set V) := Finset.univ.filter fun Y => IsNonabsPlane Γ c Y ∧ x ∈ Y
  let A0 : Finset (Set V) :=
    Finset.univ.filter fun Y => IsNonabsPlane Γ c Y ∧ x ∈ Y ∧ Disjoint X Y
  let A1 : Finset (Set V) :=
    Finset.univ.filter fun Y => IsNonabsPlane Γ c Y ∧ x ∈ Y ∧ (X ∩ Y).ncard = 1
  let A2 : Finset (Set V) :=
    Finset.univ.filter fun Y => IsNonabsPlane Γ c Y ∧ x ∈ Y ∧ (X ∩ Y).ncard = t + 1
  have hA0card : {Y | IsNonabsPlane Γ c Y ∧ x ∈ Y ∧ Disjoint X Y}.ncard = A0.card := by
    rw [← ncard_setOf_eq_card_filter]
  have hA1card : A1.card = s * t - t := by
    rw [← ncard_setOf_eq_card_filter
      (fun Y : Set V => IsNonabsPlane Γ c Y ∧ x ∈ Y ∧ (X ∩ Y).ncard = 1)]
    exact ncard_nonabs_planes_inter_singleton hP hT c hdeg hreg hii hX hx hxX
  have hNcard : N.card = s * (s - t) := by
    rw [← ncard_setOf_eq_card_filter (fun Y : Set V => IsNonabsPlane Γ c Y ∧ x ∈ Y)]
    exact ncard_nonabsPlanes_through hP hT c hdeg hreg hii hx
  have hs : 2 ≤ s := two_le_s hP hT c hdeg
  have ht : 2 ≤ t := two_le_t hP hT c hdeg
  have hA1subN : A1 ⊆ N := by
    intro Y hY
    rw [Finset.mem_filter] at hY
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hY.2.1, hY.2.2.1⟩
  have hA1pos : 0 < A1.card := by
    rw [hA1card]
    have h1 : t < s * t := by
      calc t = 1 * t := (one_mul t).symm
        _ < s * t := Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
    omega
  have htle : t ≤ s := by
    by_contra h
    have hNpos : 0 < N.card := lt_of_lt_of_le hA1pos (Finset.card_le_card hA1subN)
    have hst0 : s - t = 0 := by omega
    rw [hNcard, hst0, mul_zero] at hNpos
    omega
  have hNcases : ∀ Y ∈ N, X ∩ Y = ∅ ∨ (∃ z, X ∩ Y = {z}) ∨ IsStarLine Γ c (X ∩ Y) := by
    intro Y hY
    rw [Finset.mem_filter] at hY
    have hxY : x ∈ Y := hY.2.2
    have hXne : X ≠ Y := by
      intro heq
      exact hxX (heq.symm ▸ hxY)
    exact inter_cases hP hT c hdeg hreg hX.1 hY.2.1.1 hXne
  have hk : ∀ Y ∈ N, (X ∩ Y).ncard = 0 ∨ (X ∩ Y).ncard = 1 ∨ (X ∩ Y).ncard = t + 1 := by
    intro Y hY
    rcases hNcases Y hY with h | ⟨z, hz⟩ | h
    · left
      rw [h]
      simp
    · right
      left
      rw [hz]
      simp
    · right
      right
      exact ncard_of_isStarLine_subset_isOvoid hP hT c hdeg hreg hX.2 h (fun z hz => hz.1)
  have hA0eq : N.filter (fun Y => (X ∩ Y).ncard = 0) = A0 := by
    ext Y
    simp only [N, A0, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨hYnon, hxY⟩, h0⟩
      refine ⟨hYnon, hxY, ?_⟩
      rw [Set.disjoint_iff_inter_eq_empty]
      exact (Set.ncard_eq_zero (s := X ∩ Y)).mp h0
    · rintro ⟨hYnon, hxY, hdisj⟩
      refine ⟨⟨hYnon, hxY⟩, ?_⟩
      rw [Set.disjoint_iff_inter_eq_empty] at hdisj
      rw [hdisj]
      simp
  have hA1eq : N.filter (fun Y => (X ∩ Y).ncard = 1) = A1 := by
    ext Y
    simp only [N, A1, Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  have hA2eq : N.filter (fun Y => (X ∩ Y).ncard = t + 1) = A2 := by
    ext Y
    simp only [N, A2, Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  have hNsum : N.card = A0.card + A1.card + A2.card := by
    have hpoint : ∀ Y ∈ N, (1 : ℕ) =
        (if (X ∩ Y).ncard = 0 then 1 else 0) + (if (X ∩ Y).ncard = 1 then 1 else 0) +
          (if (X ∩ Y).ncard = t + 1 then 1 else 0) := by
      intro Y hY
      rcases hk Y hY with h | h | h <;> simp [h] <;> omega
    calc N.card = ∑ Y ∈ N, (1 : ℕ) := Finset.card_eq_sum_ones N
      _ = ∑ Y ∈ N, ((if (X ∩ Y).ncard = 0 then 1 else 0) +
            (if (X ∩ Y).ncard = 1 then 1 else 0) +
              (if (X ∩ Y).ncard = t + 1 then 1 else 0)) :=
          Finset.sum_congr rfl hpoint
      _ = (N.filter fun Y => (X ∩ Y).ncard = 0).card +
            (N.filter fun Y => (X ∩ Y).ncard = 1).card +
              (N.filter fun Y => (X ∩ Y).ncard = t + 1).card := by
          simp only [Finset.sum_add_distrib, ← Finset.card_filter]
      _ = A0.card + A1.card + A2.card := by rw [hA0eq, hA1eq, hA2eq]
  have hEq1nat : A0.card + A1.card + A2.card = s * (s - t) := by
    rw [← hNsum, hNcard]
  have h1z : (A0.card : ℤ) + (A1.card : ℤ) + (A2.card : ℤ) =
      (s : ℤ) * ((s : ℤ) - (t : ℤ)) := by
    have h := congrArg (fun n : ℕ => (n : ℤ)) hEq1nat
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_sub htle] at h
    exact h
  have hSumEq : (∑ Y ∈ N, (X ∩ Y).ncard) = A1.card + (t + 1) * A2.card := by
    have hpoint : ∀ Y ∈ N, (X ∩ Y).ncard =
        (if (X ∩ Y).ncard = 1 then 1 else 0) +
          (t + 1) * (if (X ∩ Y).ncard = t + 1 then 1 else 0) := by
      intro Y hY
      rcases hk Y hY with h | h | h <;> simp [h] <;> omega
    calc (∑ Y ∈ N, (X ∩ Y).ncard)
        = ∑ Y ∈ N, ((if (X ∩ Y).ncard = 1 then 1 else 0) +
            (t + 1) * (if (X ∩ Y).ncard = t + 1 then 1 else 0)) :=
          Finset.sum_congr rfl hpoint
      _ = (∑ Y ∈ N, (if (X ∩ Y).ncard = 1 then 1 else 0)) +
            (∑ Y ∈ N, (t + 1) * (if (X ∩ Y).ncard = t + 1 then 1 else 0)) :=
          Finset.sum_add_distrib
      _ = (N.filter fun Y => (X ∩ Y).ncard = 1).card +
            (t + 1) * (N.filter fun Y => (X ∩ Y).ncard = t + 1).card := by
          rw [← Finset.card_filter]
          congr 1
          rw [← Finset.mul_sum, ← Finset.card_filter]
      _ = A1.card + (t + 1) * A2.card := by rw [hA1eq, hA2eq]
  have hsumW : (∑ Y ∈ N, (X ∩ Y).ncard) = (s * t - t) * (s - t) :=
    sum_ncard_inter_eq hP hT c hdeg hreg hii hX hx hxX
  have hEq2nat : A1.card + (t + 1) * A2.card = (s * t - t) * (s - t) := by
    rw [← hSumEq, hsumW]
  have hst_le : t ≤ s * t := by
    simpa [Nat.mul_comm] using Nat.le_mul_of_pos_left t (by omega : 0 < s)
  have h2z : (A1.card : ℤ) + ((t : ℤ) + 1) * (A2.card : ℤ) =
      ((s : ℤ) * (t : ℤ) - (t : ℤ)) * ((s : ℤ) - (t : ℤ)) := by
    have h := congrArg (fun n : ℕ => (n : ℤ)) hEq2nat
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_sub htle,
      Nat.cast_sub hst_le] at h
    exact h
  have hstz : ((s * t - t : ℕ) : ℤ) = (s : ℤ) * (t : ℤ) - (t : ℤ) := by
    rw [Nat.cast_sub hst_le, Nat.cast_mul]
  have h3z : (A1.card : ℤ) = (s : ℤ) * (t : ℤ) - (t : ℤ) := by
    rw [hA1card, hstz]
  have hgoal : ((t : ℤ) + 1) * (A0.card : ℤ) =
      (s : ℤ) * ((s : ℤ) - (t : ℤ) ^ 2) := by
    linear_combination ((t : ℤ) + 1) * h1z - h2z - (t : ℤ) * h3z
  rw [hA0card, hgoal]

end UnitalCount

section SEqualsTSq

variable {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj]

theorem s_eq_t_sq (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ) (c : Γ.Coloring (Fin 2))
    {s t : ℕ} (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hreg : ∀ x, c x = 0 → IsRegularVertex Γ x) (hst : s ≠ t)
    (hii : TalliniCondPrime Γ c) : s = t ^ 2 := by
  classical
  have hts : t < s := t_lt_s hP hT c hdeg hreg hst
  have hs : 2 ≤ s := two_le_s hP hT c hdeg
  have ht : 2 ≤ t := two_le_t hP hT c hdeg
  obtain ⟨⟨x, hx⟩⟩ := hP.exists_point (by norm_num) hT c
  have hOpp : 0 < (Finset.univ.filter fun y => Γ.dist x y = 4).card := by
    rw [card_opposite hP hT c hdeg hx]
    have : 0 < s ^ 2 := by positivity
    positivity
  obtain ⟨y, hy⟩ := Finset.card_pos.mp hOpp
  have hy4 : Γ.dist x y = 4 := by simpa using hy
  have hℓhyp : IsHypLine Γ c (starLine Γ c x y) := ⟨x, y, hx, hy4, rfl⟩
  have hcount := (ncard_planes_superset_hypLine hP hT c hdeg hreg hii hℓhyp).2.2
  have hpos : 0 < {X | IsNonabsPlane Γ c X ∧ starLine Γ c x y ⊆ X}.ncard := by
    rw [hcount]
    omega
  obtain ⟨X, hXmem⟩ := (Set.ncard_pos (s := {X | IsNonabsPlane Γ c X ∧
    starLine Γ c x y ⊆ X})).mp hpos
  have hXnon : IsNonabsPlane Γ c X := hXmem.1
  obtain ⟨x0, hx0, hx0X⟩ := hXnon.1.1.2
  have hb5 := card_mul_nonabs_disjoint hP hT c hdeg hreg hii hXnon hx0 hx0X
  have hlhs : (0 : ℤ) ≤ ((t : ℤ) + 1) *
      ({Y | IsNonabsPlane Γ c Y ∧ x0 ∈ Y ∧ Disjoint X Y}.ncard : ℤ) := by
    have h1 : (0 : ℤ) ≤ (t : ℤ) + 1 := by omega
    exact mul_nonneg h1 (by positivity)
  have hrhs : (0 : ℤ) ≤ (s : ℤ) * ((s : ℤ) - (t : ℤ) ^ 2) := by
    rw [← hb5]
    exact hlhs
  have hsZ : (0 : ℤ) < (s : ℤ) := by
    have : (2 : ℤ) ≤ (s : ℤ) := by exact_mod_cast hs
    omega
  have hnonneg : (0 : ℤ) ≤ (s : ℤ) - (t : ℤ) ^ 2 :=
    (mul_nonneg_iff_of_pos_left hsZ).mp hrhs
  have hle : t ^ 2 ≤ s := by
    have hZ : ((t ^ 2 : ℕ) : ℤ) ≤ (s : ℤ) := by
      push_cast at hnonneg ⊢
      linarith
    exact_mod_cast hZ
  exact le_antisymm (higman_s_le_t_sq hP hT c hdeg) hle

end SEqualsTSq

section PlanesMeet

variable {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj]

theorem IsStarPlane.nonempty {c : Γ.Coloring (Fin 2)} {X : Set V}
    (hX : IsStarPlane Γ c X) : X.Nonempty := by
  obtain ⟨x, hx, -⟩ := hX.2
  exact ⟨x, hx⟩

theorem exists_adj_of_color_zero (hT : IsThick Γ) {c : Γ.Coloring (Fin 2)} {u : V}
    (hu : c u = 0) : ∃ L, Γ.Adj u L := by
  have hpos : 0 < (Γ.neighborFinset u).card := by
    rw [card_neighborFinset_eq_degree]
    have := hT u
    omega
  obtain ⟨L, hL⟩ := Finset.card_pos.mp hpos
  exact ⟨L, by simpa using hL⟩

theorem inter_nonempty_of_isAbsPlane (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    {c : Γ.Coloring (Fin 2)} {X Y : Set V} (hX : IsAbsPlane Γ c X)
    (hY : IsAbsPlane Γ c Y) : (X ∩ Y).Nonempty := by
  classical
  obtain ⟨u, hu, rfl⟩ := hX
  obtain ⟨v, hv, rfl⟩ := hY
  have hu_mem : u ∈ ptPerp Γ c {u} := by
    rw [mem_ptPerp]
    exact ⟨hu, by intro z hz; rw [Set.mem_singleton_iff] at hz; rw [hz]; simp⟩
  by_cases huv : u = v
  · subst huv
    exact ⟨u, hu_mem, hu_mem⟩
  · have hne0 : Γ.dist u v ≠ 0 := fun h => huv ((hP.connected.dist_eq_zero_iff).mp h)
    have heven : Even (Γ.dist u v) := (hP.eq_iff_even_dist c u v).1 (hu.trans hv.symm)
    have hle : Γ.dist u v ≤ 4 := hP.dist_le (by norm_num) u v
    have h2or4 : Γ.dist u v = 2 ∨ Γ.dist u v = 4 := by
      obtain ⟨k, hk⟩ := heven
      omega
    rcases h2or4 with h2 | h4
    · have hu_mem' : u ∈ ptPerp Γ c {v} := by
        rw [mem_ptPerp]
        exact ⟨hu, by intro z hz; rw [Set.mem_singleton_iff] at hz; rw [hz]; omega⟩
      exact ⟨u, hu_mem, hu_mem'⟩
    · obtain ⟨L, hLu⟩ := exists_adj_of_color_zero hT hu
      have hvL : Γ.dist v L = 3 := dist_eq_three_of_adj_of_dist_eq_four hP h4 hLu
      let w := proj hP hvL
      have hLw : Γ.Adj L w := proj_adj hP hvL
      have hvw : Γ.dist v w = 2 := proj_dist hP hvL
      have hwu : Γ.dist w u = 2 := by
        have h4' : Γ.dist v u = 4 := by rw [SimpleGraph.dist_comm]; exact h4
        have hwne : w ≠ u := by
          intro h
          rw [h] at hvw
          omega
        exact dist_eq_two_of_adj_of_adj_of_ne hP hLw.symm hLu.symm hwne
      have hwv : Γ.dist w v = 2 := by rw [SimpleGraph.dist_comm]; exact hvw
      have hL1 : c L = 1 := color_eq_one_of_adj_of_color_eq_zero hu hLu
      have hw0 : c w = 0 := color_eq_zero_of_adj_of_color_eq_one hL1 hLw
      refine ⟨w, ?_, ?_⟩
      · rw [mem_ptPerp]
        exact ⟨hw0, by intro z hz; rw [Set.mem_singleton_iff] at hz; rw [hz]; omega⟩
      · rw [mem_ptPerp]
        exact ⟨hw0, by intro z hz; rw [Set.mem_singleton_iff] at hz; rw [hz]; omega⟩

theorem inter_nonempty_of_isAbsPlane_of_isNonabsPlane (hP : IsGeneralizedPolygon Γ 4)
    (hT : IsThick Γ) {c : Γ.Coloring (Fin 2)} {X Y : Set V} (hX : IsAbsPlane Γ c X)
    (hY : IsNonabsPlane Γ c Y) : (X ∩ Y).Nonempty := by
  classical
  obtain ⟨u, hu, rfl⟩ := hX
  obtain ⟨L, hLu⟩ := exists_adj_of_color_zero hT hu
  have hL1 : c L = 1 := color_eq_one_of_adj_of_color_eq_zero hu hLu
  obtain ⟨z, hz⟩ := Set.ncard_eq_one.mp (hY.2.2 L hL1)
  have hzmem : z ∈ Γ.neighborSet L ∩ Y := by rw [hz]; simp
  by_cases hzu : z = u
  · refine ⟨u, ?_, hzu ▸ hzmem.2⟩
    rw [mem_ptPerp]
    refine ⟨hu, ?_⟩
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    rw [ha]
    simp
  · have hzu2 : Γ.dist z u = 2 :=
      dist_eq_two_of_adj_of_adj_of_ne hP hzmem.1.symm hLu.symm hzu
    refine ⟨z, ?_, hzmem.2⟩
    rw [mem_ptPerp]
    refine ⟨(hY.1.1.1.1) z hzmem.2, ?_⟩
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    rw [ha]
    omega

theorem inter_nonempty (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hreg : ∀ x, c x = 0 → IsRegularVertex Γ x) (hst : s ≠ t)
    (hii : TalliniCondPrime Γ c) {X Y : Set V} (hX : IsStarPlane Γ c X)
    (hY : IsStarPlane Γ c Y) : (X ∩ Y).Nonempty := by
  classical
  rcases isStarPlane_cases hP hT c hdeg hreg hX with hXabs | hXnon
  · rcases isStarPlane_cases hP hT c hdeg hreg hY with hYabs | hYnon
    · exact inter_nonempty_of_isAbsPlane hP hT hXabs hYabs
    · exact inter_nonempty_of_isAbsPlane_of_isNonabsPlane hP hT hXabs hYnon
  · rcases isStarPlane_cases hP hT c hdeg hreg hY with hYabs | hYnon
    · have h := inter_nonempty_of_isAbsPlane_of_isNonabsPlane hP hT hYabs hXnon
      rwa [Set.inter_comm] at h
    · by_cases hXY : X = Y
      · rw [hXY]
        simpa using IsStarPlane.nonempty hY
      · have hnotsub : ¬ Y ⊆ X := by
          intro hsub
          have hXc : X.ncard = s * t + 1 := ncard_of_isOvoid hP hT c hdeg hXnon.2
          have hYc : Y.ncard = s * t + 1 := ncard_of_isOvoid hP hT c hdeg hYnon.2
          have hEq : Y = X := Set.eq_of_subset_of_ncard_le hsub (by rw [hXc, hYc])
          exact hXY hEq.symm
        obtain ⟨x, hxY, hxX⟩ := Set.not_subset.mp hnotsub
        have hx0 : c x = 0 := hYnon.1.1.1.1 x hxY
        have hb5 := card_mul_nonabs_disjoint hP hT c hdeg hreg hii hXnon hx0 hxX
        have hb6 : s = t ^ 2 := s_eq_t_sq hP hT c hdeg hreg hst hii
        have hzero : ((t : ℤ) + 1) *
            ({Y' | IsNonabsPlane Γ c Y' ∧ x ∈ Y' ∧ Disjoint X Y'}.ncard : ℤ) = 0 := by
          have h := hb5
          rw [hb6] at h
          push_cast at h
          simpa using h
        have hA0 : {Y' | IsNonabsPlane Γ c Y' ∧ x ∈ Y' ∧ Disjoint X Y'}.ncard = 0 := by
          have hpos : (0 : ℤ) < (t : ℤ) + 1 := by omega
          rcases mul_eq_zero.mp hzero with h | h
          · omega
          · exact_mod_cast h
        by_contra hemp
        have hdisj : Disjoint X Y := by
          rw [Set.disjoint_iff_inter_eq_empty]
          exact Set.not_nonempty_iff_eq_empty.mp hemp
        have hYmem : Y ∈ {Y' | IsNonabsPlane Γ c Y' ∧ x ∈ Y' ∧ Disjoint X Y'} :=
          ⟨hYnon, hxY, hdisj⟩
        have hpos : 0 < {Y' | IsNonabsPlane Γ c Y' ∧ x ∈ Y' ∧ Disjoint X Y'}.ncard :=
          (Set.ncard_pos (s := {Y' | IsNonabsPlane Γ c Y' ∧ x ∈ Y' ∧ Disjoint X Y'})).mpr
            ⟨Y, hYmem⟩
        omega

end PlanesMeet

end CFSG.Geometry.GeneralizedQuadrangles
