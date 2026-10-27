module

public import CFSG.Geometry.GeneralizedQuadrangles.Hermitian.Tallini.Bundles

public section

namespace CFSG.Geometry.GeneralizedQuadrangles

open SimpleGraph CFSG.Geometry.GeneralizedPolygons

universe u

variable {V : Type u}

section PaschF

variable {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj]

theorem ncard_starPlanes (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hreg : ∀ x, c x = 0 → IsRegularVertex Γ x) (hst : s ≠ t) (hii : TalliniCondPrime Γ c) :
    {X | IsStarPlane Γ c X}.ncard = s ^ 3 + s ^ 2 + s + 1 := by
  classical
  have hPcard : {u : V | c u = 0}.ncard = (s + 1) * (s * t + 1) := by
    have hset : {u : V | c u = 0} = (pointFinset c : Set V) := by
      ext u
      simp [mem_pointFinset]
    rw [hset, Set.ncard_coe_finset, card_pointFinset hP hT c hdeg]
  have hAcard : {X : Set V | IsAbsPlane Γ c X}.ncard = (s + 1) * (s * t + 1) := by
    calc
      {X : Set V | IsAbsPlane Γ c X}.ncard = {u : V | c u = 0}.ncard := by
        refine (Set.ncard_congr (s := {u : V | c u = 0})
          (t := {X : Set V | IsAbsPlane Γ c X}) (fun u _ => ptPerp Γ c {u}) ?_ ?_ ?_).symm
        · intro u hu
          exact ⟨u, hu, rfl⟩
        · intro u v hu hv h
          exact ptPerp_singleton_injective hP hT hu hv h
        · intro X hX
          obtain ⟨u, hu, rfl⟩ := hX
          exact ⟨u, hu, rfl⟩
      _ = (s + 1) * (s * t + 1) := hPcard
  let P : Finset V := pointFinset c
  let N : Finset (Set V) := Finset.univ.filter fun X => IsNonabsPlane Γ c X
  let Pairs : Finset (V × Set V) := (P ×ˢ N).filter fun p => p.1 ∈ p.2
  have hPcard' : P.card = (s + 1) * (s * t + 1) := card_pointFinset hP hT c hdeg
  have hrow : Pairs.card = P.card * (s * (s - t)) := by
    rw [Finset.card_filter, Finset.sum_product]
    have hinner : ∀ x ∈ P, (∑ X ∈ N, if x ∈ X then 1 else 0) = s * (s - t) := by
      intro x hx
      have hx0 : c x = 0 := by
        have hx' : x ∈ pointFinset c := by simpa [P] using hx
        simpa using (mem_pointFinset.mp hx')
      have hb2 := ncard_nonabsPlanes_through hP hT c hdeg hreg hii hx0
      have hcoe : ((N.filter fun X => x ∈ X : Finset (Set V)) : Set (Set V)) =
          {X : Set V | IsNonabsPlane Γ c X ∧ x ∈ X} := by
        ext X
        simp [N]
      calc
        (∑ X ∈ N, if x ∈ X then 1 else 0) = (N.filter fun X => x ∈ X).card := by
          rw [Finset.card_filter]
        _ = {X : Set V | IsNonabsPlane Γ c X ∧ x ∈ X}.ncard := by
          rw [← Set.ncard_coe_finset, hcoe]
        _ = s * (s - t) := hb2
    calc
      (∑ x ∈ P, ∑ X ∈ N, if x ∈ X then 1 else 0)
          = ∑ x ∈ P, (N.filter fun X => x ∈ X).card := by
            apply Finset.sum_congr rfl
            intro x hx
            rw [Finset.card_filter]
      _ = ∑ x ∈ P, s * (s - t) := by
            apply Finset.sum_congr rfl
            intro x hx
            rw [Finset.card_filter]
            exact hinner x hx
      _ = P.card * (s * (s - t)) := by
            rw [Finset.sum_const, smul_eq_mul]
  have hcol : Pairs.card = N.card * (s * t + 1) := by
    rw [Finset.card_filter, Finset.sum_product, Finset.sum_comm]
    have hinner : ∀ X ∈ N, (∑ x ∈ P, if x ∈ X then 1 else 0) = s * t + 1 := by
      intro X hX
      have hXnon : IsNonabsPlane Γ c X := by simpa [N] using hX
      have hXc : X.ncard = s * t + 1 := ncard_of_isOvoid hP hT c hdeg hXnon.2
      have hset : ((P.filter fun x => x ∈ X : Finset V) : Set V) = X := by
        ext x
        constructor
        · intro hx
          rw [Finset.mem_coe, Finset.mem_filter] at hx
          exact hx.2
        · intro hxX
          rw [Finset.mem_coe, Finset.mem_filter]
          exact ⟨by simpa [P] using (mem_pointFinset.mpr (hXnon.2.1 x hxX)), hxX⟩
      calc
        (∑ x ∈ P, if x ∈ X then 1 else 0) = (P.filter fun x => x ∈ X).card := by
          rw [Finset.card_filter]
        _ = X.ncard := by rw [← Set.ncard_coe_finset, hset]
        _ = s * t + 1 := hXc
    calc
      (∑ X ∈ N, ∑ x ∈ P, if x ∈ X then 1 else 0)
          = ∑ X ∈ N, (P.filter fun x => x ∈ X).card := by
            apply Finset.sum_congr rfl
            intro X hX
            rw [Finset.card_filter]
      _ = ∑ X ∈ N, (s * t + 1) := by
            apply Finset.sum_congr rfl
            intro X hX
            rw [Finset.card_filter]
            exact hinner X hX
      _ = N.card * (s * t + 1) := by
            rw [Finset.sum_const, smul_eq_mul]
  have hNcard : N.card = (s + 1) * s * (s - t) := by
    have hmul : N.card * (s * t + 1) = P.card * (s * (s - t)) := by
      rw [← hcol, hrow]
    rw [hPcard'] at hmul
    have hR : ((s + 1) * (s * t + 1)) * (s * (s - t)) =
        ((s + 1) * s * (s - t)) * (s * t + 1) := by ring
    rw [hR] at hmul
    exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < s * t + 1) hmul
  have hNset : N.card = {X : Set V | IsNonabsPlane Γ c X}.ncard := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext X
    simp [N]
  have hUnion : {X : Set V | IsStarPlane Γ c X} =
      {X : Set V | IsAbsPlane Γ c X} ∪ {X : Set V | IsNonabsPlane Γ c X} := by
    ext X
    constructor
    · intro hX
      rcases isStarPlane_cases hP hT c hdeg hreg hX with h | h
      · exact Or.inl h
      · exact Or.inr h
    · rintro (h | h)
      · obtain ⟨u, hu, rfl⟩ := h
        exact isStarPlane_ptPerp_singleton hP hT c hdeg hu
      · exact h.1
  have hDisj : Disjoint {X : Set V | IsAbsPlane Γ c X} {X : Set V | IsNonabsPlane Γ c X} := by
    rw [Set.disjoint_left]
    intro X hXa hXn
    obtain ⟨u, hu, rfl⟩ := hXa
    have h1 : (ptPerp Γ c {u}).ncard = s * t + s + 1 :=
      ncard_ptPerp_singleton hP hT c hdeg hu
    have h2 : (ptPerp Γ c {u}).ncard = s * t + 1 :=
      ncard_of_isOvoid hP hT c hdeg hXn.2
    have hs : 2 ≤ s := two_le_s hP hT c hdeg
    omega
  rw [hUnion, Set.ncard_union_eq hDisj, hAcard, ← hNset, hNcard]
  have hts : t ≤ s := le_of_lt (t_lt_s hP hT c hdeg hreg hst)
  have hsum : s * t + s * (s - t) = s * s := by
    rw [← Nat.mul_add, Nat.add_sub_of_le hts]
  have hinner : (s * t + 1) + s * (s - t) = s * s + 1 := by
    calc
      (s * t + 1) + s * (s - t) = (s * t + s * (s - t)) + 1 := by ring
      _ = s * s + 1 := by rw [hsum]
  calc
    (s + 1) * (s * t + 1) + (s + 1) * s * (s - t)
        = (s + 1) * ((s * t + 1) + s * (s - t)) := by ring
    _ = (s + 1) * (s * s + 1) := by rw [hinner]
    _ = s ^ 3 + s ^ 2 + s + 1 := by ring

theorem eq_axisBundle_of_pairwise (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hreg : ∀ x, c x = 0 → IsRegularVertex Γ x) (hst : s ≠ t) (hii : TalliniCondPrime Γ c)
    {F : Set (Set V)} {L : Set V} (hL : IsStarLine Γ c L) (hF : ∀ X ∈ F, IsStarPlane Γ c X)
    (hcard : F.ncard = s + 1) (hpair : ∀ X ∈ F, ∀ Y ∈ F, X ≠ Y → X ∩ Y = L) :
    F = axisBundle Γ c L := by
  classical
  have hs : 2 ≤ s := two_le_s hP hT c hdeg
  have hsub : F ⊆ axisBundle Γ c L := by
    intro X hX
    refine ⟨hF X hX, ?_⟩
    have hlt : 1 < F.ncard := by rw [hcard]; omega
    obtain ⟨Y, hY, hYX⟩ := Set.exists_ne_of_one_lt_ncard hlt X
    have hXY : X ≠ Y := (fun h => hYX h.symm)
    have hinter := hpair X hX Y hY hXY
    rw [← hinter]
    exact Set.inter_subset_left
  have hcardb : (axisBundle Γ c L).ncard = s + 1 :=
    ncard_of_isPlaneBundle hP hT c hdeg hreg hst hii (Or.inl ⟨L, hL, rfl⟩)
  exact Set.eq_of_subset_of_ncard_le hsub (by rw [hcardb, hcard])

theorem eq_tangentBundle_of_pairwise (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hreg : ∀ x, c x = 0 → IsRegularVertex Γ x) (hst : s ≠ t) (hii : TalliniCondPrime Γ c)
    {F : Set (Set V)} {x : V} (hF : ∀ X ∈ F, IsStarPlane Γ c X) (hcard : F.ncard = s + 1)
    (hpair : ∀ X ∈ F, ∀ Y ∈ F, X ≠ Y → X ∩ Y = {x}) :
    ∃ X ∈ F, IsNonabsPlane Γ c X ∧ F = tangentBundle Γ c X x := by
  classical
  have hs : 2 ≤ s := two_le_s hP hT c hdeg
  have hlt : 1 < F.ncard := by rw [hcard]; omega
  have hnonabs : ∃ X ∈ F, IsNonabsPlane Γ c X := by
    by_contra h
    have hno : ∀ X ∈ F, ¬ IsNonabsPlane Γ c X := by
      intro X hX hXn
      exact h ⟨X, hX, hXn⟩
    have hpos : 0 < F.ncard := by rw [hcard]; omega
    obtain ⟨X, hX⟩ := (Set.ncard_pos (s := F)).mp hpos
    obtain ⟨Y, hY, hYX⟩ := Set.exists_ne_of_one_lt_ncard hlt X
    have hXY : X ≠ Y := (fun h => hYX h.symm)
    have hXabs : IsAbsPlane Γ c X := by
      rcases isStarPlane_cases hP hT c hdeg hreg (hF X hX) with h' | h'
      · exact h'
      · exact absurd h' (hno X hX)
    have hYabs : IsAbsPlane Γ c Y := by
      rcases isStarPlane_cases hP hT c hdeg hreg (hF Y hY) with h' | h'
      · exact h'
      · exact absurd h' (hno Y hY)
    exact not_inter_eq_singleton_of_isAbsPlane hP hT c hdeg hXabs hYabs hXY
      (hpair X hX Y hY hXY)
  obtain ⟨X, hXF, hXnon⟩ := hnonabs
  have hxX : x ∈ X := by
    obtain ⟨Y, hY, hYX⟩ := Set.exists_ne_of_one_lt_ncard hlt X
    have hXY : X ≠ Y := (fun h => hYX h.symm)
    have hinter := hpair X hXF Y hY hXY
    have hxint : x ∈ X ∩ Y := by rw [hinter]; exact Set.mem_singleton x
    exact hxint.1
  have hsub : F ⊆ tangentBundle Γ c X x := by
    intro Y hY
    refine ⟨hF Y hY, ?_⟩
    by_cases hYX : Y = X
    · exact Or.inl hYX
    · exact Or.inr (hpair X hXF Y hY (fun h => hYX h.symm))
  have hcardb : (tangentBundle Γ c X x).ncard = s + 1 :=
    ncard_of_isPlaneBundle hP hT c hdeg hreg hst hii
      (Or.inr ⟨X, x, hXnon, hxX, rfl⟩)
  have heq : F = tangentBundle Γ c X x :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [hcard, hcardb])
  exact ⟨X, hXF, hXnon, heq⟩

end PaschF

end CFSG.Geometry.GeneralizedQuadrangles
