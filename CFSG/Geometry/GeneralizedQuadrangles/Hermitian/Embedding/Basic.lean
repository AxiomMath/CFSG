module

public import CFSG.Geometry.GeneralizedQuadrangles.Subquadrangle2
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import CFSG.Geometry.GeneralizedQuadrangles.Hermitian.Tallini.Varieties
public import Mathlib.RingTheory.LocalRing.Basic

public section

namespace CFSG.Geometry.GeneralizedQuadrangles

open SimpleGraph CFSG.Geometry.GeneralizedPolygons Module

universe u

variable {V : Type u}

structure IsProjGQ {Γ : SimpleGraph V} (c : Γ.Coloring (Fin 2)) {K W : Type*} [Field K]
    [AddCommGroup W] [Module K W] (ι : V → Submodule K W) (A : Submodule K W) : Prop where
  injective : Function.Injective ι
  finrank_point : ∀ x, c x = 0 → finrank K (ι x) = 1
  finrank_line : ∀ L, c L = 1 → finrank K (ι L) = 2
  le_ambient : ∀ v, ι v ≤ A
  adj_iff : ∀ x L, c x = 0 → c L = 1 → (Γ.Adj x L ↔ ι x ≤ ι L)
  full : ∀ L, c L = 1 → ∀ U : Submodule K W, finrank K U = 1 → U ≤ ι L →
    ∃ x, Γ.Adj L x ∧ ι x = U
  span : ⨆ (x : V) (_ : c x = 0), ι x = A

section Sections

variable {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj] {c : Γ.Coloring (Fin 2)}
variable {K : Type*} [Field K] {W : Type*} [AddCommGroup W] [Module K W]
variable {ι : V → Submodule K W} {A U : Submodule K W}

@[expose] def sectionPoints (c : Γ.Coloring (Fin 2)) (ι : V → Submodule K W)
    (U : Submodule K W) : Set V :=
  {x | c x = 0 ∧ ι x ≤ U}

@[expose] def sectionLines (c : Γ.Coloring (Fin 2)) (ι : V → Submodule K W)
    (U : Submodule K W) : Set V :=
  {L | c L = 1 ∧ ι L ≤ U}

@[expose] def fullSectionLines (c : Γ.Coloring (Fin 2)) (ι : V → Submodule K W)
    (U : Submodule K W) : Set V :=
  {L | c L = 1 ∧ Γ.neighborSet L ⊆ sectionPoints c ι U}

@[simp] theorem mem_sectionPoints {x : V} :
    x ∈ sectionPoints c ι U ↔ c x = 0 ∧ ι x ≤ U := Iff.rfl

@[simp] theorem mem_sectionLines {L : V} :
    L ∈ sectionLines c ι U ↔ c L = 1 ∧ ι L ≤ U := Iff.rfl

@[simp] theorem mem_fullSectionLines {L : V} :
    L ∈ fullSectionLines c ι U ↔
      c L = 1 ∧ Γ.neighborSet L ⊆ sectionPoints c ι U := Iff.rfl

end Sections

section Incidence

variable {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj] {c : Γ.Coloring (Fin 2)}
variable {K : Type*} [Field K] {W : Type*} [AddCommGroup W] [Module K W]
variable {ι : V → Submodule K W} {A U : Submodule K W}

theorem line_eq_sup_of_two_adjacent_points (hι : IsProjGQ c ι A) {x y L : V}
    (hx : c x = 0) (hy : c y = 0) (hxy : x ≠ y)
    (hxL : Γ.Adj x L) (hyL : Γ.Adj y L) :
    ι L = ι x ⊔ ι y := by
  have hL : c L = 1 := color_eq_one_of_adj_of_color_eq_zero hx hxL
  have hx1 : finrank K (ι x) = 1 := hι.finrank_point x hx
  have hy1 : finrank K (ι y) = 1 := hι.finrank_point y hy
  have hL2 : finrank K (ι L) = 2 := hι.finrank_line L hL
  haveI : FiniteDimensional K (ι x) := Module.finite_of_finrank_pos (by omega)
  haveI : FiniteDimensional K (ι y) := Module.finite_of_finrank_pos (by omega)
  haveI : FiniteDimensional K (ι L) := Module.finite_of_finrank_pos (by omega)
  have hne : ι x ≠ ι y := fun h => hxy (hι.injective h)
  have hbot : ι x ⊓ ι y = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro v hv
    by_contra hv0
    have hxspan : ι x = K ∙ v :=
      eq_span_singleton_of_mem_of_finrank_eq_one hx1 hv.1 hv0
    have hyspan : ι y = K ∙ v :=
      eq_span_singleton_of_mem_of_finrank_eq_one hy1 hv.2 hv0
    exact hne (hxspan.trans hyspan.symm)
  have hsup2 : finrank K ↥(ι x ⊔ ι y) = 2 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq (ι x) (ι y)
    rw [hbot, finrank_bot, hx1, hy1] at h
    omega
  have hle : ι x ⊔ ι y ≤ ι L :=
    sup_le ((hι.adj_iff x L hx hL).1 hxL) ((hι.adj_iff y L hy hL).1 hyL)
  exact (Submodule.eq_of_le_of_finrank_eq hle (by rw [hsup2, hL2])).symm

theorem line_le_of_two_sectionPoints (hι : IsProjGQ c ι A) {x y L : V}
    (hx : x ∈ sectionPoints c ι U) (hy : y ∈ sectionPoints c ι U) (hxy : x ≠ y)
    (hxL : Γ.Adj x L) (hyL : Γ.Adj y L) : ι L ≤ U := by
  rw [line_eq_sup_of_two_adjacent_points hι hx.1 hy.1 hxy hxL hyL]
  exact sup_le hx.2 hy.2

theorem neighborSet_subset_of_sectionLines (hι : IsProjGQ c ι A) {L : V}
    (hL : L ∈ sectionLines c ι U) : Γ.neighborSet L ⊆ sectionPoints c ι U := by
  intro x hx
  have hx0 : c x = 0 := color_eq_zero_of_adj_of_color_eq_one hL.1 hx
  exact ⟨hx0, ((hι.adj_iff x L hx0 hL.1).1 hx.symm).trans hL.2⟩

theorem le_of_neighborSet_subset_sectionPoints (hι : IsProjGQ c ι A) {L : V}
    (hL : c L = 1) (hneigh : Γ.neighborSet L ⊆ sectionPoints c ι U) : ι L ≤ U := by
  intro v hv
  by_contra hvU
  have hv0 : v ≠ 0 := by
    rintro rfl
    exact hvU (Submodule.zero_mem U)
  let P : Submodule K W := K ∙ v
  have hP1 : finrank K P = 1 := finrank_span_singleton hv0
  have hPle : P ≤ ι L := (Submodule.span_singleton_le_iff_mem v (ι L)).mpr hv
  obtain ⟨x, hLx, hxP⟩ := hι.full L hL P hP1 hPle
  have hxsec : x ∈ sectionPoints c ι U := hneigh hLx
  have hxU : ι x ≤ U := hxsec.2
  rw [hxP] at hxU
  exact hvU (hxU (Submodule.mem_span_singleton_self v))

end Incidence

section Vocabulary

variable {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj] {c : Γ.Coloring (Fin 2)}
variable {K : Type*} [Field K] {W : Type*} [AddCommGroup W] [Module K W]
variable {ι : V → Submodule K W} {A U : Submodule K W}

@[expose] def IsPencilSection (c : Γ.Coloring (Fin 2)) (ι : V → Submodule K W)
    (U : Submodule K W) : Prop :=
  ∃ p, c p = 0 ∧
    (∀ L, c L = 1 → ι L ≤ U → Γ.Adj p L) ∧
    ∀ x, c x = 0 → ι x ≤ U → ∃ L, c L = 1 ∧ ι L ≤ U ∧ Γ.Adj x L

@[expose] def IsPairwiseNoncollinear (Γ : SimpleGraph V) (X : Set V) : Prop :=
  ∀ x ∈ X, ∀ y ∈ X, x ≠ y → Γ.dist x y ≠ 2

@[expose] def HasOrdinaryQuadrangle (Γ : SimpleGraph V) (X : Set V) : Prop :=
  ∃ x ∈ X, ∃ y ∈ X, Γ.dist x y = 4 ∧ 2 ≤ (traceSet Γ x y ∩ X).ncard

@[expose] def HasConstantSecants (c : Γ.Coloring (Fin 2)) (ι : V → Submodule K W)
    (A : Submodule K W) (ℓ : ℕ) : Prop :=
  ∀ U : Submodule K W, U ≤ A → finrank K U = 2 → (∀ L, c L = 1 → ι L ≠ U) →
    2 ≤ (sectionPoints c ι U).ncard → (sectionPoints c ι U).ncard = ℓ + 1

theorem HasConstantSecants.ncard_eq {ℓ : ℕ} (h : HasConstantSecants c ι A ℓ)
    {U : Submodule K W} (hU : U ≤ A) (h2 : finrank K U = 2)
    (hne : ∀ L, c L = 1 → ι L ≠ U) (hge : 2 ≤ (sectionPoints c ι U).ncard) :
    (sectionPoints c ι U).ncard = ℓ + 1 :=
  h U hU h2 hne hge

end Vocabulary

section Elementary

variable {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj] {c : Γ.Coloring (Fin 2)}
variable {K : Type*} [Field K] {W : Type*} [AddCommGroup W] [Module K W]
variable {ι : V → Submodule K W} {A U : Submodule K W}

theorem pairwiseNoncollinear_of_sectionLines_eq_empty (hP : IsGeneralizedPolygon Γ 4)
    (hι : IsProjGQ c ι A) (hempty : sectionLines c ι U = ∅) :
    IsPairwiseNoncollinear Γ (sectionPoints c ι U) := by
  intro x hx y hy hxy hdist
  obtain ⟨L, ⟨hxL, hyL⟩, -⟩ := existsUnique_commonNeighbor hP hdist
  have hL : L ∈ sectionLines c ι U :=
    ⟨color_eq_one_of_adj_of_color_eq_zero hx.1 hxL,
      line_le_of_two_sectionPoints hι hx hy hxy hxL hyL⟩
  rw [hempty] at hL
  exact hL

theorem exists_isFullSubquadrangle_of_hasOrdinaryQuadrangle (hP : IsGeneralizedPolygon Γ 4)
    (hT : IsThick Γ) (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hι : IsProjGQ c ι A) (hquad : HasOrdinaryQuadrangle Γ (sectionPoints c ι U)) :
    ∃ t' : ℕ, 1 ≤ t' ∧ IsFullSubquadrangle c (sectionPoints c ι U) t' := by
  classical
  have h0 : ∀ x ∈ sectionPoints c ι U, c x = 0 := fun x hx => hx.1
  have hfull : ∀ L, c L = 1 → 2 ≤ (Γ.neighborSet L ∩ sectionPoints c ι U).ncard →
      Γ.neighborSet L ⊆ sectionPoints c ι U := by
    intro L hL h2
    have h1 : 1 < (Γ.neighborSet L ∩ sectionPoints c ι U).ncard := by omega
    obtain ⟨x, hx, y, hy, hxy⟩ :=
      (Set.one_lt_ncard (s := Γ.neighborSet L ∩ sectionPoints c ι U)).mp h1
    have hLU : ι L ≤ U :=
      line_le_of_two_sectionPoints hι hx.2 hy.2 hxy hx.1.symm hy.1.symm
    intro z hz
    have hz0 : c z = 0 := color_eq_zero_of_adj_of_color_eq_one hL hz
    exact ⟨hz0, ((hι.adj_iff z L hz0 hL).1 hz.symm).trans hLU⟩
  exact exists_isFullSubquadrangle hP hT c hdeg h0 hfull hquad

end Elementary

end CFSG.Geometry.GeneralizedQuadrangles

namespace CFSG.Geometry.GeneralizedQuadrangles

open SimpleGraph CFSG.Geometry.GeneralizedPolygons Module

universe u

variable {V : Type u}

public section

section Grid

variable {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj] {c : Γ.Coloring (Fin 2)}
variable {K : Type*} [Field K] {W : Type*} [AddCommGroup W] [Module K W]
variable {ι : V → Submodule K W} {A U : Submodule K W}

theorem hasOrdinaryQuadrangle_of_two_disjoint_sectionLines
    (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ) (hι : IsProjGQ c ι A)
    {L1 L2 : V} (hL1 : L1 ∈ sectionLines c ι U) (hL2 : L2 ∈ sectionLines c ι U)
    (hdisj : ∀ p, ¬ (Γ.Adj L1 p ∧ Γ.Adj L2 p)) :
    HasOrdinaryQuadrangle Γ (sectionPoints c ι U) := by
  classical
  have hX1 : Γ.neighborSet L1 ⊆ sectionPoints c ι U :=
    neighborSet_subset_of_sectionLines hι hL1
  have hX2 : Γ.neighborSet L2 ⊆ sectionPoints c ι U :=
    neighborSet_subset_of_sectionLines hι hL2
  have hL1c : c L1 = 1 := hL1.1
  have hL2c : c L2 = 1 := hL2.1
  have h3 : 3 ≤ (Γ.neighborSet L1).ncard := by
    rw [ncard_neighborSet]
    exact hT L1
  have h2 : 1 < (Γ.neighborSet L1).ncard := by omega
  obtain ⟨x1, hx1, x2, hx2, hx12⟩ :=
    (Set.one_lt_ncard (s := Γ.neighborSet L1)).mp h2
  have hx1X : x1 ∈ sectionPoints c ι U := hX1 hx1
  have hx2X : x2 ∈ sectionPoints c ι U := hX1 hx2
  have hproj : ∀ x ∈ Γ.neighborSet L1, ∃ y, Γ.Adj L2 y ∧ Γ.dist x y = 2 ∧
      ∀ y', Γ.Adj L2 y' → Γ.dist x y' = 2 → y' = y := by
    intro x hx
    have hnot : ¬ Γ.Adj x L2 := by
      intro hxL2
      exact hdisj x ⟨hx, hxL2.symm⟩
    have hx0 : c x = 0 := (hX1 hx).1
    have hc : c x ≠ c L2 := by rw [hx0, hL2c]; decide
    have hdist : Γ.dist x L2 = 3 :=
      dist_eq_three_of_not_adj_of_color_ne hP c hnot hc
    obtain ⟨y, hy, huniq⟩ := existsUnique_proj hP hdist
    exact ⟨y, hy.1, hy.2, fun y' hy' hdy' => huniq y' ⟨hy', hdy'⟩⟩
  obtain ⟨y1, hy1L2, hx1y1, hy1uniq⟩ := hproj x1 hx1
  obtain ⟨y2, hy2L2, hx2y2, _hy2uniq⟩ := hproj x2 hx2
  have hy1X : y1 ∈ sectionPoints c ι U := hX2 hy1L2
  have hy2X : y2 ∈ sectionPoints c ι U := hX2 hy2L2
  have hy1y2 : y1 ≠ y2 := by
    intro hy
    have hy10 : c y1 = 0 := hy1X.1
    have hnot : ¬ Γ.Adj y1 L1 := by
      intro hyL1
      exact hdisj y1 ⟨hyL1.symm, hy1L2⟩
    have hc : c y1 ≠ c L1 := by rw [hy10, hL1c]; decide
    have hdist : Γ.dist y1 L1 = 3 :=
      dist_eq_three_of_not_adj_of_color_ne hP c hnot hc
    have hx1' : Γ.Adj L1 x1 ∧ Γ.dist y1 x1 = 2 :=
      ⟨hx1, by rw [SimpleGraph.dist_comm]; exact hx1y1⟩
    have hx2' : Γ.Adj L1 x2 ∧ Γ.dist y1 x2 = 2 := by
      refine ⟨hx2, ?_⟩
      rw [SimpleGraph.dist_comm, hy]
      exact hx2y2
    exact hx12 ((existsUnique_proj hP hdist).unique hx1' hx2')
  have hx1y2_ne : x1 ≠ y2 := by
    intro h
    exact hdisj x1 ⟨hx1, by rw [h]; exact hy2L2⟩
  have hx2y1_ne : x2 ≠ y1 := by
    intro h
    exact hdisj x2 ⟨hx2, by rw [h]; exact hy1L2⟩
  have hy1y2_dist : Γ.dist y1 y2 = 2 :=
    dist_eq_two_of_adj_of_adj_of_ne hP hy1L2.symm hy2L2 hy1y2
  have hx1x2_dist : Γ.dist x1 x2 = 2 :=
    dist_eq_two_of_adj_of_adj_of_ne hP hx1.symm hx2 hx12
  have hx1y2_opp : Γ.dist x1 y2 = 4 := by
    rcases dist_eq_two_or_four_of_color_zero hP hx1X.1 hy2X.1 hx1y2_ne with h | h
    · exact absurd (hy1uniq y2 hy2L2 h) (Ne.symm hy1y2)
    · exact h
  have hy1trace : y1 ∈ traceSet Γ x1 y2 :=
    ⟨hx1y1, by rw [SimpleGraph.dist_comm]; exact hy1y2_dist⟩
  have hx2trace : x2 ∈ traceSet Γ x1 y2 :=
    ⟨hx1x2_dist, by rw [SimpleGraph.dist_comm]; exact hx2y2⟩
  have htrace : 2 ≤ (traceSet Γ x1 y2 ∩ sectionPoints c ι U).ncard := by
    have h1 : 1 < (traceSet Γ x1 y2 ∩ sectionPoints c ι U).ncard :=
      (Set.one_lt_ncard (s := traceSet Γ x1 y2 ∩ sectionPoints c ι U)).mpr
        ⟨y1, ⟨hy1trace, hy1X⟩, x2, ⟨hx2trace, hx2X⟩, Ne.symm hx2y1_ne⟩
    omega
  exact ⟨x1, hx1X, y2, hy2X, hx1y2_opp, htrace⟩

end Grid

section Trichotomy

variable {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj] {c : Γ.Coloring (Fin 2)}
variable {K : Type*} [Field K] {W : Type*} [AddCommGroup W] [Module K W]
variable {ι : V → Submodule K W} {A U : Submodule K W}

theorem section_trichotomy (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hι : IsProjGQ c ι A) (hU : U ≤ A) :
    IsPencilSection c ι U ∨ IsPairwiseNoncollinear Γ (sectionPoints c ι U) ∨
      ∃ t' : ℕ, 1 ≤ t' ∧ IsFullSubquadrangle c (sectionPoints c ι U) t' := by
  classical
  by_cases hB : (sectionLines c ι U).Nonempty
  · by_cases hgrid : ∃ L1 ∈ sectionLines c ι U, ∃ L2 ∈ sectionLines c ι U,
        L1 ≠ L2 ∧ ∀ p, ¬ (Γ.Adj L1 p ∧ Γ.Adj L2 p)
    · obtain ⟨L1, hL1, L2, hL2, _hne, hdisj⟩ := hgrid
      exact Or.inr (Or.inr
        (exists_isFullSubquadrangle_of_hasOrdinaryQuadrangle hP hT c hdeg hι
          (hasOrdinaryQuadrangle_of_two_disjoint_sectionLines hP hT hι hL1 hL2 hdisj)))
    ·
      have hmeet : ∀ L1 ∈ sectionLines c ι U, ∀ L2 ∈ sectionLines c ι U, L1 ≠ L2 →
          ∃ p, Γ.Adj L1 p ∧ Γ.Adj L2 p := by
        intro L1 h1 L2 h2 hne
        by_contra h
        exact hgrid ⟨L1, h1, L2, h2, hne, fun p hp => h ⟨p, hp⟩⟩
      obtain ⟨L0, hL0⟩ := hB
      have hL0deg : 0 < Γ.degree L0 := by
        have := hT L0
        omega
      obtain ⟨p0, hL0p0⟩ :=
        (SimpleGraph.degree_pos_iff_exists_adj (G := Γ) (v := L0)).mp hL0deg
      obtain ⟨p, hall⟩ : ∃ p, ∀ L ∈ sectionLines c ι U, Γ.Adj L p := by
        by_cases htwo : ∃ L1 ∈ sectionLines c ι U, ∃ L2 ∈ sectionLines c ι U, L1 ≠ L2
        · obtain ⟨L1, hL1, L2, hL2, hL1L2⟩ := htwo
          obtain ⟨p, hL1p, hL2p⟩ := hmeet L1 hL1 L2 hL2 hL1L2
          refine ⟨p, fun L hL => ?_⟩
          by_cases hLL1 : L = L1
          · exact hLL1 ▸ hL1p
          by_cases hLL2 : L = L2
          · exact hLL2 ▸ hL2p
          obtain ⟨pA, hLpA, hL1pA⟩ := hmeet L hL L1 hL1 hLL1
          obtain ⟨pB, hLpB, hL2pB⟩ := hmeet L hL L2 hL2 hLL2
          rcases eq_left_or_eq_right_of_three_lines hP hL1L2 hLL1
            hLpA hLpB hL1pA hL1p hL2pB hL2p with hpA | hpB
          · exact hpA ▸ hLpA
          · exact hpB ▸ hLpB
        · refine ⟨p0, fun L hL => ?_⟩
          have huniq : L = L0 := by
            by_contra hne
            exact htwo ⟨L0, hL0, L, hL, Ne.symm hne⟩
          exact huniq ▸ hL0p0
      have hp0 : c p = 0 := color_eq_zero_of_adj_of_color_eq_one hL0.1 (hall L0 hL0)
      refine Or.inl ⟨p, hp0, fun L hL1 hLU => (hall L ⟨hL1, hLU⟩).symm, ?_⟩
      intro x hx0 hxU
      by_contra hno
      have hxX : x ∈ sectionPoints c ι U := ⟨hx0, hxU⟩
      have hnotAdj : ¬ Γ.Adj x L0 := by
        intro hxL0
        exact hno ⟨L0, hL0.1, hL0.2, hxL0⟩
      have hcne : c x ≠ c L0 := by rw [hx0, hL0.1]; decide
      have hdist : Γ.dist x L0 = 3 :=
        dist_eq_three_of_not_adj_of_color_ne hP c hnotAdj hcne
      obtain ⟨u, ⟨hL0u, hxu⟩, -⟩ := existsUnique_proj hP hdist
      have huX : u ∈ sectionPoints c ι U := neighborSet_subset_of_sectionLines hι hL0 hL0u
      have hxu_ne : x ≠ u := by
        intro h
        exact hnotAdj (h ▸ hL0u).symm
      let M := commonNeighbor hP hxu
      have hxM : Γ.Adj x M := commonNeighbor_adj_left hP hxu
      have huM : Γ.Adj u M := commonNeighbor_adj_right hP hxu
      have hM : M ∈ sectionLines c ι U := by
        refine ⟨color_eq_one_of_adj_of_color_eq_zero hx0 hxM, ?_⟩
        exact line_le_of_two_sectionPoints hι hxX huX hxu_ne hxM huM
      exact hno ⟨M, hM.1, hM.2, hxM⟩
  · exact Or.inr (Or.inl
      (pairwiseNoncollinear_of_sectionLines_eq_empty hP hι
        (Set.not_nonempty_iff_eq_empty.mp hB)))

end Trichotomy

end

end CFSG.Geometry.GeneralizedQuadrangles
