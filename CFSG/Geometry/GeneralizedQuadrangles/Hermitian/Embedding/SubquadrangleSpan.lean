module

public import CFSG.Geometry.GeneralizedQuadrangles.Hermitian.Embedding.PerpSpan
public import CFSG.Geometry.GeneralizedQuadrangles.Hermitian.Setting

public section

namespace CFSG.Geometry.GeneralizedQuadrangles

open SimpleGraph CFSG.Geometry.GeneralizedPolygons Module

universe u

variable {V : Type u}
variable {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj]
variable {K : Type*} [Field K] {W : Type*} [AddCommGroup W] [Module K W]
variable {ι : V → Submodule K W} {A : Submodule K W}

omit [Fintype V] [DecidableRel Γ.Adj] in
theorem isProjGQ_subquadrangle {c : Γ.Coloring (Fin 2)} (hι : IsProjGQ c ι A) {P' : Set V}
    {t' : ℕ} (hF : IsFullSubquadrangle c P' t') :
    IsProjGQ (subquadrangleColoring c P') (fun v : subquadrangleSet Γ c P' => ι v.1)
      (⨆ y : {y : V // y ∈ P'}, ι y.1) := by
  classical
  let S : Set V := subquadrangleSet Γ c P'
  let c' : (Γ.induce S).Coloring (Fin 2) := subquadrangleColoring c P'
  let B : Submodule K W := ⨆ y : {y : V // y ∈ P'}, ι y.1
  have hP0 : ∀ x ∈ P', c x = 0 := hF.1
  refine
    { injective := ?_
      finrank_point := ?_
      finrank_line := ?_
      le_ambient := ?_
      adj_iff := ?_
      full := ?_
      span := ?_ }
  · intro u v huv
    exact Subtype.ext (hι.injective huv)
  · intro x hx
    exact hι.finrank_point x.1 hx
  · intro L hL
    exact hι.finrank_line L.1 hL
  · intro v
    rcases (show v.1 ∈ P' ∨ c v.1 = 1 ∧ Γ.neighborSet v.1 ⊆ P' from v.2) with hvP | hvL
    · exact le_iSup (fun y : {y : V // y ∈ P'} => ι y.1) ⟨v.1, hvP⟩
    · intro u hu
      by_cases hu0 : u = 0
      · rw [hu0]
        exact Submodule.zero_mem B
      · let P : Submodule K W := K ∙ u
        have hP1 : finrank K P = 1 := finrank_span_singleton hu0
        have hPle : P ≤ ι v.1 :=
          (Submodule.span_singleton_le_iff_mem u (ι v.1)).mpr hu
        obtain ⟨x, hvx, hxP⟩ := hι.full v.1 hvL.1 P hP1 hPle
        have hxP' : x ∈ P' := hvL.2 hvx
        have hxle : ι x ≤ B :=
          le_iSup (fun y : {y : V // y ∈ P'} => ι y.1) ⟨x, hxP'⟩
        exact hxle (hxP ▸ Submodule.mem_span_singleton_self u)
  · intro x L hx hL
    exact hι.adj_iff x.1 L.1 hx hL
  · intro L hL U hU1 hUle
    have hL1 : c L.1 = 1 := hL
    have hLS : L.1 ∈ subquadrangleLines Γ c P' := by
      rcases (show L.1 ∈ P' ∨ c L.1 = 1 ∧ Γ.neighborSet L.1 ⊆ P' from L.2) with hLP | hLL
      · exact absurd (hL1.symm.trans (hP0 L.1 hLP)) (by decide)
      · exact hLL
    obtain ⟨x, hLx, hxU⟩ := hι.full L.1 hL1 U hU1 hUle
    have hxP' : x ∈ P' := hLS.2 hLx
    exact ⟨⟨x, (show x ∈ subquadrangleSet Γ c P' from Or.inl hxP')⟩,
      SimpleGraph.induce_adj.mpr hLx, hxU⟩
  · refine le_antisymm ?_ ?_
    · refine iSup₂_le fun x hx => ?_
      have hxP : x.1 ∈ P' := by
        rcases (show x.1 ∈ P' ∨ c x.1 = 1 ∧ Γ.neighborSet x.1 ⊆ P' from x.2) with hxP | hxL
        · exact hxP
        · exact absurd (hxL.1.symm.trans hx) (by decide)
      exact le_iSup (fun y : {y : V // y ∈ P'} => ι y.1) ⟨x.1, hxP⟩
    · refine iSup_le fun y => ?_
      exact le_iSup₂ (f := fun x (_ : c' x = 0) => ι x.1)
        ⟨y.1, (show y.1 ∈ subquadrangleSet Γ c P' from Or.inl y.2)⟩ (hP0 y.1 y.2)


omit [DecidableRel Γ.Adj] in
theorem hasConstantSecants_subquadrangle
    (hP : IsGeneralizedPolygon Γ 4) {c : Γ.Coloring (Fin 2)} (hι : IsProjGQ c ι A)
    {P' : Set V} {t' : ℕ} (hF : IsFullSubquadrangle c P' t') {ℓ : ℕ}
    (hsec : HasConstantSecants c ι A ℓ)
    (hclosed : ∀ x ∈ P', ∀ y ∈ P', Γ.dist x y = 4 →
      sectionPoints c ι (ι x ⊔ ι y) ⊆ P') :
    HasConstantSecants (subquadrangleColoring c P') (fun v : subquadrangleSet Γ c P' => ι v.1)
      (⨆ y : {y : V // y ∈ P'}, ι y.1) ℓ := by
  classical
  intro U hUB hU2 hneU hge
  let B : Submodule K W := ⨆ y : {y : V // y ∈ P'}, ι y.1
  have hP0 : ∀ x ∈ P', c x = 0 := hF.1
  have hBA : B ≤ A := by
    refine iSup_le ?_
    rintro ⟨y, -⟩
    exact hι.le_ambient y
  have hUA : U ≤ A := hUB.trans hBA
  have h1lt : 1 < (sectionPoints (subquadrangleColoring c P')
      (fun v : subquadrangleSet Γ c P' => ι v.1) U).ncard := by omega
  obtain ⟨x, hxS, y, hyS, hxy⟩ :=
    (Set.one_lt_ncard (s := sectionPoints (subquadrangleColoring c P')
      (fun v : subquadrangleSet Γ c P' => ι v.1) U)).mp h1lt
  have hx0 : c x.1 = 0 := hxS.1
  have hy0 : c y.1 = 0 := hyS.1
  have hxU : ι x.1 ≤ U := hxS.2
  have hyU : ι y.1 ≤ U := hyS.2
  have hxP : x.1 ∈ P' := by
    rcases mem_subquadrangleSet.mp x.2 with h | h
    · exact h
    · exact absurd (h.1.symm.trans hx0) (by decide)
  have hyP : y.1 ∈ P' := by
    rcases mem_subquadrangleSet.mp y.2 with h | h
    · exact h
    · exact absurd (h.1.symm.trans hy0) (by decide)
  have hxyv : x.1 ≠ y.1 := fun h => hxy (Subtype.ext h)
  have hneU' : ∀ L, c L = 1 → ι L ≠ U := by
    intro L hL hLU
    have hxL : Γ.Adj x.1 L :=
      (hι.adj_iff x.1 L hx0 hL).2 (hLU ▸ hxU)
    have hyL : Γ.Adj y.1 L :=
      (hι.adj_iff y.1 L hy0 hL).2 (hLU ▸ hyU)
    have h2L : 2 ≤ (Γ.neighborSet L ∩ P').ncard := by
      have hlt : 1 < (Γ.neighborSet L ∩ P').ncard :=
        (Set.one_lt_ncard (s := Γ.neighborSet L ∩ P')).mpr
          ⟨x.1, ⟨hxL.symm, hxP⟩, y.1, ⟨hyL.symm, hyP⟩, hxyv⟩
      omega
    have hfull : Γ.neighborSet L ⊆ P' := hF.2.1 L hL h2L
    let L' : subquadrangleSet Γ c P' := ⟨L, mem_subquadrangleSet.mpr (Or.inr ⟨hL, hfull⟩)⟩
    have hL' : subquadrangleColoring c P' L' = 1 := hL
    have hLU' : (fun v : subquadrangleSet Γ c P' => ι v.1) L' = U := hLU
    exact hneU L' hL' hLU'
  have hUsup : U = ι x.1 ⊔ ι y.1 :=
    submodule_eq_sup_of_finrank_two hU2 (hι.finrank_point x.1 hx0)
      (hι.finrank_point y.1 hy0)
      (fun h => hxyv (hι.injective h)) hxU hyU
  have hdist4 : Γ.dist x.1 y.1 = 4 := by
    rcases dist_eq_two_or_four_of_color_zero hP hx0 hy0 hxyv with h2 | h4
    · exfalso
      have hxL : Γ.Adj x.1 (commonNeighbor hP h2) := commonNeighbor_adj_left hP h2
      have hyL : Γ.Adj y.1 (commonNeighbor hP h2) := commonNeighbor_adj_right hP h2
      exact hneU' _ (color_eq_one_of_adj_of_color_eq_zero hx0 hxL)
        ((line_eq_sup_of_two_adjacent_points hι hx0 hy0 hxyv hxL hyL).trans hUsup.symm)
    · exact h4
  have hsub : sectionPoints c ι U ⊆ P' := by
    rw [hUsup]
    exact hclosed x.1 hxP y.1 hyP hdist4
  have hncard : (sectionPoints (subquadrangleColoring c P')
      (fun v : subquadrangleSet Γ c P' => ι v.1) U).ncard =
      (sectionPoints c ι U).ncard := by
    refine Set.ncard_congr (fun v (_ : v ∈ sectionPoints (subquadrangleColoring c P')
      (fun v : subquadrangleSet Γ c P' => ι v.1) U) => v.1) ?_ ?_ ?_
    · rintro v hv
      exact ⟨hv.1, hv.2⟩
    · rintro v _ w _ hvw
      exact Subtype.ext hvw
    · intro z hz
      have hzP : z ∈ P' := hsub hz
      refine ⟨⟨z, mem_subquadrangleSet.mpr (Or.inl hzP)⟩, ⟨?_, hz.2⟩, rfl⟩
      exact hz.1
  have hge' : 2 ≤ (sectionPoints c ι U).ncard := by
    rwa [hncard] at hge
  rw [hncard]
  exact hsec U hUA hU2 hneU' hge'

end CFSG.Geometry.GeneralizedQuadrangles
