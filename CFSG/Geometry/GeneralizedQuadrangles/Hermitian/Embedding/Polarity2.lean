module

public import CFSG.Geometry.GeneralizedQuadrangles.Hermitian.Embedding.Polarity
public import CFSG.LocalAnalysis.ComponentInitial.ProjectiveGeometryLattice

public section

namespace CFSG.Geometry.GeneralizedQuadrangles

open SimpleGraph CFSG.Geometry.GeneralizedPolygons Module

universe u

variable {V : Type u}

section Main

variable {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj]

open CFSG.LocalAnalysis.ComponentInitial

theorem buekenhout_lefevre (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    {ℓ : ℕ} {K : Type*} [Field K] [Fintype K]
    (ι : V → Submodule K (Fin 5 → K)) (hι : IsProjGQ c ι ⊤)
    (hsec : HasConstantSecants c ι ⊤ ℓ) (hℓ : 2 ≤ ℓ) :
    ∃ π : ProjectiveGeometry.Point 5 K → ProjectiveGeometry.Hyperplane 5 K,
      (∀ x y : ProjectiveGeometry.Point 5 K,
        (x : Submodule K (Fin 5 → K)) ≤ π y ↔ (y : Submodule K (Fin 5 → K)) ≤ π x) ∧
      (∀ x : ProjectiveGeometry.Point 5 K,
        ((x : Submodule K (Fin 5 → K)) ≤ π x ↔ ∃ v, c v = 0 ∧ ι v = x)) ∧
      ∀ U : Submodule K (Fin 5 → K), finrank K U = 2 →
        ((∀ x : ProjectiveGeometry.Point 5 K, (x : Submodule K (Fin 5 → K)) ≤ U → U ≤ π x) ↔
          ∃ L, c L = 1 ∧ ι L = U) := by
  classical
  have h5 : finrank K (Fin 5 → K) = 5 := Module.finrank_fin_fun K
  have htop : finrank K (⊤ : Submodule K (Fin 5 → K)) = 5 := by rw [finrank_top, h5]
  let π : ProjectiveGeometry.Point 5 K → ProjectiveGeometry.Hyperplane 5 K := fun x =>
    ⟨polar c ι x.1, by
      have h := finrank_polar_add_one hP hT c hdeg hι hsec hℓ htop x.2 le_top
      rw [finrank_top, h5] at h
      show finrank K (polar c ι x.1) = 5 - 1
      omega⟩
  have hπ : ∀ x y : ProjectiveGeometry.Point 5 K,
      (x : Submodule K (Fin 5 → K)) ≤ π y ↔ (y : Submodule K (Fin 5 → K)) ≤ π x := by
    intro x y
    change (x : Submodule K (Fin 5 → K)) ≤ polar c ι y.1 ↔
      (y : Submodule K (Fin 5 → K)) ≤ polar c ι x.1
    by_cases hxP : ∃ v, c v = 0 ∧ ι v = (x : Submodule K (Fin 5 → K))
    · obtain ⟨p, hp, hp_eq⟩ := hxP
      rw [← hp_eq]
      by_cases hyP : ∃ v, c v = 0 ∧ ι v = (y : Submodule K (Fin 5 → K))
      · obtain ⟨q, hq, hq_eq⟩ := hyP
        rw [← hq_eq, polar_eq_perpSpan hP hT hι hq, polar_eq_perpSpan hP hT hι hp]
        have h := le_perpSpan_iff_le_polar hP hT c hdeg hι hsec hℓ htop
          (X := ι q) (hι.finrank_point q hq) le_top hp
        rw [polar_eq_perpSpan hP hT hι hq] at h
        exact h.symm
      · rw [polar_eq_perpSpan hP hT hι hp]
        exact (le_perpSpan_iff_le_polar hP hT c hdeg hι hsec hℓ htop (X := y.1) y.2 le_top
          hp).symm
    · by_cases hyP : ∃ v, c v = 0 ∧ ι v = (y : Submodule K (Fin 5 → K))
      · obtain ⟨q, hq, hq_eq⟩ := hyP
        rw [← hq_eq, polar_eq_perpSpan hP hT hι hq]
        exact le_perpSpan_iff_le_polar hP hT c hdeg hι hsec hℓ htop (X := x.1) x.2 le_top hq
      · exact ⟨fun h => le_polar_comm hP hT c hdeg hι hsec hℓ h5 y.2 hyP x.2 hxP h,
          fun h => le_polar_comm hP hT c hdeg hι hsec hℓ h5 x.2 hxP y.2 hyP h⟩
  have habs : ∀ x : ProjectiveGeometry.Point 5 K,
      ((x : Submodule K (Fin 5 → K)) ≤ π x ↔ ∃ v, c v = 0 ∧ ι v = x) := by
    intro x
    change (x : Submodule K (Fin 5 → K)) ≤ polar c ι x.1 ↔
      ∃ v, c v = 0 ∧ ι v = (x : Submodule K (Fin 5 → K))
    exact le_polar_self_iff hP hT c hdeg hι hsec hℓ htop x.2 le_top
  have hlines : ∀ U : Submodule K (Fin 5 → K), finrank K U = 2 →
      ((∀ x : ProjectiveGeometry.Point 5 K,
          (x : Submodule K (Fin 5 → K)) ≤ U → U ≤ π x) ↔
        ∃ L, c L = 1 ∧ ι L = U) := by
    intro U hU2
    constructor
    · intro hU
      have hUne : U ≠ ⊥ := by
        intro hbot
        rw [hbot, finrank_bot] at hU2
        omega
      obtain ⟨v, hvU, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hUne
      have hv1 : finrank K (K ∙ v) = 1 := finrank_span_singleton hv0
      have hKvle : K ∙ v ≤ U := (Submodule.span_singleton_le_iff_mem v U).mpr hvU
      have hlt : K ∙ v < U := by
        refine lt_of_le_of_ne hKvle ?_
        intro heq
        have hrank := congrArg (fun M : Submodule K (Fin 5 → K) => finrank K M) heq
        rw [hv1, hU2] at hrank
        omega
      have hnotle : ¬ U ≤ K ∙ v := fun hle => (not_lt_of_ge hle) hlt
      obtain ⟨w, hwU, hwv⟩ := Set.not_subset.mp hnotle
      have hw0 : w ≠ 0 := fun h => hwv (h ▸ Submodule.zero_mem (K ∙ v))
      have hw1 : finrank K (K ∙ w) = 1 := finrank_span_singleton hw0
      let x : ProjectiveGeometry.Point 5 K := ⟨K ∙ v, hv1⟩
      let y : ProjectiveGeometry.Point 5 K := ⟨K ∙ w, hw1⟩
      have hxU : (x : Submodule K (Fin 5 → K)) ≤ U := hKvle
      have hyU : (y : Submodule K (Fin 5 → K)) ≤ U :=
        (Submodule.span_singleton_le_iff_mem w U).mpr hwU
      have hxne : x ≠ y := by
        intro hxy
        have hspan : K ∙ v = K ∙ w := congrArg Subtype.val hxy
        exact hwv (by rw [hspan]; exact Submodule.mem_span_singleton_self w)
      have hxabs : (x : Submodule K (Fin 5 → K)) ≤ π x := hxU.trans (hU x hxU)
      have hyabs : (y : Submodule K (Fin 5 → K)) ≤ π y := hyU.trans (hU y hyU)
      obtain ⟨p, hp0, hp_eq⟩ := (habs x).1 hxabs
      obtain ⟨q, hq0, hq_eq⟩ := (habs y).1 hyabs
      have hpqne : p ≠ q := by
        intro hpq
        apply hxne
        apply Subtype.ext
        rw [← hp_eq, hpq, hq_eq]
      have hqHp : ι q ≤ perpSpan c ι p := by
        have hle : (y : Submodule K (Fin 5 → K)) ≤ polar c ι (x : Submodule K (Fin 5 → K)) :=
          hyU.trans (hU x hxU)
        rw [← hq_eq, ← hp_eq, polar_eq_perpSpan hP hT hι hp0] at hle
        exact hle
      have hqperp : q ∈ ptPerp Γ c {p} := by
        rw [← sectionPoints_perpSpan hP hT hι hp0]
        exact ⟨hq0, hqHp⟩
      have hpq2 : Γ.dist p q = 2 :=
        dist_eq_two_of_le_two_of_ne hP hp0 hq0 hpqne (by
          rw [SimpleGraph.dist_comm]
          exact hqperp.2 p rfl)
      obtain ⟨L, ⟨hpL, hqL⟩, -⟩ := existsUnique_commonNeighbor hP hpq2
      have hL1 : c L = 1 := color_eq_one_of_adj_of_color_eq_zero hp0 hpL
      have hline : ι L = ι p ⊔ ι q :=
        line_eq_sup_of_two_adjacent_points hι hp0 hq0 hpqne hpL hqL
      have hKWne : (K ∙ v : Submodule K (Fin 5 → K)) ≠ K ∙ w := by
        intro h
        exact hwv (h ▸ Submodule.mem_span_singleton_self w)
      have hxy2 : finrank K (K ∙ v ⊔ K ∙ w : Submodule K (Fin 5 → K)) = 2 :=
        finrank_sup_eq_two_of_finrank_eq_one hv1 hw1 hKWne
      refine ⟨L, hL1, ?_⟩
      rw [hline, hp_eq, hq_eq]
      exact Submodule.eq_of_le_of_finrank_eq (sup_le hKvle hyU) (by rw [hxy2, hU2])
    · rintro ⟨L, hL1, hLU⟩ x hxU
      change U ≤ polar c ι x.1
      obtain ⟨p, hLp, hp_eq⟩ := hι.full L hL1 x.1 x.2 (hLU ▸ hxU)
      have hp0 : c p = 0 := color_eq_zero_of_adj_of_color_eq_one hL1 hLp
      have hle : ι L ≤ perpSpan c ι p := by
        refine le_of_neighborSet_subset_sectionPoints hι hL1 ?_
        intro q hq
        have hq0 : c q = 0 := color_eq_zero_of_adj_of_color_eq_one hL1 hq
        refine ⟨hq0, ?_⟩
        by_cases hpq : p = q
        · rw [hpq]
          exact submodule_le_perpSpan ⟨hq0, by simp⟩
        · have hpq2 : Γ.dist p q = 2 :=
            dist_eq_two_of_adj_of_adj_of_ne hP hLp.symm hq hpq
          refine submodule_le_perpSpan ⟨hq0, ?_⟩
          intro a ha
          rw [Set.mem_singleton_iff] at ha
          subst ha
          rw [SimpleGraph.dist_comm]
          exact le_of_eq hpq2
      rw [← hLU, ← hp_eq, polar_eq_perpSpan hP hT hι hp0]
      exact hle
  exact ⟨π, hπ, habs, hlines⟩

end Main

end CFSG.Geometry.GeneralizedQuadrangles

end
