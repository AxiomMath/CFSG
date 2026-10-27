module

public import CFSG.Geometry.GeneralizedQuadrangles.Hermitian.ThreeSpaces.Unique2

public section

namespace CFSG.Geometry.GeneralizedQuadrangles

open SimpleGraph CFSG.Geometry.GeneralizedPolygons

universe u

variable {V : Type u} {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj]
  {c : Γ.Coloring (Fin 2)} {q : ℕ}

theorem existsUnique_cone_of_dist_two (hΓ : IsThasQuadrangle Γ c q) {a b z x : V}
    (ha : c a = 0) (hab : Γ.dist a b = 4) (hz : z ∈ traceSet Γ a b) (hx : c x = 0)
    (hxT : x ∉ ptPerp Γ c {z} ∩ clSet Γ a b) (hxz : Γ.dist x z = 2) :
    ∃! E, IsThreespace Γ c q E ∧ (ptPerp Γ c {z} ∩ clSet Γ a b) ⊆ E ∧ x ∈ E := by
  classical
  have hP : IsGeneralizedPolygon Γ 4 := hΓ.gp
  have hT : IsThick Γ := hΓ.thick
  have hz0 : c z = 0 := color_eq_zero_of_dist_eq_two hP ha hz.1
  refine ⟨ptPerp Γ c {z}, ⟨Or.inl ⟨z, hz0, rfl⟩, ?_, ?_⟩, ?_⟩
  · intro w hw
    exact hw.1
  · rw [mem_ptPerp]
    refine ⟨hx, ?_⟩
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact le_of_eq hxz
  · rintro E ⟨hE, hTE, hxE⟩
    rcases hE with ⟨v, hv0, rfl⟩ | hFE
    · have hv : v ∈ ptPerp Γ c (ptPerp Γ c {z} ∩ clSet Γ a b) := by
        rw [mem_ptPerp]
        refine ⟨hv0, ?_⟩
        intro w hw
        rw [SimpleGraph.dist_comm]
        exact (mem_ptPerp.mp (hTE hw)).2 v rfl
      rw [ptPerp_conePlane_eq_singleton hP hΓ ha hab hz] at hv
      rw [Set.mem_singleton_iff] at hv
      rw [hv]
    · exfalso
      have hzT : z ∈ ptPerp Γ c {z} ∩ clSet Γ a b := by
        refine ⟨?_, ?_⟩
        · rw [mem_ptPerp]
          exact ⟨hz0, by intro y hy; rw [Set.mem_singleton_iff] at hy; subst hy; simp⟩
        · refine ⟨a, left_mem_spanSet hab, ?_⟩
          rw [SimpleGraph.dist_comm]
          exact le_of_eq (dist_eq_two_of_mem_span_of_mem_trace (z := a) (w := z) hP hT hab
            (left_mem_spanSet hab) hz)
      have hzE : z ∈ E := hTE hzT
      have hxne : x ≠ z := by
        intro h
        rw [h] at hxz
        simp at hxz
      let Span' := {v : V // v ∈ spanSet Γ a b}
      let Ft := {L : V // L ∈ fullLinesThrough Γ E z}
      have hSpancard : Nat.card Span' = q + 1 := by
        change Nat.card ↥(spanSet Γ a b) = q + 1
        rw [Nat.card_coe_set_eq]
        exact hΓ.span a b ha hab
      have hFcard : Nat.card Ft = q + 1 := by
        change Nat.card ↥(fullLinesThrough Γ E z) = q + 1
        rw [Nat.card_coe_set_eq]
        exact hFE.2.2.1 z hzE
      have hOpt : Nat.card (Option Span') = q + 2 := by
        rw [Nat.card_eq_fintype_card, Fintype.card_option]
        have hsc : Fintype.card Span' = q + 1 := by
          rw [← Nat.card_eq_fintype_card]
          exact hSpancard
        omega
      have hzv : ∀ v : Span', Γ.dist z (v : V) = 2 := fun v => by
        have hv : (v : V) ∈ spanSet Γ a b := v.2
        rw [SimpleGraph.dist_comm]
        exact dist_eq_two_of_mem_span_of_mem_trace (z := (v : V)) (w := z) hP hT hab hv hz
      have hKxzline : c (commonNeighbor hP hxz) = 1 :=
        color_eq_one_of_adj_of_color_eq_zero hx (commonNeighbor_adj_left hP hxz)
      have hKxzE : Γ.neighborSet (commonNeighbor hP hxz) ⊆ E :=
        neighborSet_subset_of_isFullSubquadrangle_of_two_mem hΓ hFE hKxzline hxE hzE hxne
          (commonNeighbor_adj_left hP hxz).symm (commonNeighbor_adj_right hP hxz).symm
      let g : Option Span' → Ft := fun o =>
        match o with
        | none => ⟨commonNeighbor hP hxz, ⟨commonNeighbor_adj_right hP hxz, hKxzE⟩⟩
        | some v =>
            ⟨commonNeighbor hP (hzv v), ⟨commonNeighbor_adj_left hP (hzv v), fun w hw => by
              have hsub : Γ.neighborSet (commonNeighbor hP (hzv v)) ⊆
                  ptPerp Γ c {z} ∩ clSet Γ a b :=
                neighborSet_coneLine_subset hP hΓ ha hab hz v.2 (hzv v)
              exact hTE (Set.mem_of_subset_of_mem (a := w) hsub hw)⟩⟩
      have hg : Function.Injective g := by
        intro o₁ o₂ hEq
        match o₁, o₂ with
        | none, none => rfl
        | none, some v =>
            exfalso
            have hK : commonNeighbor hP hxz = commonNeighbor hP (hzv v) :=
              congrArg Subtype.val hEq
            have hxK : x ∈ Γ.neighborSet (commonNeighbor hP (hzv v)) := by
              rw [← hK]
              exact (commonNeighbor_adj_left hP hxz).symm
            have hsub : Γ.neighborSet (commonNeighbor hP (hzv v)) ⊆
                ptPerp Γ c {z} ∩ clSet Γ a b :=
              neighborSet_coneLine_subset hP hΓ ha hab hz v.2 (hzv v)
            exact hxT (Set.mem_of_subset_of_mem (a := x) hsub hxK)
        | some v, none =>
            exfalso
            have hK : commonNeighbor hP (hzv v) = commonNeighbor hP hxz :=
              congrArg Subtype.val hEq
            have hxK : x ∈ Γ.neighborSet (commonNeighbor hP (hzv v)) := by
              rw [hK]
              exact (commonNeighbor_adj_left hP hxz).symm
            have hsub : Γ.neighborSet (commonNeighbor hP (hzv v)) ⊆
                ptPerp Γ c {z} ∩ clSet Γ a b :=
              neighborSet_coneLine_subset hP hΓ ha hab hz v.2 (hzv v)
            exact hxT (Set.mem_of_subset_of_mem (a := x) hsub hxK)
        | some v, some w =>
            have hK : commonNeighbor hP (hzv v) = commonNeighbor hP (hzv w) :=
              congrArg Subtype.val hEq
            have hvw : (v : V) = (w : V) := by
              by_contra hne
              exact coneLines_ne hP hΓ ha hab hz v.2 w.2 hne (hzv v) (hzv w) hK
            exact congrArg some (Subtype.ext hvw)
      have hle := Nat.card_le_card_of_injective g hg
      rw [hOpt, hFcard] at hle
      omega

theorem existsUnique_cone_of_dist_four (hΓ : IsThasQuadrangle Γ c q) {a b z x : V}
    (ha : c a = 0) (hab : Γ.dist a b = 4) (hz : z ∈ traceSet Γ a b) (hx : c x = 0)
    (hxT : x ∉ ptPerp Γ c {z} ∩ clSet Γ a b) (hxz : Γ.dist x z = 4) :
    ∃! E, IsThreespace Γ c q E ∧ (ptPerp Γ c {z} ∩ clSet Γ a b) ⊆ E ∧ x ∈ E := by
  classical
  have hP : IsGeneralizedPolygon Γ 4 := hΓ.gp
  have hT : IsThick Γ := hΓ.thick
  have hz0 : c z = 0 := color_eq_zero_of_dist_eq_two hP ha hz.1
  have hxne : x ≠ z := by
    intro h
    rw [h] at hxz
    simp at hxz
  have hspanCard : (spanSet Γ a b).ncard = q + 1 := hΓ.span a b ha hab
  have hspan2 : 1 < (spanSet Γ a b).ncard := by
    rw [hspanCard]
    have := hΓ.two_le
    omega
  obtain ⟨v₀, hv₀, v₁, hv₁, hv₀₁⟩ :=
    (Set.one_lt_ncard (s := spanSet Γ a b)).mp hspan2
  have hzv₀ : Γ.dist z v₀ = 2 := by
    rw [SimpleGraph.dist_comm]
    exact dist_eq_two_of_mem_span_of_mem_trace (z := v₀) (w := z) hP hT hab hv₀ hz
  have hzv₁ : Γ.dist z v₁ = 2 := by
    rw [SimpleGraph.dist_comm]
    exact dist_eq_two_of_mem_span_of_mem_trace (z := v₁) (w := z) hP hT hab hv₁ hz
  let L₀ := commonNeighbor hP hzv₀
  let L₁ := commonNeighbor hP hzv₁
  have hL₀line : c L₀ = 1 :=
    color_eq_one_of_adj_of_color_eq_zero hz0 (commonNeighbor_adj_left hP hzv₀)
  have hL₁line : c L₁ = 1 :=
    color_eq_one_of_adj_of_color_eq_zero hz0 (commonNeighbor_adj_left hP hzv₁)
  have hL₀z : Γ.Adj L₀ z := (commonNeighbor_adj_left hP hzv₀).symm
  have hL₁z : Γ.Adj L₁ z := (commonNeighbor_adj_left hP hzv₁).symm
  have hL₀ne : L₀ ≠ L₁ :=
    coneLines_ne hP hΓ ha hab hz hv₀ hv₁ hv₀₁ hzv₀ hzv₁
  have hnotL₀ : ¬ Γ.Adj x L₀ := by
    intro hxL
    have h2 : Γ.dist x z = 2 :=
      dist_eq_two_of_adj_of_adj_of_ne hP hxL hL₀z hxne
    omega
  have hdistL₀ : Γ.dist x L₀ = 3 :=
    dist_eq_three_of_not_adj_of_color_ne hP c hnotL₀ (by rw [hx, hL₀line]; decide)
  let p := proj hP hdistL₀
  have hpL₀ : Γ.Adj L₀ p := proj_adj hP hdistL₀
  have hxp : Γ.dist x p = 2 := proj_dist hP hdistL₀
  have hpne : p ≠ z := by
    intro hpz
    rw [hpz] at hxp
    omega
  let M := commonNeighbor hP hxp
  have hMline : c M = 1 := color_eq_one_of_adj_of_color_eq_zero hx (commonNeighbor_adj_left hP hxp)
  have hMx : Γ.Adj x M := commonNeighbor_adj_left hP hxp
  have hMp : Γ.Adj p M := commonNeighbor_adj_right hP hxp
  have hL₁Mne : L₁ ≠ M := by
    intro hEq
    have h2 : Γ.dist x z = 2 := by
      refine dist_eq_two_of_adj_of_adj_of_ne hP hMx ?_ hxne
      exact hEq ▸ hL₁z
    omega
  have hL₁M4 : Γ.dist L₁ M = 4 := by
    have heven : Even (Γ.dist L₁ M) :=
      (hP.eq_iff_even_dist c L₁ M).1 (by rw [hL₁line, hMline])
    have hle := hP.dist_le (by norm_num) L₁ M
    have hne0 : Γ.dist L₁ M ≠ 0 := by
      intro h0
      exact hL₁Mne ((hP.connected.dist_eq_zero_iff).mp h0)
    have hne2 : Γ.dist L₁ M ≠ 2 := by
      intro h2
      obtain ⟨r, hr, -⟩ := existsUnique_commonNeighbor hP h2
      have hcases := eq_left_or_eq_right_of_three_lines hP
        (M := L₀) (A := L₁) (B := M) (pA := z) (pB := p) (u := r)
        hL₁Mne hL₀ne hL₀z hpL₀ hL₁z hr.1 hMp.symm hr.2
      rcases hcases with hzr | hpr
      · have hzM : Γ.Adj z M := by rw [hzr]; exact hr.2.symm
        have h2' : Γ.dist z x = 2 :=
          dist_eq_two_of_adj_of_adj_of_ne hP hzM hMx.symm (Ne.symm hxne)
        rw [SimpleGraph.dist_comm] at h2'
        omega
      · have hpL₁ : Γ.Adj L₁ p := by rw [hpr]; exact hr.1
        exact hL₀ne (eq_of_two_common_points hP hpne hpL₀ hL₀z hpL₁ hL₁z)
    obtain ⟨k, hk⟩ := heven
    omega
  obtain ⟨S, ⟨hFS, hL₁S, hMS⟩, hSuniq⟩ := existsUnique_fullSubquadrangle hΓ hL₁line hL₁M4
  have hxS : x ∈ S := hMS hMx.symm
  have hpS : p ∈ S := hMS hMp.symm
  have hzS : z ∈ S := hL₁S hL₁z
  have hL₀full : Γ.neighborSet L₀ ⊆ S :=
    neighborSet_subset_of_isFullSubquadrangle_of_two_mem hΓ hFS hL₀line hpS hzS hpne
      hpL₀ hL₀z
  have hv₀S : v₀ ∈ S := hL₀full (commonNeighbor_adj_right hP hzv₀).symm
  have hv₁S : v₁ ∈ S := hL₁S (commonNeighbor_adj_right hP hzv₁).symm
  have hspanEq : spanSet Γ v₀ v₁ = spanSet Γ a b :=
    (span_eq_of_mem hP hT hab hv₀ hv₁ hv₀₁).2.1
  have hdist₀₁ : Γ.dist v₀ v₁ = 4 :=
    (span_eq_of_mem hP hT hab hv₀ hv₁ hv₀₁).1
  have hspanSub : spanSet Γ v₀ v₁ ⊆ S :=
    spanSet_subset_of_isFullSubquadrangle hΓ hFS hv₀S hv₁S hdist₀₁
  have hTS : ptPerp Γ c {z} ∩ clSet Γ a b ⊆ S := by
    intro w hw
    obtain ⟨v, hv, hzv, hwK⟩ := conePlane_subset_iUnion hP hΓ ha hab hz hw
    have hvS : v ∈ S := hspanSub (hspanEq.symm ▸ hv)
    have hzneq : z ≠ v := by
      intro h
      have hzv' : v ∈ traceSet Γ a b := h ▸ hz
      exact not_mem_spanSet_of_mem_traceSet hP hT hab hzv' hv
    have hKline : c (commonNeighbor hP hzv) = 1 :=
      color_eq_one_of_adj_of_color_eq_zero hz0 (commonNeighbor_adj_left hP hzv)
    have hKfull : Γ.neighborSet (commonNeighbor hP hzv) ⊆ S :=
      neighborSet_subset_of_isFullSubquadrangle_of_two_mem hΓ hFS hKline hzS hvS hzneq
        (commonNeighbor_adj_left hP hzv).symm (commonNeighbor_adj_right hP hzv).symm
    exact Set.mem_of_subset_of_mem (a := w) hKfull hwK
  refine ⟨S, ⟨Or.inr hFS, hTS, hxS⟩, ?_⟩
  rintro E ⟨hE, hTE, hxE⟩
  rcases hE with ⟨v, hv0, rfl⟩ | hFE
  · exfalso
    have hv : v ∈ ptPerp Γ c (ptPerp Γ c {z} ∩ clSet Γ a b) := by
      rw [mem_ptPerp]
      refine ⟨hv0, ?_⟩
      intro w hw
      rw [SimpleGraph.dist_comm]
      exact (mem_ptPerp.mp (hTE hw)).2 v rfl
    rw [ptPerp_conePlane_eq_singleton hP hΓ ha hab hz] at hv
    rw [Set.mem_singleton_iff] at hv
    have : Γ.dist x z ≤ 2 := by
      rw [hv] at hxE
      exact (mem_ptPerp.mp hxE).2 z rfl
    omega
  · have hL₁E : Γ.neighborSet L₁ ⊆ E := by
      have hsub : Γ.neighborSet L₁ ⊆ ptPerp Γ c {z} ∩ clSet Γ a b :=
        neighborSet_coneLine_subset hP hΓ ha hab hz hv₁ hzv₁
      intro w hw
      exact hTE (Set.mem_of_subset_of_mem (a := w) hsub hw)
    have hpE : p ∈ E := by
      have hsub : Γ.neighborSet L₀ ⊆ ptPerp Γ c {z} ∩ clSet Γ a b :=
        neighborSet_coneLine_subset hP hΓ ha hab hz hv₀ hzv₀
      exact hTE (Set.mem_of_subset_of_mem (a := p) hsub hpL₀)
    have hME : Γ.neighborSet M ⊆ E :=
      neighborSet_subset_of_isFullSubquadrangle_of_two_mem hΓ hFE hMline hxE hpE
        (by intro h; rw [h] at hxp; simp at hxp) hMx.symm hMp.symm
    exact hSuniq E ⟨hFE, hL₁E, hME⟩

theorem existsUnique_threespace (hΓ : IsThasQuadrangle Γ c q) {T : Set V}
    (hT : IsTracePlane Γ c T ∨ IsConePlane Γ c T) {x : V} (hx : c x = 0) (hxT : x ∉ T) :
    ∃! E, IsThreespace Γ c q E ∧ T ⊆ E ∧ x ∈ E := by
  have hP : IsGeneralizedPolygon Γ 4 := hΓ.gp
  rcases hT with ⟨y, z, hy, hyz, rfl⟩ | ⟨a, b, z, ha, hab, hz, rfl⟩
  · by_cases hxcl : x ∈ clSet Γ y z
    · exact existsUnique_trace_of_mem_cl hΓ hy hyz hx hxT hxcl
    · exact existsUnique_trace_of_not_mem_cl hΓ hy hyz hx hxT hxcl
  · have hz0 : c z = 0 := color_eq_zero_of_dist_eq_two hP ha hz.1
    have hzT : z ∈ ptPerp Γ c {z} ∩ clSet Γ a b := by
      refine ⟨?_, ?_⟩
      · rw [mem_ptPerp]
        exact ⟨hz0, by intro y hy; rw [Set.mem_singleton_iff] at hy; subst hy; simp⟩
      · refine ⟨a, left_mem_spanSet hab, ?_⟩
        rw [SimpleGraph.dist_comm]
        exact le_of_eq (dist_eq_two_of_mem_span_of_mem_trace (z := a) (w := z) hP
          hΓ.thick hab (left_mem_spanSet hab) hz)
    have hxne : x ≠ z := by
      intro h
      exact hxT (h.symm ▸ hzT)
    rcases dist_eq_two_or_four_of_color_zero hP hx hz0 hxne with h2 | h4
    · exact existsUnique_cone_of_dist_two hΓ ha hab hz hx hxT h2
    · exact existsUnique_cone_of_dist_four hΓ ha hab hz hx hxT h4

end CFSG.Geometry.GeneralizedQuadrangles
