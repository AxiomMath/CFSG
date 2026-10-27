module

public import CFSG.Geometry.GeneralizedQuadrangles.Hermitian.Embedding.Tangent

public section

namespace CFSG.Geometry.GeneralizedQuadrangles

open SimpleGraph CFSG.Geometry.GeneralizedPolygons Module

universe u

variable {V : Type u}

section Pencil

variable {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj] {c : Γ.Coloring (Fin 2)}
variable {K : Type*} [Field K] {W : Type*} [AddCommGroup W] [Module K W]
variable {ι : V → Submodule K W} {A : Submodule K W}

theorem sectionPoints_perpSpan_inf (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (hι : IsProjGQ c ι A) [FiniteDimensional K A] {p q L : V}
    (hp : c p = 0) (hq : c q = 0) (hpq : p ≠ q)
    (hpL : Γ.Adj p L) (hqL : Γ.Adj q L) :
    sectionPoints c ι (perpSpan c ι p ⊓ perpSpan c ι q) = Γ.neighborSet L := by
  have hL : c L = 1 := color_eq_one_of_adj_of_color_eq_zero hp hpL
  ext x
  constructor
  · intro hx
    have hx0 : c x = 0 := hx.1
    have hxp : x ∈ ptPerp Γ c {p} := by
      have hxsec : x ∈ sectionPoints c ι (perpSpan c ι p) :=
        ⟨hx0, hx.2.trans inf_le_left⟩
      rwa [sectionPoints_perpSpan hP hT hι hp] at hxsec
    have hxq : x ∈ ptPerp Γ c {q} := by
      have hxsec : x ∈ sectionPoints c ι (perpSpan c ι q) :=
        ⟨hx0, hx.2.trans inf_le_right⟩
      rwa [sectionPoints_perpSpan hP hT hι hq] at hxsec
    have hinter : x ∈ ptPerp Γ c {p} ∩ ptPerp Γ c {q} := ⟨hxp, hxq⟩
    rwa [ptPerp_inter_ptPerp_of_collinear hP hp hq hpq hpL hqL] at hinter
  · intro hx
    have hx0 : c x = 0 := color_eq_zero_of_adj_of_color_eq_one hL hx
    have hinter : x ∈ ptPerp Γ c {p} ∩ ptPerp Γ c {q} := by
      rw [ptPerp_inter_ptPerp_of_collinear hP hp hq hpq hpL hqL]
      exact hx
    exact ⟨hx0, le_inf (submodule_le_perpSpan hinter.1) (submodule_le_perpSpan hinter.2)⟩

theorem perpSpan_inf_le_perpSpan (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (hι : IsProjGQ c ι A) [FiniteDimensional K A] {p q r L : V}
    (hp : c p = 0) (hq : c q = 0) (hr : c r = 0) (hpq : p ≠ q)
    (hpL : Γ.Adj p L) (hqL : Γ.Adj q L) (hrL : Γ.Adj r L) :
    perpSpan c ι p ⊓ perpSpan c ι q ≤ perpSpan c ι r := by
  intro v hv
  have hYr : ι r ≤ perpSpan c ι p ⊓ perpSpan c ι q := by
    have hmem : r ∈ sectionPoints c ι (perpSpan c ι p ⊓ perpSpan c ι q) := by
      rw [sectionPoints_perpSpan_inf hP hT hι hp hq hpq hpL hqL]
      exact hrL.symm
    exact hmem.2
  by_cases hvr : v ∈ ι r
  · exact (submodule_le_perpSpan (p := r) (x := r) ⟨hr, by simp⟩) hvr
  · have hv0 : v ≠ 0 := fun h => hvr (h ▸ Submodule.zero_mem (ι r))
    let T : Submodule K W := ι r ⊔ K ∙ v
    have hspan1 : finrank K (K ∙ v) = 1 := finrank_span_singleton hv0
    have hspanne : K ∙ v ≠ ι r := by
      intro heq
      exact hvr (heq ▸ Submodule.mem_span_singleton_self v)
    have hT2 : finrank K T = 2 :=
      finrank_sup_eq_two_of_finrank_eq_one (hι.finrank_point r hr) hspan1 hspanne.symm
    have hTleY : T ≤ perpSpan c ι p ⊓ perpSpan c ι q :=
      sup_le hYr ((Submodule.span_singleton_le_iff_mem v _).mpr hv)
    have hTA : T ≤ A :=
      hTleY.trans (inf_le_left.trans (perpSpan_le_ambient hι p))
    have htang : IsTangentLine c ι r T := by
      refine ⟨hT2, le_sup_left, ?_⟩
      by_cases hkind : ∃ x, c x = 0 ∧ ι x ≤ T ∧ ι x ≠ ι r
      · obtain ⟨x, hx0, hxT, hxne⟩ := hkind
        have hxY : ι x ≤ perpSpan c ι p ⊓ perpSpan c ι q := hxT.trans hTleY
        have hxsec : x ∈ sectionPoints c ι (perpSpan c ι p ⊓ perpSpan c ι q) :=
          ⟨hx0, hxY⟩
        have hxneigh : x ∈ Γ.neighborSet L := by
          rw [← sectionPoints_perpSpan_inf hP hT hι hp hq hpq hpL hqL]
          exact hxsec
        have hxL : Γ.Adj x L := hxneigh.symm
        have hxr : x ≠ r := fun h => hxne (h ▸ rfl)
        have hTeq : T = ι r ⊔ ι x :=
          submodule_eq_sup_of_finrank_two hT2 (hι.finrank_point r hr)
            (hι.finrank_point x hx0) hxne.symm le_sup_left hxT
        refine Or.inl ⟨L, color_eq_one_of_adj_of_color_eq_zero hp hpL, hrL, ?_⟩
        exact (line_eq_sup_of_two_adjacent_points hι hr hx0 hxr.symm hrL hxL).trans hTeq.symm
      · refine Or.inr ?_
        intro x hx0 hxT
        by_contra hxne
        exact hkind ⟨x, hx0, hxT, hxne⟩
    exact le_perpSpan_of_isTangentLine hP hT hι hr hTA htang
      (Submodule.mem_sup_right (Submodule.mem_span_singleton_self v))

theorem perpSpan_ne_of_adj (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (hι : IsProjGQ c ι A) [FiniteDimensional K A] {p q L : V}
    (hp : c p = 0) (hq : c q = 0) (hpq : p ≠ q)
    (hpL : Γ.Adj p L) (hqL : Γ.Adj q L) :
    perpSpan c ι p ≠ perpSpan c ι q := by
  intro heq
  have hL' : 1 < (Γ.neighborSet p).ncard := by
    have h3 : 3 ≤ (Γ.neighborSet p).ncard := by
      rw [ncard_neighborSet]
      exact hT p
    omega
  obtain ⟨L', hpL', hL'ne⟩ := Set.exists_ne_of_one_lt_ncard hL' L
  have hL'c : c L' = 1 := color_eq_one_of_adj_of_color_eq_zero hp hpL'
  have hx' : 1 < (Γ.neighborSet L').ncard := by
    have h3 : 3 ≤ (Γ.neighborSet L').ncard := by
      rw [ncard_neighborSet]
      exact hT L'
    omega
  obtain ⟨x, hxL', hxp⟩ := Set.exists_ne_of_one_lt_ncard hx' p
  have hx0 : c x = 0 := color_eq_zero_of_adj_of_color_eq_one hL'c hxL'
  have hxperp : x ∈ ptPerp Γ c {p} := mem_ptPerp_of_adj_of_adj hx0 hpL' hxL'.symm
  have hxHq : ι x ≤ perpSpan c ι q := heq ▸ submodule_le_perpSpan hxperp
  have hxperpQ : x ∈ ptPerp Γ c {q} := by
    have hxsec : x ∈ sectionPoints c ι (perpSpan c ι q) := ⟨hx0, hxHq⟩
    rwa [sectionPoints_perpSpan hP hT hι hq] at hxsec
  have hxneigh : x ∈ Γ.neighborSet L := by
    have hinter : x ∈ ptPerp Γ c {p} ∩ ptPerp Γ c {q} := ⟨hxperp, hxperpQ⟩
    rwa [ptPerp_inter_ptPerp_of_collinear hP hp hq hpq hpL hqL] at hinter
  have hxL : Γ.Adj L x := hxneigh
  exact hL'ne ((eq_of_two_common_points hP hxp.symm hpL.symm hxL hpL'.symm hxL').symm)

theorem finrank_perpSpan_inf_add_two (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (hι : IsProjGQ c ι A) [FiniteDimensional K A] {p q L : V}
    (hp : c p = 0) (hq : c q = 0) (hpq : p ≠ q)
    (hpL : Γ.Adj p L) (hqL : Γ.Adj q L) :
    finrank K ↥(perpSpan c ι p ⊓ perpSpan c ι q) + 2 = finrank K A := by
  haveI : FiniteDimensional K (perpSpan c ι p) :=
    Submodule.finiteDimensional_of_le (perpSpan_le_ambient hι p)
  haveI : FiniteDimensional K (perpSpan c ι q) :=
    Submodule.finiteDimensional_of_le (perpSpan_le_ambient hι q)
  have hpne : perpSpan c ι p ≠ perpSpan c ι q :=
    perpSpan_ne_of_adj hP hT hι hp hq hpq hpL hqL
  have hnotle : ¬ perpSpan c ι q ≤ perpSpan c ι p := by
    intro hle
    have hqdim := finrank_perpSpan_add_one hP hT hι hq
    have hpdim := finrank_perpSpan_add_one hP hT hι hp
    exact hpne.symm (Submodule.eq_of_le_of_finrank_eq hle (by omega))
  have hsup : perpSpan c ι p ⊔ perpSpan c ι q = A :=
    perpSpan_sup_eq_of_not_le hP hT hι hp (perpSpan_le_ambient hι q) hnotle
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq
    (perpSpan c ι p) (perpSpan c ι q)
  rw [hsup] at hdim
  have hpdim := finrank_perpSpan_add_one hP hT hι hp
  have hqdim := finrank_perpSpan_add_one hP hT hι hq
  omega

end Pencil

end CFSG.Geometry.GeneralizedQuadrangles

end
