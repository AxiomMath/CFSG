module

public import CFSG.Geometry.GeneralizedQuadrangles.Hermitian.Embedding.Basic

public section

namespace CFSG.Geometry.GeneralizedQuadrangles

open SimpleGraph CFSG.Geometry.GeneralizedPolygons Module

universe u

variable {V : Type u}

section PerpSpan

variable {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj] {c : Γ.Coloring (Fin 2)}
variable {K : Type*} [Field K] {W : Type*} [AddCommGroup W] [Module K W]
variable {ι : V → Submodule K W} {A : Submodule K W}

@[expose] noncomputable def perpSpan (c : Γ.Coloring (Fin 2)) (ι : V → Submodule K W)
    (p : V) : Submodule K W :=
  ⨆ x : {x : V // x ∈ ptPerp Γ c {p}}, ι x.1

theorem submodule_le_perpSpan {p x : V} (hx : x ∈ ptPerp Γ c {p}) :
    ι x ≤ perpSpan c ι p :=
  le_iSup (fun x : {x : V // x ∈ ptPerp Γ c {p}} => ι x.1) ⟨x, hx⟩

theorem perpSpan_le_ambient (hι : IsProjGQ c ι A) (p : V) : perpSpan c ι p ≤ A := by
  refine iSup_le ?_
  rintro ⟨x, -⟩
  exact hι.le_ambient x

theorem ptPerp_inter_ptPerp_of_collinear (hP : IsGeneralizedPolygon Γ 4) {p q L : V}
    (hp : c p = 0) (hq : c q = 0) (hpq : p ≠ q)
    (hpL : Γ.Adj p L) (hqL : Γ.Adj q L) :
    ptPerp Γ c {p} ∩ ptPerp Γ c {q} = Γ.neighborSet L := by
  classical
  have hL : c L = 1 := color_eq_one_of_adj_of_color_eq_zero hp hpL
  ext z
  constructor
  · intro hz
    have hz0 : c z = 0 := hz.1.1
    have hzp : Γ.dist z p ≤ 2 := hz.1.2 p rfl
    have hzq : Γ.dist z q ≤ 2 := hz.2.2 q rfl
    by_cases hzp_eq : z = p
    · rw [hzp_eq]
      exact hpL.symm
    by_cases hzq_eq : z = q
    · rw [hzq_eq]
      exact hqL.symm
    · have hzp2 : Γ.dist z p = 2 := by
        rcases dist_eq_two_or_four_of_color_zero hP hz0 hp hzp_eq with h | h
        · exact h
        · omega
      have hzq2 : Γ.dist z q = 2 := by
        rcases dist_eq_two_or_four_of_color_zero hP hz0 hq hzq_eq with h | h
        · exact h
        · omega
      by_contra hzL
      have hnot : ¬ Γ.Adj z L := fun h => hzL h.symm
      have hdist : Γ.dist z L = 3 :=
        dist_eq_three_of_not_adj_of_color_ne hP c hnot (by rw [hz0, hL]; decide)
      obtain ⟨u, ⟨hLu, hzu⟩, huniq⟩ := existsUnique_proj hP hdist
      have hup : u = p := (huniq p ⟨hpL.symm, hzp2⟩).symm
      have huq : u = q := (huniq q ⟨hqL.symm, hzq2⟩).symm
      exact hpq (hup.symm.trans huq)
  · intro hzL
    have hz0 : c z = 0 := color_eq_zero_of_adj_of_color_eq_one hL hzL
    refine ⟨⟨hz0, ?_⟩, ⟨hz0, ?_⟩⟩
    · have h1 : Γ.dist z p ≤ Γ.dist z L + Γ.dist L p := hP.connected.dist_triangle
      rw [SimpleGraph.dist_eq_one_iff_adj.mpr hzL.symm,
        SimpleGraph.dist_eq_one_iff_adj.mpr hpL.symm] at h1
      have h2 : Γ.dist z p ≤ 2 := by omega
      simpa using h2
    · have h1 : Γ.dist z q ≤ Γ.dist z L + Γ.dist L q := hP.connected.dist_triangle
      rw [SimpleGraph.dist_eq_one_iff_adj.mpr hzL.symm,
        SimpleGraph.dist_eq_one_iff_adj.mpr hqL.symm] at h1
      have h2 : Γ.dist z q ≤ 2 := by omega
      simpa using h2

@[expose] def pointsOf (V : Submodule K W) : Set (Submodule K W) :=
  {U | finrank K U = 1 ∧ U ≤ V}

@[expose] def IsTangentLine (c : Γ.Coloring (Fin 2)) (ι : V → Submodule K W) (p : V)
    (T : Submodule K W) : Prop :=
  finrank K T = 2 ∧ ι p ≤ T ∧
    ((∃ L, c L = 1 ∧ Γ.Adj p L ∧ ι L = T) ∨
      ∀ x, c x = 0 → ι x ≤ T → ι x = ι p)

theorem submodule_eq_sup_of_finrank_two {T P Q : Submodule K W}
    (hT2 : finrank K T = 2) (hP1 : finrank K P = 1) (hQ1 : finrank K Q = 1)
    (hPQ : P ≠ Q) (hP : P ≤ T) (hQ : Q ≤ T) : T = P ⊔ Q := by
  haveI : FiniteDimensional K P := Module.finite_of_finrank_pos (by omega)
  haveI : FiniteDimensional K Q := Module.finite_of_finrank_pos (by omega)
  haveI : FiniteDimensional K T := Module.finite_of_finrank_pos (by omega)
  have hbot : P ⊓ Q = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro v hv
    by_contra hv0
    have hPspan : P = K ∙ v :=
      eq_span_singleton_of_mem_of_finrank_eq_one hP1 hv.1 hv0
    have hQspan : Q = K ∙ v :=
      eq_span_singleton_of_mem_of_finrank_eq_one hQ1 hv.2 hv0
    exact hPQ (hPspan.trans hQspan.symm)
  have hsup2 : finrank K ↥(P ⊔ Q) = 2 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq P Q
    rw [hbot, finrank_bot, hP1, hQ1] at h
    omega
  have hle : P ⊔ Q ≤ T := sup_le hP hQ
  exact (Submodule.eq_of_le_of_finrank_eq hle (by rw [hsup2, hT2])).symm

theorem finrank_sup_eq_two_of_finrank_eq_one {P Q : Submodule K W}
    (hP1 : finrank K P = 1) (hQ1 : finrank K Q = 1) (hPQ : P ≠ Q) :
    finrank K ↥(P ⊔ Q) = 2 := by
  haveI : FiniteDimensional K P := Module.finite_of_finrank_pos (by omega)
  haveI : FiniteDimensional K Q := Module.finite_of_finrank_pos (by omega)
  have hbot : P ⊓ Q = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro v hv
    by_contra hv0
    have hPspan : P = K ∙ v :=
      eq_span_singleton_of_mem_of_finrank_eq_one hP1 hv.1 hv0
    have hQspan : Q = K ∙ v :=
      eq_span_singleton_of_mem_of_finrank_eq_one hQ1 hv.2 hv0
    exact hPQ (hPspan.trans hQspan.symm)
  have h := Submodule.finrank_sup_add_finrank_inf_eq P Q
  rw [hbot, finrank_bot, hP1, hQ1] at h
  omega

end PerpSpan

end CFSG.Geometry.GeneralizedQuadrangles

end
