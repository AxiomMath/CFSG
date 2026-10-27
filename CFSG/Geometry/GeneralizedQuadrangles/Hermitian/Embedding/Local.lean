module

public import CFSG.Geometry.GeneralizedQuadrangles.Hermitian.Embedding.PerpSpan

public section

namespace CFSG.Geometry.GeneralizedQuadrangles

open SimpleGraph CFSG.Geometry.GeneralizedPolygons Module

universe u

variable {V : Type u}

variable {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj] {c : Γ.Coloring (Fin 2)}
variable {K : Type*} [Field K] {W : Type*} [AddCommGroup W] [Module K W]
variable {ι : V → Submodule K W} {A : Submodule K W}

theorem exists_finrank_eq_one_le_inf {X Y Z : Submodule K W} [FiniteDimensional K Z]
    (hXZ : X ≤ Z) (hYZ : Y ≤ Z) (h : finrank K Z < finrank K X + finrank K Y) :
    ∃ P : Submodule K W, finrank K P = 1 ∧ P ≤ X ⊓ Y := by
  haveI : FiniteDimensional K X := Submodule.finiteDimensional_of_le hXZ
  haveI : FiniteDimensional K Y := Submodule.finiteDimensional_of_le hYZ
  have hsup : finrank K ↥(X ⊔ Y) ≤ finrank K Z := Submodule.finrank_mono (sup_le hXZ hYZ)
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq X Y
  have hpos : 0 < finrank K ↥(X ⊓ Y) := by omega
  have hne : X ⊓ Y ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hpos
    omega
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  exact ⟨K ∙ v, finrank_span_singleton hv0,
    (Submodule.span_singleton_le_iff_mem v (X ⊓ Y)).mpr hv⟩

theorem finrank_sup_line_eq_succ (hι : IsProjGQ c ι A) [FiniteDimensional K A] {p L : V}
    (hp : c p = 0) {U : Submodule K W} (hpU : ι p ≤ U) (hpL : Γ.Adj p L)
    (hLU : ¬ ι L ≤ U) (hU : U ≤ A) :
    finrank K ↥(U ⊔ ι L) = finrank K U + 1 := by
  have hL1 : c L = 1 := color_eq_one_of_adj_of_color_eq_zero hp hpL
  have hp1 : finrank K (ι p) = 1 := hι.finrank_point p hp
  have hL2 : finrank K (ι L) = 2 := hι.finrank_line L hL1
  have hpLle : ι p ≤ ι L := (hι.adj_iff p L hp hL1).1 hpL
  haveI : FiniteDimensional K U := Submodule.finiteDimensional_of_le hU
  haveI : FiniteDimensional K (ι L) := Submodule.finiteDimensional_of_le (hι.le_ambient L)
  have hpU' : ι p ≤ U ⊓ ι L := le_inf hpU hpLle
  have hne : U ⊓ ι L ≠ ι L := fun h => hLU (h ▸ inf_le_left)
  have hlt : U ⊓ ι L < ι L := lt_of_le_of_ne inf_le_right hne
  have hrank_lt : finrank K ↥(U ⊓ ι L) < finrank K (ι L) :=
    Submodule.finrank_lt_finrank_of_lt hlt
  have hrank_ge : finrank K (ι p) ≤ finrank K ↥(U ⊓ ι L) := Submodule.finrank_mono hpU'
  have hinf1 : finrank K ↥(U ⊓ ι L) = 1 := by omega
  have hinf : ι p = U ⊓ ι L :=
    Submodule.eq_of_le_of_finrank_eq hpU' (by rw [hp1, hinf1])
  have h := Submodule.finrank_sup_add_finrank_inf_eq U (ι L)
  rw [hinf.symm, hp1, hL2] at h
  omega

theorem exists_adj_le_of_line_inf_ne_bot (hι : IsProjGQ c ι A) {M : V} (hM : c M = 1)
    {X : Submodule K W} (h : ι M ⊓ X ≠ ⊥) : ∃ x, Γ.Adj M x ∧ ι x ≤ X := by
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  have hP1 : finrank K (K ∙ v) = 1 := finrank_span_singleton hv0
  have hPle : K ∙ v ≤ ι M := (Submodule.span_singleton_le_iff_mem v (ι M)).mpr hv.1
  obtain ⟨x, hMx, hx⟩ := hι.full M hM (K ∙ v) hP1 hPle
  refine ⟨x, hMx, ?_⟩
  rw [hx]
  exact (Submodule.span_singleton_le_iff_mem v X).mpr hv.2

theorem mem_ptPerp_of_adj_of_adj {p x L : V} (hx : c x = 0) (hpL : Γ.Adj p L)
    (hxL : Γ.Adj x L) : x ∈ ptPerp Γ c {p} := by
  refine ⟨hx, ?_⟩
  intro a ha
  rw [Set.mem_singleton_iff] at ha
  rw [ha]
  let w : Γ.Walk x p := .cons hxL (.cons hpL.symm .nil)
  have hw : w.length = 2 := by simp [w]
  have := SimpleGraph.dist_le w
  omega

theorem eq_of_mem_ptPerp_of_adj_line (hP : IsGeneralizedPolygon Γ 4) {p M x y : V}
    (hp : c p = 0) (hpM : ¬ Γ.Adj p M) (hxM : Γ.Adj M x) (hyM : Γ.Adj M y)
    (hx : x ∈ ptPerp Γ c {p}) (hy : y ∈ ptPerp Γ c {p}) : x = y := by
  have hM1 : c M = 1 := color_eq_one_of_adj_of_color_eq_zero hx.1 hxM.symm
  obtain ⟨u, hu, huniq⟩ := existsUnique_proj_of_not_adj hP hp hM1 hpM
  have hxu : x = u := by
    refine huniq x ⟨hxM, ?_⟩
    have hxp : x ≠ p := by
      rintro rfl
      exact hpM hxM.symm
    rw [SimpleGraph.dist_comm]
    exact dist_eq_two_of_le_two_of_ne hP hx.1 hp hxp (hx.2 p rfl)
  have hyu : y = u := by
    refine huniq y ⟨hyM, ?_⟩
    have hyp : y ≠ p := by
      rintro rfl
      exact hpM hyM.symm
    rw [SimpleGraph.dist_comm]
    exact dist_eq_two_of_le_two_of_ne hP hy.1 hp hyp (hy.2 p rfl)
  rw [hxu, hyu]

@[expose] def IsLocalAt (c : Γ.Coloring (Fin 2)) (ι : V → Submodule K W) (p : V)
    (U : Submodule K W) : Prop :=
  ι p ≤ U ∧ sectionPoints c ι U ⊆ ptPerp Γ c {p}

theorem isLocalAt_self (hι : IsProjGQ c ι A) {p : V} (hp : c p = 0) :
    IsLocalAt c ι p (ι p) := by
  refine ⟨le_rfl, ?_⟩
  intro x hx
  have hx1 : finrank K (ι x) = 1 := hι.finrank_point x hx.1
  have hp1 : finrank K (ι p) = 1 := hι.finrank_point p hp
  haveI : FiniteDimensional K (ι p) := Module.finite_of_finrank_pos (by omega)
  have hxeq : ι x = ι p :=
    Submodule.eq_of_le_of_finrank_eq hx.2 (by rw [hx1, hp1])
  have hxp : x = p := hι.injective hxeq
  subst hxp
  exact ⟨hp, by simp⟩

namespace IsLocalAt

theorem sup_line (hP : IsGeneralizedPolygon Γ 4) (hι : IsProjGQ c ι A) [FiniteDimensional K A]
    {p : V} (hp : c p = 0) {U : Submodule K W} (hU : U ≤ A) (hUloc : IsLocalAt c ι p U)
    {L : V} (hpL : Γ.Adj p L) : IsLocalAt c ι p (U ⊔ ι L) := by
  classical
  have hL1 : c L = 1 := color_eq_one_of_adj_of_color_eq_zero hp hpL
  have hpLle : ι p ≤ ι L := (hι.adj_iff p L hp hL1).1 hpL
  have hUA : U ⊔ ι L ≤ A := sup_le hU (hι.le_ambient L)
  haveI : FiniteDimensional K ↥(U ⊔ ι L) := Submodule.finiteDimensional_of_le hUA
  haveI : FiniteDimensional K U := Submodule.finiteDimensional_of_le hU
  haveI : FiniteDimensional K (ι L) := Submodule.finiteDimensional_of_le (hι.le_ambient L)
  refine ⟨hUloc.1.trans le_sup_left, ?_⟩
  intro z hz
  by_cases hLU : ι L ≤ U
  · have hsup : U ⊔ ι L = U := sup_eq_left.mpr hLU
    exact hUloc.2 (hsup ▸ hz)
  · have hdim : finrank K ↥(U ⊔ ι L) = finrank K U + 1 :=
      finrank_sup_line_eq_succ hι hp hUloc.1 hpL hLU hU
    by_contra hznot
    have hdist : ¬ Γ.dist z p ≤ 2 := by
      intro hle
      exact hznot ⟨hz.1, by
        intro a ha
        rw [Set.mem_singleton_iff] at ha
        subst ha
        exact hle⟩
    have hzp : z ≠ p := by
      rintro rfl
      exact hdist (by simp)
    have hnotzL : ¬ Γ.Adj z L := fun hzL =>
      hdist ((mem_ptPerp_of_adj_of_adj hz.1 hpL hzL).2 p rfl)
    obtain ⟨y, ⟨hLy, hzy⟩, -⟩ := existsUnique_proj_of_not_adj hP hz.1 hL1 hnotzL
    have hy0 : c y = 0 := color_eq_zero_of_dist_eq_two hP hz.1 hzy
    have hyp : y ≠ p := by
      intro h
      rw [h] at hzy
      exact hdist hzy.le
    have hzyne : z ≠ y := by
      rintro rfl
      simp at hzy
    let M := commonNeighbor hP hzy
    have hzM : Γ.Adj z M := commonNeighbor_adj_left hP hzy
    have hyM : Γ.Adj y M := commonNeighbor_adj_right hP hzy
    have hM1 : c M = 1 := color_eq_one_of_adj_of_color_eq_zero hz.1 hzM
    have hM2 : finrank K (ι M) = 2 := hι.finrank_line M hM1
    have hMeq : ι M = ι z ⊔ ι y :=
      line_eq_sup_of_two_adjacent_points hι hz.1 hy0 hzyne hzM hyM
    have hMle : ι M ≤ U ⊔ ι L := by
      rw [hMeq]
      exact sup_le hz.2 (((hι.adj_iff y L hy0 hL1).1 hLy.symm).trans le_sup_right)
    have hpM : ¬ Γ.Adj p M := by
      intro hpM'
      have hML : M = L := eq_of_two_common_points hP (Ne.symm hyp) hpM'.symm hyM.symm hpL.symm hLy
      exact hnotzL (hML ▸ hzM)
    have hlt : finrank K ↥(U ⊔ ι L) < finrank K (ι M) + finrank K U := by
      rw [hdim, hM2]
      omega
    obtain ⟨P, hP1, hPle⟩ :=
      exists_finrank_eq_one_le_inf (X := ι M) (Y := U) (Z := U ⊔ ι L) hMle le_sup_left hlt
    have hPne : P ≠ ⊥ := by
      intro hPbot
      rw [hPbot, finrank_bot] at hP1
      omega
    have hinfne : ι M ⊓ U ≠ ⊥ := by
      intro hbot
      exact hPne (le_antisymm (hbot ▸ hPle) bot_le)
    obtain ⟨x, hMx, hxU⟩ := exists_adj_le_of_line_inf_ne_bot hι hM1 hinfne
    have hx0 : c x = 0 := color_eq_zero_of_adj_of_color_eq_one hM1 hMx
    have hxloc : x ∈ ptPerp Γ c {p} := hUloc.2 ⟨hx0, hxU⟩
    have hxp : x ≠ p := by
      intro h
      exact hpM (h ▸ hMx.symm)
    have hxp2 : Γ.dist x p = 2 :=
      dist_eq_two_of_le_two_of_ne hP hx0 hp hxp (hxloc.2 p rfl)
    have hxy : x = y := by
      by_contra hne
      have hxy2 : Γ.dist x y = 2 :=
        dist_eq_two_of_adj_of_adj_of_ne hP hMx.symm hyM.symm hne
      have hyp2 : Γ.dist y p = 2 :=
        dist_eq_two_of_adj_of_adj_of_ne hP hLy.symm hpL.symm hyp
      obtain ⟨w, ⟨hxw, hyw, hpw⟩, -⟩ :=
        existsUnique_commonNeighbor_of_pairwise_dist_two hP hxy2 hxp2 hyp2
      have hwM : w = M :=
        (existsUnique_commonNeighbor hP hxy2).unique ⟨hxw, hyw⟩ ⟨hMx.symm, hyM⟩
      exact hpM (hwM ▸ hpw)
    have hyU : ι y ≤ U := hxy ▸ hxU
    have hLle : ι L ≤ U := by
      rw [line_eq_sup_of_two_adjacent_points hι hp hy0 (Ne.symm hyp) hpL hLy.symm]
      exact sup_le hUloc.1 hyU
    exact hLU hLle

end IsLocalAt

theorem perpSpan_eq_iSup_neighborFinset (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (hι : IsProjGQ c ι A) {p : V} (hp : c p = 0) :
    perpSpan c ι p = ⨆ L ∈ Γ.neighborFinset p, ι L := by
  classical
  refine le_antisymm ?_ ?_
  · refine iSup_le ?_
    rintro ⟨x, hx⟩
    by_cases hxp : x = p
    · have hpdeg : 0 < Γ.degree p := by
        have := hT p
        omega
      obtain ⟨L, hpL⟩ := (SimpleGraph.degree_pos_iff_exists_adj (G := Γ) (v := p)).mp hpdeg
      have hL1 : c L = 1 := color_eq_one_of_adj_of_color_eq_zero hp hpL
      have hxle : ι x ≤ ι L := by
        rw [hxp]
        exact (hι.adj_iff p L hp hL1).1 hpL
      exact hxle.trans (le_iSup_of_le L (le_iSup_of_le (by simpa using hpL) le_rfl))
    · have hpxle : Γ.dist p x ≤ 2 := by
        rw [SimpleGraph.dist_comm]
        exact hx.2 p rfl
      have hxp2 : Γ.dist p x = 2 :=
        dist_eq_two_of_le_two_of_ne hP hp hx.1 (Ne.symm hxp) hpxle
      let L := commonNeighbor hP hxp2
      have hpL : Γ.Adj p L := commonNeighbor_adj_left hP hxp2
      have hxL : Γ.Adj x L := commonNeighbor_adj_right hP hxp2
      have hL1 : c L = 1 := color_eq_one_of_adj_of_color_eq_zero hp hpL
      exact (hι.adj_iff x L hx.1 hL1).1 hxL |>.trans
        (le_iSup_of_le L (le_iSup_of_le (by simpa using hpL) le_rfl))
  · refine iSup_le fun L => iSup_le fun hL => ?_
    rw [mem_neighborFinset] at hL
    have hL1 : c L = 1 := color_eq_one_of_adj_of_color_eq_zero hp hL
    refine le_of_neighborSet_subset_sectionPoints hι hL1 fun x hx => ?_
    have hx0 : c x = 0 := color_eq_zero_of_adj_of_color_eq_one hL1 hx
    refine ⟨hx0, submodule_le_perpSpan ⟨hx0, ?_⟩⟩
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    rw [ha]
    let w : Γ.Walk x p := .cons hx.symm (.cons hL.symm .nil)
    have hw : w.length = 2 := by simp [w]
    have := SimpleGraph.dist_le w
    omega

theorem IsLocalAt.sup_perpSpan (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (hι : IsProjGQ c ι A) [FiniteDimensional K A] {p : V} (hp : c p = 0)
    {U : Submodule K W} (hU : U ≤ A) (hUloc : IsLocalAt c ι p U) :
    IsLocalAt c ι p (U ⊔ perpSpan c ι p) := by
  classical
  have hmain : ∀ S : Finset V, (∀ L ∈ S, Γ.Adj p L) →
      IsLocalAt c ι p (U ⊔ ⨆ L ∈ S, ι L) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro _
      simpa using hUloc
    | insert a s ha ih =>
      intro hS
      have has : Γ.Adj p a := hS a (Finset.mem_insert_self a s)
      have hs : ∀ L ∈ s, Γ.Adj p L := fun L hL => hS L (Finset.mem_insert_of_mem hL)
      have hloc := ih hs
      rw [Finset.iSup_insert]
      have hsup : U ⊔ (ι a ⊔ ⨆ L ∈ s, ι L) = (U ⊔ ⨆ L ∈ s, ι L) ⊔ ι a := by
        rw [sup_comm (ι a), sup_assoc]
      rw [hsup]
      refine IsLocalAt.sup_line hP hι hp ?_ hloc has
      exact sup_le hU (iSup_le fun L => iSup_le fun _ => hι.le_ambient L)
  have hall := hmain (Γ.neighborFinset p) fun L hL => by simpa using hL
  rw [perpSpan_eq_iSup_neighborFinset hP hT hι hp]
  exact hall

theorem sectionPoints_perpSpan (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (hι : IsProjGQ c ι A) [FiniteDimensional K A] {p : V} (hp : c p = 0) :
    sectionPoints c ι (perpSpan c ι p) = ptPerp Γ c {p} := by
  have hpp : ι p ≤ perpSpan c ι p := submodule_le_perpSpan ⟨hp, by simp⟩
  have hloc : IsLocalAt c ι p (perpSpan c ι p) := by
    have h := IsLocalAt.sup_perpSpan hP hT hι hp (hι.le_ambient p) (isLocalAt_self hι hp)
    rwa [sup_eq_right.mpr hpp] at h
  refine Set.Subset.antisymm hloc.2 ?_
  intro x hx
  exact ⟨hx.1, submodule_le_perpSpan hx⟩

theorem dist_eq_two_of_le_perpSpan (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (hι : IsProjGQ c ι A) [FiniteDimensional K A] {p q : V} (hp : c p = 0) (hq : c q = 0)
    (hle : ι q ≤ perpSpan c ι p) (hqp : q ≠ p) : Γ.dist p q = 2 := by
  have hmem : q ∈ ptPerp Γ c {p} := by
    rw [← sectionPoints_perpSpan hP hT hι hp]
    exact ⟨hq, hle⟩
  rw [SimpleGraph.dist_comm]
  exact dist_eq_two_of_le_two_of_ne hP hq hp hqp (hmem.2 p rfl)

theorem tangentLine_of_le_perpSpan (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (hι : IsProjGQ c ι A) [FiniteDimensional K A] {p : V} (hp : c p = 0)
    {T : Submodule K W} (hT2 : finrank K T = 2) (hpT : ι p ≤ T)
    (hTV : T ≤ perpSpan c ι p) : IsTangentLine c ι p T := by
  classical
  refine ⟨hT2, hpT, ?_⟩
  by_cases hline : ∃ L, c L = 1 ∧ Γ.Adj p L ∧ ι L = T
  · exact Or.inl hline
  · refine Or.inr ?_
    intro x hx hxT
    by_cases hxp : x = p
    · subst hxp
      rfl
    · have hTeq : T = ι p ⊔ ι x :=
        submodule_eq_sup_of_finrank_two hT2 (hι.finrank_point p hp)
          (hι.finrank_point x hx) (fun h => hxp (hι.injective h).symm) hpT hxT
      have hxle : ι x ≤ perpSpan c ι p :=
        le_trans le_sup_right (hTeq ▸ hTV)
      have hdist : Γ.dist p x = 2 :=
        dist_eq_two_of_le_perpSpan hP hT hι hp hx hxle hxp
      have hxL : Γ.Adj x (commonNeighbor hP hdist) := commonNeighbor_adj_right hP hdist
      have hpL : Γ.Adj p (commonNeighbor hP hdist) := commonNeighbor_adj_left hP hdist
      have hL1 : c (commonNeighbor hP hdist) = 1 :=
        color_eq_one_of_adj_of_color_eq_zero hp hpL
      have hLeq : ι (commonNeighbor hP hdist) = T :=
        (line_eq_sup_of_two_adjacent_points hι hp hx (Ne.symm hxp) hpL hxL).trans hTeq.symm
      exact absurd ⟨commonNeighbor hP hdist, hL1, hpL, hLeq⟩ hline

end CFSG.Geometry.GeneralizedQuadrangles

end
