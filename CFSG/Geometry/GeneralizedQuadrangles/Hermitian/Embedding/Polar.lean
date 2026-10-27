module

public import CFSG.Geometry.GeneralizedQuadrangles.Hermitian.Embedding.Pencil
public import CFSG.Geometry.GeneralizedQuadrangles.Hermitian.Embedding.Elation

public section

namespace CFSG.Geometry.GeneralizedQuadrangles

open SimpleGraph CFSG.Geometry.GeneralizedPolygons Module

universe u

variable {V : Type u}

section Polar

variable {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj] {c : Γ.Coloring (Fin 2)}
variable {K : Type*} [Field K] {W : Type*} [AddCommGroup W] [Module K W]
variable {ι : V → Submodule K W} {A : Submodule K W}

@[expose] def collar (c : Γ.Coloring (Fin 2)) (ι : V → Submodule K W) (X : Submodule K W) :
    Set V :=
  {y | c y = 0 ∧ X ≤ perpSpan c ι y}

@[expose] noncomputable def polar (c : Γ.Coloring (Fin 2)) (ι : V → Submodule K W)
    (X : Submodule K W) : Submodule K W :=
  ⨆ y : {y : V // y ∈ collar c ι X}, ι y.1

theorem le_polar_of_mem_collar {X : Submodule K W} {y : V} (hy : y ∈ collar c ι X) :
    ι y ≤ polar c ι X :=
  le_iSup (fun z : {z : V // z ∈ collar c ι X} => ι z.1) ⟨y, hy⟩

theorem polar_le_ambient (hι : IsProjGQ c ι A) (X : Submodule K W) : polar c ι X ≤ A := by
  change (⨆ y : {y : V // y ∈ collar c ι X}, ι y.1) ≤ A
  refine iSup_le ?_
  rintro ⟨y, -⟩
  exact hι.le_ambient y

private theorem mem_ptPerp_singleton {z y : V} (hy : c y = 0) (h : Γ.dist y z ≤ 2) :
    y ∈ ptPerp Γ c {z} := by
  refine ⟨hy, ?_⟩
  intro a ha
  rw [Set.mem_singleton_iff] at ha
  rw [ha]
  exact h

theorem collar_eq_ptPerp (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (hι : IsProjGQ c ι A) [FiniteDimensional K A] {p : V} (hp : c p = 0) :
    collar c ι (ι p) = ptPerp Γ c {p} := by
  ext y
  constructor
  · rintro ⟨hy0, hle⟩
    have hmem : p ∈ sectionPoints c ι (perpSpan c ι y) := ⟨hp, hle⟩
    rw [sectionPoints_perpSpan hP hT hι hy0] at hmem
    exact mem_ptPerp_singleton hy0 (by rw [SimpleGraph.dist_comm]; exact hmem.2 y rfl)
  · rintro ⟨hy0, hyp⟩
    refine ⟨hy0, ?_⟩
    exact submodule_le_perpSpan (mem_ptPerp_singleton hp (by
      rw [SimpleGraph.dist_comm]
      exact hyp p rfl))

theorem polar_eq_perpSpan (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (hι : IsProjGQ c ι A) [FiniteDimensional K A] {p : V} (hp : c p = 0) :
    polar c ι (ι p) = perpSpan c ι p := by
  have h := collar_eq_ptPerp hP hT hι hp
  change (⨆ y : {y : V // y ∈ collar c ι (ι p)}, ι y.1) = perpSpan c ι p
  refine le_antisymm ?_ ?_
  · refine iSup_le fun y => ?_
    exact submodule_le_perpSpan (by rw [← h]; exact y.2)
  · refine iSup_le fun y => ?_
    exact le_polar_of_mem_collar (by rw [h]; exact y.2)

theorem finrank_sup_eq_three_of_finrank_eq_one_of_not_le {X Y : Submodule K W}
    (hX : finrank K X = 1) (hY : finrank K Y = 2) (hXY : ¬ X ≤ Y) :
    finrank K ↥(X ⊔ Y) = 3 := by
  haveI : FiniteDimensional K X := Module.finite_of_finrank_pos (by omega)
  haveI : FiniteDimensional K Y := Module.finite_of_finrank_pos (by omega)
  have hbot : X ⊓ Y = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro v hv
    by_contra hv0
    have hXv : X = K ∙ v := eq_span_singleton_of_mem_of_finrank_eq_one hX hv.1 hv0
    exact hXY (hXv ▸ (Submodule.span_singleton_le_iff_mem v Y).mpr hv.2)
  have h := Submodule.finrank_sup_add_finrank_inf_eq X Y
  rw [hbot, finrank_bot, hX, hY] at h
  omega

theorem exists_adj_mem_collar (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (hι : IsProjGQ c ι A) [FiniteDimensional K A] {X : Submodule K W}
    (hX1 : finrank K X = 1) (hXA : X ≤ A) {L : V} (hL : c L = 1) :
    ∃ y, Γ.Adj L y ∧ y ∈ collar c ι X := by
  classical
  by_cases hXP : ∃ v, c v = 0 ∧ ι v = X
  · obtain ⟨p, hp, rfl⟩ := hXP
    have hlt : 1 < (Γ.neighborSet L).ncard := by
      rw [ncard_neighborSet]
      have := hT L
      omega
    obtain ⟨y, hyL, hyp⟩ := Set.exists_ne_of_one_lt_ncard hlt p
    have hy0 : c y = 0 := color_eq_zero_of_adj_of_color_eq_one hL hyL
    by_cases hpL : Γ.Adj p L
    · refine ⟨y, hyL, ?_⟩
      rw [collar_eq_ptPerp hP hT hι hp]
      exact mem_ptPerp_singleton hy0 (by
        rw [SimpleGraph.dist_comm]
        exact le_of_eq (dist_eq_two_of_adj_of_adj_of_ne hP hpL hyL (Ne.symm hyp)))
    · obtain ⟨u, ⟨hLu, hpu⟩, -⟩ := existsUnique_proj_of_not_adj hP hp hL hpL
      have hu0 : c u = 0 := color_eq_zero_of_adj_of_color_eq_one hL hLu
      refine ⟨u, hLu, ?_⟩
      rw [collar_eq_ptPerp hP hT hι hp]
      exact mem_ptPerp_singleton hu0 (by rw [SimpleGraph.dist_comm]; exact le_of_eq hpu)
  · push Not at hXP
    have hXL : ¬ X ≤ ι L := by
      intro hle
      obtain ⟨x, hLx, hxX⟩ := hι.full L hL X hX1 hle
      exact hXP x (color_eq_zero_of_adj_of_color_eq_one hL hLx) hxX
    have hL2 : finrank K (ι L) = 2 := hι.finrank_line L hL
    have hPi3 : finrank K ↥(X ⊔ ι L) = 3 :=
      finrank_sup_eq_three_of_finrank_eq_one_of_not_le hX1 hL2 hXL
    haveI hLfin : FiniteDimensional K ↥(ι L) := Submodule.finiteDimensional_of_le (hι.le_ambient L)
    haveI hPifin : FiniteDimensional K ↥(X ⊔ ι L) :=
      Submodule.finiteDimensional_of_le (sup_le hXA (hι.le_ambient L))
    have hdegL : 0 < Γ.degree L := by
      have := hT L
      omega
    obtain ⟨y₀, hy₀L⟩ := (SimpleGraph.degree_pos_iff_exists_adj (G := Γ) (v := L)).mp hdegL
    have hy₀0 : c y₀ = 0 := color_eq_zero_of_adj_of_color_eq_one hL hy₀L
    have hy₀Lle : ι y₀ ≤ ι L := (hι.adj_iff y₀ L hy₀0 hL).1 hy₀L.symm
    have hXne : X ≠ ι y₀ := fun h => hXL (h ▸ hy₀Lle)
    have hT2 : finrank K ↥(X ⊔ ι y₀) = 2 :=
      finrank_sup_eq_two_of_finrank_eq_one hX1 (hι.finrank_point y₀ hy₀0) hXne
    have hTA : X ⊔ ι y₀ ≤ A := sup_le hXA (hι.le_ambient y₀)
    haveI hy₀fin : FiniteDimensional K ↥(ι y₀) :=
      Module.finite_of_finrank_pos (by rw [hι.finrank_point y₀ hy₀0]; norm_num)
    by_cases hcase : ∀ z, c z = 0 → ι z ≤ X ⊔ ι L → Γ.Adj L z
    ·
      have hsecond : ∀ w, c w = 0 → ι w ≤ X ⊔ ι y₀ → ι w = ι y₀ := by
        intro w hw0 hwT
        have hwPi : ι w ≤ X ⊔ ι L := hwT.trans (sup_le le_sup_left (le_trans hy₀Lle le_sup_right))
        have hwleL : ι w ≤ ι L := (hι.adj_iff w L hw0 hL).1 (hcase w hw0 hwPi).symm
        have hle₀ : ι y₀ ≤ (X ⊔ ι y₀) ⊓ ι L := le_inf le_sup_right hy₀Lle
        have hne : (X ⊔ ι y₀) ⊓ ι L ≠ ι L := by
          intro heq
          have hLle : ι L ≤ X ⊔ ι y₀ := heq ▸ inf_le_left
          haveI : FiniteDimensional K ↥(X ⊔ ι y₀) := Submodule.finiteDimensional_of_le hTA
          have hdim : finrank K (ι L) = finrank K ↥(X ⊔ ι y₀) := by rw [hL2, hT2]
          have hsup : ι L = X ⊔ ι y₀ := Submodule.eq_of_le_of_finrank_eq hLle hdim
          exact hXL (hsup.symm ▸ le_sup_left)
        haveI : FiniteDimensional K ↥((X ⊔ ι y₀) ⊓ ι L) :=
          Submodule.finiteDimensional_of_le (inf_le_right : (X ⊔ ι y₀) ⊓ ι L ≤ ι L)
        have hlt : (X ⊔ ι y₀) ⊓ ι L < ι L := lt_of_le_of_ne inf_le_right hne
        have hrank_lt := Submodule.finrank_lt_finrank_of_lt hlt
        have hge : finrank K (ι y₀) ≤ finrank K ↥((X ⊔ ι y₀) ⊓ ι L) :=
          Submodule.finrank_mono hle₀
        rw [hL2] at hrank_lt
        rw [hι.finrank_point y₀ hy₀0] at hge
        have hone : finrank K ↥((X ⊔ ι y₀) ⊓ ι L) = 1 := by omega
        have hinf' : ι y₀ = (X ⊔ ι y₀) ⊓ ι L :=
          Submodule.eq_of_le_of_finrank_eq hle₀ (by rw [hone, hι.finrank_point y₀ hy₀0])
        have hinf : (X ⊔ ι y₀) ⊓ ι L = ι y₀ := hinf'.symm
        exact Submodule.eq_of_le_of_finrank_eq (hinf ▸ le_inf hwT hwleL)
          (by rw [hι.finrank_point w hw0, hι.finrank_point y₀ hy₀0])
      have htang : IsTangentLine c ι y₀ (X ⊔ ι y₀) :=
        ⟨hT2, le_sup_right, Or.inr hsecond⟩
      have hle := (isTangentLine_iff_le_perpSpan hP hT hι hy₀0 hT2 le_sup_right hTA).1 htang
      exact ⟨y₀, hy₀L, hy₀0, le_trans le_sup_left hle⟩
    ·
      push Not at hcase
      obtain ⟨z, hz0, hzPi, hzLnot⟩ := hcase
      have hdist : Γ.dist z L = 3 :=
        dist_eq_three_of_not_adj_of_color_ne hP c (fun h => hzLnot h.symm)
          (by rw [hz0, hL]; decide)
      obtain ⟨p, ⟨hLp, hzp⟩, -⟩ := existsUnique_proj hP hdist
      have hp0 : c p = 0 := color_eq_zero_of_adj_of_color_eq_one hL hLp
      have hzpne : z ≠ p := by
        intro h
        rw [h] at hzp
        simp at hzp
      let M := commonNeighbor hP hzp
      have hzM : Γ.Adj z M := commonNeighbor_adj_left hP hzp
      have hpM : Γ.Adj p M := commonNeighbor_adj_right hP hzp
      have hM1 : c M = 1 := color_eq_one_of_adj_of_color_eq_zero hz0 hzM
      have hM2 : finrank K (ι M) = 2 := hι.finrank_line M hM1
      haveI hMfin : FiniteDimensional K ↥(ι M) :=
        Module.finite_of_finrank_pos (by rw [hM2]; norm_num)
      have hMeq : ι M = ι z ⊔ ι p :=
        line_eq_sup_of_two_adjacent_points hι hz0 hp0 hzpne hzM hpM
      have hpLle : ι p ≤ ι L := (hι.adj_iff p L hp0 hL).1 hLp.symm
      have hpMle : ι p ≤ ι M := hMeq ▸ le_sup_right
      have hMle : ι M ≤ X ⊔ ι L := by
        rw [hMeq]
        exact sup_le hzPi (le_trans hpLle le_sup_right)
      have hML : M ≠ L := by
        intro hML
        have hzle : ι z ≤ ι L := by
          rw [hML] at hMeq
          exact hMeq ▸ le_sup_left
        exact hzLnot ((hι.adj_iff z L hz0 hL).2 hzle).symm
      have hsupLM : ι L ⊔ ι M = X ⊔ ι L := by
        refine Submodule.eq_of_le_of_finrank_eq (sup_le le_sup_right hMle) ?_
        have hge : ι p ≤ ι L ⊓ ι M := le_inf hpLle hpMle
        have hne : ι L ⊓ ι M ≠ ι L := by
          intro heq
          have hle : ι L ≤ ι M := heq ▸ inf_le_right
          have heq2 : ι L = ι M := Submodule.eq_of_le_of_finrank_eq hle (by rw [hL2, hM2])
          exact hML (hι.injective heq2).symm
        haveI : FiniteDimensional K ↥(ι L ⊓ ι M) :=
          Submodule.finiteDimensional_of_le (inf_le_left : ι L ⊓ ι M ≤ ι L)
        have hlt : ι L ⊓ ι M < ι L := lt_of_le_of_ne inf_le_left hne
        have hrank_lt := Submodule.finrank_lt_finrank_of_lt hlt
        have hge1 : finrank K (ι p) ≤ finrank K ↥(ι L ⊓ ι M) := Submodule.finrank_mono hge
        rw [hL2] at hrank_lt
        rw [hι.finrank_point p hp0] at hge1
        have hone : finrank K ↥(ι L ⊓ ι M) = 1 := by omega
        have hdim := Submodule.finrank_sup_add_finrank_inf_eq (ι L) (ι M)
        rw [hone, hL2, hM2] at hdim
        rw [hPi3]
        omega
      have hPperp : ∀ w, c w = 0 → ι w ≤ X ⊔ ι L → w ∈ ptPerp Γ c {p} := by
        intro w hw0 hwPi
        have hwLM : ι w ≤ ι L ⊔ ι M := by
          rw [hsupLM]
          exact hwPi
        exact mem_ptPerp_of_le_sup_lines hP hι hp0 (Ne.symm hML) hLp.symm hpM hw0 hwLM
      have hXp : X ≠ ι p := fun h => hXL (h ▸ hpLle)
      have hT2p : finrank K ↥(X ⊔ ι p) = 2 :=
        finrank_sup_eq_two_of_finrank_eq_one hX1 (hι.finrank_point p hp0) hXp
      have hsec : ∀ w, c w = 0 → ι w ≤ X ⊔ ι p → w = p := by
        intro w hw0 hwT
        have hwperp : w ∈ ptPerp Γ c {p} :=
          hPperp w hw0 (hwT.trans (sup_le le_sup_left (le_trans hpLle le_sup_right)))
        by_contra hwp
        have hwp2 : Γ.dist w p = 2 :=
          dist_eq_two_of_le_two_of_ne hP hw0 hp0 hwp (hwperp.2 p rfl)
        let N := commonNeighbor hP hwp2
        have hwN : Γ.Adj w N := commonNeighbor_adj_left hP hwp2
        have hpN : Γ.Adj p N := commonNeighbor_adj_right hP hwp2
        have hN1 : c N = 1 := color_eq_one_of_adj_of_color_eq_zero hw0 hwN
        have hTeq : X ⊔ ι p = ι p ⊔ ι w :=
          submodule_eq_sup_of_finrank_two hT2p (hι.finrank_point p hp0)
            (hι.finrank_point w hw0) (fun h => hwp (hι.injective h).symm) le_sup_right hwT
        have hNle : ι N = ι w ⊔ ι p :=
          line_eq_sup_of_two_adjacent_points hι hw0 hp0 hwp hwN hpN
        have hile : X ≤ ι N := by
          rw [hNle, sup_comm]
          exact hTeq ▸ le_sup_left
        obtain ⟨x, hNx, hxX⟩ := hι.full N hN1 X hX1 hile
        exact hXP x (color_eq_zero_of_adj_of_color_eq_one hN1 hNx) hxX
      have htang : IsTangentLine c ι p (X ⊔ ι p) :=
        ⟨hT2p, le_sup_right, Or.inr fun w hw0 hwT => by rw [hsec w hw0 hwT]⟩
      have hTpA : X ⊔ ι p ≤ A := sup_le hXA (hι.le_ambient p)
      have hle := (isTangentLine_iff_le_perpSpan hP hT hι hp0 hT2p le_sup_right hTpA).1 htang
      exact ⟨p, hLp, hp0, le_trans le_sup_left hle⟩

theorem mem_collar_of_two_mem_collar (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (hι : IsProjGQ c ι A) [FiniteDimensional K A] {X : Submodule K W} {L y y' x : V}
    (hL : c L = 1) (hy : Γ.Adj L y) (hy' : Γ.Adj L y') (hne : y ≠ y')
    (hyX : y ∈ collar c ι X) (hy'X : y' ∈ collar c ι X) (hx : Γ.Adj L x) :
    x ∈ collar c ι X := by
  have hx0 : c x = 0 := color_eq_zero_of_adj_of_color_eq_one hL hx
  have hy0 : c y = 0 := color_eq_zero_of_adj_of_color_eq_one hL hy
  have hy'0 : c y' = 0 := color_eq_zero_of_adj_of_color_eq_one hL hy'
  refine ⟨hx0, ?_⟩
  have hle : perpSpan c ι y ⊓ perpSpan c ι y' ≤ perpSpan c ι x :=
    perpSpan_inf_le_perpSpan hP hT hι hy0 hy'0 hx0 hne hy.symm hy'.symm hx.symm
  exact le_trans (le_inf hyX.2 hy'X.2) hle

private theorem ncard_collar_inter_perp (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (hι : IsProjGQ c ι A) [FiniteDimensional K A] {X : Submodule K W}
    (hX1 : finrank K X = 1) (hXA : X ≤ A) {z : V} (hz : c z = 0)
    (hzX : z ∉ collar c ι X) :
    (collar c ι X ∩ ptPerp Γ c {z}).ncard = Γ.degree z := by
  classical
  rw [← ncard_neighborSet]
  let f : ∀ y ∈ collar c ι X ∩ ptPerp Γ c {z}, V := fun y hy =>
    commonNeighbor hP (dist_eq_two_of_le_two_of_ne hP hy.1.1 hz
      (fun h => hzX (h ▸ hy.1)) (hy.2.2 z rfl))
  have hf : ∀ y hy, Γ.Adj y (f y hy) ∧ Γ.Adj z (f y hy) := by
    intro y hy
    exact ⟨commonNeighbor_adj_left hP _, commonNeighbor_adj_right hP _⟩
  refine Set.ncard_congr f ?_ ?_ ?_
  · intro y hy
    exact (hf y hy).2
  · intro y y' hy hy' heq
    by_contra hne
    have hL : c (f y hy) = 1 := color_eq_one_of_adj_of_color_eq_zero hy.1.1 (hf y hy).1
    have hyL : Γ.Adj (f y hy) y := (hf y hy).1.symm
    have hy'L : Γ.Adj (f y hy) y' := by
      rw [heq]
      exact (hf y' hy').1.symm
    have hzL : Γ.Adj (f y hy) z := (hf y hy).2.symm
    exact hzX (mem_collar_of_two_mem_collar hP hT hι hL hyL hy'L hne hy.1 hy'.1 hzL)
  · intro L hL
    rw [mem_neighborSet] at hL
    obtain ⟨y, hyL, hycol⟩ :=
      exists_adj_mem_collar hP hT hι hX1 hXA (color_eq_one_of_adj_of_color_eq_zero hz hL)
    have hyz : y ≠ z := fun h => hzX (h ▸ hycol)
    have hyz2 : Γ.dist y z = 2 := dist_eq_two_of_adj_of_adj_of_ne hP hyL.symm hL.symm hyz
    have hmem : y ∈ collar c ι X ∩ ptPerp Γ c {z} :=
      ⟨hycol, mem_ptPerp_singleton hycol.1 (le_of_eq hyz2)⟩
    refine ⟨y, hmem, ?_⟩
    exact (eq_commonNeighbor hP hyz2 hyL.symm hL).symm

private theorem traceSet_subset_collar (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (hι : IsProjGQ c ι A) [FiniteDimensional K A] {X : Submodule K W}
    (hX1 : finrank K X = 1) (hXA : X ≤ A) {z m : V} (hz : c z = 0)
    (hzX : z ∉ collar c ι X) (hcol : ∀ y ∈ collar c ι X, Γ.dist z y = 2)
    (hzm : Γ.dist z m = 4) : traceSet Γ z m ⊆ collar c ι X := by
  classical
  have hm0 : c m = 0 := by
    have heven : Even (Γ.dist z m) := ⟨2, by rw [hzm]⟩
    have hc := (hP.eq_iff_even_dist c z m).2 heven
    rw [hz] at hc
    exact hc.symm
  intro u hu
  have hu0 : c u = 0 := color_eq_zero_of_dist_eq_two hP hz hu.1
  have hmu : Γ.dist m u = 2 := hu.2
  let N := commonNeighbor hP hmu
  have hmN : Γ.Adj m N := commonNeighbor_adj_left hP hmu
  have huN : Γ.Adj N u := (commonNeighbor_adj_right hP hmu).symm
  have hN1 : c N = 1 := color_eq_one_of_adj_of_color_eq_zero hm0 hmN
  have hzN : ¬ Γ.Adj z N := by
    intro hzN
    have htri := hP.connected.dist_triangle (u := z) (v := N) (w := m)
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr hzN,
      SimpleGraph.dist_eq_one_iff_adj.mpr hmN.symm] at htri
    omega
  have hdist : Γ.dist z N = 3 :=
    dist_eq_three_of_not_adj_of_color_ne hP c hzN (by rw [hz, hN1]; decide)
  obtain ⟨y, ⟨hNy, hzy⟩, huniq⟩ := existsUnique_proj hP hdist
  obtain ⟨y', hy'N, hy'col⟩ := exists_adj_mem_collar hP hT hι hX1 hXA hN1
  have hy'eq : y' = y := huniq y' ⟨hy'N, hcol y' hy'col⟩
  have hueq : u = y := huniq u ⟨huN, hu.1⟩
  rw [hueq, ← hy'eq]
  exact hy'col

private theorem eq_collar_inter_perp_of_traceSet_subset (hP : IsGeneralizedPolygon Γ 4)
    (hT : IsThick Γ) (hι : IsProjGQ c ι A) [FiniteDimensional K A] {X : Submodule K W}
    (hX1 : finrank K X = 1) (hXA : X ≤ A) {z m : V} (hz : c z = 0)
    (hzX : z ∉ collar c ι X) (hzm : Γ.dist z m = 4)
    (hsub : traceSet Γ z m ⊆ collar c ι X) :
    traceSet Γ z m = collar c ι X ∩ ptPerp Γ c {z} := by
  refine Set.eq_of_subset_of_ncard_le ?_ ?_
  · intro u hu
    exact ⟨hsub hu, mem_ptPerp_singleton (hsub hu).1 (by
      rw [SimpleGraph.dist_comm]
      exact le_of_eq hu.1)⟩
  · have h1 := ncard_collar_inter_perp hP hT hι hX1 hXA hz hzX
    have h2 := ncard_trace hP hzm
    omega

theorem exists_dist_eq_four_mem_collar (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (hι : IsProjGQ c ι A) [FiniteDimensional K A] {X : Submodule K W}
    (hX1 : finrank K X = 1) (hXA : X ≤ A) {z : V} (hz : c z = 0)
    (hzX : z ∉ collar c ι X) :
    ∃ w ∈ collar c ι X, Γ.dist z w = 4 := by
  classical
  by_contra hcon
  push Not at hcon
  have hcol : ∀ y ∈ collar c ι X, Γ.dist z y = 2 := by
    intro y hy
    have hyz : y ≠ z := fun h => hzX (h ▸ hy)
    rcases dist_eq_two_or_four_of_color_zero hP hz hy.1 (Ne.symm hyz) with h2 | h4
    · exact h2
    · exact absurd h4 (hcon y hy)
  have hcolsub : collar c ι X ⊆ ptPerp Γ c {z} := fun y hy =>
    mem_ptPerp_singleton hy.1 (by rw [SimpleGraph.dist_comm]; exact le_of_eq (hcol y hy))
  have hdegz : 0 < Γ.degree z := by
    have := hT z
    omega
  obtain ⟨L₀, hzL₀⟩ := (SimpleGraph.degree_pos_iff_exists_adj (G := Γ) (v := z)).mp hdegz
  obtain ⟨m, hzm, -⟩ := hP.exists_dist_eq hT hzL₀ 4 (by norm_num) (by norm_num)
  have hm0 : c m = 0 := by
    have heven : Even (Γ.dist z m) := ⟨2, by rw [hzm]⟩
    have hc := (hP.eq_iff_even_dist c z m).2 heven
    rw [hz] at hc
    exact hc.symm
  have hsub := traceSet_subset_collar hP hT hι hX1 hXA hz hzX hcol hzm
  have heqT := eq_collar_inter_perp_of_traceSet_subset hP hT hι hX1 hXA hz hzX hzm hsub
  rw [Set.inter_eq_left.mpr hcolsub] at heqT
  have hdegm : 0 < Γ.degree m := by
    have := hT m
    omega
  obtain ⟨N₀, hmN₀⟩ := (SimpleGraph.degree_pos_iff_exists_adj (G := Γ) (v := m)).mp hdegm
  have hN₀1 : c N₀ = 1 := color_eq_one_of_adj_of_color_eq_zero hm0 hmN₀
  have hzmN : Γ.dist z N₀ = 3 :=
    dist_eq_three_of_adj_of_dist_eq_four hP (by rw [SimpleGraph.dist_comm]; exact hzm) hmN₀
  obtain ⟨n, ⟨hN₀n, hzn⟩, huniq⟩ := existsUnique_proj hP hzmN
  have hzN₀ : ¬ Γ.Adj z N₀ := by
    intro h
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr h] at hzmN
    omega
  have hmn : m ≠ n := by
    intro h
    rw [← h] at hzn
    omega
  have hcardN : 3 ≤ (Γ.neighborFinset N₀).card := by
    rw [card_neighborFinset_eq_degree]
    exact hT N₀
  have hposm' : 0 < (((Γ.neighborFinset N₀).erase m).erase n).card := by
    have h1 := Finset.pred_card_le_card_erase (s := Γ.neighborFinset N₀) (a := m)
    have h2 := Finset.pred_card_le_card_erase (s := (Γ.neighborFinset N₀).erase m) (a := n)
    omega
  obtain ⟨m', hm'⟩ := Finset.card_pos.mp hposm'
  simp only [Finset.mem_erase, mem_neighborFinset] at hm'
  obtain ⟨hm'n, hm'm, hm'N₀⟩ := hm'
  have hm'0 : c m' = 0 := color_eq_zero_of_adj_of_color_eq_one hN₀1 hm'N₀
  have hm'z : m' ≠ z := fun h => hzN₀ (h ▸ hm'N₀.symm)
  have hm'4 : Γ.dist z m' = 4 := by
    rcases dist_eq_two_or_four_of_color_zero hP hz hm'0 (Ne.symm hm'z) with h2 | h4
    · exact absurd (huniq m' ⟨hm'N₀, h2⟩) hm'n
    · exact h4
  have hsub' := traceSet_subset_collar hP hT hι hX1 hXA hz hzX hcol hm'4
  have heqT' := eq_collar_inter_perp_of_traceSet_subset hP hT hι hX1 hXA hz hzX hm'4 hsub'
  rw [Set.inter_eq_left.mpr hcolsub] at heqT'
  have htracecard : 1 < (traceSet Γ z m).ncard := by
    rw [ncard_trace hP hzm]
    have := hT z
    omega
  obtain ⟨u, hu, hun⟩ := Set.exists_ne_of_one_lt_ncard htracecard n
  have hu0 : c u = 0 := color_eq_zero_of_dist_eq_two hP hz hu.1
  have huN₀ : ¬ Γ.Adj u N₀ := by
    intro h
    exact hun (huniq u ⟨h.symm, hu.1⟩)
  have huc : u ∈ collar c ι X := by
    rw [← heqT]
    exact hu
  have hum' : Γ.dist u m' = 2 := by
    have hu' : u ∈ traceSet Γ z m' := by
      rw [heqT']
      exact huc
    rw [SimpleGraph.dist_comm]
    exact hu'.2
  have hum : Γ.dist u m = 2 := by
    rw [SimpleGraph.dist_comm]
    exact hu.2
  exact hm'm (eq_of_mem_ptPerp_of_adj_line hP hu0 huN₀ hmN₀.symm hm'N₀
    (mem_ptPerp_singleton hm0 (by rw [SimpleGraph.dist_comm]; exact le_of_eq hum))
    (mem_ptPerp_singleton hm'0 (by rw [SimpleGraph.dist_comm]; exact le_of_eq hum'))).symm

theorem polar_sup_eq_of_not_mem_collar (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (hι : IsProjGQ c ι A) [FiniteDimensional K A] {X : Submodule K W}
    (hX1 : finrank K X = 1) (hXA : X ≤ A) {z : V} (hz : c z = 0)
    (hzX : z ∉ collar c ι X) :
    polar c ι X ⊔ ι z = A := by
  classical
  obtain ⟨w, hwcol, hzw⟩ := exists_dist_eq_four_mem_collar hP hT hι hX1 hXA hz hzX
  refine le_antisymm (sup_le (polar_le_ambient hι X) (hι.le_ambient z)) ?_
  have hHz : perpSpan c ι z ≤ polar c ι X ⊔ ι z := by
    rw [perpSpan_eq_iSup_neighborFinset hP hT hι hz]
    refine iSup_le fun L => iSup_le fun hL => ?_
    rw [mem_neighborFinset] at hL
    have hL1 : c L = 1 := color_eq_one_of_adj_of_color_eq_zero hz hL
    obtain ⟨y, hyL, hycol⟩ := exists_adj_mem_collar hP hT hι hX1 hXA hL1
    have hyz : z ≠ y := fun h => hzX (h ▸ hycol)
    have hline : ι L = ι z ⊔ ι y :=
      line_eq_sup_of_two_adjacent_points hι hz hycol.1 hyz hL hyL.symm
    rw [hline]
    exact sup_le le_sup_right (le_trans (le_polar_of_mem_collar hycol) le_sup_left)
  have hzH : perpSpan c ι z ⊔ ι w = A :=
    perpSpan_sup_eq_ambient_of_dist_eq_four hP hT hι hz hzw
  rw [← hzH]
  exact sup_le hHz (le_trans (le_polar_of_mem_collar hwcol) le_sup_left)

theorem sectionPoints_polar_of_ne (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (hι : IsProjGQ c ι A) [FiniteDimensional K A] {X : Submodule K W}
    (hX1 : finrank K X = 1) (hXA : X ≤ A) (hne : polar c ι X ≠ A) :
    sectionPoints c ι (polar c ι X) = collar c ι X := by
  ext z
  constructor
  · intro hz
    by_contra hzc
    have hsup := polar_sup_eq_of_not_mem_collar hP hT hι hX1 hXA hz.1 hzc
    exact hne (by rwa [sup_eq_left.mpr hz.2] at hsup)
  · intro hz
    exact ⟨hz.1, le_polar_of_mem_collar hz⟩

theorem finrank_polar_add_one_of_ne (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (hι : IsProjGQ c ι A) [FiniteDimensional K A] {X : Submodule K W}
    (hX1 : finrank K X = 1) (hXA : X ≤ A) (hne : polar c ι X ≠ A) {z : V} (hz : c z = 0)
    (hzX : z ∉ collar c ι X) :
    finrank K (polar c ι X) + 1 = finrank K A := by
  have hsup := polar_sup_eq_of_not_mem_collar hP hT hι hX1 hXA hz hzX
  have hPA : polar c ι X ≤ A := polar_le_ambient hι X
  haveI : FiniteDimensional K (polar c ι X) := Submodule.finiteDimensional_of_le hPA
  haveI : FiniteDimensional K (ι z) := Submodule.finiteDimensional_of_le (hι.le_ambient z)
  have hlt : polar c ι X < A := lt_of_le_of_ne hPA hne
  have hrank_lt : finrank K (polar c ι X) < finrank K A :=
    Submodule.finrank_lt_finrank_of_lt hlt
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq (polar c ι X) (ι z)
  rw [hsup, hι.finrank_point z hz] at hdim
  have hinfle : finrank K ↥(polar c ι X ⊓ ι z) ≤ 1 := by
    have h := Submodule.finrank_mono (inf_le_right : polar c ι X ⊓ ι z ≤ ι z)
    rwa [hι.finrank_point z hz] at h
  omega

theorem mem_collar_iff_sectionPoints_sup (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (hι : IsProjGQ c ι A) [FiniteDimensional K A] {X : Submodule K W}
    (hX1 : finrank K X = 1) (hXA : X ≤ A) (hXP : ¬ ∃ v, c v = 0 ∧ ι v = X)
    {z : V} (hz : c z = 0) :
    z ∈ collar c ι X ↔ sectionPoints c ι (X ⊔ ι z) = {z} := by
  have hXz : X ≠ ι z := fun h => hXP ⟨z, hz, h.symm⟩
  have hT2 : finrank K ↥(X ⊔ ι z) = 2 :=
    finrank_sup_eq_two_of_finrank_eq_one hX1 (hι.finrank_point z hz) hXz
  have hTA : X ⊔ ι z ≤ A := sup_le hXA (hι.le_ambient z)
  constructor
  · intro hzcol
    have hTle : X ⊔ ι z ≤ perpSpan c ι z :=
      sup_le hzcol.2 (submodule_le_perpSpan ⟨hz, by simp⟩)
    have htang : IsTangentLine c ι z (X ⊔ ι z) :=
      (isTangentLine_iff_le_perpSpan hP hT hι hz hT2 le_sup_right hTA).2 hTle
    ext w
    constructor
    · intro hw
      rcases htang.2.2 with ⟨L, hL1, hzL, hLeq⟩ | hsecond
      · have hXle : X ≤ ι L := hLeq ▸ le_sup_left
        obtain ⟨x, hLx, hxX⟩ := hι.full L hL1 X hX1 hXle
        exact absurd ⟨x, color_eq_zero_of_adj_of_color_eq_one hL1 hLx, hxX⟩ hXP
      · exact hι.injective (hsecond w hw.1 hw.2)
    · intro hw
      rw [Set.mem_singleton_iff] at hw
      subst hw
      exact ⟨hz, le_sup_right⟩
  · intro hsec
    refine ⟨hz, ?_⟩
    have hsecond : ∀ x, c x = 0 → ι x ≤ X ⊔ ι z → ι x = ι z := by
      intro x hx hxle
      have hxmem : x ∈ sectionPoints c ι (X ⊔ ι z) := ⟨hx, hxle⟩
      rw [hsec, Set.mem_singleton_iff] at hxmem
      rw [hxmem]
    have htang : IsTangentLine c ι z (X ⊔ ι z) := ⟨hT2, le_sup_right, Or.inr hsecond⟩
    exact le_trans le_sup_left
      ((isTangentLine_iff_le_perpSpan hP hT hι hz hT2 le_sup_right hTA).1 htang)

theorem sectionPoints_sup_of_not_mem_collar (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (hι : IsProjGQ c ι A) [FiniteDimensional K A] {ℓ : ℕ}
    (hsec : HasConstantSecants c ι A ℓ) {X : Submodule K W} (hX1 : finrank K X = 1)
    (hXA : X ≤ A) (hXP : ¬ ∃ v, c v = 0 ∧ ι v = X) {z : V} (hz : c z = 0)
    (hzX : z ∉ collar c ι X) :
    (sectionPoints c ι (X ⊔ ι z)).ncard = ℓ + 1 ∧
      ∀ w ∈ sectionPoints c ι (X ⊔ ι z), w ∉ collar c ι X := by
  have hXz : X ≠ ι z := fun h => hXP ⟨z, hz, h.symm⟩
  have hT2 : finrank K ↥(X ⊔ ι z) = 2 :=
    finrank_sup_eq_two_of_finrank_eq_one hX1 (hι.finrank_point z hz) hXz
  have hTA : X ⊔ ι z ≤ A := sup_le hXA (hι.le_ambient z)
  have hnotle : ¬ X ⊔ ι z ≤ perpSpan c ι z := by
    intro hle
    exact hzX ⟨hz, le_trans le_sup_left hle⟩
  obtain ⟨x, hx0, hxT, hzx⟩ :=
    exists_dist_eq_four_of_not_le_perpSpan hP hT hι hz hT2 le_sup_right hTA hnotle
  have hne : ∀ L, c L = 1 → ι L ≠ X ⊔ ι z := by
    intro L hL1 hLeq
    have hXle : X ≤ ι L := hLeq ▸ le_sup_left
    obtain ⟨y, hLy, hyX⟩ := hι.full L hL1 X hX1 hXle
    exact hXP ⟨y, color_eq_zero_of_adj_of_color_eq_one hL1 hLy, hyX⟩
  have hzxne : z ≠ x := by
    intro h
    rw [h] at hzx
    simp at hzx
  have hge : 2 ≤ (sectionPoints c ι (X ⊔ ι z)).ncard := by
    have h1 : 1 < (sectionPoints c ι (X ⊔ ι z)).ncard :=
      (Set.one_lt_ncard (s := sectionPoints c ι (X ⊔ ι z))).mpr
        ⟨z, ⟨hz, le_sup_right⟩, x, ⟨hx0, hxT⟩, hzxne⟩
    omega
  refine ⟨hsec.ncard_eq hTA hT2 hne hge, ?_⟩
  intro w hw hwc
  have hXw : X ≠ ι w := fun h => hXP ⟨w, hw.1, h.symm⟩
  have hTweq : X ⊔ ι w = X ⊔ ι z :=
    (submodule_eq_sup_of_finrank_two hT2 hX1 (hι.finrank_point w hw.1) hXw
      le_sup_left hw.2).symm
  have hsec' := (mem_collar_iff_sectionPoints_sup hP hT hι hX1 hXA hXP hw.1).1 hwc
  rw [hTweq] at hsec'
  have hzmem : z ∈ sectionPoints c ι (X ⊔ ι z) := ⟨hz, le_sup_right⟩
  have hxmem : x ∈ sectionPoints c ι (X ⊔ ι z) := ⟨hx0, hxT⟩
  rw [hsec'] at hzmem hxmem
  rw [Set.mem_singleton_iff] at hzmem hxmem
  rw [hzmem, hxmem] at hzx
  simp at hzx

theorem collar_compl_induction (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (hι : IsProjGQ c ι A) [FiniteDimensional K A] {X : Submodule K W}
    (hX1 : finrank K X = 1) (hXA : X ≤ A) {Q : V → Prop} {z₀ : V} (hz₀ : c z₀ = 0)
    (hz₀X : z₀ ∉ collar c ι X) (h₀ : Q z₀)
    (hstep : ∀ z w, c z = 0 → z ∉ collar c ι X → c w = 0 → w ∉ collar c ι X →
      Γ.dist z w = 2 → Q z → Q w)
    {w : V} (hw : c w = 0) (hwX : w ∉ collar c ι X) : Q w := by
  classical
  by_cases hwz : w = z₀
  · rw [hwz]
    exact h₀
  have hne : z₀ ≠ w := fun h => hwz h.symm
  rcases dist_eq_two_or_four_of_color_zero hP hz₀ hw hne with h2 | h4
  · exact hstep z₀ w hz₀ hz₀X hw hwX h2 h₀
  by_cases htrace : ∃ a ∈ traceSet Γ z₀ w, a ∉ collar c ι X
  · obtain ⟨a, haT, haX⟩ := htrace
    have ha0 : c a = 0 := color_eq_zero_of_dist_eq_two hP hz₀ haT.1
    have h1 : Q a := hstep z₀ a hz₀ hz₀X ha0 haX haT.1 h₀
    exact hstep a w ha0 haX hw hwX (by rw [SimpleGraph.dist_comm]; exact haT.2) h1
  push Not at htrace
  have hdegw : 0 < Γ.degree w := by
    have := hT w
    omega
  obtain ⟨N, hwN⟩ := (SimpleGraph.degree_pos_iff_exists_adj (G := Γ) (v := w)).mp hdegw
  have hN1 : c N = 1 := color_eq_one_of_adj_of_color_eq_zero hw hwN
  have hdistN : Γ.dist z₀ N = 3 :=
    dist_eq_three_of_adj_of_dist_eq_four hP (by rw [SimpleGraph.dist_comm]; exact h4) hwN
  obtain ⟨m, ⟨hNm, hz₀m⟩, huniq⟩ := existsUnique_proj hP hdistN
  have hwm : Γ.dist w m = 2 :=
    dist_eq_two_of_adj_of_adj_of_ne hP hwN hNm (by
      intro h
      rw [← h] at hz₀m
      omega)
  have hmcol : m ∈ collar c ι X := htrace m ⟨hz₀m, hwm⟩
  have hz₀N : ¬ Γ.Adj z₀ N := by
    intro h
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr h] at hdistN
    omega
  have hcardN : 3 ≤ (Γ.neighborFinset N).card := by
    rw [card_neighborFinset_eq_degree]
    exact hT N
  have hposn : 0 < (((Γ.neighborFinset N).erase w).erase m).card := by
    have h1 := Finset.pred_card_le_card_erase (s := Γ.neighborFinset N) (a := w)
    have h2 := Finset.pred_card_le_card_erase (s := (Γ.neighborFinset N).erase w) (a := m)
    omega
  obtain ⟨n, hn⟩ := Finset.card_pos.mp hposn
  simp only [Finset.mem_erase, mem_neighborFinset] at hn
  obtain ⟨hnm, hnw, hnN⟩ := hn
  have hn0 : c n = 0 := color_eq_zero_of_adj_of_color_eq_one hN1 hnN
  have hnX : n ∉ collar c ι X := by
    intro hncol
    exact hwX (mem_collar_of_two_mem_collar hP hT hι hN1 hnN hNm hnm hncol hmcol hwN.symm)
  have hn4 : Γ.dist z₀ n = 4 := by
    have hnz : n ≠ z₀ := fun h => hz₀N (h ▸ hnN.symm)
    rcases dist_eq_two_or_four_of_color_zero hP hz₀ hn0 (Ne.symm hnz) with h2 | h4'
    · exact absurd (huniq n ⟨hnN, h2⟩) hnm
    · exact h4'
  have hnw2 : Γ.dist n w = 2 :=
    dist_eq_two_of_adj_of_adj_of_ne hP hnN.symm hwN.symm hnw
  have hcontr : ¬ traceSet Γ z₀ n ⊆ collar c ι X := by
    intro hsub'
    have heqT := eq_collar_inter_perp_of_traceSet_subset hP hT hι hX1 hXA hz₀ hz₀X h4 htrace
    have heqT' :=
      eq_collar_inter_perp_of_traceSet_subset hP hT hι hX1 hXA hz₀ hz₀X hn4 hsub'
    have heqTn : traceSet Γ z₀ w = traceSet Γ z₀ n := heqT.trans heqT'.symm
    have htracecard : 1 < (traceSet Γ z₀ n).ncard := by
      rw [ncard_trace hP hn4]
      have := hT z₀
      omega
    obtain ⟨o, ho, hom⟩ := Set.exists_ne_of_one_lt_ncard htracecard m
    have ho' : o ∈ traceSet Γ z₀ w := by
      rw [heqTn]
      exact ho
    have ho0 : c o = 0 := color_eq_zero_of_dist_eq_two hP hz₀ ho.1
    have hoN : ¬ Γ.Adj o N := by
      intro h
      exact hom (huniq o ⟨h.symm, ho.1⟩)
    exact hnw (eq_of_mem_ptPerp_of_adj_line hP ho0 hoN hwN.symm hnN
      (mem_ptPerp_singleton hw (le_of_eq ho'.2))
      (mem_ptPerp_singleton hn0 (le_of_eq ho.2))).symm
  obtain ⟨a, haT, haX⟩ := Set.not_subset.mp hcontr
  have ha0 : c a = 0 := color_eq_zero_of_dist_eq_two hP hz₀ haT.1
  have h1 : Q a := hstep z₀ a hz₀ hz₀X ha0 haX haT.1 h₀
  have h2 : Q n := hstep a n ha0 haX hn0 hnX (by
    rw [SimpleGraph.dist_comm]
    exact haT.2) h1
  exact hstep n w hn0 hnX hw hwX hnw2 h2

theorem sectionPoints_sup_subset_spanSet (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (hι : IsProjGQ c ι A) [FiniteDimensional K A] {x y : V} (hx : c x = 0)
    (hxy : Γ.dist x y = 4) :
    sectionPoints c ι (ι x ⊔ ι y) ⊆ spanSet Γ x y := by
  intro z hz
  have hz0 : c z = 0 := hz.1
  have hzle : ι z ≤ ι x ⊔ ι y := hz.2
  intro u hu
  have hu0 : c u = 0 := color_eq_zero_of_dist_eq_two hP hx hu.1
  have hy0 : c y = 0 :=
    color_eq_zero_of_dist_eq_two hP hu0 (by rw [SimpleGraph.dist_comm]; exact hu.2)
  have hxH : ι x ≤ perpSpan c ι u :=
    submodule_le_perpSpan ⟨hx, fun a ha => by
      rw [Set.mem_singleton_iff] at ha
      subst ha
      exact le_of_eq hu.1⟩
  have hyH : ι y ≤ perpSpan c ι u :=
    submodule_le_perpSpan ⟨hy0, fun a ha => by
      rw [Set.mem_singleton_iff] at ha
      subst ha
      exact le_of_eq hu.2⟩
  have hle : ι z ≤ perpSpan c ι u := hzle.trans (sup_le hxH hyH)
  have hmem : z ∈ sectionPoints c ι (perpSpan c ι u) := ⟨hz0, hle⟩
  rw [sectionPoints_perpSpan hP hT hι hu0] at hmem
  exact hmem.2 u rfl

end Polar

end CFSG.Geometry.GeneralizedQuadrangles

end
