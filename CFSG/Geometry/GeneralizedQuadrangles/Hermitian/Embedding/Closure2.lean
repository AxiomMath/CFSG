module

public import CFSG.Geometry.GeneralizedQuadrangles.Hermitian.Embedding.Closure

public section

namespace CFSG.Geometry.GeneralizedQuadrangles

open SimpleGraph CFSG.Geometry.GeneralizedPolygons Module

universe u

variable {V : Type u}

section Closure

variable {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj]
variable {K : Type*} [Field K] [Fintype K] {W : Type*} [AddCommGroup W] [Module K W]
variable {ι : V → Submodule K W} {A : Submodule K W}

theorem mem_collar_of_mem_sectionPoints_sup (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hι : IsProjGQ c ι A) [FiniteDimensional K A] {ℓ : ℕ}
    (hsec : HasConstantSecants c ι A ℓ) (h5 : finrank K A = 5) {X : Submodule K W}
    {x y z : V} (hx : c x = 0) (hxy : Γ.dist x y = 4) (hxX : x ∈ collar c ι X)
    (hyX : y ∈ collar c ι X) (hz : z ∈ sectionPoints c ι (ι x ⊔ ι y)) :
    z ∈ collar c ι X := by
  classical
  have hXD : X ≤ perpSpan c ι x ⊓ perpSpan c ι y := le_inf hxX.2 hyX.2
  have hz0 : c z = 0 := hz.1
  have hzSpan : z ∈ spanSet Γ x y :=
    sectionPoints_sup_subset_spanSet hP hT hι hx hxy hz
  have hD : perpSpan c ι x ⊓ perpSpan c ι y =
      ⨆ u : {u : V // u ∈ traceSet Γ x y}, ι u.1 :=
    (iSup_traceSet_eq_perpSpan_inf hP hT c hdeg hι hsec h5 hx hxy).symm
  have hleHz : perpSpan c ι x ⊓ perpSpan c ι y ≤ perpSpan c ι z := by
    rw [hD]
    refine iSup_le fun u => ?_
    have hu0 : c u.1 = 0 := color_eq_zero_of_dist_eq_two hP hx u.2.1
    exact submodule_le_perpSpan ⟨hu0, by
      intro a ha
      rw [Set.mem_singleton_iff] at ha
      subst ha
      rw [SimpleGraph.dist_comm]
      exact hzSpan u.1 u.2⟩
  exact ⟨hz0, hXD.trans hleHz⟩


theorem collar_ne_ptPerp (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hι : IsProjGQ c ι A) [FiniteDimensional K A] {ℓ : ℕ}
    (hsec : HasConstantSecants c ι A ℓ) (hℓ : 2 ≤ ℓ) (h5 : finrank K A = 5)
    {X : Submodule K W} (hX1 : finrank K X = 1) (hXA : X ≤ A)
    (hXP : ¬ ∃ v, c v = 0 ∧ ι v = X) (p : V) :
    collar c ι X ≠ ptPerp Γ c {p} := by
  classical
  intro h
  have hmem : ∀ z, c z = 0 → (z ∈ collar c ι X ↔ Γ.dist z p ≤ 2) := by
    intro z hz
    rw [h]
    constructor
    · intro hz'
      simpa using hz'.2 p rfl
    · intro hd
      exact ⟨hz, by
        intro a ha
        rw [Set.mem_singleton_iff] at ha
        subst ha
        exact hd⟩
  have hs : 2 ≤ s := two_le_s hP hT c hdeg
  have ht : 2 ≤ t := two_le_t hP hT c hdeg
  have hcp : c p = 0 ∨ c p = 1 := by
    have hfin : ∀ a : Fin 2, a = 0 ∨ a = 1 := by decide
    exact hfin (c p)
  rcases hcp with hp0 | hp1
  ·
    have hpp : p ∈ collar c ι X := (hmem p hp0).2 (by simp)
    have hXHp : X ≤ perpSpan c ι p := hpp.2
    have hpdim : finrank K (ι p) = 1 := hι.finrank_point p hp0
    have hXne : ι p ≠ X := by
      intro hEq
      exact hXP ⟨p, hp0, hEq⟩
    let Hp : Submodule K W := perpSpan c ι p
    let E0 : Submodule K W := ι p ⊔ X
    have hE0dim : finrank K E0 = 2 :=
      finrank_sup_eq_two_of_finrank_eq_one hpdim hX1 hXne
    have hHpA : Hp ≤ A := perpSpan_le_ambient hι p
    have hE0Hp : E0 ≤ Hp :=
      sup_le (submodule_le_perpSpan ⟨hp0, by simp⟩) hXHp
    let Lines := {L : V // c L = 1 ∧ Γ.Adj p L}
    let E : Set (Submodule K W) := {M | E0 ≤ M ∧ M ≤ Hp ∧ finrank K M = 3}
    haveI : Finite A := Module.finite_of_finite K
    haveI hfinSub : Finite {T : Submodule K W // T ≤ A} := by
      haveI : Finite (Submodule K A) :=
        Finite.of_injective (fun L : Submodule K A => (L : Set A)) SetLike.coe_injective
      exact Finite.of_equiv (Submodule K A) (Submodule.MapSubtype.orderIso A).toEquiv
    haveI : Finite E :=
      Finite.of_injective (fun T : E => (⟨T.1, T.2.2.1.trans hHpA⟩ :
        {T : Submodule K W // T ≤ A}))
        (fun a b h => Subtype.ext
          (congrArg (fun x : {T : Submodule K W // T ≤ A} => (x : Submodule K W)) h))
    have hdegL : ∀ L : Lines, (Γ.neighborSet L.1).ncard = s + 1 := by
      intro L
      rw [ncard_neighborSet, hdeg L.1, if_neg (by rw [L.2.1]; decide)]
    have hex : ∀ L : Lines, ∃ y1 y2, y1 ≠ y2 ∧ Γ.Adj L.1 y1 ∧ Γ.Adj L.1 y2 := by
      intro L
      have h1 : 1 < (Γ.neighborSet L.1).ncard := by
        rw [hdegL L]
        omega
      obtain ⟨y1, hy1, y2, hy2, hne⟩ :=
        (Set.one_lt_ncard (s := Γ.neighborSet L.1)).mp h1
      exact ⟨y1, y2, hne, hy1, hy2⟩
    let y1 (L : Lines) : V := Classical.choose (hex L)
    let y2 (L : Lines) : V := Classical.choose (Classical.choose_spec (hex L))
    have hy1 : ∀ L : Lines, Γ.Adj L.1 (y1 L) := fun L =>
      (Classical.choose_spec (Classical.choose_spec (hex L))).2.1
    have hy2 : ∀ L : Lines, Γ.Adj L.1 (y2 L) := fun L =>
      (Classical.choose_spec (Classical.choose_spec (hex L))).2.2
    have hy12 : ∀ L : Lines, y1 L ≠ y2 L := fun L =>
      (Classical.choose_spec (Classical.choose_spec (hex L))).1
    let Y (L : Lines) : Submodule K W :=
      perpSpan c ι (y1 L) ⊓ perpSpan c ι (y2 L)
    have hLsub : ∀ (L : Lines) (z : V), Γ.Adj L.1 z → z ∈ collar c ι X := by
      intro L z hz
      have hz0 : c z = 0 := color_eq_zero_of_adj_of_color_eq_one L.2.1 hz
      have hd : Γ.dist z p ≤ 2 := by
        have ht1 := hP.connected.dist_triangle (u := z) (v := L.1) (w := p)
        rw [SimpleGraph.dist_eq_one_iff_adj.mpr hz.symm,
          SimpleGraph.dist_eq_one_iff_adj.mpr L.2.2.symm] at ht1
        omega
      exact (hmem z hz0).2 hd
    have hYE : ∀ L : Lines, Y L ∈ E := by
      intro L
      have hy10 : c (y1 L) = 0 := color_eq_zero_of_adj_of_color_eq_one L.2.1 (hy1 L)
      have hy20 : c (y2 L) = 0 := color_eq_zero_of_adj_of_color_eq_one L.2.1 (hy2 L)
      have hpy1 : p ∈ ptPerp Γ c {y1 L} := by
        refine ⟨hp0, ?_⟩
        intro a ha
        rw [Set.mem_singleton_iff] at ha
        subst ha
        have ht1 := hP.connected.dist_triangle (u := p) (v := L.1) (w := y1 L)
        rw [SimpleGraph.dist_eq_one_iff_adj.mpr L.2.2,
          SimpleGraph.dist_eq_one_iff_adj.mpr (hy1 L)] at ht1
        omega
      have hpy2 : p ∈ ptPerp Γ c {y2 L} := by
        refine ⟨hp0, ?_⟩
        intro a ha
        rw [Set.mem_singleton_iff] at ha
        subst ha
        have ht1 := hP.connected.dist_triangle (u := p) (v := L.1) (w := y2 L)
        rw [SimpleGraph.dist_eq_one_iff_adj.mpr L.2.2,
          SimpleGraph.dist_eq_one_iff_adj.mpr (hy2 L)] at ht1
        omega
      refine ⟨?_, ?_, ?_⟩
      · refine sup_le (le_inf ?_ ?_) (le_inf ?_ ?_)
        · exact submodule_le_perpSpan hpy1
        · exact submodule_le_perpSpan hpy2
        · exact (hLsub L (y1 L) (hy1 L)).2
        · exact (hLsub L (y2 L) (hy2 L)).2
      · exact perpSpan_inf_le_perpSpan hP hT hι hy10 hy20 hp0 (hy12 L)
          (hy1 L).symm (hy2 L).symm L.2.2
      · have h := finrank_perpSpan_inf_add_two hP hT hι hy10 hy20 (hy12 L)
          (hy1 L).symm (hy2 L).symm
        dsimp only [Y]
        omega
    let g : Lines → E := fun L => ⟨Y L, hYE L⟩
    have hginj : Function.Injective g := by
      intro L L' hLL'
      have hYeq : Y L = Y L' := congrArg Subtype.val hLL'
      have hy10 : c (y1 L) = 0 := color_eq_zero_of_adj_of_color_eq_one L.2.1 (hy1 L)
      have hy20 : c (y2 L) = 0 := color_eq_zero_of_adj_of_color_eq_one L.2.1 (hy2 L)
      have hy10' : c (y1 L') = 0 := color_eq_zero_of_adj_of_color_eq_one L'.2.1 (hy1 L')
      have hy20' : c (y2 L') = 0 := color_eq_zero_of_adj_of_color_eq_one L'.2.1 (hy2 L')
      have hsecL : sectionPoints c ι (Y L) = Γ.neighborSet L.1 :=
        sectionPoints_perpSpan_inf hP hT hι hy10 hy20 (hy12 L)
          (hy1 L).symm (hy2 L).symm
      have hsecL' : sectionPoints c ι (Y L') = Γ.neighborSet L'.1 :=
        sectionPoints_perpSpan_inf hP hT hι hy10' hy20' (hy12 L')
          (hy1 L').symm (hy2 L').symm
      have hset : Γ.neighborSet L.1 = Γ.neighborSet L'.1 := by
        rw [← hsecL, ← hsecL', hYeq]
      apply Subtype.ext
      have h1 : 1 < (Γ.neighborSet L.1).ncard := by
        rw [hdegL L]
        omega
      obtain ⟨y, hyL, hyp⟩ := Set.exists_ne_of_one_lt_ncard h1 p
      have hyL' : y ∈ Γ.neighborSet L'.1 := by
        rw [← hset]
        exact hyL
      exact eq_of_two_common_points hP (Ne.symm hyp) L.2.2.symm hyL L'.2.2.symm hyL'
    have hLines : Nat.card Lines = t + 1 := by
      have e : Lines ≃ {L : V // Γ.Adj p L} :=
        Equiv.subtypeEquivRight fun L =>
          ⟨fun h => h.2, fun h => ⟨color_eq_one_of_adj_of_color_eq_zero hp0 h, h⟩⟩
      rw [Nat.card_congr e]
      change Nat.card {L : V // Γ.Adj p L} = t + 1
      rw [show Nat.card {L : V // Γ.Adj p L} = (Γ.neighborSet p).ncard from
        Nat.card_coe_set_eq _]
      rw [ncard_neighborSet, hdeg p, if_pos hp0]
    have hEcount : Nat.card E = s + 1 := by
      haveI : FiniteDimensional K Hp := Submodule.finiteDimensional_of_le hHpA
      have hgap : finrank K Hp = finrank K E0 + 2 := by
        have hHdim := finrank_perpSpan_add_one hP hT hι hp0
        have hE0dim' : finrank K ↥(ι p ⊔ X) = 2 := hE0dim
        dsimp only [Hp, E0]
        omega
      have h' := card_submodule_between_two (K := K) (W := W) (U := E0) (X := Hp)
        hE0Hp hgap
      have hEq : Nat.card E =
          Nat.card {M : Submodule K W // E0 ≤ M ∧ M ≤ Hp ∧
            finrank K M = finrank K E0 + 1} := by
        refine Nat.card_congr (Equiv.subtypeEquivRight fun M => ?_)
        rw [hE0dim]
        constructor
        · rintro ⟨h1, h2, h3⟩
          exact ⟨h1, h2, by omega⟩
        · rintro ⟨h1, h2, h3⟩
          exact ⟨h1, h2, by omega⟩
      rw [hEq, h', card_field_eq_of_isProjGQ hP hT c hdeg hι]
    have hle : Nat.card Lines ≤ Nat.card E := Nat.card_le_card_of_injective g hginj
    rw [hLines, hEcount] at hle
    have ht' : t = ℓ * s := t_eq_mul_of_finrank_eq_five hP hT c hdeg hι hsec h5
    have h2s : 2 * s ≤ ℓ * s := Nat.mul_le_mul_right s hℓ
    have hlt : s < 2 * s := by omega
    omega
  ·
    have hS : collar c ι X = Γ.neighborSet p := by
      ext z
      constructor
      · intro hz
        have hz0 : c z = 0 := hz.1
        have hd : Γ.dist z p ≤ 2 := (hmem z hz0).1 hz
        have hne : c z ≠ c p := by rw [hz0, hp1]; decide
        have hodd : Odd (Γ.dist z p) := by
          rw [← Nat.not_even_iff_odd]
          intro heven
          exact hne ((hP.eq_iff_even_dist c z p).2 heven)
        have hle4 : Γ.dist z p ≤ 4 := hP.dist_le (by norm_num) z p
        obtain ⟨k, hk⟩ := hodd
        have h1 : Γ.dist z p = 1 := by omega
        exact (SimpleGraph.dist_eq_one_iff_adj.mp h1).symm
      · intro hz
        have hz0 : c z = 0 := color_eq_zero_of_adj_of_color_eq_one hp1 hz
        refine (hmem z hz0).2 ?_
        rw [SimpleGraph.dist_comm]
        exact le_trans (le_of_eq (SimpleGraph.dist_eq_one_iff_adj.mpr hz)) (by norm_num)
    have hpoint : ∃ z, c z = 0 ∧ ¬ Γ.Adj p z := by
      by_contra h'
      push Not at h'
      have hsub : {z : V | c z = 0} ⊆ Γ.neighborSet p := fun z hz => h' z hz
      have hsub' : (pointFinset c : Set V) ⊆ Γ.neighborSet p := by
        intro z hz
        exact hsub (by simpa using hz)
      have hcard1 : (pointFinset c : Set V).ncard ≤ (Γ.neighborSet p).ncard :=
        Set.ncard_le_ncard hsub' (Set.toFinite _)
      have hcardP : (pointFinset c : Set V).ncard = (s + 1) * (s * t + 1) := by
        rw [Set.ncard_coe_finset, card_pointFinset hP hT c hdeg]
      have hcardN : (Γ.neighborSet p).ncard = s + 1 := by
        rw [ncard_neighborSet, hdeg p, if_neg (by rw [hp1]; decide)]
      rw [hcardP, hcardN] at hcard1
      have hst : 2 * s ≤ s * t := by
        calc 2 * s = s * 2 := by ring
          _ ≤ s * t := Nat.mul_le_mul_left s ht
      have hge : (s + 1) * (2 * s + 1) ≤ (s + 1) * (s * t + 1) :=
        Nat.mul_le_mul_left (s + 1) (by omega)
      have hspos : 0 < s + 1 := by omega
      have hlt : s + 1 < (s + 1) * (2 * s + 1) := by
        rw [show (s + 1) * (2 * s + 1) = (s + 1) * (2 * s) + (s + 1) by ring]
        have : 0 < (s + 1) * (2 * s) := Nat.mul_pos hspos (by omega)
        omega
      omega
    obtain ⟨z, hz0, hzp⟩ := hpoint
    have hdist : Γ.dist z p = 3 :=
      dist_eq_three_of_not_adj_of_color_ne hP c (fun h => hzp h.symm)
        (by rw [hz0, hp1]; decide)
    let p0 : V := proj hP hdist
    have hp0adj : Γ.Adj p p0 := proj_adj hP hdist
    have hzp0 : Γ.dist z p0 = 2 := proj_dist hP hdist
    let N0 : V := commonNeighbor hP hzp0
    have hN0z : Γ.Adj z N0 := commonNeighbor_adj_left hP hzp0
    have hN0p0 : Γ.Adj N0 p0 := (commonNeighbor_adj_right hP hzp0).symm
    have hdegz : (Γ.neighborSet z).ncard = t + 1 := by
      rw [ncard_neighborSet, hdeg z, if_pos hz0]
    have h1 : 1 < (Γ.neighborSet z).ncard := by
      rw [hdegz]
      omega
    obtain ⟨N, hNz, hNne⟩ := Set.exists_ne_of_one_lt_ncard h1 N0
    have hN1 : c N = 1 := color_eq_one_of_adj_of_color_eq_zero hz0 hNz
    have hdisj : ∀ y, ¬ (Γ.Adj N y ∧ Γ.Adj p y) := by
      intro y hy
      have hyz : z ≠ y := by
        intro hzy
        have hpz : Γ.Adj p z := by simpa [hzy] using hy.2
        exact hzp hpz
      have hzy2 : Γ.dist z y = 2 :=
        dist_eq_two_of_adj_of_adj_of_ne hP hNz hy.1 hyz
      have hy_eq : y = p0 :=
        (existsUnique_proj hP hdist).unique ⟨hy.2, hzy2⟩ ⟨hp0adj, hzp0⟩
      have hNp0 : Γ.Adj N p0 := hy_eq ▸ hy.1
      have hzp0ne : z ≠ p0 := by
        intro hzp0'
        rw [hzp0'] at hzp0
        simp at hzp0
      exact hNne (eq_of_two_common_points hP hzp0ne hNz.symm hNp0 hN0z.symm hN0p0)
    obtain ⟨y, hNy, hyS⟩ := exists_adj_mem_collar hP hT hι hX1 hXA hN1
    have hyp : Γ.Adj p y := by
      rw [hS] at hyS
      exact hyS
    exact hdisj y ⟨hNy, hyp⟩

end Closure

end CFSG.Geometry.GeneralizedQuadrangles

end
