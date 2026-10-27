module

public import CFSG.Geometry.GeneralizedQuadrangles.Hermitian.Embedding.Polar
public import CFSG.Geometry.GeneralizedQuadrangles.Hermitian.Embedding.SubspaceCount

public section

namespace CFSG.Geometry.GeneralizedQuadrangles

open SimpleGraph CFSG.Geometry.GeneralizedPolygons Module

universe u

variable {V : Type u}

section Closure

variable {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj]
variable {K : Type*} [Field K] [Fintype K] {W : Type*} [AddCommGroup W] [Module K W]
variable {ι : V → Submodule K W} {A : Submodule K W}

theorem card_field_eq_of_isProjGQ (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hι : IsProjGQ c ι A) : Fintype.card K = s := by
  classical
  obtain ⟨L, hL⟩ := exists_line hP hT c
  haveI : FiniteDimensional K (ι L) :=
    Module.finite_of_finrank_pos (by rw [hι.finrank_line L hL]; norm_num)
  let B := {M : Submodule K W // ⊥ ≤ M ∧ M ≤ ι L ∧
    finrank K M = finrank K (⊥ : Submodule K W) + 1}
  have hcard : Nat.card B = Fintype.card K + 1 :=
    card_submodule_between_two (K := K) (W := W) (U := ⊥) (X := ι L) bot_le
      (by rw [hι.finrank_line L hL, finrank_bot, zero_add])
  let invF : B → {x : V // Γ.Adj L x} := fun M =>
    let h := hι.full L hL M.1 (by rw [M.2.2.2, finrank_bot, zero_add]) M.2.2.1
    ⟨Classical.choose h, (Classical.choose_spec h).1⟩
  have hinv : ∀ M : B, ι (invF M).1 = M.1 := fun M =>
    (Classical.choose_spec (hι.full L hL M.1
      (by rw [M.2.2.2, finrank_bot, zero_add]) M.2.2.1)).2
  have hbij : Nat.card {x : V // Γ.Adj L x} = Nat.card B := by
    refine Nat.card_congr ?_
    refine
      { toFun := fun x => ⟨ι x.1, bot_le, ?_, ?_⟩
        invFun := invF
        left_inv := fun x => ?_
        right_inv := fun M => ?_ }
    · exact (hι.adj_iff x.1 L (color_eq_zero_of_adj_of_color_eq_one hL x.2) hL).1 x.2.symm
    · rw [hι.finrank_point x.1 (color_eq_zero_of_adj_of_color_eq_one hL x.2), finrank_bot,
        zero_add]
    ·
      apply Subtype.ext
      exact hι.injective (hinv ⟨ι x.1, bot_le,
        (hι.adj_iff x.1 L (color_eq_zero_of_adj_of_color_eq_one hL x.2) hL).1 x.2.symm,
        by rw [hι.finrank_point x.1 (color_eq_zero_of_adj_of_color_eq_one hL x.2),
          finrank_bot, zero_add]⟩)
    ·
      apply Subtype.ext
      exact hinv M
  have hN : Nat.card {x : V // Γ.Adj L x} = s + 1 := by
    change (Γ.neighborSet L).ncard = s + 1
    rw [ncard_neighborSet, hdeg L, if_neg (by rw [hL]; decide)]
  rw [hbij, hcard] at hN
  omega

theorem sq_mul_eq_mul_pow (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hι : IsProjGQ c ι A) [FiniteDimensional K A] {ℓ : ℕ}
    (hsec : HasConstantSecants c ι A ℓ) :
    s ^ 2 * t = ℓ * s ^ (finrank K A - 2) := by
  classical
  obtain ⟨p, hp⟩ := hP.exists_point (by norm_num) hT c
  have hp1 : finrank K (ι p) = 1 := hι.finrank_point p hp
  let H : Submodule K W := perpSpan c ι p
  have hHA : H ≤ A := perpSpan_le_ambient hι p
  haveI : FiniteDimensional K H := Submodule.finiteDimensional_of_le hHA
  have hHdim : finrank K H + 1 = finrank K A := finrank_perpSpan_add_one hP hT hι hp
  have hA2 : 2 ≤ finrank K A := by
    have hle : ι p ≤ H := submodule_le_perpSpan ⟨hp, by simp⟩
    have h1 : 1 ≤ finrank K H := by
      have := Submodule.finrank_mono hle
      rwa [hp1] at this
    omega
  have hc4 : ∀ {z : V}, Γ.dist p z = 4 → c z = 0 := by
    intro z hz
    have heven : Even (Γ.dist p z) := ⟨2, by rw [hz]⟩
    have hc := (hP.eq_iff_even_dist c p z).2 heven
    rw [hp] at hc
    exact hc.symm
  let B1 := {T : Submodule K W // ι p ≤ T ∧ T ≤ A ∧
    finrank K T = finrank K (ι p) + 1}
  let B2 := {T : Submodule K W // ι p ≤ T ∧ T ≤ H ∧
    finrank K T = finrank K (ι p) + 1}
  let S := {T : Submodule K W // ι p ≤ T ∧ T ≤ A ∧
    finrank K T = finrank K (ι p) + 1 ∧ ¬ T ≤ H}
  let Opp := {w : V // Γ.dist p w = 4}
  have hdimB1 : ∀ T : B1, finrank K T.1 = 2 := by
    intro T
    rw [T.2.2.2, hp1]
  have hdimB2 : ∀ T : B2, finrank K T.1 = 2 := by
    intro T
    rw [T.2.2.2, hp1]
  have hdimS : ∀ T : S, finrank K T.1 = 2 := by
    intro T
    rw [T.2.2.2.1, hp1]
  haveI : Finite A := Module.finite_of_finite K
  haveI hfinSub : Finite {T : Submodule K W // T ≤ A} := by
    haveI : Finite (Submodule K A) :=
      Finite.of_injective (fun L : Submodule K A => (L : Set A)) SetLike.coe_injective
    exact Finite.of_equiv (Submodule K A) (Submodule.MapSubtype.orderIso A).toEquiv
  haveI : Finite B1 :=
    Finite.of_injective (fun T : B1 => (⟨T.1, T.2.2.1⟩ : {T : Submodule K W // T ≤ A}))
      (fun _ _ h => Subtype.ext (Subtype.mk.inj h))
  haveI : Finite B2 :=
    Finite.of_injective (fun T : B2 => (⟨T.1, T.2.2.1.trans hHA⟩ : {T : Submodule K W // T ≤ A}))
      (fun _ _ h => Subtype.ext (Subtype.mk.inj h))
  haveI : Finite S :=
    Finite.of_injective (fun T : S => (⟨T.1, T.2.2.1⟩ : {T : Submodule K W // T ≤ A}))
      (fun _ _ h => Subtype.ext (Subtype.mk.inj h))
  have hfiber : ∀ T : S, Nat.card {w : Opp // ι w.1 ≤ T.1} = ℓ := by
    intro T
    haveI : FiniteDimensional K T.1 := Submodule.finiteDimensional_of_le T.2.2.1
    have hT2 : finrank K T.1 = 2 := hdimS T
    have hTline : ∀ L, c L = 1 → ι L ≠ T.1 := by
      intro L hL hLeq
      obtain ⟨w, hw0, hwT, hw4⟩ :=
        exists_dist_eq_four_of_not_le_perpSpan hP hT hι hp hT2 T.2.1 T.2.2.1 T.2.2.2.2
      have hpL : Γ.Adj p L := (hι.adj_iff p L hp hL).2 (by rw [hLeq]; exact T.2.1)
      have hwL : Γ.Adj w L := (hι.adj_iff w L hw0 hL).2 (by rw [hLeq]; exact hwT)
      have h2 : Γ.dist p w = 2 :=
        dist_eq_two_of_adj_of_adj_of_ne hP hpL hwL.symm (by rintro rfl; simp at hw4)
      omega
    have hsecT : (sectionPoints c ι T.1).ncard = ℓ + 1 := by
      refine hsec T.1 T.2.2.1 hT2 hTline ?_
      obtain ⟨w, hw0, hwT, hw4⟩ :=
        exists_dist_eq_four_of_not_le_perpSpan hP hT hι hp hT2 T.2.1 T.2.2.1 T.2.2.2.2
      have hpS : p ∈ sectionPoints c ι T.1 := ⟨hp, T.2.1⟩
      have hwS : w ∈ sectionPoints c ι T.1 := ⟨hw0, hwT⟩
      have hpw : p ≠ w := by rintro rfl; simp at hw4
      have h1 : 1 < (sectionPoints c ι T.1).ncard :=
        (Set.one_lt_ncard (s := sectionPoints c ι T.1)).mpr ⟨p, hpS, w, hwS, hpw⟩
      omega
    have hset : {w : V | Γ.dist p w = 4 ∧ ι w ≤ T.1} =
        sectionPoints c ι T.1 \ {p} := by
      ext z
      constructor
      · rintro ⟨h4, hzT⟩
        exact ⟨⟨hc4 h4, hzT⟩, by rintro rfl; simp at h4⟩
      · rintro ⟨⟨hz0, hzT⟩, hzp⟩
        have h4 : Γ.dist p z = 4 := by
          rcases dist_eq_two_or_four_of_color_zero hP hp hz0 (Ne.symm hzp) with h2 | h4
          · exfalso
            obtain ⟨L, ⟨hpL, hzL⟩, -⟩ := existsUnique_commonNeighbor hP h2
            have hL1 : c L = 1 := color_eq_one_of_adj_of_color_eq_zero hp hpL
            have hsup : ι L = ι p ⊔ ι z :=
              line_eq_sup_of_two_adjacent_points hι hp hz0 (Ne.symm hzp) hpL hzL
            have hLeq : ι L = T.1 := by
              rw [hsup]
              refine Submodule.eq_of_le_of_finrank_eq (sup_le T.2.1 hzT) ?_
              rw [finrank_sup_eq_two_of_finrank_eq_one hp1 (hι.finrank_point z hz0)
                (fun h => hzp (hι.injective h).symm), hT2]
            exact hTline L hL1 hLeq
          · exact h4
        exact ⟨h4, hzT⟩
    rw [Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter
      (fun w : V => Γ.dist p w = 4) (fun w => ι w ≤ T.1))]
    change {w : V | Γ.dist p w = 4 ∧ ι w ≤ T.1}.ncard = ℓ
    have hpS : p ∈ sectionPoints c ι T.1 := ⟨hp, T.2.1⟩
    rw [hset, Set.ncard_sdiff_singleton_of_mem hpS, hsecT]
    omega
  have hone : ∀ w : Opp, Nat.card {T : S // ι w.1 ≤ T.1} = 1 := by
    intro w
    have hw0 : c w.1 = 0 := hc4 w.2
    have hwne : w.1 ≠ p := by
      intro h
      have h4 : Γ.dist p p = 4 := by simpa [h] using w.2
      simp at h4
    let Tw : Submodule K W := ι p ⊔ ι w.1
    have hTw2 : finrank K Tw = 2 :=
      finrank_sup_eq_two_of_finrank_eq_one hp1 (hι.finrank_point w.1 hw0)
        (fun h => hwne (hι.injective h).symm)
    have hTwA : Tw ≤ A := sup_le (hι.le_ambient p) (hι.le_ambient w.1)
    have hTwH : ¬ Tw ≤ H := by
      intro hle
      have hwH : ι w.1 ≤ H := le_sup_right.trans hle
      have h2 : Γ.dist p w.1 = 2 :=
        dist_eq_two_of_le_perpSpan hP hT hι hp hw0 hwH hwne
      omega
    let TwS : S :=
      ⟨Tw, ⟨le_sup_left, hTwA, ⟨by rw [hTw2, hp1], hTwH⟩⟩⟩
    refine Nat.card_eq_one_iff_exists.mpr ⟨⟨TwS, le_sup_right⟩, ?_⟩
    rintro ⟨T, hwT⟩
    haveI : FiniteDimensional K T.1 := Submodule.finiteDimensional_of_le T.2.2.1
    apply Subtype.ext
    apply Subtype.ext
    exact (Submodule.eq_of_le_of_finrank_eq (sup_le T.2.1 hwT)
      (by rw [hTw2, hdimS T])).symm
  have hdouble : Nat.card Opp * 1 = Nat.card S * ℓ := by
    classical
    letI : Fintype Opp := Fintype.ofFinite Opp
    letI : Fintype S := Fintype.ofFinite S
    let r : Opp → S → Prop := fun w T => ι w.1 ≤ T.1
    have hm : ∀ w : Opp, (Finset.univ.bipartiteAbove r w).card = 1 := by
      intro w
      simpa [Finset.bipartiteAbove, r, Nat.card_eq_fintype_card, Fintype.card_subtype]
        using hone w
    have hn : ∀ T : S, (Finset.univ.bipartiteBelow r T).card = ℓ := by
      intro T
      simpa [Finset.bipartiteBelow, r, Nat.card_eq_fintype_card, Fintype.card_subtype]
        using hfiber T
    have h := Finset.card_mul_eq_card_mul (r := r) (s := (Finset.univ : Finset Opp))
      (t := (Finset.univ : Finset S)) (fun w _ => hm w) (fun T _ => hn T)
    simp only [Finset.card_univ, Nat.card_eq_fintype_card] at h
    simpa only [Nat.card_eq_fintype_card] using h
  have hOpp : Nat.card Opp = s ^ 2 * t := by
    rw [show Nat.card Opp = ({w : V | Γ.dist p w = 4}).ncard from Nat.card_coe_set_eq _]
    have hset : {w : V | Γ.dist p w = 4} =
        ((Finset.univ.filter fun y => Γ.dist p y = 4) : Set V) := by
      ext w
      simp
    rw [hset, Set.ncard_coe_finset, card_opposite hP hT c hdeg hp]
  let splitEquiv : B1 ≃ B2 ⊕ S :=
    { toFun := fun T => if h : T.1 ≤ H then Sum.inl ⟨T.1, T.2.1, h, T.2.2.2⟩
        else Sum.inr ⟨T.1, T.2.1, T.2.2.1, T.2.2.2, h⟩
      invFun := fun U => match U with
        | Sum.inl T => ⟨T.1, T.2.1, T.2.2.1.trans hHA, T.2.2.2⟩
        | Sum.inr T => ⟨T.1, T.2.1, T.2.2.1, T.2.2.2.1⟩
      left_inv := by
        intro T
        by_cases h : T.1 ≤ H <;> simp [h]
      right_inv := by
        intro U
        rcases U with T | T
        · simp [T.2.2.1]
        · simp [T.2.2.2.2] }
  have hsplit : Nat.card B1 = Nat.card B2 + Nat.card S := by
    rw [← Nat.card_sum]
    exact Nat.card_congr splitEquiv
  have hB1 : Nat.card B1 = ∑ i ∈ Finset.range (finrank K A - 1), Fintype.card K ^ i := by
    have h := card_submodule_between_eq_geom_sum (K := K) (W := W) (U := ι p) (X := A)
      (hι.le_ambient p)
    simpa [B1, hp1] using h
  have hB2 : Nat.card B2 = ∑ i ∈ Finset.range (finrank K A - 2), Fintype.card K ^ i := by
    have h := card_submodule_between_eq_geom_sum (K := K) (W := W) (U := ι p) (X := H)
      (submodule_le_perpSpan ⟨hp, by simp⟩)
    have hgap : finrank K H - finrank K (ι p) = finrank K A - 2 := by omega
    rw [hgap] at h
    simpa [B2] using h
  have hS : Nat.card S = Fintype.card K ^ (finrank K A - 2) := by
    have hgeom : (∑ i ∈ Finset.range (finrank K A - 1), Fintype.card K ^ i) =
        (∑ i ∈ Finset.range (finrank K A - 2), Fintype.card K ^ i) +
          Fintype.card K ^ (finrank K A - 2) := by
      have hd : finrank K A - 1 = (finrank K A - 2) + 1 := by omega
      rw [hd, Finset.sum_range_succ]
    have h1 : Nat.card B2 + Nat.card S =
        Nat.card B2 + Fintype.card K ^ (finrank K A - 2) := by
      rw [← hsplit, hB1, hgeom, hB2]
    exact Nat.add_left_cancel h1
  have hq : Fintype.card K = s := card_field_eq_of_isProjGQ hP hT c hdeg hι
  rw [hOpp, hS, hq, mul_one] at hdouble
  rwa [Nat.mul_comm (s ^ (finrank K A - 2)) ℓ] at hdouble

theorem t_eq_mul_of_finrank_eq_five (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hι : IsProjGQ c ι A) [FiniteDimensional K A] {ℓ : ℕ}
    (hsec : HasConstantSecants c ι A ℓ) (h5 : finrank K A = 5) :
    t = ℓ * s := by
  have h := sq_mul_eq_mul_pow hP hT c hdeg hι hsec
  rw [h5, show 5 - 2 = 3 by norm_num] at h
  have hs : 0 < s ^ 2 := by
    have := two_le_s hP hT c hdeg
    positivity
  have h' : s ^ 2 * (ℓ * s) = ℓ * (s ^ 2 * s) := by ring
  exact Nat.eq_of_mul_eq_mul_left hs (h.trans h'.symm)

theorem sq_le_of_hasConstantSecants (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hι : IsProjGQ c ι A) [FiniteDimensional K A] {ℓ : ℕ}
    (hsec : HasConstantSecants c ι A ℓ) (h5 : finrank K A = 5) :
    ℓ ^ 2 ≤ s := by
  classical
  obtain ⟨p, hp⟩ := hP.exists_point (by norm_num) hT c
  have hs : 2 ≤ s := two_le_s hP hT c hdeg
  have ht : 2 ≤ t := two_le_t hP hT c hdeg
  have hOpp : 0 < (Finset.univ.filter fun y => Γ.dist p y = 4).card := by
    rw [card_opposite hP hT c hdeg hp]
    positivity
  obtain ⟨y, hy⟩ := Finset.card_pos.mp hOpp
  rw [Finset.mem_filter] at hy
  have hpy : Γ.dist p y = 4 := hy.2
  have hy0 : c y = 0 := by
    have heven : Even (Γ.dist p y) := ⟨2, by rw [hpy]⟩
    have hc := (hP.eq_iff_even_dist c p y).2 heven
    rw [hp] at hc
    exact hc.symm
  let U : Submodule K W := ι p ⊔ ι y
  have hU2 : finrank K U = 2 :=
    finrank_sup_eq_two_of_finrank_eq_one (hι.finrank_point p hp) (hι.finrank_point y hy0)
      (fun h => by
        have hpy' : p = y := hι.injective h
        rw [hpy'] at hpy
        simp at hpy)
  have hUA : U ≤ A := sup_le (hι.le_ambient p) (hι.le_ambient y)
  have hline : ∀ L, c L = 1 → ι L ≠ U := by
    intro L hL hLeq
    have hpL : Γ.Adj p L := (hι.adj_iff p L hp hL).2 (by rw [hLeq]; exact le_sup_left)
    have hyL : Γ.Adj y L := (hι.adj_iff y L hy0 hL).2 (by rw [hLeq]; exact le_sup_right)
    have h2 : Γ.dist p y = 2 :=
      dist_eq_two_of_adj_of_adj_of_ne hP hpL hyL.symm (by rintro rfl; simp at hpy)
    omega
  have hge : 2 ≤ (sectionPoints c ι U).ncard := by
    have hpS : p ∈ sectionPoints c ι U := ⟨hp, le_sup_left⟩
    have hyS : y ∈ sectionPoints c ι U := ⟨hy0, le_sup_right⟩
    have h1 : 1 < (sectionPoints c ι U).ncard :=
      (Set.one_lt_ncard (s := sectionPoints c ι U)).mpr
        ⟨p, hpS, y, hyS, by rintro rfl; simp at hpy⟩
    omega
  have hsecU : (sectionPoints c ι U).ncard = ℓ + 1 := hsec U hUA hU2 hline hge
  let X : Finset V := (sectionPoints c ι U).toFinset
  have hXcard : X.card = ℓ + 1 := by
    rw [show X.card = (sectionPoints c ι U).ncard by
      rw [Set.ncard_eq_toFinset_card']]
    exact hsecU
  have hXsub : (X : Set V) ⊆ spanSet Γ p y := by
    rw [show (X : Set V) = sectionPoints c ι U from Set.coe_toFinset _]
    exact sectionPoints_sup_subset_spanSet hP hT hι hp hpy
  have hm : 2 ≤ X.card := by rw [hXcard]; omega
  have hmul := mul_le_sq_of_subset_span hP hT c hdeg hp hpy hXsub hm
  rw [hXcard] at hmul
  have hm1 : ℓ + 1 - 1 = ℓ := by omega
  rw [hm1] at hmul
  have ht' : t = ℓ * s := t_eq_mul_of_finrank_eq_five hP hT c hdeg hι hsec h5
  rw [ht'] at hmul
  have h' : s * ℓ ^ 2 ≤ s * s := by
    calc
      s * ℓ ^ 2 = ℓ * (ℓ * s) := by ring
      _ ≤ s ^ 2 := hmul
      _ = s * s := by ring
  exact Nat.le_of_mul_le_mul_left h' (by omega)

theorem iSup_traceSet_eq_perpSpan_inf (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hι : IsProjGQ c ι A) [FiniteDimensional K A] {ℓ : ℕ}
    (hsec : HasConstantSecants c ι A ℓ) (h5 : finrank K A = 5) {x y : V} (hx : c x = 0)
    (hxy : Γ.dist x y = 4) :
    ⨆ u : {u : V // u ∈ traceSet Γ x y}, ι u.1 = perpSpan c ι x ⊓ perpSpan c ι y := by
  classical
  have hy0 : c y = 0 := by
    have heven : Even (Γ.dist x y) := ⟨2, by rw [hxy]⟩
    have hc := (hP.eq_iff_even_dist c x y).2 heven
    rw [hx] at hc
    exact hc.symm
  let D : Submodule K W := ⨆ u : {u : V // u ∈ traceSet Γ x y}, ι u.1
  have hDle : D ≤ perpSpan c ι x ⊓ perpSpan c ι y := by
    refine iSup_le fun u => le_inf ?_ ?_
    · have hu0 : c u.1 = 0 := color_eq_zero_of_dist_eq_two hP hx u.2.1
      exact submodule_le_perpSpan ⟨hu0, by
        intro a ha
        rw [Set.mem_singleton_iff] at ha
        subst ha
        simpa [SimpleGraph.dist_comm] using u.2.1.le⟩
    · have hu0 : c u.1 = 0 := color_eq_zero_of_dist_eq_two hP hx u.2.1
      exact submodule_le_perpSpan ⟨hu0, by
        intro a ha
        rw [Set.mem_singleton_iff] at ha
        subst ha
        simpa [SimpleGraph.dist_comm] using u.2.2.le⟩
  have hxA : perpSpan c ι x ≤ A := perpSpan_le_ambient hι x
  have hyA : perpSpan c ι y ≤ A := perpSpan_le_ambient hι y
  haveI : FiniteDimensional K (perpSpan c ι x) := Submodule.finiteDimensional_of_le hxA
  haveI : FiniteDimensional K (perpSpan c ι y) := Submodule.finiteDimensional_of_le hyA
  haveI : FiniteDimensional K D :=
    Submodule.finiteDimensional_of_le (hDle.trans (inf_le_left.trans hxA))
  have hyH : ι y ≤ perpSpan c ι y := submodule_le_perpSpan ⟨hy0, by simp⟩
  have hHne : perpSpan c ι x ≠ perpSpan c ι y := by
    intro hEq
    have hle : ι y ≤ perpSpan c ι x := hEq ▸ hyH
    have h2 : Γ.dist x y = 2 :=
      dist_eq_two_of_le_perpSpan hP hT hι hx hy0 hle (by rintro rfl; simp at hxy)
    omega
  have hnotle : ¬ perpSpan c ι y ≤ perpSpan c ι x := by
    intro hle
    have h2 : Γ.dist x y = 2 :=
      dist_eq_two_of_le_perpSpan hP hT hι hx hy0 (hyH.trans hle) (by rintro rfl; simp at hxy)
    omega
  have hsup : perpSpan c ι x ⊔ perpSpan c ι y = A :=
    perpSpan_sup_eq_of_not_le hP hT hι hx hyA hnotle
  have hxdim := finrank_perpSpan_add_one hP hT hι hx
  have hydim := finrank_perpSpan_add_one hP hT hι hy0
  haveI : FiniteDimensional K ↥(perpSpan c ι x ⊓ perpSpan c ι y) :=
    Submodule.finiteDimensional_of_le inf_le_left
  have hinf3 : finrank K ↥(perpSpan c ι x ⊓ perpSpan c ι y) = 3 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq
      (perpSpan c ι x) (perpSpan c ι y)
    rw [hsup, h5] at h
    omega
  have htracecard : (traceSet Γ x y).ncard = t + 1 := by
    rw [ncard_trace hP hxy, hdeg x, if_pos hx]
  have htrace3 : 3 ≤ (traceSet Γ x y).ncard := by
    have := two_le_t hP hT c hdeg
    omega
  obtain ⟨u, hu, v, hv, huv⟩ :=
    (Set.one_lt_ncard (s := traceSet Γ x y)).mp (by omega)
  have hu0 : c u = 0 := color_eq_zero_of_dist_eq_two hP hx hu.1
  have hv0 : c v = 0 := color_eq_zero_of_dist_eq_two hP hx hv.1
  have huv2 : finrank K ↥(ι u ⊔ ι v) = 2 :=
    finrank_sup_eq_two_of_finrank_eq_one (hι.finrank_point u hu0) (hι.finrank_point v hv0)
      (fun h => huv (hι.injective h))
  have hleD : ι u ⊔ ι v ≤ D :=
    sup_le (le_iSup (fun w : {w : V // w ∈ traceSet Γ x y} => ι w.1) ⟨u, hu⟩)
      (le_iSup (fun w : {w : V // w ∈ traceSet Γ x y} => ι w.1) ⟨v, hv⟩)
  have hD2le : 2 ≤ finrank K D := by
    have := Submodule.finrank_mono hleD
    omega
  have hDline : ∀ L, c L = 1 → ι L ≠ D := by
    intro L hL hLeq
    have huL : Γ.Adj u L := (hι.adj_iff u L hu0 hL).2 (by rw [hLeq]; exact le_sup_left.trans hleD)
    have hvL : Γ.Adj v L := (hι.adj_iff v L hv0 hL).2 (by rw [hLeq]; exact le_sup_right.trans hleD)
    have h2 : Γ.dist u v = 2 :=
      dist_eq_two_of_adj_of_adj_of_ne hP huL hvL.symm huv
    have h4 : Γ.dist u v = 4 := dist_eq_four_of_mem_trace hP hxy hu hv huv
    omega
  have hDtrace : traceSet Γ x y ⊆ sectionPoints c ι D := by
    intro w hw
    have hw0 : c w = 0 := color_eq_zero_of_dist_eq_two hP hx hw.1
    exact ⟨hw0, le_iSup (fun z : {z : V // z ∈ traceSet Γ x y} => ι z.1) ⟨w, hw⟩⟩
  have hDge2 : 2 ≤ (sectionPoints c ι D).ncard := by
    have h := Set.ncard_le_ncard hDtrace (Set.toFinite _)
    omega
  have hD3 : finrank K D = 3 := by
    by_contra hne
    have hle3 : finrank K D ≤ 3 := by
      have := Submodule.finrank_mono hDle
      omega
    have hD2 : finrank K D = 2 := by omega
    have hsecD : (sectionPoints c ι D).ncard = ℓ + 1 :=
      hsec D (hDle.trans (inf_le_left.trans hxA)) hD2 hDline hDge2
    have ht' : t = ℓ * s := t_eq_mul_of_finrank_eq_five hP hT c hdeg hι hsec h5
    have hle : (traceSet Γ x y).ncard ≤ (sectionPoints c ι D).ncard :=
      Set.ncard_le_ncard hDtrace (Set.toFinite _)
    have hs : 2 ≤ s := two_le_s hP hT c hdeg
    have hls_le : ℓ * s ≤ ℓ := by omega
    have h2l_le : 2 * ℓ ≤ ℓ * s := by
      calc 2 * ℓ = ℓ * 2 := by ring
        _ ≤ ℓ * s := Nat.mul_le_mul_left ℓ hs
    have hℓpos : 0 < ℓ := by
      rcases Nat.eq_zero_or_pos ℓ with h | h
      · rw [h, zero_mul] at ht'
        omega
      · exact h
    omega
  have hDeq : D = perpSpan c ι x ⊓ perpSpan c ι y :=
    Submodule.eq_of_le_of_finrank_eq hDle (by rw [hD3, hinf3])
  exact hDeq

theorem exists_not_mem_collar (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hι : IsProjGQ c ι A) [FiniteDimensional K A] {ℓ : ℕ}
    (hsec : HasConstantSecants c ι A ℓ) (hℓ : 2 ≤ ℓ) (h5 : finrank K A = 5)
    {X : Submodule K W} (hX1 : finrank K X = 1) (hXA : X ≤ A)
    (hXP : ¬ ∃ v, c v = 0 ∧ ι v = X) :
    ∃ z, c z = 0 ∧ z ∉ collar c ι X := by
  classical
  by_contra h
  push Not at h
  let B := {T : Submodule K W // X ≤ T ∧ T ≤ A ∧ finrank K T = finrank K X + 1}
  haveI : Finite A := Module.finite_of_finite K
  haveI hfinSub : Finite {T : Submodule K W // T ≤ A} := by
    haveI : Finite (Submodule K A) :=
      Finite.of_injective (fun L : Submodule K A => (L : Set A)) SetLike.coe_injective
    exact Finite.of_equiv (Submodule K A) (Submodule.MapSubtype.orderIso A).toEquiv
  haveI : Finite B :=
    Finite.of_injective (fun T : B => (⟨T.1, T.2.2.1⟩ : {T : Submodule K W // T ≤ A}))
      (fun _ _ h => Subtype.ext (Subtype.mk.inj h))
  let f : {z : V // c z = 0} → B := fun z =>
    ⟨X ⊔ ι z.1, ⟨le_sup_left, sup_le hXA (hι.le_ambient z.1),
      by rw [finrank_sup_eq_two_of_finrank_eq_one hX1 (hι.finrank_point z.1 z.2)
        (fun hEq => hXP ⟨z.1, z.2, hEq.symm⟩)]; omega⟩⟩
  have hinj : Function.Injective f := by
    intro z z' hzz'
    have hz : sectionPoints c ι (X ⊔ ι z.1) = {z.1} :=
      (mem_collar_iff_sectionPoints_sup hP hT hι hX1 hXA hXP z.2).1 (h z.1 z.2)
    have hz' : sectionPoints c ι (X ⊔ ι z'.1) = {z'.1} :=
      (mem_collar_iff_sectionPoints_sup hP hT hι hX1 hXA hXP z'.2).1 (h z'.1 z'.2)
    have heq : X ⊔ ι z.1 = X ⊔ ι z'.1 := congrArg Subtype.val hzz'
    have hs : ({z.1} : Set V) = {z'.1} := by rw [← hz, ← hz', heq]
    apply Subtype.ext
    simpa using hs
  have hcard_le : Nat.card {z : V // c z = 0} ≤ Nat.card B :=
    Nat.card_le_card_of_injective f hinj
  have hcardP : Nat.card {z : V // c z = 0} = (s + 1) * (s * t + 1) := by
    rw [show Nat.card {z : V // c z = 0} = ({z : V | c z = 0}).ncard from
      Nat.card_coe_set_eq _]
    have hset : {z : V | c z = 0} = (pointFinset c : Set V) := by
      ext z
      simp
    rw [hset, Set.ncard_coe_finset, card_pointFinset hP hT c hdeg]
  have hcardB : Nat.card B = ∑ i ∈ Finset.range 4, Fintype.card K ^ i := by
    have h' := card_submodule_between_eq_geom_sum (K := K) (W := W) (U := X) (X := A) hXA
    have hgap : finrank K A - finrank K X = 4 := by omega
    rw [hgap] at h'
    simpa [B] using h'
  have hle : (s + 1) * (s * t + 1) ≤ ∑ i ∈ Finset.range 4, Fintype.card K ^ i := by
    rw [← hcardP, ← hcardB]
    exact hcard_le
  have hq : Fintype.card K = s := card_field_eq_of_isProjGQ hP hT c hdeg hι
  rw [hq] at hle
  have hsum : (∑ i ∈ Finset.range 4, s ^ i) = 1 + s + s ^ 2 + s ^ 3 := by
    norm_num [Finset.sum_range_succ]
  rw [hsum] at hle
  have ht : t = ℓ * s := t_eq_mul_of_finrank_eq_five hP hT c hdeg hι hsec h5
  rw [ht] at hle
  have hs : 2 ≤ s := two_le_s hP hT c hdeg
  have h2s : 2 * s ≤ ℓ * s := Nat.mul_le_mul_right s hℓ
  nlinarith

end Closure

end CFSG.Geometry.GeneralizedQuadrangles

end
