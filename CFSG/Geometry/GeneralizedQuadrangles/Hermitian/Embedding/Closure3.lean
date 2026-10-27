module

public import CFSG.Geometry.GeneralizedQuadrangles.Hermitian.Embedding.Closure
public import CFSG.Geometry.GeneralizedQuadrangles.Hermitian.Embedding.Hyperplane

public section

namespace CFSG.Geometry.GeneralizedQuadrangles

open SimpleGraph CFSG.Geometry.GeneralizedPolygons Module

universe u

variable {V : Type u}

section Closure

variable {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj]
variable {K : Type*} [Field K] [Fintype K] {W : Type*} [AddCommGroup W] [Module K W]
variable {ι : V → Submodule K W} {A : Submodule K W}

theorem not_isPairwiseNoncollinear_of_hyperplane (hP : IsGeneralizedPolygon Γ 4)
    (hT : IsThick Γ) (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hι : IsProjGQ c ι A) [FiniteDimensional K A] {ℓ : ℕ}
    (hsec : HasConstantSecants c ι A ℓ) (hℓ : 2 ≤ ℓ) (h5 : finrank K A = 5)
    {U : Submodule K W} (hU : U ≤ A) (hhyper : finrank K U + 1 = finrank K A) :
    ¬ IsPairwiseNoncollinear Γ (sectionPoints c ι U) := by
  classical
  intro hnc
  have hs : 2 ≤ s := two_le_s hP hT c hdeg
  have ht : 2 ≤ t := two_le_t hP hT c hdeg
  have hUdim : finrank K U = 4 := by omega
  haveI : FiniteDimensional K U := Submodule.finiteDimensional_of_le hU
  have hline_notle : ∀ L, c L = 1 → ¬ ι L ≤ U := by
    intro L hL hle
    have hsub : Γ.neighborSet L ⊆ sectionPoints c ι U :=
      neighborSet_subset_of_sectionLines hι ⟨hL, hle⟩
    have h1 : 1 < (Γ.neighborSet L).ncard := by
      rw [ncard_neighborSet, hdeg L, if_neg (by rw [hL]; decide)]
      omega
    obtain ⟨x, hx, y, hy, hxy⟩ := (Set.one_lt_ncard (s := Γ.neighborSet L)).mp h1
    have h2 : Γ.dist x y = 2 := dist_eq_two_of_adj_of_adj_of_ne hP hx.symm hy hxy
    exact hnc x (hsub hx) y (hsub hy) hxy h2
  have hline_exists : ∀ L, c L = 1 → ∃ q, q ∈ sectionPoints c ι U ∧ Γ.Adj L q :=
    fun L hL => exists_sectionPoint_on_line hι hU hhyper hL (hline_notle L hL)
      (hι.le_ambient L)
  have hline_unique : ∀ L, c L = 1 → ∀ q q', q ∈ sectionPoints c ι U →
      q' ∈ sectionPoints c ι U → Γ.Adj L q → Γ.Adj L q' → q = q' := by
    intro L hL q q' hq hq' hLq hLq'
    by_contra hne
    have h2 : Γ.dist q q' = 2 := dist_eq_two_of_adj_of_adj_of_ne hP hLq.symm hLq' hne
    exact hnc q hq q' hq' hne h2
  have hLinesOne : ∀ L : {L : V // c L = 1},
      Nat.card {q : {q : V // q ∈ sectionPoints c ι U} // Γ.Adj L.1 q.1} = 1 := by
    intro L
    obtain ⟨q, hq, hLq⟩ := hline_exists L.1 L.2
    refine Nat.card_eq_one_iff_exists.mpr ⟨⟨⟨q, hq⟩, hLq⟩, ?_⟩
    rintro ⟨⟨q', hq'⟩, hLq'⟩
    exact Subtype.ext (Subtype.ext (hline_unique L.1 L.2 q' q hq' hq hLq' hLq))
  have hPoints : ∀ q : {q : V // q ∈ sectionPoints c ι U},
      Nat.card {L : {L : V // c L = 1} // Γ.Adj L.1 q.1} = t + 1 := by
    intro q
    have hq0 : c q.1 = 0 := q.2.1
    have hdegq : (Γ.neighborSet q.1).ncard = t + 1 := by
      rw [ncard_neighborSet, hdeg q.1, if_pos hq0]
    have e : {L : {L : V // c L = 1} // Γ.Adj L.1 q.1} ≃ ↥(Γ.neighborSet q.1) :=
      { toFun := fun L => ⟨L.1.1, L.2.symm⟩
        invFun := fun L => ⟨⟨L.1, color_eq_one_of_adj_of_color_eq_zero hq0 L.2⟩, L.2.symm⟩
        left_inv := fun L => Subtype.ext (Subtype.ext rfl)
        right_inv := fun L => Subtype.ext rfl }
    rw [Nat.card_congr e, Nat.card_coe_set_eq, hdegq]
  have hdouble : Nat.card {L : V // c L = 1} * 1 =
      Nat.card {q : V // q ∈ sectionPoints c ι U} * (t + 1) := by
    classical
    letI : Fintype {L : V // c L = 1} := Fintype.ofFinite _
    letI : Fintype {q : V // q ∈ sectionPoints c ι U} := Fintype.ofFinite _
    let r : {L : V // c L = 1} → {q : V // q ∈ sectionPoints c ι U} → Prop :=
      fun L q => Γ.Adj L.1 q.1
    have hm : ∀ L : {L : V // c L = 1},
        (Finset.univ.bipartiteAbove r L).card = 1 := by
      intro L
      simpa [Finset.bipartiteAbove, r, Nat.card_eq_fintype_card, Fintype.card_subtype]
        using hLinesOne L
    have hn : ∀ q : {q : V // q ∈ sectionPoints c ι U},
        (Finset.univ.bipartiteBelow r q).card = t + 1 := by
      intro q
      simpa [Finset.bipartiteBelow, r, Nat.card_eq_fintype_card, Fintype.card_subtype]
        using hPoints q
    have h := Finset.card_mul_eq_card_mul (r := r)
      (s := (Finset.univ : Finset {L : V // c L = 1}))
      (t := (Finset.univ : Finset {q : V // q ∈ sectionPoints c ι U}))
      (fun L _ => hm L) (fun q _ => hn q)
    simp only [Finset.card_univ, Nat.card_eq_fintype_card] at h
    simpa only [Nat.card_eq_fintype_card] using h
  have hlinecard : Nat.card {L : V // c L = 1} = (t + 1) * (s * t + 1) := by
    rw [show Nat.card {L : V // c L = 1} = (lineFinset c).card from ?_]
    · rw [card_lineFinset hP hT c hdeg]
    · have e : {L : V // c L = 1} ≃ ↥((lineFinset c : Finset V) : Set V) :=
        { toFun := fun L => ⟨L.1, by
            change L.1 ∈ lineFinset c
            rw [mem_lineFinset]
            exact L.2⟩
          invFun := fun L => ⟨L.1, by
            have h : L.1 ∈ lineFinset c := L.2
            rwa [mem_lineFinset] at h⟩
          left_inv := fun L => Subtype.ext rfl
          right_inv := fun L => Subtype.ext rfl }
      rw [Nat.card_congr e, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  have hScard : Nat.card {q : V // q ∈ sectionPoints c ι U} = s * t + 1 := by
    have h := hdouble
    rw [hlinecard, mul_one] at h
    rw [mul_comm (Nat.card {q : V // q ∈ sectionPoints c ι U}) (t + 1)] at h
    exact (Nat.eq_of_mul_eq_mul_left (by omega : 0 < t + 1) h).symm
  have ht' : t = ℓ * s := t_eq_mul_of_finrank_eq_five hP hT c hdeg hι hsec h5
  obtain ⟨p, hp0, hpU⟩ := exists_point_not_le_of_hyperplane hι hU hhyper
  have hpdeg : 0 < Γ.degree p := by have := hT p; omega
  obtain ⟨L, hpL⟩ := (SimpleGraph.degree_pos_iff_exists_adj (G := Γ) (v := p)).mp hpdeg
  have hL1 : c L = 1 := color_eq_one_of_adj_of_color_eq_zero hp0 hpL
  have hLnotU : ¬ ι L ≤ U := by
    intro hle
    exact hpU (((hι.adj_iff p L hp0 hL1).1 hpL).trans hle)
  obtain ⟨y, hyS, hyL⟩ := exists_sectionPoint_on_line hι hU hhyper hL1 hLnotU
    (hι.le_ambient L)
  have hy0 : c y = 0 := hyS.1
  let H := perpSpan c ι y
  have hHA : H ≤ A := perpSpan_le_ambient hι y
  haveI : FiniteDimensional K H := Submodule.finiteDimensional_of_le hHA
  have hHdim : finrank K H + 1 = finrank K A := finrank_perpSpan_add_one hP hT hι hy0
  have hUneH : U ≠ H := by
    intro hEq
    have hydeg : 0 < Γ.degree y := by have := hT y; omega
    obtain ⟨M, hyM⟩ := (SimpleGraph.degree_pos_iff_exists_adj (G := Γ) (v := y)).mp hydeg
    have hM1 : c M = 1 := color_eq_one_of_adj_of_color_eq_zero hy0 hyM
    have h1 : 1 < (Γ.neighborSet M).ncard := by
      rw [ncard_neighborSet, hdeg M, if_neg (by rw [hM1]; decide)]
      omega
    obtain ⟨y', hy'M, hy'ne⟩ := Set.exists_ne_of_one_lt_ncard h1 y
    have hy'0 : c y' = 0 := color_eq_zero_of_adj_of_color_eq_one hM1 hy'M
    have hdist : Γ.dist y y' = 2 :=
      dist_eq_two_of_adj_of_adj_of_ne hP hyM hy'M (Ne.symm hy'ne)
    have hy'S : y' ∈ sectionPoints c ι U := by
      rw [hEq, sectionPoints_perpSpan hP hT hι hy0]
      exact ⟨hy'0, by
        intro a ha
        rw [Set.mem_singleton_iff] at ha
        subst ha
        rw [SimpleGraph.dist_comm]
        exact le_of_eq hdist⟩
    exact hnc y hyS y' hy'S (Ne.symm hy'ne) hdist
  let E : Submodule K W := H ⊓ U
  have hEA : E ≤ A := inf_le_left.trans hHA
  haveI : FiniteDimensional K E := Submodule.finiteDimensional_of_le hEA
  have hhy : ι y ≤ E := le_inf (submodule_le_perpSpan ⟨hy0, by simp⟩) hyS.2
  have hEdim : finrank K E = 3 := by
    have hnotle : ¬ U ≤ H := by
      intro hle
      exact hUneH (Submodule.eq_of_le_of_finrank_eq hle (by omega))
    have hsup : H ⊔ U = A := perpSpan_sup_eq_of_not_le hP hT hι hy0 hU hnotle
    have hdimH : finrank K H = 4 := by omega
    have h := Submodule.finrank_sup_add_finrank_inf_eq H U
    rw [hsup, h5, hdimH, hUdim] at h
    dsimp only [E]
    omega
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (ι y)
  let R : Submodule K W := C ⊓ E
  have hRE : R ≤ E := inf_le_right
  have hRU : R ≤ U := hRE.trans inf_le_right
  have hRdisj : ι y ⊓ R = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro v hv
    exact (Disjoint.le_bot hC.disjoint) ⟨hv.1, hv.2.1⟩
  have hRsup : ι y ⊔ R = E := by
    refine le_antisymm (sup_le hhy hRE) ?_
    intro e he
    have htop : e ∈ (ι y) ⊔ C := by
      rw [codisjoint_iff.mp hC.codisjoint]
      exact Submodule.mem_top
    obtain ⟨a, ha, c, hc, hac⟩ := Submodule.mem_sup.mp htop
    have hcE : c ∈ E := by
      have h : c = e - a := by
        rw [← hac]
        abel
      rw [h]
      exact E.sub_mem he (hhy ha)
    exact Submodule.mem_sup.mpr ⟨a, ha, c, ⟨hc, hcE⟩, hac⟩
  have hRdim : finrank K R = 2 := by
    have hy1 : finrank K (ι y) = 1 := hι.finrank_point y hy0
    haveI : FiniteDimensional K (ι y) := Module.finite_of_finrank_pos (by rw [hy1]; norm_num)
    haveI : FiniteDimensional K R := Submodule.finiteDimensional_of_le hRE
    have h := Submodule.finrank_sup_add_finrank_inf_eq (ι y) R
    rw [hRsup, hEdim, hRdisj, finrank_bot, hy1] at h
    omega
  have hRempty : ∀ z, c z = 0 → ¬ ι z ≤ R := by
    intro z hz0 hzR
    have hzE : ι z ≤ E := hzR.trans hRE
    have hzH : ι z ≤ H := hzE.trans inf_le_left
    have hzU : ι z ≤ U := hzE.trans inf_le_right
    have hzS : z ∈ sectionPoints c ι U := ⟨hz0, hzU⟩
    have hzy : z = y := by
      by_contra hne
      have hzsec : z ∈ sectionPoints c ι H := ⟨hz0, hzH⟩
      rw [sectionPoints_perpSpan hP hT hι hy0] at hzsec
      have hle : Γ.dist z y ≤ 2 := hzsec.2 y rfl
      have h2 : Γ.dist y z = 2 := by
        rw [SimpleGraph.dist_comm]
        exact dist_eq_two_of_le_two_of_ne hP hz0 hy0 hne hle
      exact hnc y hyS z hzS (Ne.symm hne) h2
    have hyR : ι y ≤ R := by simpa [hzy] using hzR
    have hbot : ι y ≤ (⊥ : Submodule K W) := by
      rw [← hRdisj]
      exact le_inf le_rfl hyR
    have heq : ι y = ⊥ := le_antisymm hbot bot_le
    have h1 := hι.finrank_point y hy0
    rw [heq, finrank_bot] at h1
    omega
  let Fset : Set (Submodule K W) := {F | R ≤ F ∧ F ≤ U ∧ finrank K F = 3}
  haveI : Finite A := Module.finite_of_finite K
  haveI hfinU : Finite {T : Submodule K W // T ≤ A} := by
    haveI : Finite (Submodule K A) :=
      Finite.of_injective (fun L : Submodule K A => (L : Set A)) SetLike.coe_injective
    exact Finite.of_equiv (Submodule K A) (Submodule.MapSubtype.orderIso A).toEquiv
  haveI : Finite ↥Fset :=
    Finite.of_injective (fun F : Fset => (⟨F.1, F.2.2.1.trans hU⟩ :
      {T : Submodule K W // T ≤ A}))
      (fun a b h => Subtype.ext
        (congrArg (fun x : {T : Submodule K W // T ≤ A} => (x : Submodule K W)) h))
  have hFcount : Nat.card Fset = s + 1 := by
    have hgap : finrank K U = finrank K R + 2 := by omega
    have h := card_submodule_between_two (K := K) (W := W) (U := R) (X := U) hRU hgap
    have hEq : Nat.card Fset =
        Nat.card {F : Submodule K W // R ≤ F ∧ F ≤ U ∧
          finrank K F = finrank K R + 1} := by
      refine Nat.card_congr (Equiv.subtypeEquivRight fun F => ?_)
      rw [hRdim]
      constructor
      · rintro ⟨h1, h2, h3⟩
        exact ⟨h1, h2, by omega⟩
      · rintro ⟨h1, h2, h3⟩
        exact ⟨h1, h2, by omega⟩
    rw [hEq, h]
    rw [card_field_eq_of_isProjGQ hP hT c hdeg hι]
  let F_of : {q : V // q ∈ sectionPoints c ι U} → Fset := fun o =>
    ⟨R ⊔ ι o.1, ⟨le_sup_left, sup_le hRU o.2.2, by
      have hbot : R ⊓ ι o.1 = ⊥ := by
        rw [Submodule.eq_bot_iff]
        intro v hv
        by_contra hv0
        have hspan : ι o.1 = K ∙ v :=
          eq_span_singleton_of_mem_of_finrank_eq_one (hι.finrank_point o.1 o.2.1) hv.2 hv0
        have hoR : ι o.1 ≤ R := by
          rw [hspan]
          exact (Submodule.span_singleton_le_iff_mem v R).mpr hv.1
        exact hRempty o.1 o.2.1 hoR
      have ho1 : finrank K (ι o.1) = 1 := hι.finrank_point o.1 o.2.1
      haveI : FiniteDimensional K R := Submodule.finiteDimensional_of_le hRE
      haveI : FiniteDimensional K (ι o.1) :=
        Module.finite_of_finrank_pos (by rw [ho1]; norm_num)
      have h := Submodule.finrank_sup_add_finrank_inf_eq R (ι o.1)
      rw [hbot, finrank_bot, hRdim, ho1] at h
      omega⟩⟩
  letI : Fintype Fset := Fintype.ofFinite Fset
  let cF : Fset → ℕ := fun F => (sectionPoints c ι F.1).ncard
  have hsum : ∑ F : Fset, cF F = Nat.card {q : V // q ∈ sectionPoints c ι U} := by
    have hfiber : ∀ F : Fset,
        Nat.card {q : {q : V // q ∈ sectionPoints c ι U} // F_of q = F} = cF F := by
      intro F
      have e : {q : {q : V // q ∈ sectionPoints c ι U} // F_of q = F} ≃
          {q : V // q ∈ sectionPoints c ι F.1} :=
        { toFun := fun q => ⟨q.1.1, ⟨q.1.2.1, by
            have hfval : (F_of q.1).1 = F.1 := congrArg Subtype.val q.2
            exact hfval ▸ le_sup_right⟩⟩
          invFun := fun q =>
            ⟨⟨q.1, ⟨q.2.1, q.2.2.trans F.2.2.1⟩⟩, by
              have ho1 : finrank K (ι q.1) = 1 := hι.finrank_point q.1 q.2.1
              haveI : FiniteDimensional K (ι q.1) :=
                Module.finite_of_finrank_pos (by rw [ho1]; norm_num)
              haveI : FiniteDimensional K F.1 :=
                Submodule.finiteDimensional_of_le (F.2.2.1.trans hU)
              have hle : R ⊔ ι q.1 ≤ F.1 := sup_le F.2.1 q.2.2
              have hdim : finrank K ↥(R ⊔ ι q.1) = finrank K F.1 := by
                haveI : FiniteDimensional K R := Submodule.finiteDimensional_of_le hRE
                have hbot : R ⊓ ι q.1 = ⊥ := by
                  rw [Submodule.eq_bot_iff]
                  intro v hv
                  by_contra hv0
                  have hspan : ι q.1 = K ∙ v :=
                    eq_span_singleton_of_mem_of_finrank_eq_one ho1 hv.2 hv0
                  have hqR : ι q.1 ≤ R := by
                    rw [hspan]
                    exact (Submodule.span_singleton_le_iff_mem v R).mpr hv.1
                  exact hRempty q.1 q.2.1 hqR
                have h := Submodule.finrank_sup_add_finrank_inf_eq R (ι q.1)
                rw [hbot, finrank_bot, hRdim, ho1] at h
                rw [F.2.2.2]
                omega
              exact Subtype.ext (Submodule.eq_of_le_of_finrank_eq hle hdim)⟩
          left_inv := fun q => Subtype.ext (Subtype.ext rfl)
          right_inv := fun q => Subtype.ext rfl }
      rw [Nat.card_congr e, Nat.card_coe_set_eq]
    have hsigma := Nat.card_congr (Equiv.sigmaFiberEquiv F_of)
    calc ∑ F : Fset, cF F
        = ∑ F : Fset, Nat.card {q : {q : V // q ∈ sectionPoints c ι U} //
            F_of q = F} := by
          refine Finset.sum_congr rfl ?_
          intro F _
          exact (hfiber F).symm
      _ = Nat.card (Σ F : Fset, {q : {q : V // q ∈ sectionPoints c ι U} //
            F_of q = F}) := (Nat.card_sigma).symm
      _ = Nat.card {q : V // q ∈ sectionPoints c ι U} := hsigma
  have hclass : ∀ F : Fset, cF F = 0 ∨ cF F = 1 ∨ cF F = ℓ * s + 1 := by
    intro F
    change (sectionPoints c ι F.1).ncard = 0 ∨ (sectionPoints c ι F.1).ncard = 1 ∨
      (sectionPoints c ι F.1).ncard = ℓ * s + 1
    by_cases hne : (sectionPoints c ι F.1).Nonempty
    · obtain ⟨o, hoF⟩ := hne
      have ho0 : c o = 0 := hoF.1
      have hoS : o ∈ sectionPoints c ι U := ⟨ho0, hoF.2.trans F.2.2.1⟩
      by_cases hle : F.1 ≤ perpSpan c ι o
      ·
        right; left
        have hset : sectionPoints c ι F.1 = {o} := by
          refine Set.Subset.antisymm ?_ ?_
          · intro z hz
            have hzsec : z ∈ sectionPoints c ι (perpSpan c ι o) :=
              ⟨hz.1, hz.2.trans hle⟩
            rw [sectionPoints_perpSpan hP hT hι ho0] at hzsec
            have hzo : Γ.dist z o ≤ 2 := hzsec.2 o rfl
            by_contra hzne
            have h2 : Γ.dist o z = 2 := by
              rw [SimpleGraph.dist_comm]
              exact dist_eq_two_of_le_two_of_ne hP hz.1 ho0 hzne hzo
            exact hnc o hoS z ⟨hz.1, hz.2.trans F.2.2.1⟩ (Ne.symm hzne) h2
          · intro z hz
            rw [Set.mem_singleton_iff] at hz
            subst hz
            exact hoF
        rw [hset, Set.ncard_singleton]
      ·
        right; right
        let Ho : Submodule K W := perpSpan c ι o
        have hHoA : Ho ≤ A := perpSpan_le_ambient hι o
        haveI : FiniteDimensional K Ho := Submodule.finiteDimensional_of_le hHoA
        have hHodim : finrank K Ho + 1 = finrank K A := finrank_perpSpan_add_one hP hT hι ho0
        have hFdim : finrank K F.1 = 3 := F.2.2.2
        haveI : FiniteDimensional K F.1 :=
          Submodule.finiteDimensional_of_le (F.2.2.1.trans hU)
        let Ro : Submodule K W := F.1 ⊓ Ho
        have hRoF : Ro ≤ F.1 := inf_le_left
        have hRoH : Ro ≤ Ho := inf_le_right
        have hioRo : ι o ≤ Ro :=
          le_inf hoF.2 (submodule_le_perpSpan ⟨ho0, by simp⟩)
        have hRoDim : finrank K Ro = 2 := by
          haveI : FiniteDimensional K Ro := Submodule.finiteDimensional_of_le hRoF
          have hsup : Ho ⊔ F.1 = A :=
            perpSpan_sup_eq_of_not_le hP hT hι ho0 (F.2.2.1.trans hU) hle
          have h := Submodule.finrank_sup_add_finrank_inf_eq F.1 Ho
          rw [sup_comm F.1 Ho, hsup, h5] at h
          have hdimHo : finrank K Ho = 4 := by omega
          rw [hdimHo, hFdim] at h
          change finrank K ↥(F.1 ⊓ Ho) = 2
          omega
        let Nset : Set (Submodule K W) :=
          {N | ι o ≤ N ∧ N ≤ F.1 ∧ finrank K N = finrank K (ι o) + 1}
        have ho1 : finrank K (ι o) = 1 := hι.finrank_point o ho0
        have hRoMem : Ro ∈ Nset := ⟨hioRo, hRoF, by rw [hRoDim, ho1]⟩
        haveI : Finite ↥Nset :=
          Finite.of_injective (fun N : Nset =>
            (⟨N.1, N.2.2.1.trans (F.2.2.1.trans hU)⟩ :
              {T : Submodule K W // T ≤ A}))
            (fun a b h => Subtype.ext
              (congrArg (fun x : {T : Submodule K W // T ≤ A} =>
                (x : Submodule K W)) h))
        have hNcount : Nat.card Nset = s + 1 := by
          have hgap : finrank K F.1 = finrank K (ι o) + 2 := by rw [hFdim, ho1]
          change Nat.card {N : Submodule K W // ι o ≤ N ∧ N ≤ F.1 ∧
            finrank K N = finrank K (ι o) + 1} = s + 1
          rw [card_submodule_between_two (K := K) (W := W) (U := ι o) (X := F.1)
            hoF.2 hgap]
          rw [card_field_eq_of_isProjGQ hP hT c hdeg hι]
        have hNdim : ∀ N : Nset, finrank K N.1 = 2 := by
          intro N
          have h := N.2.2.2
          rw [ho1] at h
          omega
        have hsecN : ∀ N : Nset, N.1 ≠ Ro →
            (sectionPoints c ι N.1).ncard = ℓ + 1 := by
          intro N hNe
          have hN2 : finrank K N.1 = 2 := hNdim N
          have hNA : N.1 ≤ A := N.2.2.1.trans (F.2.2.1.trans hU)
          have hNnotle : ¬ N.1 ≤ Ho := by
            intro hleN
            have hleRo : N.1 ≤ Ro := le_inf N.2.2.1 hleN
            have hdim : finrank K N.1 = finrank K Ro := by rw [hN2, hRoDim]
            exact hNe (Submodule.eq_of_le_of_finrank_eq hleRo hdim)
          have hNline : ∀ L, c L = 1 → ι L ≠ N.1 := by
            intro L hL hLeq
            have hneigh : Γ.neighborSet L ⊆ sectionPoints c ι N.1 := by
              refine neighborSet_subset_of_sectionLines hι ?_
              exact ⟨hL, by rw [hLeq]⟩
            have h1 : 1 < (Γ.neighborSet L).ncard := by
              rw [ncard_neighborSet, hdeg L, if_neg (by rw [hL]; decide)]
              omega
            obtain ⟨x, hx, y', hy', hxy⟩ :=
              (Set.one_lt_ncard (s := Γ.neighborSet L)).mp h1
            have hxS : x ∈ sectionPoints c ι U := by
              have hxN := hneigh hx
              exact ⟨hxN.1, hxN.2.trans (N.2.2.1.trans F.2.2.1)⟩
            have hyS : y' ∈ sectionPoints c ι U := by
              have hyN := hneigh hy'
              exact ⟨hyN.1, hyN.2.trans (N.2.2.1.trans F.2.2.1)⟩
            have h2 : Γ.dist x y' = 2 :=
              dist_eq_two_of_adj_of_adj_of_ne hP hx.symm hy' hxy
            exact hnc x hxS y' hyS hxy h2
          have hgeo : 2 ≤ (sectionPoints c ι N.1).ncard := by
            obtain ⟨w, hw0, hwN, how⟩ :=
              exists_dist_eq_four_of_not_le_perpSpan hP hT hι ho0 hN2 N.2.1 hNA hNnotle
            have hoN : o ∈ sectionPoints c ι N.1 := ⟨ho0, N.2.1⟩
            have hwSN : w ∈ sectionPoints c ι N.1 := ⟨hw0, hwN⟩
            have hone : 1 < (sectionPoints c ι N.1).ncard :=
              (Set.one_lt_ncard (s := sectionPoints c ι N.1)).mpr
                ⟨o, hoN, w, hwSN, by intro h; rw [h] at how; simp at how⟩
            omega
          exact hsec N.1 hNA hN2 hNline hgeo
        let Nq : {q : V // q ∈ sectionPoints c ι F.1 ∧ q ≠ o} →
            {N : Submodule K W // N ∈ Nset ∧ N ≠ Ro} := fun q =>
          ⟨ι o ⊔ ι q.1, ⟨⟨le_sup_left, sup_le hoF.2 q.2.1.2, by
              have hq1 : finrank K (ι q.1) = 1 := hι.finrank_point q.1 q.2.1.1
              have hne' : ι o ≠ ι q.1 := fun h => q.2.2 (hι.injective h).symm
              have hsup2 : finrank K ↥(ι o ⊔ ι q.1) = 2 :=
                finrank_sup_eq_two_of_finrank_eq_one ho1 hq1 hne'
              rw [hsup2, ho1]⟩, by
              intro hEq
              have hqRo : ι q.1 ≤ Ro := by
                rw [← hEq]
                exact le_sup_right
              have hqH : ι q.1 ≤ Ho := hqRo.trans hRoH
              have hqsec : q.1 ∈ sectionPoints c ι Ho := ⟨q.2.1.1, hqH⟩
              rw [sectionPoints_perpSpan hP hT hι ho0] at hqsec
              have hle2 : Γ.dist q.1 o ≤ 2 := hqsec.2 o rfl
              have h2 : Γ.dist o q.1 = 2 := by
                rw [SimpleGraph.dist_comm]
                exact dist_eq_two_of_le_two_of_ne hP q.2.1.1 ho0 q.2.2 hle2
              have hqS : q.1 ∈ sectionPoints c ι U :=
                ⟨q.2.1.1, q.2.1.2.trans F.2.2.1⟩
              exact hnc o hoS q.1 hqS (Ne.symm q.2.2) h2⟩⟩
        have hfiber : ∀ N : {N : Submodule K W // N ∈ Nset ∧ N ≠ Ro},
            Nat.card {q : {q : V // q ∈ sectionPoints c ι F.1 ∧ q ≠ o} //
              Nq q = N} = ℓ := by
          intro N
          have hNqEq : ∀ q : {q : V // q ∈ sectionPoints c ι N.1 ∧ q ≠ o},
              Nq ⟨q.1, ⟨q.2.1.1, q.2.1.2.trans N.2.1.2.1⟩, q.2.2⟩ = N := by
            intro q
            apply Subtype.ext
            haveI : FiniteDimensional K N.1 :=
              Submodule.finiteDimensional_of_le (N.2.1.2.1.trans (F.2.2.1.trans hU))
            have hq1 : finrank K (ι q.1) = 1 := hι.finrank_point q.1 q.2.1.1
            have hne' : ι o ≠ ι q.1 := fun h => q.2.2 (hι.injective h).symm
            have hsup2 : finrank K ↥(ι o ⊔ ι q.1) = 2 :=
              finrank_sup_eq_two_of_finrank_eq_one ho1 hq1 hne'
            have hNd : finrank K N.1 = 2 := hNdim ⟨N.1, N.2.1⟩
            exact Submodule.eq_of_le_of_finrank_eq (sup_le N.2.1.1 q.2.1.2) (by
              rw [hsup2, hNd])
          have e : {q : {q : V // q ∈ sectionPoints c ι F.1 ∧ q ≠ o} // Nq q = N} ≃
              {q : V // q ∈ sectionPoints c ι N.1 ∧ q ≠ o} :=
            { toFun := fun q => ⟨q.1.1, ⟨q.1.2.1.1, by
                have hfval : (Nq q.1).1 = N.1 := congrArg Subtype.val q.2
                have hle : ι q.1.1 ≤ (Nq q.1).1 := le_sup_right
                exact hfval ▸ hle⟩, q.1.2.2⟩
              invFun := fun q =>
                ⟨⟨q.1, ⟨q.2.1.1, q.2.1.2.trans N.2.1.2.1⟩, q.2.2⟩, hNqEq q⟩
              left_inv := fun q => Subtype.ext (Subtype.ext rfl)
              right_inv := fun q => Subtype.ext rfl }
          rw [Nat.card_congr e]
          have hoN : o ∈ sectionPoints c ι N.1 := ⟨ho0, N.2.1.1⟩
          have hNsec : (sectionPoints c ι N.1).ncard = ℓ + 1 :=
            hsecN ⟨N.1, N.2.1⟩ N.2.2
          have e2 : {q : V // q ∈ sectionPoints c ι N.1 ∧ q ≠ o} ≃
              ↥(sectionPoints c ι N.1 \ {o}) :=
            Equiv.subtypeEquivRight fun q => by
              constructor
              · rintro ⟨hq, hne'⟩
                exact ⟨hq, by simpa using hne'⟩
              · rintro ⟨hq, hne'⟩
                exact ⟨hq, by simpa using hne'⟩
          rw [Nat.card_congr e2, Nat.card_coe_set_eq,
            Set.ncard_sdiff_singleton_of_mem hoN, hNsec]
          omega
        have hdomcard : Nat.card {q : V // q ∈ sectionPoints c ι F.1 ∧ q ≠ o} =
            (sectionPoints c ι F.1).ncard - 1 := by
          have e0 : {q : V // q ∈ sectionPoints c ι F.1 ∧ q ≠ o} ≃
              ↥(sectionPoints c ι F.1 \ {o}) :=
            Equiv.subtypeEquivRight fun q => by
              constructor
              · rintro ⟨hq, hne'⟩
                exact ⟨hq, by simpa using hne'⟩
              · rintro ⟨hq, hne'⟩
                exact ⟨hq, by simpa using hne'⟩
          rw [Nat.card_congr e0, Nat.card_coe_set_eq,
            Set.ncard_sdiff_singleton_of_mem hoF]
        have htarget : Nat.card {N : Submodule K W // N ∈ Nset ∧ N ≠ Ro} = s := by
          have e0 : {N : Submodule K W // N ∈ Nset ∧ N ≠ Ro} ≃ ↥(Nset \ {Ro}) :=
            Equiv.subtypeEquivRight fun N => by
              constructor
              · rintro ⟨hN, hNe⟩
                exact ⟨hN, by simpa using hNe⟩
              · rintro ⟨hN, hNe⟩
                exact ⟨hN, by simpa using hNe⟩
          rw [Nat.card_congr e0, Nat.card_coe_set_eq,
            Set.ncard_sdiff_singleton_of_mem hRoMem]
          have hNn : Nset.ncard = s + 1 := by
            rw [← Nat.card_coe_set_eq]
            exact hNcount
          omega
        haveI : Finite {N : Submodule K W // N ∈ Nset ∧ N ≠ Ro} :=
          Finite.of_injective (fun N : {N : Submodule K W // N ∈ Nset ∧ N ≠ Ro} =>
            (⟨N.1, N.2.1⟩ : Nset))
            (fun a b h => Subtype.ext
              (congrArg (fun x : Nset => (x : Submodule K W)) h))
        letI : Fintype {N : Submodule K W // N ∈ Nset ∧ N ≠ Ro} := Fintype.ofFinite _
        have hsig := Nat.card_congr (Equiv.sigmaFiberEquiv Nq)
        have hsum1 : Nat.card {q : V // q ∈ sectionPoints c ι F.1 ∧ q ≠ o} =
            ∑ N : {N : Submodule K W // N ∈ Nset ∧ N ≠ Ro},
              Nat.card {q : {q : V // q ∈ sectionPoints c ι F.1 ∧ q ≠ o} //
                Nq q = N} := by
          rw [← hsig, Nat.card_sigma]
        have hsum2 : Nat.card {q : V // q ∈ sectionPoints c ι F.1 ∧ q ≠ o} = ℓ * s := by
          rw [hsum1]
          calc ∑ N : {N : Submodule K W // N ∈ Nset ∧ N ≠ Ro},
                Nat.card {q : {q : V // q ∈ sectionPoints c ι F.1 ∧ q ≠ o} //
                  Nq q = N}
              = ∑ N : {N : Submodule K W // N ∈ Nset ∧ N ≠ Ro}, ℓ :=
                Finset.sum_congr rfl fun N _ => hfiber N
            _ = (Fintype.card {N : Submodule K W // N ∈ Nset ∧ N ≠ Ro}) * ℓ := by
                rw [Finset.sum_const, nsmul_eq_mul]
                simp
            _ = s * ℓ := by rw [← Nat.card_eq_fintype_card, htarget]
            _ = ℓ * s := Nat.mul_comm s ℓ
        have hpos : 0 < (sectionPoints c ι F.1).ncard :=
          (Set.ncard_pos (s := sectionPoints c ι F.1)).mpr ⟨o, hoF⟩
        omega
    ·
      left
      have hempty : sectionPoints c ι F.1 = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
      rw [hempty, Set.ncard_empty]
  let Done : Finset Fset := Finset.univ.filter fun F => cF F = 1
  let Dbig : Finset Fset := Finset.univ.filter fun F => cF F = ℓ * s + 1
  have hDone : ∀ F ∈ Done, cF F = 1 := by
    intro F hF
    simpa [Done] using hF
  have hDbig : ∀ F ∈ Dbig, cF F = ℓ * s + 1 := by
    intro F hF
    simpa [Dbig] using hF
  have hdisj : Disjoint Done Dbig := by
    rw [Finset.disjoint_left]
    intro F hF1 hF2
    have h1 := hDone F hF1
    have h2 := hDbig F hF2
    have hge : 1 < ℓ * s + 1 := by
      have : 2 * 2 ≤ ℓ * s := Nat.mul_le_mul hℓ hs
      omega
    omega
  have hzero : ∀ F ∈ (Finset.univ : Finset Fset), F ∉ Done ∪ Dbig → cF F = 0 := by
    intro F _ hF
    have hF1 : F ∉ Done := fun h => hF (Finset.mem_union_left _ h)
    have hF2 : F ∉ Dbig := fun h => hF (Finset.mem_union_right _ h)
    rcases hclass F with h0 | h1 | hbig
    · exact h0
    · exact absurd (by simpa [Done] using h1) hF1
    · exact absurd (by simpa [Dbig] using hbig) hF2
  have hsumDone : (∑ F ∈ Done, cF F) = Done.card := by
    calc ∑ F ∈ Done, cF F = ∑ F ∈ Done, 1 := Finset.sum_congr rfl hDone
      _ = Done.card := by simp
  have hsumDbig : (∑ F ∈ Dbig, cF F) = Dbig.card * (ℓ * s + 1) := by
    calc ∑ F ∈ Dbig, cF F = ∑ F ∈ Dbig, (ℓ * s + 1) := Finset.sum_congr rfl hDbig
      _ = Dbig.card * (ℓ * s + 1) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        simp
  have hsumAB : (∑ F ∈ Done ∪ Dbig, cF F) = Done.card + Dbig.card * (ℓ * s + 1) := by
    rw [Finset.sum_union hdisj, hsumDone, hsumDbig]
  have hsum_univ : (∑ F ∈ (Finset.univ : Finset Fset), cF F) =
      Done.card + Dbig.card * (ℓ * s + 1) := by
    rw [← Finset.sum_subset (Finset.subset_univ _) hzero, hsumAB]
  have hsumval : Done.card + Dbig.card * (ℓ * s + 1) = ℓ * s ^ 2 + 1 := by
    rw [← hsum_univ]
    calc ∑ F ∈ (Finset.univ : Finset Fset), cF F
        = ∑ F : Fset, cF F := rfl
      _ = Nat.card {q : V // q ∈ sectionPoints c ι U} := hsum
      _ = s * t + 1 := hScard
      _ = ℓ * s ^ 2 + 1 := by rw [ht']; ring
  have hbound : Done.card + Dbig.card ≤ s + 1 := by
    have hle : (Done ∪ Dbig).card ≤ (Finset.univ : Finset Fset).card :=
      Finset.card_le_card (Finset.subset_univ _)
    rw [Finset.card_union_of_disjoint hdisj] at hle
    have huniv : (Finset.univ : Finset Fset).card = s + 1 := by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
      exact hFcount
    omega
  by_cases hbge : s ≤ Dbig.card
  · have hmul : s * (ℓ * s + 1) ≤ Dbig.card * (ℓ * s + 1) :=
      Nat.mul_le_mul_right _ hbge
    have hle : s * (ℓ * s + 1) ≤ Done.card + Dbig.card * (ℓ * s + 1) := by omega
    have hle2 : s * (ℓ * s + 1) ≤ ℓ * s ^ 2 + 1 := by omega
    have heq : s * (ℓ * s + 1) = ℓ * s ^ 2 + s := by ring
    omega
  · have hblt : Dbig.card < s := by omega
    have hble : Dbig.card ≤ s - 1 := by omega
    have hEq : Done.card + Dbig.card * (ℓ * s + 1) =
        (Done.card + Dbig.card) + Dbig.card * (ℓ * s) := by ring
    have h1 : (Done.card + Dbig.card) + Dbig.card * (ℓ * s) ≤
        (s + 1) + (s - 1) * (ℓ * s) :=
      Nat.add_le_add hbound (Nat.mul_le_mul_right _ hble)
    have hupper : Done.card + Dbig.card * (ℓ * s + 1) ≤
        (s + 1) + (s - 1) * (ℓ * s) := hEq ▸ h1
    have hlt : (s + 1) + (s - 1) * (ℓ * s) < ℓ * s ^ 2 + 1 := by
      have hs1 : 1 ≤ s := by omega
      have hcast : (((s + 1) + (s - 1) * (ℓ * s) : ℕ) : ℤ) <
          ((ℓ * s ^ 2 + 1 : ℕ) : ℤ) := by
        have hsub : ((s - 1 : ℕ) : ℤ) = (s : ℤ) - 1 := by
          rw [Nat.cast_sub hs1]
          norm_num
        push_cast
        rw [hsub]
        nlinarith
      exact_mod_cast hcast
    omega

theorem exists_line_le_of_le_perpSpan (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hι : IsProjGQ c ι A) [FiniteDimensional K A] {ℓ : ℕ}
    (hsec : HasConstantSecants c ι A ℓ) (hℓ : 2 ≤ ℓ) (h5 : finrank K A = 5)
    {y : V} (hy : c y = 0) {M : Submodule K W} (hyM : ι y ≤ M)
    (hM : M ≤ perpSpan c ι y) (hM3 : finrank K M = 3) :
    ∃ L, c L = 1 ∧ Γ.Adj y L ∧ ι L ≤ M := by
  classical
  have hs : 2 ≤ s := two_le_s hP hT c hdeg
  have ht : 2 ≤ t := two_le_t hP hT c hdeg
  have hydeg : 0 < Γ.degree y := by have := hT y; omega
  obtain ⟨L0, hyL0⟩ := (SimpleGraph.degree_pos_iff_exists_adj (G := Γ) (v := y)).mp hydeg
  obtain ⟨w, hyw4, -⟩ := hP.exists_dist_eq hT hyL0 4 (by norm_num) (by norm_num)
  have hw0 : c w = 0 := by
    have heven : Even (Γ.dist y w) := ⟨2, by rw [hyw4]⟩
    have hc := (hP.eq_iff_even_dist c y w).2 heven
    rw [hy] at hc
    exact hc.symm
  have hw1 : finrank K (ι w) = 1 := hι.finrank_point w hw0
  let H := perpSpan c ι y
  have hHA : H ≤ A := perpSpan_le_ambient hι y
  haveI : FiniteDimensional K H := Submodule.finiteDimensional_of_le hHA
  have hHdim : finrank K H + 1 = finrank K A := finrank_perpSpan_add_one hP hT hι hy
  have hwNotH : ¬ ι w ≤ H := by
    intro hle
    have hne : w ≠ y := by
      intro h
      rw [h] at hyw4
      simp at hyw4
    have h2 := dist_eq_two_of_le_perpSpan hP hT hι hy hw0 hle hne
    omega
  let U : Submodule K W := M ⊔ ι w
  have hUA : U ≤ A := sup_le (hM.trans hHA) (hι.le_ambient w)
  haveI : FiniteDimensional K U := Submodule.finiteDimensional_of_le hUA
  have hUnotH : ¬ U ≤ H := fun hle => hwNotH (le_sup_right.trans hle)
  have hsup : H ⊔ U = A := perpSpan_sup_eq_of_not_le hP hT hι hy hUA hUnotH
  have hdisj : M ⊓ ι w = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro v hv
    by_contra hv0
    have hspan : ι w = K ∙ v :=
      eq_span_singleton_of_mem_of_finrank_eq_one hw1 hv.2 hv0
    have hle : ι w ≤ M := by
      rw [hspan]
      exact (Submodule.span_singleton_le_iff_mem v M).mpr hv.1
    exact hwNotH (hle.trans hM)
  have hUdim : finrank K U = 4 := by
    haveI : FiniteDimensional K (ι w) := Module.finite_of_finrank_pos (by rw [hw1]; norm_num)
    haveI : FiniteDimensional K M := Submodule.finiteDimensional_of_le (hM.trans hHA)
    have h := Submodule.finrank_sup_add_finrank_inf_eq M (ι w)
    rw [hdisj, finrank_bot, hM3, hw1] at h
    omega
  have hmeet : U ⊓ H = M := by
    haveI : FiniteDimensional K ↥(U ⊓ H) := Submodule.finiteDimensional_of_le inf_le_right
    haveI : FiniteDimensional K M := Submodule.finiteDimensional_of_le (hM.trans hHA)
    haveI : FiniteDimensional K U := Submodule.finiteDimensional_of_le hUA
    have h := Submodule.finrank_sup_add_finrank_inf_eq U H
    rw [sup_comm U H, hsup, h5, hUdim] at h
    have hdimH : finrank K H = 4 := by omega
    rw [hdimH] at h
    have hdim : finrank K ↥(U ⊓ H) = 3 := by omega
    exact (Submodule.eq_of_le_of_finrank_eq (le_inf le_sup_left hM)
      (by rw [hM3, hdim])).symm
  rcases section_trichotomy hP hT c hdeg hι hUA with hpen | hnc | hfull
  · obtain ⟨p, hp0, - , hcover⟩ := hpen
    obtain ⟨L, hL1, hLU, hyL⟩ := hcover y hy (hyM.trans le_sup_left)
    refine ⟨L, hL1, hyL, ?_⟩
    have hLH : ι L ≤ H := by
      refine le_of_neighborSet_subset_sectionPoints hι hL1 ?_
      intro z hz
      have hz0 : c z = 0 := color_eq_zero_of_adj_of_color_eq_one hL1 hz
      refine ⟨hz0, submodule_le_perpSpan ⟨hz0, ?_⟩⟩
      intro a ha
      rw [Set.mem_singleton_iff] at ha
      subst a
      have ht1 := hP.connected.dist_triangle (u := z) (v := L) (w := y)
      rw [SimpleGraph.dist_eq_one_iff_adj.mpr hz.symm,
        SimpleGraph.dist_eq_one_iff_adj.mpr hyL.symm] at ht1
      omega
    rw [← hmeet]
    exact le_inf hLU hLH
  · exact absurd hnc
      (not_isPairwiseNoncollinear_of_hyperplane hP hT c hdeg hι hsec hℓ h5 hUA
        (by rw [hUdim, h5]) )
  · obtain ⟨t', ht'1, hF⟩ := hfull
    have hyU : y ∈ sectionPoints c ι U := ⟨hy, hyM.trans le_sup_left⟩
    have hpos : 0 < {L : V | Γ.Adj y L ∧ Γ.neighborSet L ⊆ sectionPoints c ι U}.ncard := by
      rw [hF.2.2.1 y hyU]
      omega
    have hne : {L : V | Γ.Adj y L ∧ Γ.neighborSet L ⊆ sectionPoints c ι U}.Nonempty :=
      (Set.ncard_pos (s := {L : V | Γ.Adj y L ∧ Γ.neighborSet L ⊆ sectionPoints c ι U})).mp
        hpos
    obtain ⟨L, hyL, hLfull⟩ := hne
    have hL1 : c L = 1 := color_eq_one_of_adj_of_color_eq_zero hy hyL
    refine ⟨L, hL1, hyL, ?_⟩
    have hLU : ι L ≤ U := le_of_neighborSet_subset_sectionPoints hι hL1 hLfull
    have hLH : ι L ≤ H := by
      refine le_of_neighborSet_subset_sectionPoints hι hL1 ?_
      intro z hz
      have hz0 : c z = 0 := color_eq_zero_of_adj_of_color_eq_one hL1 hz
      refine ⟨hz0, submodule_le_perpSpan ⟨hz0, ?_⟩⟩
      intro a ha
      rw [Set.mem_singleton_iff] at ha
      subst a
      have ht1 := hP.connected.dist_triangle (u := z) (v := L) (w := y)
      rw [SimpleGraph.dist_eq_one_iff_adj.mpr hz.symm,
        SimpleGraph.dist_eq_one_iff_adj.mpr hyL.symm] at ht1
      omega
    rw [← hmeet]
    exact le_inf hLU hLH

end Closure

end CFSG.Geometry.GeneralizedQuadrangles

end
