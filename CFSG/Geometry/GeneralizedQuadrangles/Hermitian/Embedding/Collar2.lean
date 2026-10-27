module

public import CFSG.Geometry.GeneralizedQuadrangles.Hermitian.Embedding.Collar
public import CFSG.Geometry.GeneralizedQuadrangles.Hermitian.Embedding.Closure2
public import CFSG.Geometry.GeneralizedQuadrangles.Hermitian.Embedding.SubquadrangleSpan

public section

namespace CFSG.Geometry.GeneralizedQuadrangles

open SimpleGraph CFSG.Geometry.GeneralizedPolygons Module

universe u

variable {V : Type u}

section Closure

variable {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj]
variable {K : Type*} [Field K] [Fintype K] {W : Type*} [AddCommGroup W] [Module K W]
variable {ι : V → Submodule K W} {A : Submodule K W}

theorem isFullSubquadrangle_collar (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hι : IsProjGQ c ι A) [FiniteDimensional K A] {ℓ : ℕ}
    (hsec : HasConstantSecants c ι A ℓ) (hℓ : 2 ≤ ℓ) (h5 : finrank K A = 5)
    {X : Submodule K W} (hX1 : finrank K X = 1) (hXA : X ≤ A)
    (hXP : ¬ ∃ v, c v = 0 ∧ ι v = X) :
    ∃ t' : ℕ, 2 ≤ t' ∧ t' * ℓ = s ∧ IsFullSubquadrangle c (collar c ι X) t' := by
  classical
  let S : Set V := collar c ι X
  have hS0 : ∀ x ∈ S, c x = 0 := fun x hx => hx.1
  have hSfull : ∀ L, c L = 1 → 2 ≤ (Γ.neighborSet L ∩ S).ncard → Γ.neighborSet L ⊆ S := by
    intro L hL h2 z hz
    have h1 : 1 < (Γ.neighborSet L ∩ S).ncard := by omega
    obtain ⟨x, hx, y, hy, hxy⟩ := (Set.one_lt_ncard (s := Γ.neighborSet L ∩ S)).mp h1
    exact mem_collar_of_two_mem_collar hP hT hι hL hx.1 hy.1 hxy hx.2 hy.2 hz
  obtain ⟨L0, hL0⟩ := exists_line hP hT c
  obtain ⟨y₀, -, hy₀S⟩ := exists_adj_mem_collar hP hT hι hX1 hXA hL0
  have hsq : ℓ ^ 2 ≤ s := sq_le_of_hasConstantSecants hP hT c hdeg hι hsec h5
  have hs2le : 2 ≤ s := two_le_s hP hT c hdeg
  have hmany : ∀ y ∈ S, 2 ≤ (fullLinesThrough Γ S y).ncard := by
    intro y hy
    have h := ncard_fullLinesThrough_collar_mul hP hT c hdeg hι hsec hℓ h5 hX1 hXA hXP hy
    have hs : ℓ ≤ s := by
      calc ℓ = ℓ * 1 := (mul_one ℓ).symm
        _ ≤ ℓ * ℓ := Nat.mul_le_mul_left ℓ (by omega)
        _ = ℓ ^ 2 := by ring
        _ ≤ s := hsq
    have hℓpos : 0 < ℓ := by omega
    have hge : 2 * ℓ ≤ (fullLinesThrough Γ S y).ncard * ℓ := by
      rw [h]
      omega
    exact Nat.le_of_mul_le_mul_right (by simpa [mul_comm] using hge) hℓpos
  have hquad : ∃ x ∈ S, ∃ y ∈ S, Γ.dist x y = 4 ∧ 2 ≤ (traceSet Γ x y ∩ S).ncard := by
    have h2lt : 1 < (fullLinesThrough Γ S y₀).ncard := by
      have := hmany y₀ hy₀S
      omega
    obtain ⟨L, hL, L', hL', hLL'⟩ :=
      (Set.one_lt_ncard (s := fullLinesThrough Γ S y₀)).mp h2lt
    have hL1 : c L = 1 := color_eq_one_of_adj_of_color_eq_zero hy₀S.1 hL.1
    have hL'1 : c L' = 1 := color_eq_one_of_adj_of_color_eq_zero hy₀S.1 hL'.1
    have hdegL : Γ.degree L = s + 1 := by
      rw [hdeg L, if_neg (by rw [hL1]; decide)]
    have hLlt : 1 < (Γ.neighborSet L).ncard := by
      rw [ncard_neighborSet]
      omega
    obtain ⟨x, hxL, hxy⟩ := Set.exists_ne_of_one_lt_ncard hLlt y₀
    have hx0 : c x = 0 := color_eq_zero_of_adj_of_color_eq_one hL1 hxL
    have hxS : x ∈ S := hL.2 hxL
    have h2ltx : 1 < (fullLinesThrough Γ S x).ncard := by
      have := hmany x hxS
      omega
    obtain ⟨N, hN, hNL⟩ := Set.exists_ne_of_one_lt_ncard h2ltx L
    have hN1 : c N = 1 := color_eq_one_of_adj_of_color_eq_zero hx0 hN.1
    have hdegN : Γ.degree N = s + 1 := by
      rw [hdeg N, if_neg (by rw [hN1]; decide)]
    have hNlt : 1 < (Γ.neighborSet N).ncard := by
      rw [ncard_neighborSet]
      omega
    obtain ⟨v, hvN, hvx⟩ := Set.exists_ne_of_one_lt_ncard hNlt x
    have hv0 : c v = 0 := color_eq_zero_of_adj_of_color_eq_one hN1 hvN
    have hvS : v ∈ S := hN.2 hvN
    have hy₀N : ¬ Γ.Adj y₀ N := by
      intro hyN
      have heq : L = N :=
        eq_of_two_common_points hP (Ne.symm hxy) hL.1.symm hxL hyN.symm hN.1.symm
      exact hNL heq.symm
    have hxy2 : Γ.dist y₀ x = 2 :=
      dist_eq_two_of_adj_of_adj_of_ne hP hL.1 hxL (Ne.symm hxy)
    have hxv : Γ.dist x v = 2 :=
      dist_eq_two_of_adj_of_adj_of_ne hP hN.1 hvN (Ne.symm hvx)
    have hvy0 : v ≠ y₀ := by
      intro h
      exact hy₀N (h ▸ hvN).symm
    have hy₀v : Γ.dist y₀ v = 4 := by
      rcases dist_eq_two_or_four_of_color_zero hP hy₀S.1 hv0 (Ne.symm hvy0) with h2 | h4
      · exfalso
        have hxperp : x ∈ ptPerp Γ c {y₀} := by
          refine ⟨hx0, ?_⟩
          intro a ha
          rw [Set.mem_singleton_iff] at ha
          subst ha
          rw [SimpleGraph.dist_comm]
          exact le_of_eq hxy2
        have hvperp : v ∈ ptPerp Γ c {y₀} := by
          refine ⟨hv0, ?_⟩
          intro a ha
          rw [Set.mem_singleton_iff] at ha
          subst ha
          rw [SimpleGraph.dist_comm]
          exact le_of_eq h2
        have hxeq : x = v :=
          eq_of_mem_ptPerp_of_adj_line hP hy₀S.1 hy₀N hN.1.symm hvN hxperp hvperp
        exact hvx hxeq.symm
      · exact h4
    have hvL' : ¬ Γ.Adj v L' := by
      intro hvL'
      have h2 : Γ.dist y₀ v = 2 :=
        dist_eq_two_of_adj_of_adj_of_ne hP hL'.1 hvL'.symm (Ne.symm hvy0)
      omega
    have hdistL' : Γ.dist v L' = 3 :=
      dist_eq_three_of_not_adj_of_color_ne hP c hvL' (by rw [hv0, hL'1]; decide)
    obtain ⟨w', ⟨hL'w, hvw⟩, -⟩ := existsUnique_proj hP hdistL'
    have hw'0 : c w' = 0 := color_eq_zero_of_adj_of_color_eq_one hL'1 hL'w
    have hw'y₀ : w' ≠ y₀ := by
      intro h
      rw [h] at hvw
      have h4 : Γ.dist v y₀ = 4 := by
        rw [SimpleGraph.dist_comm]
        exact hy₀v
      omega
    have hxL' : ¬ Γ.Adj x L' := by
      intro hxL'
      exact hLL' (eq_of_two_common_points hP (Ne.symm hxy) hL.1.symm hxL hL'.1.symm hxL'.symm)
    have hw'x : w' ≠ x := by
      intro h
      exact hxL' (h ▸ hL'w).symm
    have hw'S : w' ∈ S := hL'.2 hL'w
    have hw'y₀2 : Γ.dist y₀ w' = 2 :=
      dist_eq_two_of_adj_of_adj_of_ne hP hL'.1 hL'w (Ne.symm hw'y₀)
    have hxTrace : x ∈ traceSet Γ y₀ v := ⟨hxy2, by rw [SimpleGraph.dist_comm]; exact hxv⟩
    have hwTrace : w' ∈ traceSet Γ y₀ v := ⟨hw'y₀2, hvw⟩
    have h2card : 2 ≤ (traceSet Γ y₀ v ∩ S).ncard := by
      have h1lt : 1 < (traceSet Γ y₀ v ∩ S).ncard :=
        (Set.one_lt_ncard (s := traceSet Γ y₀ v ∩ S)).mpr
          ⟨x, ⟨hxTrace, hxS⟩, w', ⟨hwTrace, hw'S⟩, Ne.symm hw'x⟩
      omega
    exact ⟨y₀, hy₀S, v, hvS, hy₀v, h2card⟩
  obtain ⟨t', ht'1, hF⟩ := exists_isFullSubquadrangle hP hT c hdeg hS0 hSfull hquad
  have hcount :=
    ncard_fullLinesThrough_collar_mul hP hT c hdeg hι hsec hℓ h5 hX1 hXA hXP hy₀S
  have hFt : (fullLinesThrough Γ S y₀).ncard = t' + 1 := hF.2.2.1 y₀ hy₀S
  have h1 : (t' + 1) * ℓ = s + ℓ := by
    have h := hcount
    change (fullLinesThrough Γ S y₀).ncard * ℓ = s + ℓ at h
    rw [hFt] at h
    exact h
  have ht'ℓ : t' * ℓ = s := by
    have h2 : t' * ℓ + ℓ = s + ℓ := by simpa [Nat.succ_mul] using h1
    omega
  have ht'2 : 2 ≤ t' := by
    have hsge : 2 * ℓ ≤ s := by
      calc 2 * ℓ ≤ ℓ * ℓ := Nat.mul_le_mul_right ℓ hℓ
        _ = ℓ ^ 2 := by ring
        _ ≤ s := hsq
    have h : 2 * ℓ ≤ t' * ℓ := by rw [ht'ℓ]; exact hsge
    exact Nat.le_of_mul_le_mul_right h (by omega)
  exact ⟨t', ht'2, ht'ℓ, hF⟩

theorem polar_ne_ambient (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hι : IsProjGQ c ι A) [FiniteDimensional K A] {ℓ : ℕ}
    (hsec : HasConstantSecants c ι A ℓ) (hℓ : 2 ≤ ℓ) (h5 : finrank K A = 5)
    {X : Submodule K W} (hX1 : finrank K X = 1) (hXA : X ≤ A)
    (hXP : ¬ ∃ v, c v = 0 ∧ ι v = X) :
    polar c ι X ≠ A := by
  classical
  obtain ⟨t', ht'2, ht'ℓ, hF⟩ :=
    isFullSubquadrangle_collar hP hT c hdeg hι hsec hℓ h5 hX1 hXA hXP
  let P' : Set V := collar c ι X
  let c' : (Γ.induce (subquadrangleSet Γ c P')).Coloring (Fin 2) :=
    subquadrangleColoring c P'
  let B : Submodule K W := polar c ι X
  have hBA : B ≤ A := polar_le_ambient hι X
  haveI : FiniteDimensional K B := Submodule.finiteDimensional_of_le hBA
  have hP' : IsGeneralizedPolygon (Γ.induce (subquadrangleSet Γ c P')) 4 :=
    isGeneralizedPolygon_subquadrangleGraph hP hT c hdeg hF
  have hT' : IsThick (Γ.induce (subquadrangleSet Γ c P')) :=
    isThick_subquadrangleGraph hP hT c hdeg hF ht'2
  have hι' : IsProjGQ c' (fun v : subquadrangleSet Γ c P' => ι v.1) B := by
    have h := isProjGQ_subquadrangle hι hF
    simpa [B, c', P', polar] using h
  have hclosed : ∀ x ∈ P', ∀ y ∈ P', Γ.dist x y = 4 →
      sectionPoints c ι (ι x ⊔ ι y) ⊆ P' := by
    intro x hx y hy hxy z hz
    exact mem_collar_of_mem_sectionPoints_sup hP hT c hdeg hι hsec h5 hx.1 hxy hx hy hz
  have hsec' : HasConstantSecants c' (fun v : subquadrangleSet Γ c P' => ι v.1) B ℓ := by
    have h := hasConstantSecants_subquadrangle hP hι hF hsec hclosed
    simpa [B, c', P', polar, subquadrangleSet] using h
  have hdeg' : ∀ v : subquadrangleSet Γ c P', (Γ.induce (subquadrangleSet Γ c P')).degree v =
      if c' v = 0 then t' + 1 else s + 1 := by
    intro v
    rcases (show v.1 ∈ P' ∨ c v.1 = 1 ∧ Γ.neighborSet v.1 ⊆ P' from v.2) with hvP | hvL
    · have hveq : v = ⟨v.1, mem_subquadrangleSet.mpr (Or.inl hvP)⟩ := Subtype.ext rfl
      rw [hveq, degree_subquadrangleGraph_of_mem_point c hF hvP]
      have hv0 : c' v = 0 := hF.1 v.1 hvP
      rw [if_pos hv0]
    · have hveq : v =
          ⟨v.1, mem_subquadrangleSet.mpr (Or.inr (mem_subquadrangleLines.mp hvL))⟩ :=
        Subtype.ext rfl
      rw [hveq, degree_subquadrangleGraph_of_mem_line c hdeg hF hvL]
      have hv1 : c' v = 1 := (mem_subquadrangleLines.mp hvL).1
      rw [if_neg (by rw [hv1]; decide)]
  intro hBAeq
  have hB5 : finrank K B = 5 := by
    change finrank K (polar c ι X) = 5
    rw [hBAeq]
    exact h5
  have hC1 := sq_mul_eq_mul_pow hP' hT' c' hdeg' hι' hsec'
  rw [hB5, show 5 - 2 = 3 by norm_num] at hC1
  have hs2 : 0 < s ^ 2 := by
    have := two_le_s hP hT c hdeg
    positivity
  have ht'eq : t' = ℓ * s := by
    have h' : s ^ 2 * t' = s ^ 2 * (ℓ * s) := by
      calc s ^ 2 * t' = ℓ * s ^ 3 := hC1
        _ = s ^ 2 * (ℓ * s) := by ring
    exact Nat.eq_of_mul_eq_mul_left hs2 h'
  have hℓ2eq : ℓ * ℓ = 1 := by
    have hs0 : 0 < s := by
      have := two_le_s hP hT c hdeg
      omega
    have h : (ℓ * ℓ) * s = 1 * s := by
      calc (ℓ * ℓ) * s = (ℓ * s) * ℓ := by ring
        _ = t' * ℓ := by rw [ht'eq]
        _ = s := ht'ℓ
        _ = (1 : ℕ) * s := by ring
    exact Nat.eq_of_mul_eq_mul_right hs0 h
  nlinarith

theorem finrank_polar_add_one (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hι : IsProjGQ c ι A) [FiniteDimensional K A] {ℓ : ℕ}
    (hsec : HasConstantSecants c ι A ℓ) (hℓ : 2 ≤ ℓ) (h5 : finrank K A = 5)
    {X : Submodule K W} (hX1 : finrank K X = 1) (hXA : X ≤ A) :
    finrank K (polar c ι X) + 1 = finrank K A := by
  by_cases hXP : ∃ v, c v = 0 ∧ ι v = X
  · obtain ⟨p, hp, rfl⟩ := hXP
    rw [polar_eq_perpSpan hP hT hι hp]
    exact finrank_perpSpan_add_one hP hT hι hp
  · have hne := polar_ne_ambient hP hT c hdeg hι hsec hℓ h5 hX1 hXA hXP
    obtain ⟨z, hz0, hzX⟩ := exists_not_mem_collar hP hT c hdeg hι hsec hℓ h5 hX1 hXA hXP
    exact finrank_polar_add_one_of_ne hP hT hι hX1 hXA hne hz0 hzX

theorem sectionPoints_polar_eq_collar (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hι : IsProjGQ c ι A) [FiniteDimensional K A] {ℓ : ℕ}
    (hsec : HasConstantSecants c ι A ℓ) (hℓ : 2 ≤ ℓ) (h5 : finrank K A = 5)
    {X : Submodule K W} (hX1 : finrank K X = 1) (hXA : X ≤ A) :
    sectionPoints c ι (polar c ι X) = collar c ι X := by
  by_cases hXP : ∃ v, c v = 0 ∧ ι v = X
  · obtain ⟨p, hp, rfl⟩ := hXP
    rw [polar_eq_perpSpan hP hT hι hp, sectionPoints_perpSpan hP hT hι hp,
      collar_eq_ptPerp hP hT hι hp]
  · exact sectionPoints_polar_of_ne hP hT hι hX1 hXA
      (polar_ne_ambient hP hT c hdeg hι hsec hℓ h5 hX1 hXA hXP)

theorem le_perpSpan_iff_le_polar (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hι : IsProjGQ c ι A) [FiniteDimensional K A] {ℓ : ℕ}
    (hsec : HasConstantSecants c ι A ℓ) (hℓ : 2 ≤ ℓ) (h5 : finrank K A = 5)
    {X : Submodule K W} (hX1 : finrank K X = 1) (hXA : X ≤ A) {y : V} (hy : c y = 0) :
    X ≤ perpSpan c ι y ↔ ι y ≤ polar c ι X := by
  constructor
  · intro hle
    exact le_polar_of_mem_collar ⟨hy, hle⟩
  · intro hle
    have hmem : y ∈ sectionPoints c ι (polar c ι X) := ⟨hy, hle⟩
    rw [sectionPoints_polar_eq_collar hP hT c hdeg hι hsec hℓ h5 hX1 hXA] at hmem
    exact hmem.2

theorem le_polar_self_iff (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hι : IsProjGQ c ι A) [FiniteDimensional K A] {ℓ : ℕ}
    (hsec : HasConstantSecants c ι A ℓ) (hℓ : 2 ≤ ℓ) (h5 : finrank K A = 5)
    {X : Submodule K W} (hX1 : finrank K X = 1) (hXA : X ≤ A) :
    X ≤ polar c ι X ↔ ∃ v, c v = 0 ∧ ι v = X := by
  classical
  constructor
  · intro hle
    by_contra hXP
    haveI : Finite A := Module.finite_of_finite K
    haveI : Finite {M : Submodule K W // M ≤ A} := by
      haveI : Finite (Submodule K A) :=
        Finite.of_injective (fun L : Submodule K A => (L : Set A)) SetLike.coe_injective
      exact Finite.of_equiv (Submodule K A) (Submodule.MapSubtype.orderIso A).toEquiv
    let Ssub : Set (Submodule K W) :=
      {M | X ≤ M ∧ M ≤ polar c ι X ∧ finrank K M = finrank K X + 1}
    haveI : FiniteDimensional K (polar c ι X) :=
      Submodule.finiteDimensional_of_le (polar_le_ambient hι X)
    have hSsubcard : Ssub.ncard = s ^ 2 + s + 1 := by
      have hdim : finrank K (polar c ι X) = 4 := by
        have := finrank_polar_add_one hP hT c hdeg hι hsec hℓ h5 hX1 hXA
        omega
      have hgap : finrank K (polar c ι X) - finrank K X = 3 := by rw [hdim, hX1]
      have h := card_submodule_between_eq_geom_sum (K := K) (W := W) (U := X)
        (X := polar c ι X) hle
      rw [hgap] at h
      have hq : Fintype.card K = s := card_field_eq_of_isProjGQ hP hT c hdeg hι
      have hsum : (∑ i ∈ Finset.range 3, Fintype.card K ^ i) = 1 + s + s ^ 2 := by
        rw [show (3 : ℕ) = 2 + 1 by norm_num, Finset.sum_range_succ,
          show (2 : ℕ) = 1 + 1 by norm_num, Finset.sum_range_succ,
          Finset.sum_range_one, hq]
        ring
      rw [← Nat.card_coe_set_eq Ssub]
      change Nat.card {M : Submodule K W // X ≤ M ∧ M ≤ polar c ι X ∧
        finrank K M = finrank K X + 1} = s ^ 2 + s + 1
      rw [h, hsum]
      ring
    haveI : Finite Ssub :=
      Finite.of_injective (fun M : Ssub =>
        (⟨M.1, M.2.2.1.trans (polar_le_ambient hι X)⟩ : {M : Submodule K W // M ≤ A}))
        (fun a b h => Subtype.ext
          (congrArg (fun x : {M : Submodule K W // M ≤ A} => (x : Submodule K W)) h))
    have hinj : Function.Injective (fun y : {y : V // y ∈ collar c ι X} =>
        (⟨X ⊔ ι y.1, ⟨le_sup_left, sup_le hle (le_polar_of_mem_collar y.2),
          by rw [finrank_sup_eq_two_of_finrank_eq_one hX1 (hι.finrank_point y.1 y.2.1)
            (fun h => hXP ⟨y.1, y.2.1, h.symm⟩), hX1]⟩⟩ : Ssub)) := by
      intro y y' heq
      have hsup : X ⊔ ι y.1 = X ⊔ ι y'.1 := congrArg Subtype.val heq
      have hsec : sectionPoints c ι (X ⊔ ι y.1) = {y.1} :=
        (mem_collar_iff_sectionPoints_sup hP hT hι hX1 hXA hXP y.2.1).1 y.2
      have hsec' : sectionPoints c ι (X ⊔ ι y.1) = {y'.1} := by
        rw [hsup]
        exact (mem_collar_iff_sectionPoints_sup hP hT hι hX1 hXA hXP y'.2.1).1 y'.2
      have hsets : ({y.1} : Set V) = {y'.1} := by
        rw [← hsec, ← hsec', hsup]
      exact Subtype.ext (by simpa using hsets)
    have hSle : (collar c ι X).ncard ≤ s ^ 2 + s + 1 := by
      have hcardle : Nat.card {y : V // y ∈ collar c ι X} ≤ Nat.card Ssub :=
        Nat.card_le_card_of_injective _ hinj
      rw [← Nat.card_coe_set_eq (collar c ι X)]
      calc Nat.card ↥(collar c ι X) ≤ Nat.card ↥Ssub := hcardle
        _ = Ssub.ncard := Nat.card_coe_set_eq Ssub
        _ = s ^ 2 + s + 1 := hSsubcard
    let Lall : Set V := {L | c L = 1}
    have hlinecard : Nat.card Lall = (t + 1) * (s * t + 1) := by
      rw [show Nat.card Lall = (lineFinset c).card from ?_]
      · rw [card_lineFinset hP hT c hdeg]
      · have e : Lall ≃ ↥((lineFinset c : Finset V) : Set V) :=
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
    have hcol : ∀ L : Lall, 1 ≤ (Finset.univ.bipartiteAbove
        (fun (L : Lall) (y : {y : V // y ∈ collar c ι X}) => Γ.Adj L.1 y.1) L).card := by
      intro L
      obtain ⟨y, hyL, hyS⟩ := exists_adj_mem_collar hP hT hι hX1 hXA L.2
      have hmem : (⟨y, hyS⟩ : {y : V // y ∈ collar c ι X}) ∈
          (Finset.univ.bipartiteAbove
            (fun (L : Lall) (y : {y : V // y ∈ collar c ι X}) => Γ.Adj L.1 y.1) L) := by
        simp [Finset.mem_bipartiteAbove, hyL]
      exact Finset.card_pos.mpr ⟨_, hmem⟩
    have hrow : ∀ y : {y : V // y ∈ collar c ι X},
        (Finset.univ.bipartiteBelow
          (fun (L : Lall) (y : {y : V // y ∈ collar c ι X}) =>
            Γ.Adj L.1 y.1) y).card ≤ t + 1 := by
      intro y
      have hy0 : c y.1 = 0 := y.2.1
      let e : {L : Lall // Γ.Adj L.1 y.1} ≃ ↥(Γ.neighborSet y.1) :=
        { toFun := fun L => ⟨L.1.1, L.2.symm⟩
          invFun := fun L =>
            ⟨⟨L.1, color_eq_one_of_adj_of_color_eq_zero hy0 L.2⟩, L.2.symm⟩
          left_inv := fun L => Subtype.ext (Subtype.ext rfl)
          right_inv := fun L => Subtype.ext rfl }
      have hcard : (Finset.univ.bipartiteBelow
          (fun (L : Lall) (y : {y : V // y ∈ collar c ι X}) =>
            Γ.Adj L.1 y.1) y).card = Nat.card {L : Lall // Γ.Adj L.1 y.1} := by
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
        simp [Finset.bipartiteBelow]
      rw [hcard, Nat.card_congr e, Nat.card_coe_set_eq, ncard_neighborSet, hdeg y.1,
        if_pos hy0]
    have hdouble := Finset.card_mul_le_card_mul
      (r := fun (L : Lall) (y : {y : V // y ∈ collar c ι X}) => Γ.Adj L.1 y.1)
      (s := (Finset.univ : Finset Lall))
      (t := (Finset.univ : Finset {y : V // y ∈ collar c ι X})) (m := 1) (n := t + 1)
      (fun L _ => hcol L) (fun y _ => hrow y)
    have hSge : s * t + 1 ≤ (collar c ι X).ncard := by
      have hline' : Fintype.card Lall = (t + 1) * (s * t + 1) := by
        rw [← Nat.card_eq_fintype_card, hlinecard]
      have hle : (t + 1) * (s * t + 1) ≤ (collar c ι X).ncard * (t + 1) := by
        calc (t + 1) * (s * t + 1) = Fintype.card Lall := hline'.symm
          _ = Fintype.card Lall * 1 := (mul_one _).symm
          _ ≤ Fintype.card {y : V // y ∈ collar c ι X} * (t + 1) := hdouble
          _ = (collar c ι X).ncard * (t + 1) := by rw [← Set.fintypeCard_eq_ncard]
      have hle' : (t + 1) * (s * t + 1) ≤ (t + 1) * (collar c ι X).ncard := by
        rw [mul_comm (collar c ι X).ncard (t + 1)] at hle
        exact hle
      exact Nat.le_of_mul_le_mul_left hle' (by omega)
    have ht' : t = ℓ * s := t_eq_mul_of_finrank_eq_five hP hT c hdeg hι hsec h5
    have hs : 2 ≤ s := two_le_s hP hT c hdeg
    have h1 : 2 * s ^ 2 ≤ s * t := by
      rw [ht']
      calc 2 * s ^ 2 ≤ ℓ * s ^ 2 := Nat.mul_le_mul_right (s ^ 2) hℓ
        _ = s * (ℓ * s) := by ring
    have h2 : s * t + 1 ≤ s ^ 2 + s + 1 := le_trans hSge hSle
    have h1Z : (2 : ℤ) * (s : ℤ) ^ 2 ≤ (s : ℤ) * (t : ℤ) := by exact_mod_cast h1
    have h2Z : (s : ℤ) * (t : ℤ) + 1 ≤ (s : ℤ) ^ 2 + (s : ℤ) + 1 := by exact_mod_cast h2
    have hsZ : (2 : ℤ) ≤ (s : ℤ) := by exact_mod_cast hs
    nlinarith
  · rintro ⟨p, hp, rfl⟩
    rw [polar_eq_perpSpan hP hT hι hp]
    exact submodule_le_perpSpan ⟨hp, by simp⟩

theorem eq_of_polar_eq (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hι : IsProjGQ c ι A) [FiniteDimensional K A] {ℓ : ℕ}
    (hsec : HasConstantSecants c ι A ℓ) (hℓ : 2 ≤ ℓ) (h5 : finrank K A = 5)
    {X Y : Submodule K W} (hX1 : finrank K X = 1) (hXA : X ≤ A)
    (hXP : ¬ ∃ v, c v = 0 ∧ ι v = X) (hY1 : finrank K Y = 1) (hYA : Y ≤ A)
    (hYP : ¬ ∃ v, c v = 0 ∧ ι v = Y) (h : polar c ι X = polar c ι Y) :
    X = Y := by
  classical
  by_contra hXY
  have hD2 : finrank K ↥(X ⊔ Y) = 2 :=
    finrank_sup_eq_two_of_finrank_eq_one hX1 hY1 hXY
  have hDA : X ⊔ Y ≤ A := sup_le hXA hYA
  have hPXA : polar c ι X ≤ A := polar_le_ambient hι X
  have hDnotle : ¬ X ⊔ Y ≤ polar c ι X := by
    intro hle
    have hYle : Y ≤ polar c ι X := le_trans le_sup_right hle
    rw [h] at hYle
    exact hYP ((le_polar_self_iff hP hT c hdeg hι hsec hℓ h5 hY1 hYA).1 hYle)
  let D : Submodule K W := X ⊔ Y
  let R : Submodule K W := D ⊓ polar c ι X
  have hRA : R ≤ A := (inf_le_left : D ⊓ polar c ι X ≤ D).trans hDA
  have hR1 : finrank K R = 1 := by
    haveI : FiniteDimensional K D := Submodule.finiteDimensional_of_le hDA
    haveI : FiniteDimensional K (polar c ι X) := Submodule.finiteDimensional_of_le hPXA
    haveI : FiniteDimensional K R := Submodule.finiteDimensional_of_le hRA
    have hsup : D ⊔ polar c ι X = A := by
      have hle : D ⊔ polar c ι X ≤ A := sup_le hDA hPXA
      have hlt : polar c ι X < D ⊔ polar c ι X := by
        refine lt_of_le_of_ne le_sup_right ?_
        intro heq
        exact hDnotle (heq ▸ le_sup_left)
      have hdimlt := Submodule.finrank_lt_finrank_of_lt hlt
      have hXdim := finrank_polar_add_one hP hT c hdeg hι hsec hℓ h5 hX1 hXA
      have hle5 := Submodule.finrank_mono hle
      have hdimsup : finrank K ↥(D ⊔ polar c ι X) = 5 := by omega
      exact Submodule.eq_of_le_of_finrank_eq hle (by rw [hdimsup, h5])
    have h := Submodule.finrank_sup_add_finrank_inf_eq D (polar c ι X)
    rw [hsup, h5, hD2] at h
    have hXdim := finrank_polar_add_one hP hT c hdeg hι hsec hℓ h5 hX1 hXA
    dsimp only [R] at h ⊢
    omega
  have hSe : collar c ι X = collar c ι Y := by
    rw [← sectionPoints_polar_eq_collar hP hT c hdeg hι hsec hℓ h5 hX1 hXA, h,
      sectionPoints_polar_eq_collar hP hT c hdeg hι hsec hℓ h5 hY1 hYA]
  have hSsub : collar c ι X ⊆ collar c ι R := by
    intro y hy
    have hyY : y ∈ collar c ι Y := by rw [← hSe]; exact hy
    have hDHy : D ≤ perpSpan c ι y := sup_le hy.2 hyY.2
    exact ⟨hy.1, (inf_le_left : D ⊓ polar c ι X ≤ D).trans hDHy⟩
  have hmono : polar c ι X ≤ polar c ι R := by
    refine iSup_le fun y => ?_
    exact le_polar_of_mem_collar (hSsub y.2)
  haveI : FiniteDimensional K (polar c ι R) :=
    Submodule.finiteDimensional_of_le (polar_le_ambient hι R)
  have hXdim := finrank_polar_add_one hP hT c hdeg hι hsec hℓ h5 hX1 hXA
  have hRdimp := finrank_polar_add_one hP hT c hdeg hι hsec hℓ h5 hR1 hRA
  have hX4 : finrank K (polar c ι X) = 4 := by omega
  have hR4 : finrank K (polar c ι R) = 4 := by omega
  have hpolar_eq : polar c ι R = polar c ι X :=
    (Submodule.eq_of_le_of_finrank_eq hmono (by rw [hX4, hR4])).symm
  by_cases hRP : ∃ v, c v = 0 ∧ ι v = R
  · obtain ⟨p, hp0, hpR⟩ := hRP
    have hc : collar c ι X = ptPerp Γ c {p} := by
      rw [← sectionPoints_polar_eq_collar hP hT c hdeg hι hsec hℓ h5 hX1 hXA,
        ← hpolar_eq, ← hpR, polar_eq_perpSpan hP hT hι hp0,
        sectionPoints_perpSpan hP hT hι hp0]
    exact (collar_ne_ptPerp hP hT c hdeg hι hsec hℓ h5 hX1 hXA hXP p) hc
  · have hRself : R ≤ polar c ι R := by
      rw [hpolar_eq]
      exact inf_le_right
    exact hRP ((le_polar_self_iff hP hT c hdeg hι hsec hℓ h5 hR1 hRA).1 hRself)

end Closure

end CFSG.Geometry.GeneralizedQuadrangles

end
